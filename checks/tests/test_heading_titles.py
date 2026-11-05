"""Small native PDF regression for references within unnumbered titles."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import fitz
from pypdf import PdfReader, PdfWriter

ROOT = Path(os.environ.get('BOOK_TEST_ROOT', Path(__file__).resolve().parents[2]))
sys.path.insert(0, str(ROOT / 'scripts'))
from build import normalize_outline_destinations
STYLES = ('book-style.typ', 'main-defs.typ', 'note-layout.typ',
          'numbering.typ', 'statements.typ')
DRIVER = '''#import "content/book-style.typ": book-style
#import "content/main-defs.typ": reference-rules, metadata-value
#import "content/numbering.typ": section-counter
#show: book-style
#set page(header: none, footer: none)
#section-counter.update(48)
#counter(heading).update((6, 48))
FORWARD @ss:appendix

CAPTION @ss:appendix[the appendix]
#pagebreak()
== Probe <sec:probe>
INSERT
=== Basic Formulas <ss:base>
BASEBODY.
#context assert(counter(heading).get() == (6, 49, LETTER))
#pagebreak()
#heading(level: 4, numbering: none)[
  Appendix to §#strong[#emph[@ss:base]]#footnote[NOTEBODY]
] <ss:appendix>
APPENDIXBODY.
#context {
  assert(counter(heading).get() == (6, 49, LETTER))
}
#pagebreak()
=== Next Part <ss:next>
NEXTBODY.
#context assert(counter(heading).get() == (6, 49, NEXTCOUNT))
BACKWARD @ss:appendix
'''


class HeadingTitleTests(unittest.TestCase):
    def fixture(self, root, source):
        (root / 'content').mkdir()
        for name in STYLES:
            shutil.copyfile(ROOT / 'content' / name, root / 'content' / name)
        shutil.copytree(ROOT / 'assets/fonts', root / 'fonts')
        shutil.copyfile(ROOT / 'editorial.bib', root / 'editorial.bib')
        (root / 'sample.typ').write_text(source)

    def run_typst(self, root, *args):
        command, *tail = args
        source = [str(root / 'sample.typ'), *tail]
        if command == 'query':
            command = 'eval'
            source = ['--in', str(root / 'sample.typ'), 'query(' + tail[0] + ')']
        return subprocess.run(
            ['typst', command, '--root', str(root), '--font-path', str(root / 'fonts'),
             '--ignore-system-fonts', *source],
            capture_output=True, text=True, timeout=45)

    def destination(self, reader, page, link):
        # Inspect actual native /XYZ values. MuPDF's raw null-left handling
        # varies by version; do not confuse PDF bottom-origin with layout y.
        for entry in reader.pages[page.number].get('/Annots', []):
            annotation = entry.get_object()
            rect = list(map(float, annotation['/Rect']))
            if abs(rect[0] - link['from'].x0) < .05 and abs(
                    float(reader.pages[page.number].mediabox.height) - rect[3]
                    - link['from'].y0) < .05:
                dest = annotation.get('/Dest', annotation.get('/A', {}).get('/D'))
                if isinstance(dest, str):
                    dest = reader.named_destinations[dest].dest_array
                self.assertEqual(dest[1], '/XYZ')
                self.assertEqual(dest[0].idnum,
                                 reader.pages[link['page']].indirect_reference.idnum)
                return float(reader.pages[link['page']].mediabox.height) - float(dest[3])
        self.fail('No corresponding native PDF annotation')

    def test_real_pdf_forward_backward_destinations_and_counter_shift(self):
        for inserted, with_note in ((False, True), (True, True), (False, False)):
            with self.subTest(inserted=inserted, with_note=with_note), tempfile.TemporaryDirectory(
                    prefix='heading-title-', dir='/tmp') as td:
                root = Path(td)
                source = DRIVER.replace('INSERT', '=== Earlier <ss:earlier>' if inserted else '')
                source = source.replace('LETTER', str(1 + inserted)).replace('NEXTCOUNT', str(2 + inserted))
                if not with_note:
                    source = source.replace('#footnote[NOTEBODY]', '')
                self.fixture(root, source)
                result = self.run_typst(root, 'compile')
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stderr, '')
                doc = fitz.open(root / 'sample.pdf')
                reader = PdfReader(root / 'sample.pdf')
                self.assertEqual(len(doc), 4)
                name = 'Appendix to §49' + ('B' if inserted else 'A')
                for page, marker, printed in ((doc[0], 'FORWARD', name),
                                               (doc[0], 'CAPTION', 'the appendix'),
                                               (doc[3], 'BACKWARD', name)):
                    box = page.search_for(marker)[0]
                    links = [link for link in page.get_links()
                             if abs(link['from'].y0 - box.y0) < 4]
                    self.assertEqual(len(links), 2 if marker == 'CAPTION' else 1,
                                     (marker, links))
                    link = links[0]
                    area = fitz.Rect(link['from'])
                    for piece in links[1:]:
                        area |= piece['from']
                        self.assertEqual(piece['page'], link['page'])
                        self.assertEqual(self.destination(reader, page, piece),
                                         self.destination(reader, page, link))
                    self.assertEqual(page.get_textbox(area).strip(), printed)
                    self.assertEqual(link['page'], 2)
                    heading = doc[2].search_for('Appendix to')[0]
                    top = self.destination(reader, page, link)
                    self.assertLessEqual(top, heading.y0 + 2)
                    self.assertLess(heading.y0 - top, 20)
                # Only the title's own number navigates back to Basic Formulas.
                parent_links = [link for link in doc[2].get_links() if link['page'] == 1]
                self.assertEqual(len(parent_links), 1)
                parent = doc[1].search_for('Basic Formulas')[0]
                top = self.destination(reader, doc[2], parent_links[0])
                self.assertLessEqual(top, parent.y0 + 2)
                self.assertLess(parent.y0 - top, 20)
                result = self.run_typst(root, 'query', 'metadata')
                self.assertEqual(result.returncode, 0, result.stderr)
                values = [it['value'] for it in json.loads(result.stdout)]
                refs = [it for it in values if isinstance(it, dict)
                        and it.get('kind') == 'cross-reference'
                        and it['target'] == 'ss:appendix']
                self.assertEqual(len(refs), 3)
                self.assertTrue(all(it['resolved'] and it['printed'] == name for it in refs))
                self.assertNotIn('NOTEBODY', doc[0].get_text() + doc[3].get_text())
                titles = [it for it in values if isinstance(it, dict)
                          and it.get('kind') == 'bookmark-title']
                self.assertEqual([it['title'] for it in titles], [name])
                writer = PdfWriter(root / 'sample.pdf', incremental=True)
                normalize_outline_destinations(writer, reader, left=0, titles=titles)
                writer.write(root / 'normalized.pdf')
                normalized = fitz.open(root / 'normalized.pdf')
                appendix = [it for it in normalized.get_toc(simple=False)
                            if it[1] == name]
                self.assertEqual(len(appendix), 1)
                self.assertEqual(appendix[0][2], 3)
                self.assertLess(appendix[0][3]['to'].y,
                                normalized[2].search_for('Appendix to')[0].y0)

    def test_missing_nested_target_stays_unresolved(self):
        with tempfile.TemporaryDirectory(prefix='heading-missing-', dir='/tmp') as td:
            root = Path(td)
            self.fixture(root, '''#import "content/main-defs.typ": reference-rules
#show: reference-rules
@ss:appendix
#heading(level: 4, numbering: none)[Appendix to §@ss:missing] <ss:appendix>
''')
            result = self.run_typst(root, 'query', 'metadata')
            self.assertEqual(result.returncode, 0, result.stderr)
            refs = [it['value'] for it in json.loads(result.stdout)
                    if isinstance(it['value'], dict)
                    and it['value'].get('kind') == 'cross-reference']
            self.assertEqual({it['target'] for it in refs}, {'ss:appendix', 'ss:missing'})
            self.assertTrue(all(not it['resolved'] for it in refs))

    def test_cyclic_title_has_bounded_diagnostic(self):
        with tempfile.TemporaryDirectory(prefix='heading-cycle-', dir='/tmp') as td:
            root = Path(td)
            self.fixture(root, '''#import "content/main-defs.typ": reference-rules
#show: reference-rules
@ss:a
#heading(level: 4, numbering: none)[A @ss:b] <ss:a>
#heading(level: 4, numbering: none)[B @ss:a] <ss:b>
''')
            result = self.run_typst(root, 'compile')
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Cyclic heading title:', result.stderr)

    def test_ambiguous_nested_target_has_explicit_diagnostic(self):
        with tempfile.TemporaryDirectory(prefix='heading-ambiguous-', dir='/tmp') as td:
            root = Path(td)
            self.fixture(root, '''#import "content/main-defs.typ": reference-rules
#show: reference-rules
@ss:appendix
#heading(level: 4, numbering: none)[First] <ss:duplicate>
#heading(level: 4, numbering: none)[Second] <ss:duplicate>
#heading(level: 4, numbering: none)[Appendix to @ss:duplicate] <ss:appendix>
''')
            result = self.run_typst(root, 'compile')
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Ambiguous heading title target: ss:duplicate', result.stderr)

    def test_original_serializer_rejects_the_actual_native_ref_node(self):
        with tempfile.TemporaryDirectory(prefix='heading-old-', dir='/tmp') as td:
            root = Path(td)
            self.fixture(root, '''#let old(body) = {
  if body.has("text") { return body.text }
  if body.func() in ([ ].func(), linebreak) { return " " }
  if body.has("children") { return body.children.map(old).join() }
  if body.has("child") { return old(body.child) }
  if body.has("body") { return old(body.body) }
  panic("Unsupported content in a heading with a note: " + repr(body))
}
#heading(level: 3, numbering: "1")[Basic] <ss:base>
#heading(level: 4, numbering: none)[Appendix to §@ss:base] <ss:appendix>
#context old(query(<ss:appendix>).first().body)
''')
            result = self.run_typst(root, 'compile')
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Unsupported content in a heading with a note: ref(', result.stderr)


if __name__ == '__main__':
    unittest.main()
