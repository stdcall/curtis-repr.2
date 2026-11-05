"""Native mathematical attachments and plain bookmark titles.

BOOK_NOTE_LAYOUT supplies an optional helper for compatibility fixtures.
"""
import ast
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import fitz
from pypdf import PdfReader, PdfWriter
from pypdf.generic import ArrayObject, FloatObject, NameObject, NullObject
from pypdf.generic import TextStringObject

ROOT = Path(os.environ.get('BOOK_TEST_ROOT', Path(__file__).resolve().parents[2]))
STYLES = ('book-style.typ', 'main-defs.typ', 'note-layout.typ',
          'numbering.typ', 'statements.typ')
CASES = (
    ('$D_G$', 'D_G'),
    ('$"GL"_n$', 'GLₙ'),
    ('$S_x$', 'Sₓ'),
    ('$Phi_g$', 'Φ_g'),
    ('$D_(G H)$', 'D_(G H)'),
    ('$D_(G_n)$', 'D_(Gₙ)'),
    ('$D_(n+1)^(-2)$', 'Dₙ₊₁⁻²'),
    ("$D'$", 'D′'),
    ("$D''$", 'D″'),
    ('$D^G$', 'Dᴳ'),
    ('$D^Phi$', 'D^Φ'),
    ('$lr((1_B))^G$', '(1_B)ᴳ'),
)
PREAMBLE = '''#import "content/book-style.typ": book-style
#import "content/main-defs.typ": metadata-value
#import "content/note-layout.typ": title-text, title-data
#show: book-style
#set page(header: none)
'''


def normalize(writer, reader, titles):
    # Extract only this pure, pinned PDF function, never run build's module.
    path = ROOT / 'scripts/build.py'
    tree = ast.parse(path.read_text())
    fn = next(n for n in tree.body if isinstance(n, ast.FunctionDef)
              and n.name == 'normalize_outline_destinations')
    namespace = {k: v for k, v in globals().items() if k in (
        'ArrayObject', 'FloatObject', 'NameObject', 'NullObject', 'TextStringObject')}
    exec(compile(ast.Module(body=[fn], type_ignores=[]), str(path), 'exec'), namespace)
    return namespace[fn.name](writer, reader, left=0, titles=titles)


class OutlineAttachmentTests(unittest.TestCase):
    def fixture(self, name, source):
        output = os.environ.get('FIXTURE_OUTPUT')
        if output:
            root = Path(output) / name
            root.mkdir(parents=True, exist_ok=True)
        else:
            temp = tempfile.TemporaryDirectory(prefix='title-script-', dir='/tmp')
            self.addCleanup(temp.cleanup)
            root = Path(temp.name)
        (root / 'content').mkdir(exist_ok=True)
        for name in STYLES:
            path = ROOT / 'content' / name
            if name == 'note-layout.typ' and os.environ.get('BOOK_NOTE_LAYOUT'):
                path = Path(os.environ['BOOK_NOTE_LAYOUT'])
            shutil.copyfile(path, root / 'content' / name)
        (root / 'sample.typ').write_text(source)
        options = ['--root', str(root), '--ignore-system-fonts',
                   '--font-path', str(ROOT / 'assets/fonts')]
        for command, args in (
            ('compile', [str(root / 'sample.typ'), str(root / 'raw.pdf')]),
            ('eval', ['''{
              import "/content/main-defs.typ": metadata-value
              (metadata: query(metadata).map(m => (
                 value: metadata-value(m), position: m.location().position())),
               headings: query(heading).map(h => (
                 label: h.at("label", default: none),
                 counter: counter(heading).at(h.location()),
                 position: h.location().position(), body: repr(h.body))))
            }''', '--in', str(root / 'sample.typ')]),
        ):
            proc = subprocess.run(['typst', command, *options, *args],
                capture_output=True, text=True, timeout=45)
            (root / (command + '.log')).write_text(proc.stderr)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertEqual(proc.stderr, '')
            if command == 'eval':
                (root / 'metadata.json').write_text(proc.stdout)
        data = json.loads((root / 'metadata.json').read_text())
        titles = [m['value'] for m in data['metadata']
                  if m['value'].get('kind') == 'bookmark-title']
        raw = PdfReader(root / 'raw.pdf')
        writer = PdfWriter(root / 'raw.pdf', incremental=True)
        normalize(writer, raw, titles)
        writer.write(root / 'normalized.pdf')
        pdf = PdfReader(root / 'normalized.pdf')
        def outlines(items):
            for item in items:
                if isinstance(item, list):
                    yield from outlines(item)
                else:
                    d = item.dest_array
                    self.assertEqual(str(d[1]), '/XYZ')
                    self.assertEqual(float(d[2]), 0)
                    self.assertIsInstance(d[4], NullObject)
                    yield item.title, pdf.get_destination_page_number(item), float(d[3])
        actual = list(outlines(pdf.outline))
        (root / 'outlines.json').write_text(json.dumps(actual, ensure_ascii=False, indent=2))
        before, after = fitz.open(root / 'raw.pdf'), fitz.open(root / 'normalized.pdf')
        for i, (a, b) in enumerate(zip(before, after), 1):
            self.assertEqual(a.get_pixmap(dpi=108).samples, b.get_pixmap(dpi=108).samples)
            self.assertEqual(a.get_texttrace(), b.get_texttrace())
            self.assertEqual(b.get_images(), [])
            for span in b.get_texttrace():
                for char in span['chars']:
                    self.assertNotEqual(char[1], 0)
                    self.assertTrue(b.rect.contains(fitz.Rect(char[3])))
            b.get_pixmap(dpi=108).save(root / f'page-{i}.png')
        return root, data, actual

    def test_numbered_math_headings_preserve_register_and_attachments(self):
        source = PREAMBLE + '''#outline(title: [Engineering contents])
#pagebreak()
= Engineering
== Attachment serialization <sec:engineering>
Numbered native target @ss:case-0.

'''
        for i, (math, expected) in enumerate(CASES):
            source += f'=== {math} <ss:case-{i}>\nNative body control {i}.\n\n'
        root, data, outlines = self.fixture('math', source)
        expected = ['§ 1' + chr(65+i) + '. ' + item[1] for i, item in enumerate(CASES)]
        actual = [title for title, page, top in outlines if title.startswith('§ 1') and
                  not title.startswith('§ 1.')]
        self.assertEqual(actual, expected)
        heading_titles = [m['value']['title'] for m in data['metadata']
                          if m['value'].get('kind') == 'bookmark-title']
        self.assertEqual(heading_titles, expected)
        refs = [m['value'] for m in data['metadata']
                if m['value'].get('kind') == 'cross-reference']
        self.assertEqual(len(refs), 1)
        self.assertEqual(refs[0]['printed'], '1A')
        self.assertTrue(refs[0]['resolved'])
        # Parent/section counters remain native; no attachment changes them.
        self.assertEqual([h['counter'] for h in data['headings'][-len(CASES):]],
                         [[1, 1, i+1] for i in range(len(CASES))])

    def test_styled_note_title_and_forward_backward_plain_reference(self):
        source = PREAMBLE + '''= Engineering
== Plain title control <sec:control>
FORWARD @app:math

#heading(level: 4, numbering: none)[
  Appendix #strong[#emph[$D_G$]]#footnote[Only the original title has this note.]
] <app:math>
BACKWARD @app:math
#context {
  assert(title-text($D_(i j)$) == "D_(i j)")
  assert(title-text($D_("ij")$) == "Dᵢⱼ")
  assert(title-text($D_(n G)$) == "D_(n G)")
  assert(title-text($D_gamma$) == "Dᵧ")
  assert(title-text($D_g$) == "D_g")
  assert(title-text(math.attach([D], bl: [n], tr: math.primes(2))) == "ₙD″")
  assert(title-text(math.attach([D], tr: math.primes(5))) == "D⁗′")
  assert(title-text(math.attach([D], b: [n], br: [x]))
    == "attach(D, b: n, br: x)")
  assert(not title-data(math.attach([D], b: [@ss:missing])).resolved)
}
'''
        root, data, outlines = self.fixture('note-reference', source)
        titles = [m['value']['title'] for m in data['metadata']
                  if m['value'].get('kind') == 'bookmark-title']
        self.assertEqual(titles, ['Appendix D_G'])
        refs = [m['value'] for m in data['metadata']
                if m['value'].get('kind') == 'cross-reference']
        self.assertEqual(len(refs), 2)
        self.assertTrue(all(m['printed'] == 'Appendix D_G' and m['resolved'] for m in refs))
        notes = [m['value'] for m in data['metadata']
                 if m['value'].get('kind') == 'footnote-placement']
        self.assertEqual(len(notes), 1)
        self.assertEqual(notes[0]['marker-page'], notes[0]['entry-page'])
        reader = PdfReader(root / 'normalized.pdf')
        links = [a.get_object() for p in reader.pages for a in p.get('/Annots', [])]
        # Two external-to-title native references, plus note and return routes.
        self.assertEqual(len(links), 4)
        destinations = []
        for a in links:
            dest = a.get('/Dest', a.get('/A', {}).get('/D'))
            if isinstance(dest, str):
                dest = reader.named_destinations[dest].dest_array
            self.assertEqual(str(dest[1]), '/XYZ')
            if a.get('/Dest') == 'app:math':
                destinations.append((dest[0].idnum, float(dest[3])))
        self.assertEqual(len(destinations), 2)
        self.assertEqual(destinations[0], destinations[1])

    def test_existing_plain_note_and_nested_reference_titles(self):
        source = PREAMBLE + '''= Engineering
== Unchanged control <sec:control>
=== Basic Formulas <ss:base>
#heading(level: 4, numbering: none)[
  Appendix to §#strong[#emph[@ss:base]]#footnote[Original note.]
] <app:plain>
Plain target @app:plain.
'''
        root, data, outlines = self.fixture('plain-control', source)
        titles = [m['value']['title'] for m in data['metadata']
                  if m['value'].get('kind') == 'bookmark-title']
        self.assertEqual(titles, ['Appendix to §1A'])
        self.assertEqual(outlines[-1][0], 'Appendix to §1A')



    def test_native_smartquotes_preserve_math_bookmarks_and_heading_note(self):
        source = PREAMBLE + '''#import "content/main-defs.typ": ed-note
= Engineering
== Quote serialization
=== Solomon's theorem for $S_n$
Native APOS body.
=== The "quoted" title for $S_n$
Native DOUBLE body.
=== A reader's heading#ed-note[Complete heading entry.] for $S_n$
Native NOTE body.
=== Existing $S_n$ and $X'$ heading
Native CONTROL body.
'''
        root, data, outlines = self.fixture('native-quotes', source)
        expected = ["§ 1A. Solomon's theorem for Sₙ",
                    '§ 1B. The "quoted" title for Sₙ',
                    "§ 1C. A reader's heading for Sₙ",
                    '§ 1D. Existing Sₙ and X′ heading']
        actual = [title for title, page, top in outlines
                  if title.startswith(('§ 1A.', '§ 1B.', '§ 1C.', '§ 1D.'))]
        self.assertEqual(actual, expected)
        notes = [m['value'] for m in data['metadata']
                 if m['value'].get('kind') == 'footnote-placement']
        self.assertEqual(len(notes), 1)
        self.assertEqual(notes[0]['marker-page'], notes[0]['entry-page'])
        doc = fitz.open(root / 'normalized.pdf')
        text = ''.join(page.get_text() for page in doc)
        for token in ('APOS', 'DOUBLE', 'NOTE', 'CONTROL', 'Complete heading entry.'):
            self.assertIn(token, text)


if __name__ == '__main__':
    unittest.main()
