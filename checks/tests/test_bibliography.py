"""Exercise the production bibliography through small actual Typst PDFs."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import tempfile
import unittest

import fitz

ROOT = Path(__file__).resolve().parents[2]
STYLES = (
    'bibliography-data.typ', 'bibliography-style.typ', 'book-style.typ',
    'main-defs.typ', 'note-layout.typ', 'numbering.typ', 'statements.typ',
)
FONTS = (
    'LibertinusSerif-Regular.otf', 'LibertinusSerif-Italic.otf',
    'LibertinusSerif-Semibold.otf', 'LibertinusSerif-Bold.otf',
    'STIXTwoMath-Regular.otf',
)

# Synthetic records only: no network requests or claims about real DOIs.
FIXTURE_BIB = '''@book{Probe2000,
  author = {Probe, A.},
  title = {Alpha title},
  year = {2000},
  publisher = {Fixture Press},
  doi = {10.5555/fixture.alpha},
  related = {Component2002},
  annotation = {{title}. {publisher}, {year}. Related: {Component2002.title},
    {Component2002.journal}, {Component2002.pages}.},
}
@book{Other2001,
  author = {Other, B.},
  title = {Internal-only source},
  year = {2001},
  annotation = {{title}.},
}
@article{Component2002,
  author = {Component, C.},
  title = {Component before},
  year = {2002},
  journal = {Full fixture journal},
  shortjournal = {J. Fixture Before},
  pages = {101-109},
  doi = {10.5555/component.before},
}
'''

# This exact driver is reused for every mutation. Descriptions occur only
# in the BibLaTeX fixture; Typst holds structure, keys and displayed tags.
DRIVER = '''#import "content/book-style.typ": book-style
#import "content/statements.typ": bib-item
#import "content/bibliography-style.typ": bib-group, bib-description
#show: book-style
#set page(header: none, footer: none, numbering: "1")
#counter(page).update(1)
Main citation @bib:Probe2000 and duplicate @bib:Probe2000.
#pagebreak()
The second page has a citation only in its note.
#footnote[Footnote-only citation @bib:Probe2000.]
#pagebreak()
#metadata((kind: "bibliography-boundary", enter: true))
#bib-group("Probe2000")
#bib-item(tag: "00a")[#bib-description("Probe2000")] <bib:Probe2000>
#bib-group("Other2001")
#bib-item(tag: "01")[
  #bib-description("Other2001")
  See @bib:Probe2000 and @bib:Other2001.
] <bib:Other2001>
#metadata((kind: "bibliography-boundary", enter: false))
'''


class Bibliography(unittest.TestCase):
    def test_adjacent_short_items_have_disjoint_page_backlinks(self):
        with tempfile.TemporaryDirectory(prefix='adjacent-bib-links-', dir='/tmp') as td:
            root = Path(td)
            self.fixture(root)
            (root / 'references.bib').write_text('''@book{ShortA,
  author = {Probe, A.},
  title = {Alpha},
  year = {2000},
  annotation = {{title}.},
}
@book{ShortB,
  author = {Probe, A.},
  title = {Beta},
  year = {2001},
  annotation = {{title}.},
}
''')
            (root / 'sample.typ').write_text('''#import "content/book-style.typ": book-style
#import "content/statements.typ": bib-item
#import "content/bibliography-style.typ": bib-description
#show: book-style
#set page(header: none, footer: none, numbering: "1")
Main citations @bib:ShortA and @bib:ShortB.
#pagebreak()
#metadata((kind: "bibliography-boundary", enter: true))
#bib-item(tag: "00")[#bib-description("ShortA")] <bib:ShortA>
#bib-item(tag: "01")[#bib-description("ShortB")] <bib:ShortB>
#metadata((kind: "bibliography-boundary", enter: false))
''')
            path = root / 'sample.pdf'
            self.typst(root, 'compile', str(path))
            with fitz.open(path) as document:
                self.assertEqual(len(document), 2)
                backlinks = document[1].get_links()
                self.assertEqual(len(backlinks), 2)
                for link in backlinks:
                    self.assertEqual(link['kind'], fitz.LINK_GOTO)
                    self.assertEqual(link['page'], 0)
                    self.assertGreater(link['from'].width, 0)
                    self.assertGreater(link['from'].height, 0)
                self.assertTrue((backlinks[0]['from'] & backlinks[1]['from']).is_empty)

    def fixture(self, root):
        (root / 'content').mkdir()
        (root / 'assets/fonts').mkdir(parents=True)
        for name in STYLES:
            shutil.copyfile(ROOT / 'content' / name, root / 'content' / name)
        for name in FONTS:
            shutil.copyfile(ROOT / 'assets/fonts' / name,
                            root / 'assets/fonts' / name)
        (root / 'references.bib').write_text(FIXTURE_BIB)
        (root / 'editorial.bib').write_text('')
        (root / 'sample.typ').write_text(DRIVER)

    def typst(self, root, command, *arguments):
        completed = subprocess.run(
            ['typst', command, '--root', str(root), '--ignore-system-fonts',
             '--font-path', str(root / 'assets/fonts'),
             '--input', 'stage=final',
             *(['--in', str(root / 'sample.typ'), *arguments]
               if command == 'eval' else
               [str(root / 'sample.typ'), *arguments])],
            capture_output=True, text=True, timeout=60)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(completed.stderr, '', 'Warnings fail the fixture')
        return completed.stdout

    def compile(self, root, name):
        path = root / name
        self.typst(root, 'compile', str(path))
        with fitz.open(path) as document:
            self.assertEqual(len(document), 3)
            pages = [' '.join(page.get_text().split()) for page in document]
            links = [(number + 1, item)
                     for number, page in enumerate(document)
                     for item in page.get_links()]
            self.assertFalse(any(page.get_images() for page in document))
        return pages, links

    def metadata(self, root):
        result = self.typst(root, 'eval', '''{ import "/content/main-defs.typ": metadata-value
        query(metadata).map(it => (
          value: if type(it.value) == dictionary and "position" not in it.value {
            (..metadata-value(it), position: it.location().position())
          } else { metadata-value(it) },
          position: it.location().position(),
        )) }''')
        return [item for item in json.loads(result)
                if isinstance(item['value'], dict)]

    @staticmethod
    def uris(links):
        return {item['uri'] for _, item in links if 'uri' in item}

    @staticmethod
    def typst_hashes(root):
        return {str(path.relative_to(root)):
                hashlib.sha256(path.read_bytes()).hexdigest()
                for path in root.rglob('*.typ')}

    def replace_fields(self, root, changes):
        path = root / 'references.bib'
        text = path.read_text()
        for before, after in changes:
            self.assertEqual(text.count(before), 1, before)
            text = text.replace(before, after)
        path.write_text(text)

    def test_wrapped_caption_anchor_stays_with_clickable_text(self):
        with tempfile.TemporaryDirectory(prefix='bibliography-wrap-', dir='/tmp') as td:
            root = Path(td)
            self.fixture(root)
            driver = '''#import "content/book-style.typ": book-style
#import "content/statements.typ": bib-item
#import "content/bibliography-style.typ": bib-group, bib-description
#show: book-style
#set page(header: none, footer: none, numbering: "1")
'''
            for width in (280, 290, 300, 310, 320):
                driver += (f'Probe #h({width}pt) '
                           '@bib:Probe2000[Longauthor–Otherauthor, '
                           'Theorem~13].\n\n')
            for width in (338, 340):
                driver += f'Probe #h({width}pt) @bib:Probe2000[CR §~10].\n\n'
            for width in (338, 340, 345):
                driver += (f'Probe #h({width}pt) '
                           '@bib:Probe2000[\\[67, p.~128\\]].\n\n')
            driver += '''#pagebreak()
#bib-group("Probe2000")
#bib-item[#bib-description("Probe2000")] <bib:Probe2000>
'''
            (root / 'sample.typ').write_text(driver)
            self.typst(root, 'compile', str(root / 'wrapped.pdf'))
            records = [dict(item['value'], position=item['position'])
                       for item in self.metadata(root)
                       if item['value'].get('kind') == 'cross-reference']
            self.assertEqual(len(records), 10)
            with fitz.open(root / 'wrapped.pdf') as document:
                text = ' '.join(' '.join(page.get_text() for page in document).split())
                self.assertEqual(text.count('CR § 10'), 2)
                for page in document:
                    for block in page.get_text('dict')['blocks']:
                        for line in block.get('lines', []):
                            shown = ''.join(s['text'] for s in line['spans'])
                            self.assertFalse(shown.rstrip().endswith('['), shown)
                    for link in page.get_links():
                        self.assertGreater(link['from'].width, 0)
                        self.assertGreater(link['from'].height, 0)
                for record in records:
                    position = record['position']
                    x, y = (float(position[name][:-2]) for name in ('x', 'y'))
                    matches = [link for link in document[position['page'] - 1].get_links()
                               if abs(link['from'].x0 - x) < .03
                               and link['from'].y0 - .03 <= y <= link['from'].y1 + .03]
                    self.assertEqual(len(matches), 1, position)
                    destination = record['target-position']
                    self.assertEqual(matches[0]['page'] + 1, destination['page'])
                    self.assertAlmostEqual(matches[0]['to'].y,
                                           float(destination['y'][:-2]) - 10,
                                           delta=.03)

    def test_editorial_record_updates_note_link_and_description(self):
        with tempfile.TemporaryDirectory(prefix='bibliography-editorial-', dir='/tmp') as td:
            root = Path(td)
            self.fixture(root)
            editorial = root / 'editorial.bib'
            editorial.write_text('''@book{Addendum2003,
  author = {Addendum, D.},
  title = {Editorial before},
  year = {2003},
  doi = {10.5555/editorial.before},
  annotation = {{title}, {year}.},
}
''')
            driver = (root / 'sample.typ').read_text()
            driver = driver.replace('#show: book-style',
                                    '#import "content/main-defs.typ": ed-note\n#show: book-style')
            driver = driver.replace('#footnote[Footnote-only citation @bib:Probe2000.]',
                                    '#footnote[Footnote-only citation @bib:Probe2000.]\n'
                                    '#ed-note[Editorial note Addendum @bib:Addendum2003.]')
            driver = driver.replace('#metadata((kind: "bibliography-boundary", enter: false))',
                                    '#bib-group("Addendum2003")\n'
                                    '#bib-item[#bib-description("Addendum2003")] <bib:Addendum2003>\n'
                                    '#metadata((kind: "bibliography-boundary", enter: false))')
            (root / 'sample.typ').write_text(driver)
            hashes = self.typst_hashes(root)
            pages, links = self.compile(root, 'editorial-before.pdf')
            self.assertIn('Editorial before', pages[2])
            self.assertIn('https://doi.org/10.5555/editorial.before', self.uris(links))
            editorial.write_text(editorial.read_text().replace('Editorial before', 'Editorial after')
                                 .replace('editorial.before', 'editorial.after'))
            self.assertEqual(hashes, self.typst_hashes(root))
            pages, links = self.compile(root, 'editorial-after.pdf')
            self.assertIn('Editorial after', pages[2])
            self.assertNotIn('Editorial before', pages[2])
            self.assertIn('https://doi.org/10.5555/editorial.after', self.uris(links))
            self.assertNotIn('https://doi.org/10.5555/editorial.before', self.uris(links))
            backlinks = [item for item in self.metadata(root)
                         if item['value'].get('kind') == 'page-reference'
                         and item['value'].get('target') == 'bib-mention:bib:Addendum2003']
            self.assertEqual([item['value']['description'] for item in backlinks], ['2'])
            # Actual GoTo annotations return to the note on page2.
            self.assertTrue(any(page == 3 and link.get('page') == 1
                                for page, link in links if link['kind'] == fitz.LINK_GOTO))

    def test_unexpanded_related_work_does_not_borrow_its_doi(self):
        with tempfile.TemporaryDirectory(prefix='bibliography-related-', dir='/tmp') as td:
            root = Path(td)
            self.fixture(root)
            self.replace_fields(root, [
                ('Related: {Component2002.title},\n    {Component2002.journal}, {Component2002.pages}.', ''),
                ('title = {Component before},',
                 'title = {Component before},\n  annotation = {{title}.},'),
            ])
            pages, links = self.compile(root, 'unexpanded.pdf')
            self.assertNotIn('https://doi.org/10.5555/component.before', self.uris(links))
            self.assertNotIn('Component before', pages[2])
            driver = (root / 'sample.typ').read_text()
            driver = driver.replace(
                '#metadata((kind: "bibliography-boundary", enter: false))',
                '#bib-item(tag: "02")[#bib-description("Component2002")] <bib:Component2002>\n'
                '#metadata((kind: "bibliography-boundary", enter: false))')
            (root / 'sample.typ').write_text(driver)
            pages, links = self.compile(root, 'separate.pdf')
            self.assertIn('https://doi.org/10.5555/component.before', self.uris(links))
            self.assertEqual(pages[2].count('10.5555/component.before'), 1)

    def test_only_bib_title_and_doi_changes_update_pdf_text_and_uri(self):
        with tempfile.TemporaryDirectory(prefix='bibliography-',
                                         dir='/tmp') as temporary:
            root = Path(temporary)
            self.fixture(root)
            unchanged = self.typst_hashes(root)
            before, before_links = self.compile(root, 'before.pdf')
            self.replace_fields(root, [
                ('title = {Alpha title}', 'title = {Beta title}'),
                ('doi = {10.5555/fixture.alpha}',
                 'doi = {10.5555/fixture.beta}'),
            ])
            after, after_links = self.compile(root, 'after.pdf')
            self.assertEqual(self.typst_hashes(root), unchanged)
            self.assertEqual(before[:2], after[:2])
            self.assertIn('Alpha title', before[2])
            self.assertNotIn('Beta title', before[2])
            self.assertIn('Beta title', after[2])
            self.assertNotIn('Alpha title', after[2])
            old = 'https://doi.org/10.5555/fixture.alpha'
            new = 'https://doi.org/10.5555/fixture.beta'
            self.assertIn(old, self.uris(before_links))
            self.assertNotIn(new, self.uris(before_links))
            self.assertIn(new, self.uris(after_links))
            self.assertNotIn(old, self.uris(after_links))
            self.assertIn('10.5555/fixture.beta', after[2])
            self.assertNotIn('10.5555/fixture.alpha', after[2])

    def test_related_fields_and_shortjournal_update_without_typst_edits(self):
        with tempfile.TemporaryDirectory(prefix='bibliography-',
                                         dir='/tmp') as temporary:
            root = Path(temporary)
            self.fixture(root)
            unchanged = self.typst_hashes(root)
            before, before_links = self.compile(root, 'before.pdf')
            self.replace_fields(root, [
                ('title = {Component before}', 'title = {Component after}'),
                ('shortjournal = {J. Fixture Before}',
                 'shortjournal = {J. Fixture After}'),
                ('pages = {101-109}', 'pages = {901-909}'),
                ('doi = {10.5555/component.before}',
                 'doi = {10.5555/component.after}'),
            ])
            after, after_links = self.compile(root, 'after.pdf')
            self.assertEqual(self.typst_hashes(root), unchanged)
            for text in ('Component before', 'J. Fixture Before', '101-109'):
                self.assertIn(text, before[2])
                self.assertNotIn(text, after[2])
            for text in ('Component after', 'J. Fixture After', '901-909'):
                self.assertIn(text, after[2])
                self.assertNotIn(text, before[2])
            for text in before + after:
                self.assertNotIn('Full fixture journal', text)
            self.assertIn('https://doi.org/10.5555/component.before',
                          self.uris(before_links))
            self.assertNotIn('https://doi.org/10.5555/component.before',
                             self.uris(after_links))
            self.assertIn('https://doi.org/10.5555/component.after',
                          self.uris(after_links))
            self.assertIn('https://doi.org/10.5555/fixture.alpha',
                          self.uris(after_links))

    def actual_link(self, links, source, destination, offset):
        x = float(source['x'].removesuffix('pt'))
        y = float(source['y'].removesuffix('pt'))
        candidates = [item for page, item in links
                      if page == source['page']
                      and item['kind'] == fitz.LINK_GOTO
                      and abs(item['from'].x0 - x) < 0.03
                      and item['from'].y0 - 0.03 <= y
                      <= item['from'].y1 + 0.03]
        self.assertEqual(len(candidates), 1, (source, candidates))
        actual = candidates[0]
        self.assertEqual(actual['page'] + 1, destination['page'])
        expected_y = max(0, float(destination['y'].removesuffix('pt')) - offset)
        self.assertAlmostEqual(actual['to'].y, expected_y, delta=0.03)
        self.assertAlmostEqual(actual['to'].x,
                               float(destination['x'].removesuffix('pt')),
                               delta=0.03)

    def test_backlinks_include_footnote_exclude_internal_but_keep_its_link(self):
        with tempfile.TemporaryDirectory(prefix='bibliography-',
                                         dir='/tmp') as temporary:
            root = Path(temporary)
            self.fixture(root)
            pages, links = self.compile(root, 'sample.pdf')
            data = self.metadata(root)
            backlinks = [item for item in data
                         if item['value'].get('kind') == 'page-reference']
            self.assertEqual([item['value']['description']
                              for item in backlinks], ['1', '2'])
            self.assertEqual([item['value']['target'] for item in backlinks],
                             ['bib-mention:bib:Probe2000'] * 2)
            self.assertEqual([item['position']['page'] for item in backlinks],
                             [3, 3])
            self.assertEqual([item['value']['target-position']['page']
                              for item in backlinks], [1, 2])
            self.assertIn('[1, 2]', pages[2])
            self.assertNotIn('[1, 2, 3]', pages[2])
            self.assertIn('Main citation [00a] and duplicate [00a].', pages[0])
            self.assertIn('Footnote-only citation [00a].', pages[1])
            self.assertIn('See [00a] and [01].', pages[2])
            references = [item['value'] for item in data
                          if item['value'].get('kind') == 'cross-reference']
            self.assertTrue(all(item['resolved'] for item in references))
            self.assertEqual([item['position']['page'] for item in references
                              if item['target'] == 'bib:Probe2000'],
                             [1, 1, 2, 3])
            note_reference = next(item for item in references
                                  if item['position']['page'] == 2)
            self.assertGreater(
                float(note_reference['position']['y'].removesuffix('pt')), 500)
            # Verify every real PDF rectangle and destination: the two
            # backlinks, the footnote citation and both internal citations.
            for item in backlinks:
                self.actual_link(links, item['position'],
                                 item['value']['target-position'], 18)
            for item in references:
                self.actual_link(links, item['position'],
                                 item['target-position'], 10)
            internal = [item for item in references
                        if item['position']['page'] == 3]
            self.assertEqual({item['target'] for item in internal},
                             {'bib:Probe2000', 'bib:Other2001'})
            self.assertTrue(all(item['target-position']['page'] == 3
                                for item in internal))
            self.assertFalse(any(item['value'].get('target') ==
                                 'bib-mention:bib:Other2001'
                                 for item in backlinks))


if __name__ == '__main__':
    unittest.main()
