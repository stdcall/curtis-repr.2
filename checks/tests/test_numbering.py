"""Actual Typst/PDF regression fixtures for the shared numbered series.

Run with unittest. BOOK_TEST_ROOT overrides discovery for a detached candidate.
All mutations are confined to temporary copies under /tmp.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import fitz

ROOT = Path(os.environ.get('BOOK_TEST_ROOT', Path(__file__).resolve().parents[2]))
sys.path.insert(0, str(ROOT / 'scripts'))
from check_links import check_hint_links, check_links

STYLES = ('book-style.typ', 'main-defs.typ', 'note-layout.typ',
          'numbering.typ', 'statements.typ')

DRIVER = '''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#show: book-style
#set page(header: none, footer: none)
#heading(level: 1, numbering: none)[Introduction] <ch:introduction>
== Probe <sec:probe>
SERIES
INSERT
#named-equation(name: [$(ast)$])[$ upright("NAMEDBODY") = 1 $] <eq:named>
#proposition[THEOREMBODY] <prop:probe>
#lemma-suffix(base: [@prop:probe], suffix: "a")[SUFFIXBODY] <lem:suffix>
#equation-suffix(base: [@prop:probe], suffix: "b")[$ upright("EQVARIANTBODY") = 1 $] <eq:variant>
#rect(width: 100%, height: 1pt, fill: rgb("#0000ff"), stroke: none)
#numbered-block[
  #block(width: WIDTH)[
    #rect(width: 100%, height: 1pt, fill: rgb("#ff0000"), stroke: none)
    #grid(columns: (1fr, 1fr), row-gutter: 5pt,
      [NODEL], [NODER], [LOWL], [LOWR])
  ]
] <eq:grid>
#proposition-suffix(base: [@eq:grid], suffix: "a")[PROPVARIANTBODY] <prop:suffix>
#remarks(numbered: true)[REMARKBODY] <rem:probe>
$ upright("DISPLAYBODY") = 1 $ <eq:display>
#pagebreak()
REFNAMED @eq:named

REFTH @prop:probe

REFGRID @eq:grid

REFSUFFIX @lem:suffix

REFPROPVARIANT @prop:suffix

REFEQVARIANT @eq:variant

REFREM @rem:probe

REFDISPLAY @eq:display

INTRODEFAULT @ch:introduction

INTRODESC @ch:introduction[opening chapter]
'''


class NumberingTests(unittest.TestCase):
    def test_long_editorial_entry_and_adjacent_author_notes_are_not_split(self):
        for padding in (35, 40, 45, 60, 90):
            with self.subTest(padding=padding):
                with tempfile.TemporaryDirectory(prefix='long-note-flow-', dir='/tmp') as td:
                    root = Path(td)
                    self.fixture(root)
                    (root / 'sample.typ').write_text('''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#import "content/main-defs.typ": ed-note
#show: book-style
#set page(header: none, footer: none, height: 160mm)
#block(height: PADDINGmm)[FILLER]
== Probe <sec:probe>
#lorem(20) PREVIOUS#footnote[PREVIOUSNOTE #lorem(20)]
#theorem[
  #lorem(65) LIMIT#ed-note[EDITORIALBEGIN #lorem(140) EDITORIALEND]
  #lorem(10) AUTHOR#footnote[AUTHORNOTE]
] <th:note>
'''.replace('PADDING', str(padding)))
                    document = self.compile(root)
                    texts = [page.get_text() for page in document]
                    links = [(page.number, link) for page in document
                             for link in page.get_links()]
                    self.assertEqual(len(links), 6)
                    self.assertTrue(all(page == link['page'] for page, link in links))
                    for token in ('PREVIOUSNOTE', 'EDITORIALBEGIN', 'EDITORIALEND',
                                  'AUTHORNOTE'):
                        self.assertEqual(sum(text.count(token) for text in texts), 1)
                    begin = next(i for i, text in enumerate(texts)
                                 if 'EDITORIALBEGIN' in text)
                    end = next(i for i, text in enumerate(texts)
                               if 'EDITORIALEND' in text)
                    self.assertEqual(begin, end)

    def test_statement_editorial_note_and_following_author_note_stay_together(self):
        for padding in (40, 55, 60, 65, 90):
            with self.subTest(padding=padding):
                with tempfile.TemporaryDirectory(prefix='statement-note-flow-', dir='/tmp') as td:
                    root = Path(td)
                    self.fixture(root)
                    (root / 'sample.typ').write_text('''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#import "content/main-defs.typ": ed-note
#show: book-style
#set page(header: none, footer: none, height: 130mm)
#block(height: PADDINGmm)[FILLER]
== Probe <sec:probe>
#corollary[
  #lorem(35) END#ed-note[EDITORIALNOTE #lorem(45)]
] <cor:note>
AFTER#footnote[AUTHORNOTE]
#pagebreak()
Apply @cor:note.
'''.replace('PADDING', str(padding)))
                    document = self.compile(root)
                    links = [(page.number, link) for page in document
                             for link in page.get_links()]
                    note_links = [(page, link) for page, link in links
                                  if document.xref_get_key(link['xref'], 'Contents')[1]
                                  in ('Footnote *1', '*1', 'Footnote 1', '1')]
                    self.assertEqual(len(note_links), 4)
                    self.assertTrue(all(page == link['page'] for page, link in note_links))
                    self.assertEqual(sum(page.get_text().count('EDITORIALNOTE')
                                         for page in document), 1)
                    self.assertEqual(sum(page.get_text().count('AUTHORNOTE')
                                         for page in document), 1)
                    references = [(page, link) for page, link in links
                                  if (page, link) not in note_links]
                    self.assertEqual(len(references), 1)
                    self.assertIn('(1.1)', document[-1].get_text())
                    target_page = references[0][1]['page']
                    self.assertIn('(1.1)', document[target_page].get_text())

    def test_short_hint_and_following_exercise_have_disjoint_links(self):
        with tempfile.TemporaryDirectory(prefix='adjacent-hint-links-', dir='/tmp') as td:
            root = Path(td)
            self.fixture(root)
            (root / 'sample.typ').write_text('''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#show: book-style
#set page(header: none, footer: none)
== Probe <sec:probe>
#proposition[Target.] <prop:target>
#exercise[First exercise.

  #hint([@exc:first])[Use @prop:target.]
] <exc:first>

#exercise[Apply @prop:target.

  #hint([@exc:second])[Short.]
] <exc:second>
''')
            document = self.compile(root)
            self.assertEqual(len(document), 1)
            links = document[0].get_links()
            self.assertEqual(len(links), 6)
            for i, link in enumerate(links):
                self.assertEqual(link['kind'], fitz.LINK_GOTO)
                self.assertEqual(link['page'], 0)
                self.assertGreater(link['from'].width, 0)
                self.assertGreater(link['from'].height, 0)
                for following in links[i + 1:]:
                    self.assertTrue((link['from'] & following['from']).is_empty)
            command = ['typst', 'eval', '--root', str(root),
                       '--input', 'stage=draft', '--font-path', str(root / 'fonts'),
                       '--ignore-system-fonts', '--in', str(root / 'sample.typ'),
                       'query(metadata).filter(it => type(it.value) == dictionary '
                       'and it.value.at("kind", default: none) == "hint-link")'
                       '.map(it => it.value)']
            result = subprocess.run(command, capture_output=True, text=True,
                                    check=True, timeout=60)
            self.assertEqual(result.stderr, '')
            self.assertEqual(check_hint_links(
                check_links(root / 'sample.pdf', []), json.loads(result.stdout)),
                {'problems_with_hint': 2, 'problems_without_hint': 0,
                 'hint_numbers': 2})

    def test_adjacent_index_rows_have_disjoint_locators(self):
        with tempfile.TemporaryDirectory(prefix='adjacent-index-links-', dir='/tmp') as td:
            root = Path(td)
            self.fixture(root)
            shutil.copyfile(ROOT / 'content/index-style.typ',
                            root / 'content/index-style.typ')
            (root / 'sample.typ').write_text('''#import "content/book-style.typ": book-style
#import "content/main-defs.typ": idx
#import "content/index-style.typ": subject-index
#show: book-style
#set page(header: none, footer: none, numbering: "1")
One #idx("Alpha") two #idx("Alphi") three #idx("Alpho").
#pagebreak()
#subject-index
''')
            document = self.compile(root)
            self.assertEqual(len(document), 2)
            links = document[1].get_links()
            self.assertEqual(len(links), 3)
            for i, link in enumerate(links):
                self.assertEqual(link['kind'], fitz.LINK_GOTO)
                self.assertEqual(link['page'], 0)
                self.assertGreater(link['from'].width, 0)
                self.assertGreater(link['from'].height, 0)
                for following in links[i + 1:]:
                    self.assertTrue((link['from'] & following['from']).is_empty)

    def test_repeated_footnote_across_statement_and_proof_keeps_one_page(self):
        for padding in (0, 55):
            with self.subTest(padding=padding):
                with tempfile.TemporaryDirectory(prefix='shared-note-flow-', dir='/tmp') as td:
                    root = Path(td)
                    self.fixture(root)
                    (root / 'sample.typ').write_text('''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#show: book-style
#set page(header: none, footer: none, height: 130mm)
#block(height: PADDINGmm)[FILLER]
#lemma[
  RING#footnote[ONEENTRY] <fn:shared> #lorem(35)
] <lem:shared>
#proof[
  RING#footnote(<fn:shared>) #lorem(45)
]
'''.replace('PADDING', str(padding)))
                    document = self.compile(root)
                    links = [(page.number, link) for page in document
                             for link in page.get_links()]
                    self.assertEqual(len(links), 3)
                    self.assertEqual({page for page, _ in links},
                                     {0 if padding == 0 else 1})
                    self.assertTrue(all(page == link['page'] for page, link in links))
                    self.assertEqual(sum(page.get_text().count('ONEENTRY')
                                         for page in document), 1)

    def test_native_footnote_labels_reject_prose_and_duplicates(self):
        from lint_typst import LABELLED, coverage_checks
        with tempfile.TemporaryDirectory(prefix='footnote-labels-', dir='/tmp') as td:
            root = Path(td)
            self.fixture(root)
            (root / 'sample.typ').write_text('''#import "content/book-style.typ": book-style
#show: book-style
#set page(header: none, footer: none)
FIRST#footnote[SHAREDNOTE] <fn:shared>
SECOND#footnote(<fn:shared>)

[PROSE] <fn:prose>

THIRD#footnote[DUPLICATEONE] <fn:duplicate>
FOURTH#footnote[DUPLICATETWO] <fn:duplicate>
''')
            document = self.compile(root)
            self.assertEqual(len(document), 1)
            command = ['typst', 'eval', '--root', str(root),
                       '--input', 'stage=draft', '--font-path', str(root / 'fonts'),
                       '--ignore-system-fonts', '--in', str(root / 'sample.typ'),
                       LABELLED.replace('LABELS',
                                        '("fn:shared", "fn:prose", "fn:duplicate")'),
                       '--format', 'json']
            result = subprocess.run(command, capture_output=True, text=True,
                                    check=True, timeout=60)
            self.assertEqual(result.stderr, '')
            labelled = json.loads(result.stdout)
            self.assertEqual(labelled['fn:shared']['record']['value']['kind'],
                             'native-footnote')
            self.assertEqual(labelled['fn:duplicate']['count'], 2)
            self.assertIsNone(labelled['fn:prose']['record'])
            data = {'labelled': labelled, 'metadata': []}
            errors = coverage_checks(data, {}, False)
            self.assertEqual(len(errors), 2)
            self.assertTrue(all('fn:shared' not in e['message'] for e in errors))
            # A footnote label cannot satisfy a numbered statement's coverage.
            data['metadata'] = [{'label': '<numbered>', 'value': {
                'kind': 'numbered', 'family': 'prop', 'number': [1, 1]},
                'position': labelled['fn:shared']['record']['position']}]
            self.assertEqual(len(coverage_checks(data, {}, False)), 3)
            links = document[0].get_links()
            self.assertEqual(len(links), 7)
            self.assertTrue(all(link['kind'] == fitz.LINK_GOTO
                                and link['page'] == 0
                                and link['from'].width > 0
                                and link['from'].height > 0 for link in links))

    def test_two_hints_inside_one_exercise_keep_both_return_links(self):
        with tempfile.TemporaryDirectory(prefix='multiple-hints-', dir='/tmp') as td:
            root = Path(td)
            self.fixture(root)
            (root / 'sample.typ').write_text('''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#show: book-style
#set page(header: none, footer: none, height: 130mm)
== Probe <sec:probe>
#exercise[
  PROBLEMBODY
  #enum(
    [FIRSTPART #hint([@exc:several])[FIRSTHINT] #lorem(180)],
    [SECONDPART #hint([@exc:several])[SECONDHINT]],
  )
] <exc:several>
''')
            document = self.compile(root)
            self.assertEqual(len(document), 2)
            command = ['typst', 'eval', '--root', str(root),
                       '--input', 'stage=draft', '--font-path', str(root / 'fonts'),
                       '--ignore-system-fonts', '--in', str(root / 'sample.typ'),
                       'query(metadata).filter(it => type(it.value) == dictionary '
                       'and it.value.at("kind", default: none) == "hint-link")'
                       '.map(it => it.value)']
            result = subprocess.run(command, capture_output=True, text=True,
                                    check=True, timeout=60)
            self.assertEqual(result.stderr, '')
            records = json.loads(result.stdout)
            problem = [r for r in records if r['from'] == 'problem']
            hints = [r for r in records if r['from'] == 'hint']
            self.assertEqual(len(problem), 1)
            self.assertEqual([r['position']['page'] for r in hints], [1, 2])
            self.assertEqual(problem[0]['target-position']['page'], 1)
            self.assertEqual(problem[0]['target-position']['y'],
                             hints[0]['position']['y'])
            self.assertEqual(check_hint_links(check_links(root / 'sample.pdf', []),
                                             records),
                             {'problems_with_hint': 1, 'problems_without_hint': 0,
                              'hint_numbers': 2})

    def fixture(self, root, wide=False, inserted=False, zero=False):
        (root / 'content').mkdir()
        for name in STYLES:
            shutil.copyfile(ROOT / 'content' / name, root / 'content' / name)
        # Production font files, no system fonts, no full book source.
        shutil.copytree(ROOT / 'assets' / 'fonts', root / 'fonts')
        shutil.copyfile(ROOT / 'editorial.bib', root / 'editorial.bib')
        width = '345pt' if wide else '100pt'
        insertion = '#theorem[INSERTEDBODY] <th:inserted>' if inserted else ''
        (root / 'sample.typ').write_text(DRIVER.replace('WIDTH', width)
                                       .replace('INSERT', insertion)
                                       .replace('SERIES', '#item-series(start: 0)' if zero else ''))

    def compile(self, root):
        cmd = ['typst', 'compile', '--root', str(root), '--input', 'stage=draft',
               '--font-path', str(root / 'fonts'), '--ignore-system-fonts',
               str(root / 'sample.typ'), str(root / 'sample.pdf')]
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stderr, '', 'Fixture warnings are failures')
        return fitz.open(root / 'sample.pdf')

    @staticmethod
    def one(page, text):
        hits = page.search_for(text)
        if len(hits) != 1:
            raise AssertionError(f'{text}: expected one bbox, got {hits}')
        return hits[0]

    def verify(self, document, wide=False, inserted=False, zero=False):
        self.assertEqual(len(document), 2)
        body, refs = document[0], document[1]
        shift = int(inserted) - int(zero)
        destinations = [('REFTH', 'THEOREMBODY', 1, ''),
                        ('REFGRID', 'NODEL', 2, ''),
                        ('REFSUFFIX', 'SUFFIXBODY', 1, 'a'),
                        ('REFPROPVARIANT', 'PROPVARIANTBODY', 2, 'a'),
                        ('REFEQVARIANT', 'EQVARIANTBODY', 1, 'b'),
                        ('REFREM', 'REMARKBODY', 3, ''),
                        ('REFDISPLAY', 'DISPLAYBODY', 4, '')]
        links = refs.get_links()
        self.assertGreaterEqual(len(links), 6)
        named = self.one(refs, 'REFNAMED')
        named_links = [l for l in links if abs(l['from'].y0 - named.y0) < 3]
        self.assertEqual(len(named_links), 1)
        self.assertEqual(refs.get_textbox(named_links[0]['from']).strip(), '(∗)')
        self.assertEqual(named_links[0]['page'], 0)
        named_body = self.one(body, 'NAMEDBODY')
        self.assertLessEqual(named_links[0]['to'].y, named_body.y0 + 2)
        self.assertLess(named_body.y0 - named_links[0]['to'].y, 25)
        for marker, target, number, suffix in destinations:
            source = self.one(refs, marker)
            selected = [link for link in links
                        if abs(link['from'].y0 - source.y0) < 3]
            self.assertTrue(selected, marker)
            link = selected[0]
            area = fitz.Rect(link['from'])
            for piece in selected:
                area |= piece['from']
                self.assertEqual(piece['page'], link['page'])
                self.assertEqual(piece['to'], link['to'])
            self.assertEqual(link['kind'], fitz.LINK_GOTO)
            self.assertEqual(link['page'], 0)
            self.assertIn(f'(1.{number + shift}{suffix})',
                          refs.get_textbox(area))
            target_box = self.one(body, target)
            # Destination is slightly above the actual object, never another one.
            self.assertLessEqual(link['to'].y, target_box.y0 + 2)
            self.assertLess(target_box.y0 - link['to'].y, 18)
        intro = self.one(body, 'Introduction')
        for marker, caption in [('INTRODEFAULT', 'Introduction'),
                                ('INTRODESC', 'opening chapter')]:
            source = self.one(refs, marker)
            chosen = [l for l in links if abs(l['from'].y0 - source.y0) < 3]
            self.assertTrue(chosen)
            link = chosen[0]
            area = fitz.Rect(link['from'])
            for piece in chosen:
                area |= piece['from']
                self.assertEqual(piece['page'], link['page'])
                self.assertEqual(piece['to'], link['to'])
            self.assertEqual(link['kind'], fitz.LINK_GOTO)
            self.assertEqual(link['page'], 0)
            self.assertEqual(refs.get_textbox(area).strip(), caption)
            self.assertLessEqual(link['to'].y, intro.y0 + 2)
            self.assertLess(intro.y0 - link['to'].y, 55)
        # Check actual PDF body numbers as well as the independently rendered refs.
        for n in range(1, 5):
            self.assertTrue(body.search_for(f'(1.{n + shift})'))
        colors = {}
        for drawing in body.get_drawings():
            fill = drawing.get('fill')
            # ICC-based PDF colour conversion introduces sub-0.001 RGB drift.
            if fill and all(abs(c - round(c)) < .01 for c in fill):
                fill = tuple(round(c) for c in fill)
            if fill in ((1., 0., 0.), (0., 0., 1.)):
                self.assertNotIn(fill, colors)
                colors[fill] = drawing['rect']
        band, diagram = colors[(0., 0., 1.)], colors[(1., 0., 0.)]
        self.assertAlmostEqual(diagram.width, 345 if wide else 100, delta=.1)
        if wide:
            self.assertAlmostEqual(diagram.x1, band.x1, delta=.2)
            tag = self.one(body, f'(1.{2 + shift})')
            self.assertGreater(diagram.x0 - tag.x1, 7)
            self.assertGreater(diagram.width,
                               band.width - 2 * (tag.width + 8.25))
        else:
            self.assertAlmostEqual((diagram.x0 + diagram.x1) / 2,
                                   (band.x0 + band.x1) / 2, delta=.2)
        # The body is a real two-row grid, not a disguised math equation.
        self.assertGreater(self.one(body, 'LOWL').y0 -
                           self.one(body, 'NODEL').y0, 10)

    def test_series_links_and_geometry_with_and_without_insertion(self):
        for wide in (False, True):
            for inserted in (False, True):
                with self.subTest(wide=wide, inserted=inserted):
                    with tempfile.TemporaryDirectory(dir='/tmp', prefix='numbering-') as td:
                        root = Path(td)
                        self.fixture(root, wide, inserted)
                        with self.compile(root) as doc:
                            self.verify(doc, wide, inserted)

    def test_zero_start_keeps_native_insertion_and_suffix_links(self):
        for inserted in (False, True):
            with self.subTest(inserted=inserted):
                with tempfile.TemporaryDirectory(dir='/tmp', prefix='numbering-zero-') as td:
                    root = Path(td)
                    self.fixture(root, inserted=inserted, zero=True)
                    with self.compile(root) as doc:
                        self.verify(doc, inserted=inserted, zero=True)

    def test_counter_ref_and_centering_mutations_are_detected(self):
        mutations = (
            ('missing block counter step', 'statements.typ',
             '#let numbered-block(body) = {\n  family-counter("eq").step()',
             '#let numbered-block(body) = {'),
            ('wrong PDF destination, correct printed number', 'main-defs.typ',
             'link(destination,',
             'link(if target == "eq:grid" { numbered-record(<prop:probe>).location() } else { destination },'),
            ('short diagram shifted right', 'statements.typ',
             'align: (left + horizon, center + horizon, right + horizon)',
             'align: (left + horizon, right + horizon, right + horizon)'),
        )
        for name, filename, before, after in mutations:
            with self.subTest(mutation=name):
                with tempfile.TemporaryDirectory(dir='/tmp', prefix='numbering-mutant-') as td:
                    root = Path(td)
                    self.fixture(root)
                    path = root / filename if filename == 'sample.typ' else root / 'content' / filename
                    source = path.read_text()
                    self.assertEqual(source.count(before), 1, name)
                    path.write_text(source.replace(before, after))
                    with self.compile(root) as doc:
                        with self.assertRaises(AssertionError, msg=name):
                            self.verify(doc)


if __name__ == '__main__':
    unittest.main()
