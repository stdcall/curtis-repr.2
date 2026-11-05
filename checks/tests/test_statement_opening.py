"""Behavioural Typst/PDF regression; BOOK_TEST_ROOT selects OLD or NEW styles."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import fitz

ROOT = Path(os.environ.get('BOOK_TEST_ROOT', Path(__file__).resolve().parents[2]))
STYLES = ('book-style.typ', 'main-defs.typ', 'note-layout.typ',
          'numbering.typ', 'statements.typ')


class StatementOpeningTests(unittest.TestCase):
    def test_note_in_later_list_item_retains_native_outer_flow_indent(self):
        with tempfile.TemporaryDirectory(prefix='statement-note-indent-', dir='/tmp') as td:
            root = Path(td)
            (root / 'content').mkdir()
            for name in STYLES:
                shutil.copy2(ROOT / 'content' / name, root / 'content' / name)
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            (root / 'sample.typ').write_text('''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#import "content/numbering.typ": section-counter
#show: book-style
#section-counter.update(31)
Previous plain paragraph.

NATIVECONTROL This is a normal new paragraph.

Previous plain paragraph.

#proposition[
  Let $L,M,N$ be $Lambda$-lattices.
  #enum([First condition.], [Second condition.#footnote[LATERNOTE]])
] <prop:later-note>
''')
            subprocess.run(['typst', 'compile', '--root', str(root),
                            '--ignore-system-fonts', '--font-path',
                            str(root / 'assets/fonts'), str(root / 'sample.typ'),
                            str(root / 'sample.pdf')], check=True,
                           capture_output=True, text=True)
            document = fitz.open(root / 'sample.pdf')
            self.assertEqual(len(document), 1)
            native = document[0].search_for('NATIVECONTROL')
            heading = document[0].search_for('(31.1)')
            self.assertEqual(len(native), 1)
            self.assertEqual(len(heading), 1)
            self.assertAlmostEqual(native[0].x0, heading[0].x0, delta=.03)
            links = document[0].get_links()
            self.assertEqual(len(links), 2)
            self.assertTrue(all(link['page'] == 0 and link['from'].width > 0
                                and link['from'].height > 0 for link in links))

    def test_short_introductions_keep_first_blocks_and_whole_adjacent_notes(self):
        with tempfile.TemporaryDirectory(prefix='statement-opening-', dir='/tmp') as td:
            root = Path(td)
            (root / 'content').mkdir()
            for name in STYLES:
                shutil.copy2(ROOT / 'content' / name, root / 'content' / name)
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            driver = '''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#import "content/numbering.typ": section-counter
#show: book-style
#set page(header:none, footer:none, height:150mm)
#section-counter.update(31)
'''
            for listing in ('enum', 'list', 'terms'):
                driver += '#text(style:"italic")[Let $L,M,N$ be $Lambda$-lattices.\n'
                text = 'CONTROL' + listing + ' The first condition holds.'
                driver += (f'#{listing}([{text}], [Second condition.])\n'
                           if listing != 'terms' else
                           f'#terms(terms.item([{text}], [Description.]))\n')
                driver += ']\n'
            cases = []
            for kind in ('theorem', 'corollary'):
                for listing in ('enum', 'list', 'terms', 'note-enum'):
                    for padding in (50, 60, 70, 75, 80, 85):
                        token = f'CASE{len(cases)+1}X'
                        key = ('th:' if kind == 'theorem' else 'cor:') + token
                        cases.append((token, key, listing))
                        intro_note = (f'INTRO{token}#footnote[INTRONOTE{token} '
                                      f'#lorem(50) ENDINTRO{token}]'
                                      if listing == 'note-enum' else '')
                        driver += f'''#pagebreak()
#block(height:{padding}mm)[PADDING]
PREVIOUS{token}#footnote[BEFORE{token} #lorem(22) ENDBEFORE{token}]
#{kind}[Let $L,M,N$ be $Lambda$-lattices. {intro_note}
'''
                        first = (f'FIRST{token} #metadata((kind:"opening-probe", '
                                 f'id:"{token}")) The first condition holds.')
                        if listing == 'terms':
                            driver += f'#terms(terms.item([{first}],[#lorem(100)]), terms.item([Second],[#lorem(100)]))\n'
                        else:
                            native = 'enum' if listing == 'note-enum' else listing
                            driver += f'#{native}([{first}], [#lorem(100)], [#lorem(100)])\n'
                        driver += f'''] <{key}>
FOLLOWING{token}#footnote[AFTER{token} #lorem(25) ENDAFTER{token}]
'''
            driver += '#pagebreak()\n'
            for token, key, _ in cases:
                driver += f'REFERENCE{token} @{key}\n\n'
            (root / 'sample.typ').write_text(driver)
            options = ['--root', str(root), '--ignore-system-fonts',
                       '--font-path', str(root / 'assets/fonts')]
            subprocess.run(['typst', 'compile', *options,
                            str(root / 'sample.typ'), str(root / 'sample.pdf')],
                           check=True, capture_output=True, text=True)
            query = ('{ import "/content/main-defs.typ": metadata-value; '
                     'query(metadata).map(it => (value:metadata-value(it),'
                     'position:it.location().position())) }')
            output = subprocess.run(['typst', 'eval', *options, '--in',
                                     str(root / 'sample.typ'), query], check=True,
                                    capture_output=True, text=True)
            records = [dict(r['value'], position=r['value'].get('position', r['position']))
                       for r in json.loads(output.stdout) if isinstance(r['value'], dict)]
            document = fitz.open(root / 'sample.pdf')
            texts = [page.get_text() for page in document]
            lines = [[line for block in page.get_text('dict')['blocks']
                      if 'lines' in block for line in block['lines']]
                     for page in document]
            def gap(page, token):
                at = next(i for i, line in enumerate(lines[page])
                          if token in ''.join(span['text'] for span in line['spans']))
                return (lines[page][at]['spans'][0]['origin'][1]
                        - lines[page][at-1]['spans'][0]['origin'][1])
            native_gaps = {listing: gap(0, 'CONTROL' + listing)
                           for listing in ('enum', 'list', 'terms')}
            objects = [r for r in records if r.get('kind') == 'numbered'
                       and r.get('family') in ('th', 'cor')]
            starts = [r for r in records if r.get('kind') == 'opening-probe']
            self.assertEqual(len(objects), 48)
            self.assertEqual(len(starts), 48)
            split_list = False
            for i, ((token, key, listing), obj, start) in enumerate(zip(cases, objects, starts), 1):
                with self.subTest(kind=key, listing=listing):
                    self.assertEqual(obj['number'], [31, i])
                    self.assertEqual(start['id'], token)
                    self.assertEqual(sum(text.count('FIRST' + token) for text in texts), 1)
                    if listing != 'note-enum':
                        self.assertEqual(obj['position']['page'], start['position']['page'])
                        self.assertAlmostEqual(gap(start['position']['page'] - 1,
                                                   'FIRST' + token),
                                               native_gaps[listing], delta=.03)
                    following = next(j for j, text in enumerate(texts) if 'FOLLOWING' + token in text)
                    split_list |= listing in ('enum', 'list') and following + 1 > start['position']['page']
                    pairs = [('BEFORE', 'ENDBEFORE'), ('AFTER', 'ENDAFTER')]
                    if listing == 'note-enum':
                        pairs.append(('INTRONOTE', 'ENDINTRO'))
                    for begin, end in pairs:
                        a = [j for j, text in enumerate(texts) if begin + token in text]
                        b = [j for j, text in enumerate(texts) if end + token in text]
                        self.assertEqual(len(a), 1)
                        self.assertEqual(a, b)
            self.assertTrue(split_list, 'The following list must remain breakable')
            notes = [r for r in records if r.get('kind') == 'footnote-placement']
            self.assertEqual(len(notes), 108)
            self.assertTrue(all(n['marker-page'] == n['entry-page'] for n in notes))
            refs = [r for r in records if r.get('kind') == 'cross-reference']
            self.assertEqual(len(refs), 48)
            for ref, obj in zip(refs, objects):
                self.assertTrue(ref['resolved'])
                self.assertEqual(ref['target-position'], obj['position'])
                s, t = ref['position'], ref['target-position']
                pt = lambda value: float(value[:-2])
                matches = [link for link in document[s['page'] - 1].get_links()
                           if link['kind'] == fitz.LINK_GOTO
                           and link['page'] == t['page'] - 1
                           and abs(link['to'].x - pt(t['x'])) < .03
                           and abs(link['to'].y - max(0, pt(t['y']) - 10)) < .03
                           and link['from'].x0-.03 <= pt(s['x']) <= link['from'].x1+.03
                           and link['from'].y0-.03 <= pt(s['y']) <= link['from'].y1+.03]
                self.assertEqual(len(matches), 1)
            note_links = [(page.number, link) for page in document for link in page.get_links()
                          if (document.xref_get_key(link['xref'], 'Contents')[1].startswith('Footnote ')
                              or document.xref_get_key(link['xref'], 'Contents')[1].isdigit())]
            self.assertEqual(len(note_links), 216)
            self.assertTrue(all(page == link['page'] and link['from'].width > 0
                                and link['from'].height > 0 for page, link in note_links))


if __name__ == '__main__':
    unittest.main()
