"""Actual pagination, native display spacing, references and adjacent notes."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
import fitz

ROOT = Path(os.environ.get('BOOK_TEST_ROOT', Path(__file__).resolve().parents[2]))


class StatementDisplayTests(unittest.TestCase):
    def test_opening_displays_stay_with_statement_and_preserve_notes(self):
        with tempfile.TemporaryDirectory(prefix='statement-display-', dir='/tmp') as td:
            root = Path(td)
            (root / 'content').mkdir()
            for n in ('book-style.typ', 'main-defs.typ', 'note-layout.typ',
                      'numbering.typ', 'statements.typ'):
                shutil.copy2(ROOT / 'content' / n, root / 'content' / n)
            driver = '''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#import "content/main-defs.typ": *
#import "content/numbering.typ": section-counter
#show: book-style
#set page(height:150mm, header:none, footer:none)
#section-counter.update(21)
#text(style:"italic")[CONTROL A class function $psi in cf_F G$ belongs to $"ch"_K F G$ if and only if
$ "FIRSTCONTROL"=0 \\
1=1 $]
'''
            cases = []
            for family in ('theorem', 'corollary'):
                for note in (False, True):
                    for padding in (55, 60, 65, 70, 75, 80, 85, 90):
                        token = f'CASE{len(cases)+1}X'
                        key = ('th:' if family == 'theorem' else 'cor:') + token
                        cases.append((token, key, note))
                        inside = (f' Inside.#footnote[INSIDE{token} '
                                  f'#lorem(50) ENDINSIDE{token}]' if note else '')
                        driver += f'''#pagebreak()
#block(height:{padding}mm)[PADDING]
BEFOREMARK{token}#footnote[BEFORE{token} #lorem(22) ENDBEFORE{token}]
#{family}[INTRO{token} A class function $psi in cf_F G$ belongs to $"ch"_K F G$ if and only if
$ "FIRST{token}"=0 #metadata((kind:"display-probe",id:"{token}")) \\
1=1 $
Further text.{inside}
] <{key}>
AFTERMARK{token}#footnote[AFTER{token} #lorem(22) ENDAFTER{token}]
'''
            driver += '#pagebreak()\n'
            for token, key, _ in cases:
                driver += f'REFERENCE{token} @{key}\n\n'
            (root / 'sample.typ').write_text(driver)
            options = ['--root', str(root), '--font-path', str(ROOT / 'assets/fonts'),
                       '--ignore-system-fonts']
            run = lambda kind, *args: subprocess.run(['typst', kind, *options, *args],
                                                    capture_output=True, text=True)
            compiled = run('compile', str(root / 'sample.typ'), str(root / 'sample.pdf'))
            self.assertEqual(compiled.returncode, 0, compiled.stderr)
            self.assertEqual(compiled.stderr, '')
            expression = '''{ import "/content/main-defs.typ": metadata-value
            query(metadata).map(it => (value:metadata-value(it),position:it.location().position())) }'''
            q = run('eval', '--in', str(root / 'sample.typ'), expression)
            self.assertEqual(q.returncode, 0, q.stderr)
            self.assertEqual(q.stderr, '')
            records = [dict(r['value'], position=r['value'].get('position', r['position']))
                       for r in json.loads(q.stdout) if isinstance(r['value'], dict)]
            objects = [r for r in records if r.get('kind') == 'numbered'
                       and r.get('family') in ('th', 'cor')]
            starts = [r for r in records if r.get('kind') == 'display-probe']
            self.assertEqual(len(objects), 32)
            self.assertEqual(len(starts), 32)
            pdf = fitz.open(root / 'sample.pdf')
            texts = [page.get_text() for page in pdf]
            lines = [[line for b in page.get_text('dict')['blocks'] if 'lines' in b
                      for line in b['lines']] for page in pdf]
            def gap(page, token):
                i = next(i for i, line in enumerate(lines[page])
                         if token in ''.join(s['text'] for s in line['spans']))
                return lines[page][i]['spans'][0]['origin'][1] - lines[page][i-1]['spans'][0]['origin'][1]
            control = gap(0, 'FIRSTCONTROL')
            for i, ((token, key, note), obj, start) in enumerate(zip(cases, objects, starts), 1):
                with self.subTest(key=key, note=note):
                    self.assertEqual(obj['number'], [21, i])
                    if not note:
                        self.assertEqual(obj['position']['page'], start['position']['page'])
                        self.assertAlmostEqual(gap(start['position']['page']-1, 'FIRST'+token),
                                               control, delta=.03)
                    for begin, end in [('BEFORE', 'ENDBEFORE'), ('AFTER', 'ENDAFTER')]+([('INSIDE', 'ENDINSIDE')] if note else []):
                        first = [j for j, s in enumerate(texts) if begin+token in s]
                        last = [j for j, s in enumerate(texts) if end+token in s]
                        self.assertEqual(len(first), 1)
                        self.assertEqual(first, last)
            notes = [r for r in records if r.get('kind') == 'footnote-placement']
            self.assertEqual(len(notes), 80)
            self.assertTrue(all(n['marker-page'] == n['entry-page'] for n in notes))
            refs = [r for r in records if r.get('kind') == 'cross-reference']
            self.assertEqual(len(refs), 32)
            pt = lambda x: float(x[:-2])
            for ref, obj in zip(refs, objects):
                self.assertTrue(ref['resolved'])
                self.assertEqual(ref['target-position'], obj['position'])
                s, t = ref['position'], ref['target-position']
                matches = [a for a in pdf[s['page']-1].get_links()
                           if a['kind'] == fitz.LINK_GOTO and a['page'] == t['page']-1
                           and abs(a['to'].x-pt(t['x'])) < .03
                           and abs(a['to'].y-max(0,pt(t['y'])-10)) < .03
                           and a['from'].x0-.03 <= pt(s['x']) <= a['from'].x1+.03
                           and a['from'].y0-.03 <= pt(s['y']) <= a['from'].y1+.03]
                self.assertEqual(len(matches), 1)
            note_links = [(page.number, link) for page in pdf for link in page.get_links()
                          if (pdf.xref_get_key(link['xref'], 'Contents')[1].startswith('Footnote ')
                              or pdf.xref_get_key(link['xref'], 'Contents')[1].isdigit())]
            self.assertEqual(len(note_links), 160)
            self.assertTrue(all(page == link['page'] and link['from'].width > 0
                                and link['from'].height > 0 for page, link in note_links))


if __name__ == '__main__':
    unittest.main()
