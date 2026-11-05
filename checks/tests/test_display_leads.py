"""Native page-flow regressions for prose introducing later displays."""
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
BASE = '''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#import "content/main-defs.typ": ed-note
#show: book-style
#set page(width:176mm,height:88mm,margin:15mm,header:none,footer:none)
#proof[
  #lorem(100)
  $ x + y = z. $
  Applying the same argument to the image of the upper row gives
  $ [A] - [B] + [H] = [C] - [D] + [H]. $ <eq:second-display>
  Subtracting these formulas cancels $[H]$.#ed-note[
    This control editorial note explains the diagram defect. #lorem(35)
  ] This completes the proof.
]
'''
LEAD = 'Applying the same argument to the image of the upper row gives'
NOTE = '''#ed-note[
    This control editorial note explains the diagram defect. #lorem(35)
  ]'''
LONG = ('By the preceding results, the hypotheses carry over to the $B_j$-module '
        '$M_j$. Assuming the proposition for simple algebras, for each $j$ we '
        'can find $a_2, dots, a_n in B_j$ such that')


class DisplayLeadTests(unittest.TestCase):
    def test_later_displays_keep_their_prose_and_whole_notes(self):
        later = BASE.replace('height:88mm', 'height:86mm').replace(
            LEAD, LONG).replace(NOTE, '')
        hint = later.replace('height:86mm', 'height:94mm').replace(
            '#proof[', '#exercise[State an equality.] <exc:display-run>\n'
            '#hint([@exc:display-run])[')
        cases = (
            ('plain', BASE, 'Applying the same argument'),
            ('inline', BASE.replace('height:88mm', 'height:80mm').replace(
                LEAD, 'By $G_0^t lr((Lambda))$, we have'), 'By '),
            ('later', later, 'such that'),
            ('hint', hint, 'such that'),
        )
        with tempfile.TemporaryDirectory(prefix='display-leads-', dir='/tmp') as td:
            root = Path(td)
            (root / 'content').mkdir()
            for name in STYLES:
                shutil.copy2(ROOT / 'content' / name, root / 'content' / name)
            for name, source, token in cases:
                with self.subTest(name=name):
                    path = root / (name + '.typ')
                    pdf = root / (name + '.pdf')
                    path.write_text(source)
                    result = subprocess.run([
                        'typst', 'compile', '--root', str(root),
                        '--ignore-system-fonts', '--font-path',
                        str(ROOT / 'assets/fonts'), str(path), str(pdf),
                    ], check=True, capture_output=True, text=True)
                    self.assertEqual(result.stderr, '')
                    with fitz.open(pdf) as document:
                        texts = [page.get_text() for page in document]
                        lead = [i for i, text in enumerate(texts) if token in text]
                        equation = [i for i, text in enumerate(texts) if '(0.1)' in text]
                        self.assertEqual(len(lead), 1)
                        self.assertEqual(lead, equation)
                        if name in ('plain', 'inline'):
                            entry = [i for i, text in enumerate(texts)
                                     if 'This control editorial note explains' in text]
                            self.assertEqual(entry, equation)
                            self.assertIn('This completes the proof.', texts[entry[0]])
                        if name == 'hint':
                            links = [link for page in document for link in page.get_links()]
                            self.assertEqual(len(links), 2)
                            self.assertTrue(all(link['from'].width > 0
                                                and link['from'].height > 0
                                                and link['page'] == 0 for link in links))

    def test_long_unfinished_prose_remains_breakable(self):
        source = BASE.replace('height:88mm', 'height:80mm').replace(
            LEAD, '#lorem(420) This last unfinished line introduces').replace(NOTE, '')
        with tempfile.TemporaryDirectory(prefix='display-long-', dir='/tmp') as td:
            root = Path(td)
            (root / 'content').mkdir()
            for name in STYLES:
                shutil.copy2(ROOT / 'content' / name, root / 'content' / name)
            (root / 'sample.typ').write_text(source)
            subprocess.run(['typst', 'compile', '--root', str(root),
                            '--ignore-system-fonts', '--font-path',
                            str(ROOT / 'assets/fonts'), str(root / 'sample.typ'),
                            str(root / 'sample.pdf')], check=True,
                           capture_output=True, text=True)
            with fitz.open(root / 'sample.pdf') as document:
                self.assertGreaterEqual(len(document), 3)
                self.assertEqual(sum('last unfinished line introduces' in page.get_text()
                                     for page in document), 1)


if __name__ == '__main__':
    unittest.main()
