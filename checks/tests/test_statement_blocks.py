"""A statement opening stays with its first indivisible native block."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import fitz

ROOT = Path(__file__).resolve().parents[2]
STYLES = ('book-style.typ', 'main-defs.typ', 'note-layout.typ',
          'numbering.typ', 'statements.typ')


class StatementBlocks(unittest.TestCase):
    def test_inline_math_introduction_keeps_heading_with_diagram_block(self):
        with tempfile.TemporaryDirectory(prefix='statement-block-', dir='/tmp') as td:
            root = Path(td)
            (root / 'content').mkdir()
            for name in STYLES:
                shutil.copyfile(ROOT / 'content' / name, root / 'content' / name)
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            (root / 'sample.typ').write_text('''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#import "content/numbering.typ": section-counter
#show: book-style
#set page(height:150mm, header:none, footer:none)
#section-counter.update(38)
#block(height:55mm)[PADDING]
#lemma(name:"BLOCKHEADER")[
  Consider a diagram of $Lambda$-modules
  #block(height:60mm, breakable:false)[DIAGRAMTOKEN]
  The diagram completes the assertion.
] <lem:diagram-opening>
Reference @lem:diagram-opening.
''')
            output = root / 'sample.pdf'
            result = subprocess.run(['typst', 'compile', '--root', str(root),
                '--ignore-system-fonts', '--font-path', str(root / 'assets/fonts'),
                str(root / 'sample.typ'), str(output)], capture_output=True,
                text=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stderr)
            with fitz.open(output) as document:
                heads = [(i, r) for i, page in enumerate(document)
                         for r in page.search_for('BLOCKHEADER')]
                diagrams = [(i, r) for i, page in enumerate(document)
                            for r in page.search_for('DIAGRAMTOKEN')]
                self.assertEqual(len(heads), 1)
                self.assertEqual(len(diagrams), 1)
                self.assertEqual(heads[0][0], diagrams[0][0])
                self.assertLess(heads[0][1].y0, diagrams[0][1].y0)
                links = [link for page in document for link in page.get_links()]
                self.assertEqual(len(links), 1)
                self.assertEqual(links[0]['page'], heads[0][0])
