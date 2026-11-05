"""A short native table stays together when it fits on a fresh page."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import fitz

ROOT = Path(__file__).resolve().parents[2]
STYLES = ('book-style.typ', 'main-defs.typ', 'note-layout.typ',
          'numbering.typ', 'statements.typ')


class TableFlow(unittest.TestCase):
    def test_short_table_keeps_all_rows_on_one_page(self):
        with tempfile.TemporaryDirectory(prefix='table-flow-', dir='/tmp') as td:
            root = Path(td)
            (root / 'content').mkdir()
            for name in STYLES:
                shutil.copyfile(ROOT / 'content' / name,
                                root / 'content' / name)
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            (root / 'sample.typ').write_text('''#import "content/book-style.typ": book-style
#show: book-style
#set page(height:150mm, header:none, footer:none)
#block(height:80mm)[PRECEDING]
#table(
  columns: (1fr, auto, auto),
  table.header([TABLEHEADER], [Exponent], [Order]),
  [ROWONE], [$1$], [$1$],
  [ROWTWO], [$p^(m-1)$], [$p^(m-1)$],
  [ROWTHREE], [$2$], [$2$],
  [ROWFOUR], [$2$], [$1$],
  [ROWFIVE], [$4$], [$2$],
  [ROWSIX], [$2^(m-1)$], [$2^(m-2)$],
)
AFTERTABLE
''')
            output = root / 'sample.pdf'
            result = subprocess.run([
                'typst', 'compile', '--root', str(root),
                '--ignore-system-fonts', '--font-path',
                str(root / 'assets/fonts'), str(root / 'sample.typ'),
                str(output),
            ], capture_output=True, text=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stderr)
            with fitz.open(output) as document:
                tokens = ('TABLEHEADER', 'ROWONE', 'ROWTWO', 'ROWTHREE',
                          'ROWFOUR', 'ROWFIVE', 'ROWSIX')
                locations = {}
                for token in tokens:
                    found = [(n, rect) for n, page in enumerate(document)
                             for rect in page.search_for(token)]
                    self.assertEqual(len(found), 1, token)
                    locations[token] = found[0]
                self.assertEqual(len({n for n, _ in locations.values()}), 1)
                self.assertGreater(locations['TABLEHEADER'][0], 0)
                self.assertLess(locations['TABLEHEADER'][1].y0,
                                locations['ROWSIX'][1].y0)
                self.assertTrue(any(page.search_for('AFTERTABLE')
                                    for page in document))
