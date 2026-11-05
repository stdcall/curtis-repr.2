"""Actual inline math links retain exact destinations in the production export."""
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
from lint_typst import LABELLED, evaluate


class InlineReferenceExportTests(unittest.TestCase):
    def test_inline_symbolic_references_track_moved_native_targets(self):
        with tempfile.TemporaryDirectory(prefix='inline-reference-export-', dir='/tmp') as td:
            root = Path(td)
            (root / 'content').mkdir()
            (root / 'config').mkdir()
            (root / 'config/project.json').write_text(json.dumps({
                'entry': 'sample.typ', 'stage': 'final',
                'font_paths': [str(ROOT / 'assets/fonts')],
            }))
            for name in ('book-style.typ', 'main-defs.typ', 'note-layout.typ',
                         'numbering.typ', 'statements.typ'):
                shutil.copy2(ROOT / 'content' / name, root / 'content' / name)
            source = '''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#import "content/numbering.typ": section-counter
#show: book-style
#section-counter.update(31)
PADDING
#named-equation(name: [$(xi)$])[$ 0 -> L -> M -> N -> 0 $] <eq:source-sequence>
#pagebreak()
#named-equation(name: [$(hat(xi))$])[$ 0 -> hat(L) -> hat(M) -> hat(N) -> 0 $] <eq:completed-sequence>
#pagebreak()
The sequence @eq:source-sequence maps to @eq:completed-sequence.
Hence $#[@eq:source-sequence]=0$ if and only if
$#[@eq:completed-sequence]=0$.#footnote[AUTHORNOTE]
'''
            destinations = []
            for padding in ('', 'Before the targets.#pagebreak()'):
                (root / 'sample.typ').write_text(source.replace('PADDING', padding))
                base = ['typst', '--root', str(root)]
                options = ['--ignore-system-fonts', '--font-path',
                           str(ROOT / 'assets/fonts')]
                compiled = subprocess.run([base[0], 'compile', *base[1:], *options,
                                           str(root / 'sample.typ'), str(root / 'sample.pdf')],
                                          capture_output=True, text=True, check=True)
                self.assertEqual(compiled.stderr, '')
                result, data = evaluate(root, labels=[
                    'eq:source-sequence', 'eq:completed-sequence'])
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stderr, '')
                targets = subprocess.run([base[0], "eval", *base[1:], *options,
                                          "--in", str(root / "sample.typ"),
                                          LABELLED.replace("LABELS",
                                            '("eq:source-sequence", "eq:completed-sequence")')],
                                         capture_output=True, text=True, check=True)
                native_targets = json.loads(targets.stdout)
                self.assertEqual(data['labelled'], native_targets)
                refs = [it['value'] for it in data['metadata']
                        if isinstance(it['value'], dict)
                        and it['value'].get('kind') == 'cross-reference']
                self.assertEqual(len(refs), 4)
                self.assertNotIn('target-location', result.stdout)
                with fitz.open(root / 'sample.pdf') as pdf:
                    for ref in refs:
                        self.assertTrue(ref['resolved'])
                        target = native_targets[ref['target']]['record']
                        self.assertEqual(ref['target-position'], target['position'])
                        position = ref['position']
                        point = ref['target-position']
                        xy = lambda key: float(point[key][:-2])
                        links = [a for a in pdf[position['page'] - 1].get_links()
                                 if a['kind'] == fitz.LINK_GOTO
                                 and a['page'] == point['page'] - 1
                                 and abs(a['to'].x - xy('x')) < .03
                                 and abs(a['to'].y - max(0, xy('y') - 10)) < .03]
                        self.assertTrue(links)
                        sx, sy = (float(position[key][:-2]) for key in ('x', 'y'))
                        self.assertEqual(sum(a['from'].x0 - .03 <= sx <= a['from'].x1 + .03
                                             and a['from'].y0 - .03 <= sy <= a['from'].y1 + .03
                                             for a in links), 1)
                        self.assertTrue(all(a['from'].width > 0
                                            and a['from'].height > 0 for a in links))
                    destinations.append([ref['target-position']['page'] for ref in refs])
            self.assertEqual(destinations, [[1, 2, 1, 2], [2, 3, 2, 3]])
