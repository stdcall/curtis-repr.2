"""See-only rows link to generated index rows without inventing page locators."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import fitz

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_indexes import index_checks
from check_links import check_links


class IndexSeeNative(unittest.TestCase):
    def test_generated_rows_and_actual_pdf_links(self):
        with tempfile.TemporaryDirectory(prefix='index-see-', dir='/tmp') as td:
            root = Path(td)
            (root / 'content').mkdir()
            for name in ('book-style.typ', 'main-defs.typ', 'note-layout.typ',
                         'numbering.typ', 'statements.typ', 'index-style.typ'):
                shutil.copyfile(ROOT / 'content' / name, root / 'content' / name)
            shutil.copytree(ROOT / 'assets/fonts', root / 'fonts')
            source = root / 'sample.typ'
            source.write_text('''#import "content/book-style.typ": book-style
#import "content/main-defs.typ": idx
#import "content/index-style.typ": subject-index
#show: book-style
#set page(header: none, footer: none, numbering: "1")
First definition. #idx("Alpha", see-also: (("Omega",),))
Target definition. #idx("Omega")
Child definition. #idx("Group", "child")
#idx("Alias", see: ("Omega",))
#idx("Other", see: ("Group", "child"))
#pagebreak()
Repeated ordinary mark. #idx("Alpha", see-also: (("Omega",),))
Repeated redirect. #idx("Alias", see: ("Omega",))
#pagebreak()
#subject-index
''')
            arguments = ['--root', str(root), '--ignore-system-fonts',
                         '--font-path', str(root / 'fonts')]
            result = subprocess.run(['typst', 'compile', *arguments, str(source),
                                     str(root / 'sample.pdf')], capture_output=True,
                                    text=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stderr)
            expression = '''{
              import "/content/main-defs.typ": metadata-value
              query(metadata).map(it => (
                ..metadata-value(it), position: it.location().position()))
            }'''
            result = subprocess.run(['typst', 'eval', *arguments, expression,
                                     '--in', str(source)], capture_output=True,
                                    text=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stderr)
            metadata = json.loads(result.stdout)
            self.assertEqual(index_checks(metadata), ([], []))
            references = [r for r in metadata if r.get('kind') == 'cross-reference']
            locators = [r for r in references if r['target'] == 'index-mark']
            related = [r for r in references if r['target'] == 'subject-index-entry']
            self.assertEqual(len(locators), 4)
            self.assertEqual(len(related), 3)
            self.assertTrue(all(r['position']['page'] == 3 for r in related))
            self.assertCountEqual([r['index-path'] for r in related],
                                  [['Omega'], ['Omega'], ['Group', 'child']])
            report = check_links(root / 'sample.pdf', references)
            self.assertEqual(report['status'], 'passed')
            self.assertEqual(report['semantic_references_checked'], 7)
            self.assertTrue(all(r['to_page'] == 3 for r in report['references']
                                if r['target'] == 'subject-index-entry'))
            with fitz.open(root / 'sample.pdf') as document:
                self.assertEqual(len(document), 3)
                lines = [line for block in document[2].get_text('dict')['blocks']
                         if 'lines' in block for line in block['lines']]
                texts = [''.join(span['text'] for span in line['spans'])
                         for line in lines]
                alias = [text for text in texts if text.startswith('Alias')]
                other = [text for text in texts if text.startswith('Other')]
                self.assertEqual(alias, ['Alias See Omega.'])
                self.assertEqual(other, ['Other See Group, child.'])
                self.assertTrue(any('See also' in text for text in texts))
                for relation in related:
                    name = ', '.join(relation['index-path'])
                    rows = [line for line, text in zip(lines, texts)
                            if text.startswith(name)]
                    self.assertEqual(len(rows), 1)
                    self.assertLess(abs(float(relation['target-position']['y']
                                              .removesuffix('pt'))
                                        - rows[0]['bbox'][1]), 8)


if __name__ == '__main__':
    unittest.main()
