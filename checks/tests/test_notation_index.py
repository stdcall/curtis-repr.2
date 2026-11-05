"""Subject and notation marks retain separate meanings and native targets."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

from pypdf import PdfReader

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_indexes import index_checks
from check_links import check_links


class NotationIndex(unittest.TestCase):
    def test_categories_and_conflicting_explanations(self):
        data = [{'value': {'kind': 'index-mark', 'path': ['GROUP']}},
                {'value': {'kind': 'notation-mark', 'path': ['group'],
                           'meaning': 'First meaning'}}]
        self.assertEqual(index_checks(data)[0], [])
        self.assertEqual(index_checks(data, kind='notation-mark')[0], [])
        data.append({'value': {'kind': 'notation-mark', 'path': ['group'],
                               'meaning': 'Different meaning'}})
        self.assertTrue(index_checks(data, kind='notation-mark')[0])

    def test_late_marks_both_link_to_the_definition_and_its_page(self):
        with tempfile.TemporaryDirectory(prefix='notation-index-', dir='/tmp') as temporary:
            root = Path(temporary)
            (root / 'content').mkdir()
            for name in ('book-style.typ', 'main-defs.typ', 'note-layout.typ',
                         'numbering.typ', 'statements.typ', 'index-style.typ',
                         'notation-index-style.typ'):
                shutil.copyfile(ROOT / 'content' / name, root / 'content' / name)
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            source = root / 'sample.typ'
            source.write_text('''#import "content/book-style.typ": book-style
#import "content/main-defs.typ": *
#import "content/statements.typ": *
#import "content/index-style.typ": subject-index
#import "content/notation-index-style.typ": notation-index
#import "content/numbering.typ": section-counter
#show: book-style
#counter(heading).update(4)
= Algebraic K-Theory <ch:test>
#section-counter.update(38)
#definition[DEFANCHOR is the actual definition.] <def:target>
#pagebreak()
= Class Groups <ch:later>
Late marks occur on a different page.
#idx("Grothendieck group", target: [@def:target])
#nidx("$G_0(A)$", "Grothendieck group", target: [@def:target], chapter: [@ch:later])
#heading(level:1, numbering:none)[Notation Index] <ch:notation-index>
#notation-index()
#heading(level:1, numbering:none)[Index] <ch:subject-index>
#subject-index
''')
            arguments = ['--root', str(root), '--ignore-system-fonts',
                         '--font-path', str(root / 'assets/fonts')]
            result = subprocess.run(['typst', 'compile', *arguments, str(source),
                                     str(root / 'sample.pdf')], capture_output=True,
                                    text=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stderr)
            expression = '''{
              import "/content/main-defs.typ": metadata-value
              query(metadata).map(m => (
                ..metadata-value(m), position: m.location().position()))
            }'''
            result = subprocess.run(['typst', 'eval', *arguments, expression,
                '--in', str(source)], capture_output=True, text=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stderr)
            metadata = json.loads(result.stdout)
            references = [r for r in metadata if r.get('kind') == 'cross-reference']
            report = check_links(root / 'sample.pdf', references)
            locators = [r for r in report['references']
                        if r['target'] in ('index-mark', 'notation-mark')]
            self.assertEqual(len(locators), 2)
            self.assertTrue(all(r['to_page'] == 1 for r in locators))
            reader = PdfReader(root / 'sample.pdf')
            text = '\n'.join(p.extract_text() for p in reader.pages)
            self.assertIn('Notation Index', text)
            self.assertIn('Chapter 6:', ' '.join(text.split()))
            self.assertIn('Grothendieck group', text)
            self.assertEqual(index_checks(metadata, kind='notation-mark')[0], [])
