"""Native case fragments separated by an ordinary author paragraph."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

import fitz

ROOT = Path(os.environ.get('BOOK_TEST_ROOT', Path(__file__).resolve().parents[2]))
sys.path.insert(0, str(ROOT / 'scripts'))
from check_links import check_links

FRAGMENTS = '#import "content/book-style.typ": book-style\n#import "content/statements.typ": *\n#show: book-style\n#set page(header:none,footer:none,height:170mm)\n= Engineering Prefix Contracts <ch:engineering-prefix>\n== Literal Case Names <sec:engineering-prefix>\n#lemma[\n#case-list(prefix:"Case ", numbering:"1.",\n [#case[FIRST Body one.] <case:first>],\n \n [#case[LAST Body two.] <case:last>],\n)\nThe requested reference is Case~@case:last.\n#case-list(prefix:"Case ", numbering:"1.",start:4,\n [#case[START Four has a nested list.\n #case-list([#case[INNER Default nested case.] <case:inner>])\n ] <case:start>],\n [#case[RESTORE Five resumes the outer prefix.] <case:restore>],\n)\n#case-list([#case[RESET A new ordinary list.] <case:reset>])\nNative references: @case:start; @case:inner; @case:restore; @case:reset.\n] <lem:engineering-prefix>\n'


class CasePrefixTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='case-prefix-', dir='/tmp')
        self.root = Path(self.temp.name)
        (self.root / 'content').mkdir()
        for name in ('book-style.typ', 'main-defs.typ', 'note-layout.typ',
                     'numbering.typ', 'statements.typ'):
            shutil.copy2(ROOT / 'content' / name, self.root / 'content' / name)
        shutil.copytree(ROOT / 'assets/fonts', self.root / 'assets/fonts')
        shutil.copy2(ROOT / 'editorial.bib', self.root / 'editorial.bib')

    def tearDown(self):
        self.temp.cleanup()

    def command(self, action, *args):
        return subprocess.run(
            ['typst', action, '--root', '.', '--ignore-system-fonts',
             '--font-path', 'assets/fonts', *args], cwd=self.root,
            capture_output=True, text=True)

    def test_prefix_insertion_start_and_nested_restore(self):
        for inserted in (False, True):
            with self.subTest(inserted=inserted):
                source = FRAGMENTS
                if inserted:
                    source = source.replace('[#case[LAST', '[#case[INSERTED Extra case.] <case:inserted>],\n [#case[LAST')
                (self.root / 'fixture.typ').write_text(source)
                compiled = self.command('compile', 'fixture.typ', 'fixture.pdf')
                self.assertEqual(compiled.returncode, 0, compiled.stderr)
                expression = '''(
                  cases:query(metadata).filter(m=>type(m.value)==dictionary and
                    m.value.at("family",default:none)=="case").map(m=>m.value.number),
                  refs:query(metadata).filter(m=>type(m.value)==dictionary and
                    m.value.at("kind",default:none)=="cross-reference").map(m=>
                      m.value+(position:m.location().position(),
                        target-position:m.value.target-location.position())),
                  counts:(<case:first>,<case:last>,<case:start>,<case:inner>,
                    <case:restore>,<case:reset>).map(l=>query(l).len()),
                )'''
                evaluated = self.command('eval', expression, '--in', 'fixture.typ')
                self.assertEqual(evaluated.returncode, 0, evaluated.stderr)
                data = json.loads(evaluated.stdout)
                self.assertEqual(data['cases'], ([[1],[2],[3]] if inserted else [[1],[2]]) + [[4],[1],[5],[1]])
                self.assertEqual(data['counts'], [1]*6)
                self.assertEqual([r['printed'] for r in data['refs']],
                                 ['3' if inserted else '2','4','(1)','5','(1)'])
                result = check_links(self.root / 'fixture.pdf', data['refs'])
                self.assertEqual(result['semantic_references_checked'], 5)
                text = '\n'.join(p.get_text() for p in fitz.open(self.root / 'fixture.pdf'))
                self.assertIn('Case 1. FIRST', text)
                self.assertIn('Case 3. LAST' if inserted else 'Case 2. LAST', text)
                self.assertIn('Case 4. START', text)
                self.assertIn('Case 5. RESTORE', text)

    def test_prefix_validation(self):
        for replacement, diagnostic in (
            ('prefix:1', 'case-list prefix must be a string'),
            ('prefix:"Case ", numbering:(n)=>str(n)', 'case-list with prefix requires a numbering pattern'),
        ):
            source=FRAGMENTS.replace('prefix:"Case ", numbering:"1."', replacement, 1)
            (self.root/'invalid.typ').write_text(source)
            compiled=self.command('compile','invalid.typ','invalid.pdf')
            self.assertNotEqual(compiled.returncode,0)
            self.assertIn(diagnostic,compiled.stderr)


if __name__ == '__main__':
    unittest.main()
