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

FRAGMENTS = '''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#show: book-style
#set page(header:none,footer:none)
= Engineering Contracts <ch:engineering>
== Native Case Fragments <sec:case-fragments>
#definition[
A structure satisfies the following conditions.
#case-list(numbering:"(i)",
 [#case[FIRSTCASE The first condition.] <case:first>],
 [#case[SECONDCASE The second condition.] <case:second>],
 [#case[THIRDCASE The third condition.] <case:third>],
)

AUTHORPARAGRAPH This is a genuine separate explanatory paragraph, not a list item.

#case-list(numbering:"(i)", start:4,
 [#case[FOURTHCASE The final condition.] <case:fourth>],
)
] <def:fragmented-conditions>
References @case:first, @case:second, @case:third, @case:fourth.
#case-list([#case[NEXTCASE An independent ordinary list starts again.] <case:next>])
The independent reference is @case:next.
'''


class CaseStartTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='case-start-', dir='/tmp')
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

    def test_continued_fragment_has_native_numbers_and_real_destinations(self):
        (self.root / 'fixture.typ').write_text(FRAGMENTS)
        compiled = self.command('compile', 'fixture.typ', 'fixture.pdf')
        self.assertEqual(compiled.returncode, 0, compiled.stderr)
        expression = '''(
          cases:query(metadata).filter(m=>type(m.value)==dictionary and
            m.value.at("family",default:none)=="case").map(m=>m.value.number),
          counts:(<case:first>,<case:second>,<case:third>,<case:fourth>,
            <case:next>).map(l=>query(l).len()),
          refs:query(metadata).filter(m=>type(m.value)==dictionary and
            m.value.at("kind",default:none)=="cross-reference").map(m=>
              m.value+(position:m.location().position(),
                target-position:m.value.target-location.position())),
        )'''
        evaluated = self.command('eval', expression, '--in', 'fixture.typ')
        self.assertEqual(evaluated.returncode, 0, evaluated.stderr)
        data = json.loads(evaluated.stdout)
        self.assertEqual(data['cases'], [[1], [2], [3], [4], [1]])
        self.assertEqual(data['counts'], [1] * 5)
        self.assertEqual([r['printed'] for r in data['refs']],
                         ['(i)', '(ii)', '(iii)', '(iv)', '(1)'])
        actual = check_links(self.root / 'fixture.pdf', data['refs'])
        self.assertEqual(actual['semantic_references_checked'], 5)
        doc = fitz.open(self.root / 'fixture.pdf')
        text = '\n'.join(p.get_text() for p in doc)
        self.assertEqual(text.count('AUTHORPARAGRAPH'), 1)
        self.assertIn('(iv)', text)
        self.assertTrue(all(p.get_text().strip() for p in doc))

    def test_start_requires_a_positive_integer(self):
        for start in ('0', '-1', '1.5', '"4"', 'auto'):
            with self.subTest(start=start):
                source = FRAGMENTS.replace('start:4', 'start:' + start)
                (self.root / 'invalid.typ').write_text(source)
                compiled = self.command('compile', 'invalid.typ', 'invalid.pdf')
                self.assertNotEqual(compiled.returncode, 0)
                self.assertIn('case-list start must be a positive integer',
                              compiled.stderr)


if __name__ == '__main__':
    unittest.main()
