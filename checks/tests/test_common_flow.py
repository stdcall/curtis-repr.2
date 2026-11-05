"""Actual PDF contracts for closing blocks and repeated author notes."""
from pathlib import Path
import os
import json
import shutil
import subprocess
import sys
import tempfile
import unittest

import fitz

ROOT = Path(os.environ.get('BOOK_TEST_ROOT', Path(__file__).resolve().parents[2]))
sys.path.insert(0, str(ROOT / 'scripts'))
from check_links import check_hint_links, check_links


class NativeFlowContracts(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix='common-flow-', dir='/tmp')
        cls.root = Path(cls.temp.name)
        (cls.root / 'content').mkdir()
        for name in ('book-style.typ', 'main-defs.typ', 'note-layout.typ',
                     'numbering.typ', 'statements.typ'):
            shutil.copyfile(ROOT / 'content' / name, cls.root / 'content' / name)
        shutil.copytree(ROOT / 'assets/fonts', cls.root / 'assets/fonts')
        shutil.copyfile(ROOT / 'editorial.bib', cls.root / 'editorial.bib')

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def build(self, name, body, height=140):
        source = '''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#show: book-style
#set page(header:none,footer:none,height:''' + str(height) + '''mm)
== Probe <sec:probe>
''' + body
        (self.root / (name + '.typ')).write_text(source)
        p = subprocess.run(['typst', 'compile', '--root', '.', '--ignore-system-fonts', '--font-path', 'assets/fonts', name + '.typ', name + '.pdf'], cwd=self.root, capture_output=True, text=True)
        self.assertEqual(p.returncode, 0, p.stderr)
        doc = fitz.open(self.root / (name + '.pdf'))
        self.assertTrue(all(p.get_text().strip() for p in doc), 'Unexpected empty page')
        return doc

    @staticmethod
    def pages(doc, token):
        return [i + 1 for i, p in enumerate(doc) if p.search_for(token)]

    def test_definition_closes_with_its_diagram(self):
        for pad in [65, 70, 75]:
            with self.subTest(padding=pad):
                doc = self.build('definition-' + str(pad), f'#block(height:{pad}mm)[FILLER]\n' + '''#definition[
An equivalence is given by this diagram:
#block(width:100%,height:16mm,align(center)[DIAGRAM $ A arrow.r B $]) <diagram:closing>
COMMUTES commutes.
] <def:closing>
AFTER The next paragraph is outside the definition.
''')
                self.assertEqual(self.pages(doc, 'DIAGRAM'), self.pages(doc, 'COMMUTES'))

    def test_nested_hint_keeps_native_display_and_reciprocal_routes(self):
        for pad in [75, 80]:
            with self.subTest(padding=pad):
                name = 'nested-' + str(pad)
                doc = self.build(name, f'#block(height:{pad}mm)[FILLER]\n' + '''#exercise[
EXERCISE Prove the existence of the canonical map
$ t: R arrow.r S quad "DISPLAY". $ <eq:closing>
#hint([@exc:closing])[HINTSTART Use the preceding assertion and its central subgroup statement. HINTEND]
] <exc:closing>
AFTER The next paragraph is outside the exercise.
''')
                self.assertEqual(self.pages(doc, 'DISPLAY'), self.pages(doc, 'HINTSTART'))
                expression = '(equations:query(<eq:closing>).map(e=>repr(e.func())), records:query(metadata).filter(m=>type(m.value)==dictionary and m.value.at("kind",default:none)=="numbered").map(m=>m.value))'
                p = subprocess.run(['typst','eval','--root','.','--ignore-system-fonts','--font-path','assets/fonts',expression,'--in',name+'.typ'],cwd=self.root,capture_output=True,text=True)
                self.assertEqual(p.returncode,0,p.stderr)
                data=json.loads(p.stdout)
                self.assertEqual(data['equations'],['equation'])
                self.assertEqual([x['number'] for x in data['records'] if x.get('family')=='eq'],[[1,1]])
                links=[(i+1,l) for i,p in enumerate(doc) for l in p.get_links() if l['kind']==fitz.LINK_GOTO]
                self.assertEqual(len(links),2)
                self.assertTrue(all(i==l['page']+1 for i,l in links))

    def test_repeated_note_stops_before_long_proof_tail(self):
        for pad in [0,15,30]:
            with self.subTest(padding=pad):
                tail=('A continuation retains native paragraphs and all its text while crossing page boundaries. '*5+'\n\n')*10
                doc=self.build('note-'+str(pad),f'#block(height:{pad}mm)[FILLER]\n'+'''#lemma[
FIRSTMARK A short lemma has an author note#footnote[NOTEENTRY Exactly one full entry.] <fn:shared>.
#enum(numbering:"(i)",[First assertion.],[Second assertion.])
] <lem:shared>
#proof[
PROOFSTART The opening argument is short.

REPEAT The same note is used here#footnote(<fn:shared>), and the paragraph ends.

'''+tail+'''
PROOFEND The proof is complete.
]
AFTER The following paragraph is outside the proof.
''',height=150)
                self.assertEqual(self.pages(doc,'FIRSTMARK'),self.pages(doc,'REPEAT'))
                self.assertEqual(self.pages(doc,'REPEAT'),self.pages(doc,'NOTEENTRY'))
                self.assertEqual(len(self.pages(doc,'PROOFEND')),1)
                self.assertGreater(self.pages(doc,'PROOFEND')[0],self.pages(doc,'REPEAT')[0])
                for page in doc:
                    self.assertTrue(all(5<=w[1] and w[3]<=page.rect.height-5 for w in page.get_text('words')),'Proof overprints page boundary')

    def test_long_nested_hint_remains_breakable(self):
        hint='HINTSTART '+('A long hint retains native paragraphs and all of its words and symbols. '*8+'\n\n')*8+' HINTEND'
        doc=self.build('long-hint','''#exercise[
EXERCISE Prove the assertion.
$ t: R arrow.r S. $ <eq:closing>
#hint([@exc:closing])['''+hint+''']
] <exc:closing>
AFTER This follows the exercise.
''')
        self.assertGreater(self.pages(doc,'HINTEND')[0],self.pages(doc,'HINTSTART')[0])
        self.assertEqual(len(self.pages(doc,'HINTEND')),1)
        self.assertEqual(len(self.pages(doc,'AFTER')),1)

    def test_large_unrelated_native_body_beside_short_repeated_note(self):
        # Unrelated paragraphs remain outside the shared note's span.
        paragraphs = []
        for i in range(320):
            paragraphs.append(f'ROW{i:04d} ' + ' '.join(
                'A native inline symbol $x$ stays in ordinary prose.'
                for _ in range(12)
            ))
        unrelated = ('LARGEFIRST Begin.\n\n' + '\n\n'.join(paragraphs)
                     + '\n\nLARGELAST End.')
        doc = self.build('large-unrelated', '#let unrelated = [\n' + unrelated + '''
]
#lemma[FIRSTMARK A short note#footnote[NOTEENTRY Full entry.] <fn:large>.] <lem:large>
#proof[REPEAT Use the same mark#footnote(<fn:large>).]
#unrelated
''', height=250)
        text = ''.join(page.get_text() for page in doc)
        self.assertEqual(text.count('LARGEFIRST'), 1)
        self.assertEqual(text.count('LARGELAST'), 1)
        self.assertTrue(all(text.count(f'ROW{i:04d}') == 1 for i in range(320)))
        self.assertEqual(self.pages(doc, 'FIRSTMARK'), self.pages(doc, 'REPEAT'))
        self.assertEqual(self.pages(doc, 'REPEAT'), self.pages(doc, 'NOTEENTRY'))
        for page in doc:
            self.assertTrue(all(5 <= word[1] and word[3] <= page.rect.height - 5
                                for word in page.get_text('words')),
                            'Native body overprints page boundary')

    def test_nested_case_hints_keep_their_note_and_reciprocal_routes(self):
        argument = ('The argument uses the canonical module $M$ and its summand '
                    '$N$, retaining the native action. ') * 7
        body = '''#import "content/main-defs.typ": ed-note
#block(height:70mm)[FILLER]
#exercise[
Prove the following assertions for the given module.
#case-list(numbering:"(i)",
 [#case[FIRSTCASE Prove the first assertion.
 #hint([@exc:probe])[''' + argument + '''ANCHORPOINT#ed-note[
ENTRYPOINT The original assertion requires a correction. The counterexample
uses a native module and its direct summand. The full note remains available
on the page of its printed sign.]]
 ] <case:first>],
 [#case[SECONDCASE Prove the second assertion.
 #hint([@exc:probe])[Use the first assertion and the native direct sum decomposition.]
 ] <case:second>],
 [#case[THIRDCASE Prove the third assertion.
 #hint([@exc:probe])[Use the first two assertions and the native module action.]
 ] <case:third>],
)
] <exc:probe>
#exercise[EXNEXT Prove the next assertion about the same module.] <exc:next>
#hint([@exc:next])[Use the preceding assertion and the canonical decomposition.]
'''
        doc = self.build('nested-case-note', body, height=200)
        self.assertEqual(self.pages(doc, 'ANCHORPOINT'), self.pages(doc, 'ENTRYPOINT'))
        self.assertEqual(sum(len(page.get_links()) for page in doc), 8)
        expression = '''(
          cases: (<case:first>,<case:second>,<case:third>).map(l=>query(l).len()),
          hints: query(metadata).filter(m=>type(m.value)==dictionary and
            m.value.at("kind",default:none)=="hint-link").map(m=>m.value)
        )'''
        result = subprocess.run([
            'typst', 'eval', '--root', '.', '--ignore-system-fonts',
            '--font-path', 'assets/fonts', expression,
            '--in', 'nested-case-note.typ'], cwd=self.root,
            capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr)
        data = json.loads(result.stdout)
        self.assertEqual(data['cases'], [1, 1, 1])
        self.assertEqual(check_hint_links(
            check_links(self.root / 'nested-case-note.pdf', []), data['hints']),
            {'problems_with_hint': 2, 'problems_without_hint': 0, 'hint_numbers': 4})


if __name__ == '__main__':
    unittest.main()
