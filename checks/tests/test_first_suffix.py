"""Native first-suffixed objects and variant destinations, no blank base."""
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
sys.path.insert(0,str(ROOT/'scripts'))
from check_links import check_links

DRIVER = '''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#show: book-style
#set page(header:none,footer:none)
= Native Suffixed Objects <ch:suffix>
== First lettered theorem <sec:suffix>
INSERT
#theorem-suffix(suffix:"A")[FIRSTBODY] <th:first-a>
An ordinary intervening definition paragraph.
#theorem-suffix(base:[@th:first-a],suffix:"B")[SECONDBODY] <th:first-b>
$ upright("NEXTBODY")=1 $ <eq:following>
#pagebreak()
FIRSTREF @th:first-a

SECONDREF @th:first-b

NEXTREF @eq:following
'''

EXPRESSION = '''{
 import "/content/numbering.typ": numbered-record,record-number
 (
   objects:(<th:first-a>,<th:first-b>,<eq:following>).map(l=>{
     let m=numbered-record(l)
     (kind:m.value.kind,family:m.value.family,number:record-number(m),
      suffix:m.value.at("suffix",default:""))
   }),
   labels:(<th:first-a>,<th:first-b>,<eq:following>).map(l=>query(l).len()),
   refs:query(metadata).filter(m=>type(m.value)==dictionary and
     m.value.at("kind",default:none)=="cross-reference").map(m=>m.value+
       (position:m.location().position(),
        target-position:m.value.target-location.position())),
 )
}'''

class FirstSuffixTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='first-suffix-',dir='/tmp')
        self.root=Path(self.temp.name)
        shutil.copytree(ROOT/'content',self.root/'content')
        shutil.copytree(ROOT/'assets/fonts',self.root/'assets/fonts')
        shutil.copy2(ROOT/'editorial.bib',self.root/'editorial.bib')

    def tearDown(self):
        self.temp.cleanup()

    def run_typst(self, action, *args):
        return subprocess.run(['typst',action,'--root','.',
          '--ignore-system-fonts','--font-path','assets/fonts',*args],
          cwd=self.root,capture_output=True,text=True,timeout=60)

    def test_first_variant_next_and_insertion(self):
        for inserted in (False,True):
            with self.subTest(inserted=inserted):
                source=DRIVER.replace('INSERT',
                  '#proposition[PRELUDE] <prop:prelude>' if inserted else '')
                (self.root/'fixture.typ').write_text(source)
                result=self.run_typst('compile','fixture.typ','fixture.pdf')
                self.assertEqual(result.returncode,0,result.stderr)
                self.assertEqual(result.stderr,'')
                result=self.run_typst('eval',EXPRESSION,'--in','fixture.typ')
                self.assertEqual(result.returncode,0,result.stderr)
                data=json.loads(result.stdout)
                n=1+int(inserted)
                self.assertEqual(data['labels'],[1,1,1])
                self.assertEqual(data['objects'],[
                  dict(kind='numbered',family='th',number=[1,n],suffix='A'),
                  dict(kind='variant',family='th',number=[1,n],suffix='B'),
                  dict(kind='numbered',family='eq',number=[1,n+1],suffix='')])
                self.assertEqual([r['printed'] for r in data['refs']],
                                 [f'1.{n}A',f'1.{n}B',f'1.{n+1}'])
                report=check_links(self.root/'fixture.pdf',data['refs'])
                self.assertEqual(report['semantic_references_checked'],3)
                doc=fitz.open(self.root/'fixture.pdf')
                self.assertEqual(len(doc),2)
                text=doc[0].get_text()
                for value in (f'(1.{n}A)',f'(1.{n}B)',f'(1.{n+1})'):
                    self.assertIn(value,text)
                self.assertEqual(len(doc[1].get_links()),3)
                destinations=[(a['page'],a['to'].y) for a in doc[1].get_links()]
                self.assertEqual(len(set(destinations)),3)
                doc.close()

    def test_rejects_nonletter_suffix_and_unnumbered_base(self):
        for source,diagnostic in (
            (DRIVER.replace('suffix:"A"','suffix:"AB"',1),
             'A suffix is one letter or a prime'),
            (DRIVER.replace('#theorem-suffix(suffix:"A")[FIRSTBODY]',
                            '#theorem(numbered:false)[FIRSTBODY]'),
             'A suffix requires a numbered object from the shared series'),
        ):
            (self.root/'invalid.typ').write_text(source.replace('INSERT',''))
            result=self.run_typst('compile','invalid.typ','invalid.pdf')
            self.assertNotEqual(result.returncode,0)
            self.assertIn(diagnostic,result.stderr)

if __name__=='__main__':
    unittest.main()
