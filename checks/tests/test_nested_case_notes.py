"""Native footnotes inside formal cases retain their page and routes."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import tempfile
import unittest
import fitz

ROOT = Path(os.environ.get("BOOK_TEST_ROOT", Path(__file__).resolve().parents[2]))

RED_SOURCE = '''#import "content/book-style.typ": book-style
#import "content/main-defs.typ": *
#import "content/statements.typ": *
#show: book-style
#set page(height:180mm,header:none,footer:none)
#block(height:45mm)[PAGEPRESSURE]
#proof[
  #case-list(
    [#case[
      #lorem(55) FIRSTMARK#ed-note[First short explanatory note. #lorem(20)]

      #lorem(85)

      It remains to count the simple modules.SECONDMARK#ed-note[Second short explanatory note. #lorem(22)]
      #lorem(170)

      The next ordinary paragraph remains in the same formal case. #lorem(50)
    ] <case:nested-note>],
  )
]
'''
AUTHOR_PREFIX = '''#import "content/book-style.typ": book-style
#import "content/main-defs.typ": *
#import "content/statements.typ": *
#show: book-style
#set page(height:180mm,header:none,footer:none)
#proposition[
  #case-list(prefix:"Case ",numbering:"1.",
    [#case[
      FIRSTAUTHOR The first author observation#footnote[AUTHORONE The complete author explanation stays here.] <fn:shared>.
      
      REPEATAUTHOR The same author explanation applies again#footnote(<fn:shared>).
      
      #case-list(numbering:"(i)",
        [#case[
          STARTNOTE#ed-note[EDITORIALONE This nested editorial explanation has its complete native entry.]
          A nested argument begins at its note and continues normally.
          
          The same nested case also ends a paragraph with its note.ENDNOTE#footnote[AUTHORTWO A second independent author explanation remains complete.]
        ] <case:inner>],
      )
      
      '''
AUTHOR_SUFFIX = '''CASEEND The long case is complete.
    ] <case:outer>],
    [#case[SECONDCASE The second formal assertion remains independent.] <case:second>],
  )
] <prop:notes>
FOLLOWING Ordinary body after the proposition.
References Case~@case:outer, Case~@case:second, and @case:inner.
'''

class NestedCaseNoteTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="native-case-notes-", dir="/tmp")
        self.root = Path(self.temp.name)
        (self.root/"content").mkdir()
        for name in ("book-style.typ","main-defs.typ","note-layout.typ","numbering.typ","statements.typ"):
            shutil.copy2(ROOT/"content"/name,self.root/"content"/name)
        shutil.copytree(ROOT/"assets/fonts",self.root/"assets/fonts")
        shutil.copy2(ROOT/"editorial.bib",self.root/"editorial.bib")

    def tearDown(self):
        self.temp.cleanup()

    def build(self, source):
        (self.root/"fixture.typ").write_text(source)
        args=["--root",".","--ignore-system-fonts","--font-path","assets/fonts"]
        p=subprocess.run(["typst","compile",*args,"fixture.typ","fixture.pdf"],cwd=self.root,capture_output=True,text=True)
        self.assertEqual(p.returncode,0,p.stderr)
        expr='''(
          placements:query(metadata).filter(m=>type(m.value)==dictionary and m.value.at("kind",default:none)=="footnote-placement").map(m=>m.value),
          notes:query(footnote.entry).map(e=>(marker:e.note.location().position(),entry:e.location().position())),
          cases:query(metadata).filter(m=>type(m.value)==dictionary and m.value.at("family",default:none)=="case").map(m=>m.value.number),
        )'''
        p=subprocess.run(["typst","eval",*args,expr,"--in","fixture.typ"],cwd=self.root,capture_output=True,text=True)
        self.assertEqual(p.returncode,0,p.stderr)
        data=json.loads(p.stdout)
        self.assertTrue(all(x["marker-page"]==x["entry-page"]for x in data["placements"]))
        d=fitz.open(self.root/"fixture.pdf")
        self.assertTrue(all(p.get_text().strip()for p in d))
        for page in d:
            self.assertTrue(all(5<=y0 and y1<=page.rect.height-5 for _,y0,_,y1,*_ in page.get_text("words")))
        return d,data

    def note_routes(self, doc, data):
        pt=lambda s:float(s.removesuffix("pt"))
        near=lambda a,b:abs(a[0]-b[0])<.04 and abs(a[1]-b[1])<.04
        links=[(i+1,a)for i,p in enumerate(doc)for a in p.get_links()]
        forwards=backs=0
        for note in data["notes"]:
            m,e=note["marker"],note["entry"]
            fs=[(n,a)for n,a in links if a["kind"]==fitz.LINK_GOTO and a["page"]+1==e["page"]and near(a["to"],[pt(e["x"]),max(0,pt(e["y"])-10)])]
            self.assertTrue(fs)
            self.assertTrue(all(n==e["page"]for n,a in fs))
            bs=[(n,a)for n,a in links if n==e["page"]and a["kind"]==fitz.LINK_GOTO and a["page"]+1==m["page"]and near(a["to"],[pt(m["x"]),max(0,pt(m["y"])-10)])]
            self.assertEqual(len(bs),1)
            forwards+=len(fs);backs+=len(bs)
        return forwards,backs

    def test_editorial_notes_in_split_formal_case(self):
        doc,data=self.build(RED_SOURCE)
        self.assertEqual(len(doc),2)
        self.assertEqual(len(data["placements"]),2)
        self.assertEqual(data["cases"],[[1]])
        self.assertEqual(self.note_routes(doc,data),(2,2))
        self.assertEqual(sum(len(p.get_links())for p in doc),4)

    def test_author_repeated_and_nested_notes_keep_long_case_breakable(self):
        tail="\n\n".join("TAIL"+str(i)+" "+("A native argument retains its paragraphs and complete text. "*12)for i in range(6))
        doc,data=self.build(AUTHOR_PREFIX+tail+AUTHOR_SUFFIX)
        self.assertEqual(len(data["placements"]),3)
        self.assertEqual(data["cases"],[[1],[1],[2]])
        self.assertEqual(self.note_routes(doc,data),(4,3))
        pages=lambda token:[i+1 for i,p in enumerate(doc)if p.search_for(token)]
        self.assertEqual(pages("FIRSTAUTHOR"),pages("REPEATAUTHOR"))
        self.assertGreater(pages("CASEEND")[0],pages("FIRSTAUTHOR")[0])
        for token in ("AUTHORONE","EDITORIALONE","AUTHORTWO","FOLLOWING"):
            self.assertEqual(len(pages(token)),1)


if __name__=="__main__":
    unittest.main()
