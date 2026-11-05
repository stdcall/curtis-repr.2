"""Native note-bearing statement openings retain their page and routes."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import tempfile
import unittest
import fitz

ROOT = Path(os.environ.get("BOOK_TEST_ROOT", Path(__file__).resolve().parents[2]))

class NoteOpeningDisplayTests(unittest.TestCase):
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
        for placement in data["placements"]:
            self.assertEqual(placement["marker-page"], placement["entry-page"], placement)
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

    def test_opening_note_and_statement_move_together(self):
        source = (Path(__file__).parent / "fixtures" /
                  "note-opening-display.typ").read_text()
        prelude = '''#corollary[

  #metadata((kind: "engineering-prelude"))
  #counter("engineering-prelude").update(0)
  #state("engineering-prelude", 0).update(0)

'''
        for pressure, trivia in ((140, False), (150, False), (160, False),
                                 (170, False), (180, False), (170, True)):
            with self.subTest(pressure=pressure, trivia=trivia):
                text = source.replace("height:170mm", f"height:{pressure}mm")
                if trivia:
                    text = text.replace("#corollary[\n", prelude)
                doc, data = self.build(text)
                self.assertEqual(len(data["placements"]), 1)
                self.assertEqual(self.note_routes(doc, data), (1, 1))
                self.assertEqual(sum(len(p.get_links()) for p in doc), 3)
                self.assertEqual(len(doc[0].search_for("ENGINEERING")), 1)
                self.assertEqual(sum(bool(p.search_for("This hypothesis"))
                                     for p in doc), 1)
                self.assertEqual(sum(bool(p.search_for("AFTER"))
                                     for p in doc), 1)


if __name__ == "__main__":
    unittest.main()

