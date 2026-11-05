"""Prepared native paragraphs survive a repeated note-flow pass."""
from pathlib import Path
import json, os, shutil, subprocess, tempfile, unittest
import fitz

HERE = Path(__file__).parent
ROOT = Path(os.environ.get("BOOK_TEST_ROOT", Path(__file__).resolve().parents[2]))

class NoteContinuationTests(unittest.TestCase):
    def build(self, name):
        temp = tempfile.TemporaryDirectory(prefix="native-note-continuation-", dir="/tmp")
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        (root / "content").mkdir()
        for f in ("book-style.typ", "main-defs.typ", "note-layout.typ",
                  "numbering.typ", "statements.typ"):
            shutil.copy2(ROOT / "content" / f, root / "content" / f)
        shutil.copytree(ROOT / "assets/fonts", root / "assets/fonts")
        (root / "fixture.typ").write_text((HERE / "fixtures" / "note-continuation" / (name + ".typ")).read_text())
        args = ["--root", ".", "--ignore-system-fonts", "--font-path", "assets/fonts"]
        c = subprocess.run(["typst", "compile", *args, "fixture.typ", "fixture.pdf"],
                           cwd=root, capture_output=True, text=True)
        self.assertEqual((c.returncode, c.stderr), (0, ""))
        q = subprocess.run(["typst", "eval", *args, "--in", "fixture.typ",
                            (HERE / "fixtures" / "note-continuation" / "expression.typ").read_text()],
                           cwd=root, capture_output=True, text=True)
        self.assertEqual((q.returncode, q.stderr), (0, ""))
        return fitz.open(root / "fixture.pdf"), json.loads(q.stdout)

    def test_later_proof_note_and_original_prose_survive(self):
        for name, phrase in (("actual-author-proof", "cohomology of groups"),
                             ("actual-editorial-proof", "This projection commutes")):
            with self.subTest(name=name):
                doc, data = self.build(name)
                self.assertEqual(len(data["notes"]), 1)
                text = " ".join(" ".join(p.get_text() for p in doc).split())
                self.assertIn(phrase, text)
                if name == "actual-author-proof":
                    self.assertIn("Cassels", text)
                    self.assertIn("Huppert", text)
                    self.assertIn("Weiss", text)
                for note in data["notes"]:
                    self.assertEqual(note["marker"]["page"], note["entry"]["page"])

    def test_prepared_native_paragraph_is_a_fixed_point(self):
        doc, data = self.build("idempotence")
        self.assertTrue(data["idempotence"][0]["equal"])
        self.assertEqual(len(data["notes"]), 1)
        self.assertIn("A later native continuation", doc[0].get_text())

    def test_long_breakable_and_opening_ordinary_controls(self):
        doc, data = self.build("long-proof")
        self.assertEqual(len(doc), 2)
        self.assertEqual(len(data["notes"]), 1)
        self.assertTrue(any(p.search_for("LONGEND") for p in doc[1:]))
        doc, data = self.build("actual74-26")
        self.assertEqual(len(data["notes"]), 1)
        doc, data = self.build("ordinary")
        self.assertEqual(len(doc), 1)
        self.assertEqual(len(data["notes"]), 0)

if __name__ == "__main__":
    unittest.main()
