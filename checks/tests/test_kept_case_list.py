"""Explicitly kept native case lists preserve notes and references."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import tempfile
import unittest
import fitz

HERE = Path(__file__).parent
ROOT = Path(os.environ.get("BOOK_TEST_ROOT", Path(__file__).resolve().parents[2]))

class KeptCaseListTests(unittest.TestCase):
    def build(self, name):
        temp = tempfile.TemporaryDirectory(prefix="kept-native-cases-", dir="/tmp")
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        (root / "content").mkdir()
        for f in ("book-style.typ", "main-defs.typ", "note-layout.typ",
                  "numbering.typ", "statements.typ"):
            shutil.copy2(ROOT / "content" / f, root / "content" / f)
        shutil.copytree(ROOT / "assets/fonts", root / "assets/fonts")
        (root / "fixture.typ").write_text((HERE / "fixtures" / "kept-case-list" / (name + ".typ")).read_text())
        args = ["--root", ".", "--ignore-system-fonts", "--font-path", "assets/fonts"]
        c = subprocess.run(["typst", "compile", *args, "fixture.typ", "fixture.pdf"],
                           cwd=root, capture_output=True, text=True)
        self.assertEqual((c.returncode, c.stderr), (0, ""))
        q = subprocess.run(["typst", "eval", *args, "--in", "fixture.typ",
                            (HERE / "fixtures" / "kept-case-list" / "expression.typ").read_text()],
                           cwd=root, capture_output=True, text=True)
        self.assertEqual((q.returncode, q.stderr), (0, ""))
        return fitz.open(root / "fixture.pdf"), json.loads(q.stdout)

    def test_short_native_list_and_heading_stay_with_entry(self):
        for name in ("exact-176-160", "exact-156-150"):
            with self.subTest(name=name):
                doc, data = self.build(name)
                self.assertEqual(len(doc), 2)
                self.assertEqual(len(data["notes"]), 1)
                note = data["notes"][0]
                self.assertEqual(note["marker"]["page"], note["entry"]["page"])
                pages = {x["position"]["page"] for x in data["records"]
                         if x["value"]["family"] in ("th", "case")}
                self.assertEqual(pages, {2})

    def test_repeat_start_prefix_and_default_long_flow(self):
        doc, data = self.build("repeated")
        self.assertEqual(len(data["notes"]), 3)
        self.assertEqual([r["value"]["printed"] for r in data["refs"]],
                         ["3", "4", "0.1", "(1)"])
        doc, data = self.build("long-near-repeat")
        self.assertGreater(len(doc), 1)
        self.assertEqual(len(data["notes"]), 3)
        for n in data["notes"]:
            self.assertEqual(n["marker"]["page"], n["entry"]["page"])
        doc, data = self.build("ordinary")
        self.assertEqual(len(doc), 1)
        self.assertEqual(len([x for x in data["refs"]
                              if x["value"]["kind"] == "hint-link"]), 2)

if __name__ == "__main__":
    unittest.main()
