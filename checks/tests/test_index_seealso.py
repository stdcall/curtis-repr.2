"""Index cross-links retain definition locators and name actual target rows."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import fitz

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
from check_indexes import index_checks
from check_links import check_links


class IndexSeeAlso(unittest.TestCase):
    @staticmethod
    def mark(path, **fields):
        return {"value": {"kind": "index-mark", "path": path, **fields}}

    def test_unknown_and_malformed_see_also_paths(self):
        good = [self.mark(["Alpha"], **{"see-also": [["Omega"]]}),
                self.mark(["Omega"])]
        self.assertEqual(index_checks(good), ([], []))
        missing = [self.mark(["Alpha"], **{"see-also": [["Missing"]]})]
        self.assertTrue(index_checks(missing)[0])
        self.assertFalse(index_checks(missing, final=False)[0])
        self.assertTrue(index_checks(missing, final=False)[1])
        for target in (["Alpha"], [], [""], [" Omega"], ["Omega  group"]):
            with self.subTest(target=target):
                self.assertTrue(index_checks([
                    self.mark(["Alpha"], **{"see-also": [target]})])[0])
        self.assertTrue(index_checks([
            self.mark(["Alpha"], **{"see-also": "Omega"})])[0])

    def test_actual_row_destination_and_deduplicated_relation(self):
        with tempfile.TemporaryDirectory(prefix="index-see-also-", dir="/tmp") as td:
            root = Path(td)
            (root / "content").mkdir()
            for name in ("book-style.typ", "main-defs.typ", "note-layout.typ",
                         "numbering.typ", "statements.typ", "index-style.typ"):
                shutil.copyfile(ROOT / "content" / name, root / "content" / name)
            shutil.copytree(ROOT / "assets/fonts", root / "fonts")
            source = root / "sample.typ"
            source.write_text('''#import "content/book-style.typ": book-style
#import "content/main-defs.typ": idx
#import "content/index-style.typ": subject-index
#show: book-style
#set page(header: none, footer: none, numbering: "1")
First definition. #idx("Alpha", see-also: (("Omega",),))
Target definition. #idx("Omega")
#pagebreak()
Repeated mark. #idx("Alpha", see-also: (("Omega",),))
#pagebreak()
#subject-index
''')
            arguments = ["--root", str(root), "--ignore-system-fonts",
                         "--font-path", str(root / "fonts")]
            result = subprocess.run(["typst", "compile", *arguments, str(source),
                                     str(root / "sample.pdf")], capture_output=True,
                                    text=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stderr)
            expression = '''{
              import "/content/main-defs.typ": metadata-value
              query(metadata).map(it => (
                ..metadata-value(it), position: it.location().position()))
            }'''
            result = subprocess.run(["typst", "eval", *arguments, expression,
                                     "--in", str(source)], capture_output=True,
                                    text=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stderr)
            metadata = json.loads(result.stdout)
            self.assertEqual(index_checks(metadata), ([], []))
            references = [r for r in metadata if r.get("kind") == "cross-reference"]
            report = check_links(root / "sample.pdf", references)
            related = [r for r in report["references"]
                       if r["target"] == "subject-index-entry"]
            self.assertEqual(len(related), 1)
            self.assertEqual(len(report["references"]), 4)
            self.assertEqual(related[0]["to_page"], 3)
            document = fitz.open(root / "sample.pdf")
            self.assertEqual(len(document), 3)
            self.assertEqual(sum(page.get_text().count("See also") for page in document), 1)
            lines = [line for block in document[2].get_text("dict")["blocks"]
                     if "lines" in block for line in block["lines"]]
            target = [line for line in lines if "".join(
                span["text"] for span in line["spans"]).startswith("Omega")]
            self.assertEqual(len(target), 1)
            self.assertLess(abs(related[0]["target_top_origin"]
                                - (target[0]["bbox"][1] - 10)), 6)
            document.close()
