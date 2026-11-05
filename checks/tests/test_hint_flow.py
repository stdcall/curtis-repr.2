"""Native paragraph, exercise and diagram flow at actual page boundaries."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

import test_numbering
from check_links import check_hint_links, check_links


class HintFlow(unittest.TestCase):
    fixture = test_numbering.NumberingTests.fixture
    compile = test_numbering.NumberingTests.compile

    @staticmethod
    def token_page(document, token):
        pages = [page.number for page in document if token in page.get_text()]
        if len(pages) != 1:
            raise AssertionError((token, pages))
        return pages[0]

    def test_completed_brackets_do_not_bind_the_next_block(self):
        for ending in (".", ".]", ".)", ".’", ".”", ".])", ". ]", "unfinished"):
            with self.subTest(ending=ending):
                with tempfile.TemporaryDirectory(prefix="paragraph-tail-", dir="/tmp") as td:
                    root = Path(td)
                    self.fixture(root)
                    sentence = "COMPLETED This paragraph has a complete sentence" + ending
                    if ending == "unfinished":
                        sentence = "UNFINISHED This introduces the following assertion"
                    sentence = sentence.replace("]", r"\]")
                    (root / "sample.typ").write_text(
                        '#import "content/book-style.typ": book-style\n'
                        '#show: book-style\n'
                        '#set page(header: none, footer: none, height: 100mm)\n'
                        '#block(height: 38mm)[FILLER]\n'
                        + sentence
                        + '\n\n#block(height: 25mm, breakable: false)[NEXTBLOCK]\n')
                    document = self.compile(root)
                    self.assertEqual(self.token_page(document, "NEXTBLOCK"), 1)
                    token = "UNFINISHED" if ending == "unfinished" else "COMPLETED"
                    self.assertEqual(self.token_page(document, token),
                                     1 if ending == "unfinished" else 0)
                    document.close()

    def test_external_hint_stays_with_exercise_and_can_continue(self):
        for padding in (79, 81, 83):
            for long in (False, True):
                with self.subTest(padding=padding, long=long):
                    with tempfile.TemporaryDirectory(prefix="external-hint-", dir="/tmp") as td:
                        root = Path(td)
                        self.fixture(root)
                        hint = "HINTBEGIN Use the preceding assertion. HINTEND"
                        if long:
                            hint = ("HINTBEGIN " +
                                    "A long hint retains its ordinary paragraph flow. " * 60
                                    + "HINTEND")
                        (root / "sample.typ").write_text(
                            '#import "content/book-style.typ": book-style\n'
                            '#import "content/statements.typ": *\n'
                            '#show: book-style\n'
                            '#set page(header: none, footer: none, height: 140mm)\n'
                            '== Probe <sec:probe>\n'
                            f'#block(height: {padding}mm)[FILLER]\n'
                            '#exercise[EXERCISEBODY Prove the assertion for every finite group.]\n'
                            '<exc:probe>\n'
                            '#hint([@exc:probe])[' + hint + ']\n')
                        document = self.compile(root)
                        opening = self.token_page(document, "EXERCISEBODY")
                        self.assertEqual(opening, self.token_page(document, "HINTBEGIN"))
                        end = self.token_page(document, "HINTEND")
                        if long:
                            self.assertGreater(end, opening)
                        else:
                            self.assertEqual(end, opening)
                        self.assertTrue(all(page.get_text().strip() for page in document))
                        links = [link for page in document for link in page.get_links()]
                        self.assertEqual(len(links), 2)
                        self.assertTrue(all(link["from"].width > 0 and link["from"].height > 0
                                            for link in links))
                        document.close()

    def test_hint_keeps_labelled_diagram_with_closing_paragraph(self):
        for padding in (55, 60, 65):
            with self.subTest(padding=padding):
                with tempfile.TemporaryDirectory(prefix="hint-diagram-tail-", dir="/tmp") as td:
                    root = Path(td)
                    self.fixture(root)
                    (root / "sample.typ").write_text(
                        '#import "content/book-style.typ": book-style\n'
                        '#import "content/statements.typ": *\n'
                        '#show: book-style\n'
                        '#set page(header: none, footer: none, height: 140mm)\n'
                        '== Probe <sec:diagram-probe>\n'
                        f'#block(height: {padding}mm)[FILLER]\n'
                        '#exercise[EXERCISE Prove the assertion.\n\n'
                        '#hint([@exc:diagram-probe])[Use this diagram:\n'
                        '#block(width: 100%, height: 20mm, breakable: false,\n'
                        'align(center)[DIAGRAM $ A arrow.r B $]) <fig:diagram-probe>\n'
                        'CLOSING The horizontal maps are isomorphisms, so the assertion follows.]\n'
                        '] <exc:diagram-probe>\n'
                        '#context metadata((kind: "diagram-target",\n'
                        'count: query(<fig:diagram-probe>).len()))\n')
                    document = self.compile(root)
                    self.assertEqual(self.token_page(document, "DIAGRAM"),
                                     self.token_page(document, "CLOSING"))
                    self.assertEqual(sum(page.get_text().count("→") for page in document), 1)
                    self.assertTrue(all(page.get_text().strip() for page in document))
                    document.close()
                    command = [
                        "typst", "eval", "--root", str(root), "--input", "stage=draft",
                        "--font-path", str(root / "fonts"), "--ignore-system-fonts",
                        "--in", str(root / "sample.typ"),
                        'query(metadata).filter(it => type(it.value) == dictionary '
                        'and it.value.at("kind", default: none) '
                        'in ("diagram-target", "hint-link")).map(it => it.value)',
                    ]
                    result = subprocess.run(command, capture_output=True, text=True, timeout=60)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    records = json.loads(result.stdout)
                    labels = [r for r in records if r["kind"] == "diagram-target"]
                    self.assertEqual([r["count"] for r in labels], [1])
                    routes = [r for r in records if r["kind"] == "hint-link"]
                    self.assertEqual(check_hint_links(check_links(root / "sample.pdf", []), routes),
                                     {"problems_with_hint": 1, "problems_without_hint": 0,
                                      "hint_numbers": 1})
