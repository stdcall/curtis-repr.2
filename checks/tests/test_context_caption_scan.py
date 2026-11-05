from pathlib import Path
import importlib.util
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]

def load(path):
    sys.path.insert(0, str(path.parent))
    spec = importlib.util.spec_from_file_location('caption_lint', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

lint = None

class ContextCaptionScan(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        global lint
        if lint is None:
            lint = load(ROOT / 'scripts/lint_typst.py')

    def test_same_line_caption_closer_ends_context(self):
        text = '#lemma[@prop:other[#context title("x")]] <lem:after>\n'
        kinds, _ = lint.scan(text)
        self.assertEqual(kinds[text.index('<lem:after>')], lint.MARKUP)

    def test_nested_caption_preserves_later_object_labels(self):
        text = '''#lemma[
  #case-list(
    [#case[
      By @case:other[#context number-text(
        "(" + reference-data(<def:other>).text + ")",
      )]. The assertion follows.
    ] <case:part>],
  )
] <lem:parent>

#theorem[$K=QQ[x]$ is a ring.] <th:later>
'''
        kinds, _ = lint.scan(text)
        for label in ('<case:part>', '<lem:parent>', '<th:later>'):
            with self.subTest(label=label):
                self.assertEqual(kinds[text.index(label)], lint.MARKUP)
        self.assertEqual(kinds[text.index('<def:other>')], lint.CODE)

    def test_brackets_inside_code_string_and_content_are_not_terminators(self):
        text = '''#let title = [a [nested] title]
#lemma[@prop:other[#context title.at(0, default: [a [nested] title])]]
<lem:after>
#let text = "a ] bracket"
<rem:after-line>
'''
        kinds, _ = lint.scan(text)
        for label in ('<lem:after>', '<rem:after-line>'):
            self.assertEqual(kinds[text.index(label)], lint.MARKUP)
        self.assertEqual(kinds[text.index('a ] bracket')], lint.STRING)

if __name__ == '__main__':
    lint = load(ROOT / 'scripts/lint_typst.py')
    unittest.main()
