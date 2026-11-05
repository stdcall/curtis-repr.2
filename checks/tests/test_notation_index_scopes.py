"""Pure metadata checks: notation identity follows native chapter destinations."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'scripts'))
from check_indexes import index_checks


def position(page, y=10):
    return {'page': page, 'x': '10pt', 'y': f'{y}pt'}


HEADINGS = [
    {'label': '<ch:first>', 'level': 1, 'numbered': True,
     'position': position(1)},
    {'label': '<ch:later>', 'level': 1, 'numbered': True,
     'position': position(10)},
    {'label': '<ch:unnumbered>', 'level': 1, 'numbered': False,
     'position': position(11)},
]
LABELLED = {'def:first': {'count': 1, 'record': {
    'value': {'family': 'def'}, 'position': position(2)}}}


def mark(name, meaning, page=2, **extra):
    return {'value': {'kind': 'notation-mark', 'path': [name],
                      'meaning': meaning, **extra}, 'position': position(page)}


def errors(data, **extra):
    return index_checks(data, kind='notation-mark', headings=HEADINGS,
                        labelled=LABELLED, **extra)[0]


class NotationScopes(unittest.TestCase):
    def test_case_sensitive_names(self):
        self.assertEqual(errors([mark('$A(G)$', 'algebra'),
                                 mark('$a(G)$', 'ring')]), [])

    def test_distinct_chapters(self):
        self.assertEqual(errors([mark('$A(G)$', 'exponent'),
                                 mark('$A(G)$', 'algebra', 12)]), [])

    def test_explicit_later_chapter_overrides_target_and_mark(self):
        data = [mark('$A(G)$', 'exponent'),
                mark('$A(G)$', 'algebra', target='def:first',
                     **{'chapter-target': 'ch:later'}),
                mark('$A(G)$', 'algebra', 12)]
        self.assertEqual(errors(data), [])

    def test_late_mark_uses_native_target_position(self):
        self.assertEqual(errors([mark('$A(G)$', 'exponent', 12,
                                      target='def:first'),
                                 mark('$A(G)$', 'algebra', 12)]), [])

    def test_same_scope_conflict(self):
        result = errors([mark('$A(G)$', 'exponent'),
                         mark('$A(G)$', 'algebra')])
        self.assertEqual(len(result), 1)
        self.assertIn('conflicting explanations', result[0])

    def test_no_context_still_detects_conflict(self):
        result = index_checks([mark('A', 'first'), mark('A', 'second')],
                              kind='notation-mark')[0]
        self.assertEqual(len(result), 1)

    def test_missing_targets_are_diagnostic(self):
        self.assertIn('unresolved target', errors([
            mark('A', 'first', target='def:absent')])[0])
        self.assertIn('unresolved chapter target', errors([
            mark('A', 'first', **{'chapter-target': 'ch:absent'})])[0])

    def test_subject_casefold_and_global_identity_unchanged(self):
        data = [{'value': {'kind': 'index-mark', 'path': [name]},
                 'position': position(page)}
                for name, page in [('Group', 2), ('group', 12)]]
        self.assertIn('spelled several ways', index_checks(data)[0][0])

    def test_same_page_heading_boundary(self):
        headings = [HEADINGS[0], {**HEADINGS[1], 'position': position(2, 20)}]
        data = [mark('A', 'first'), mark('A', 'second')]
        data[1]['position'] = position(2, 30)
        self.assertEqual(index_checks(data, kind='notation-mark',
                                     headings=headings, labelled={})[0], [])


if __name__ == '__main__':
    unittest.main()
