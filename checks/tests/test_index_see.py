"""Pure checks for see-only rows and ordinary index cross-links."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_indexes import index_checks


def mark(path, **fields):
    return {'value': {'kind': 'index-mark', 'path': path, **fields}}


class IndexSee(unittest.TestCase):
    def test_redirect_without_a_locator_and_repeated_identical_redirect(self):
        data = [mark(['Alias'], see=['Target']),
                mark(['Alias'], see=['Target']), mark(['Target'])]
        self.assertEqual(index_checks(data), ([], []))

    def test_existing_hierarchical_row_is_a_target(self):
        data = [mark(['Alias'], see=['Group', 'child']),
                mark(['Group', 'child'])]
        self.assertEqual(index_checks(data), ([], []))

    def test_compositional_parent_has_no_generated_anchor(self):
        data = [mark(['Alias'], see=['Group']), mark(['Group', 'child'])]
        self.assertIn('missing see target', index_checks(data)[0][0])

    def test_missing_target_has_draft_warning(self):
        data = [mark(['Alias'], see=['Missing'])]
        self.assertTrue(index_checks(data)[0])
        errors, warnings = index_checks(data, final=False)
        self.assertEqual(errors, [])
        self.assertEqual(len(warnings), 1)

    def test_empty_invalid_and_stray_whitespace_targets(self):
        for target in (None, 'Target', [], [''], [4], [' Target'],
                       ['Target '], ['Two  words']):
            with self.subTest(target=target):
                self.assertTrue(index_checks([
                    mark(['Alias'], see=target), mark(['Target'])])[0])

    def test_self_redirect(self):
        self.assertIn('refers to itself', index_checks([
            mark(['Alias'], see=['Alias'])])[0][0])

    def test_redirect_has_no_body_target(self):
        errors = index_checks([mark(['Alias'], see=['Target'],
                                    target='def:body'), mark(['Target'])])[0]
        self.assertIn('has a body target', errors[0])

    def test_conflicting_redirects(self):
        errors = index_checks([mark(['Alias'], see=['One']),
                               mark(['Alias'], see=['Two']),
                               mark(['One']), mark(['Two'])])[0]
        self.assertEqual(len(errors), 1)
        self.assertIn('conflicting see targets', errors[0])

    def test_redirect_and_locator_conflict_in_either_order(self):
        for reverse in (False, True):
            data = [mark(['Alias'], see=['Target']), mark(['Alias'])]
            if reverse:
                data.reverse()
            errors = index_checks(data + [mark(['Target'])])[0]
            self.assertEqual(len(errors), 1)
            self.assertIn('mixes see and locators', errors[0])

    def test_redirect_does_not_waive_spelling_mismatch(self):
        errors = index_checks([mark(['Alias'], see=['Target']),
                               mark(['alias'], see=['Target']),
                               mark(['Target'])])[0]
        self.assertIn('spelled several ways', errors[0])

    def test_ordinary_and_see_also_semantics_remain(self):
        data = [mark(['Alpha'], **{'see-also': [['Target']]}),
                mark(['Target']), mark(['Target'])]
        self.assertEqual(index_checks(data), ([], []))
        self.assertIn('missing see-also target', index_checks([
            mark(['Alpha'], **{'see-also': [['Missing']]})])[0][0])
        self.assertTrue(index_checks([
            mark(['Alpha'], **{'see-also': [['Alpha']]})])[0])


if __name__ == '__main__':
    unittest.main()
