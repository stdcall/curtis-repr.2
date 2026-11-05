"""Native unnumbered appendices have their own strictly checked label family."""
import copy
import json
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

import fitz
from pypdf import PdfReader

import test_heading_titles as titles
from lint_typst import coverage_checks, label_problem, LABELLED, EXPRESSION


class AppendixContractTests(unittest.TestCase):
    def evaluated(self, root, source, labels):
        titles.HeadingTitleTests().fixture(root, source)
        names = '(' + ', '.join(json.dumps(name) for name in labels) + ',)'
        expression = '(..(' + EXPRESSION + '), labelled: ' + LABELLED.replace('LABELS', names) + ')'
        result = subprocess.run([
            'typst', 'eval', '--root', str(root), '--font-path', str(root / 'fonts'),
            '--ignore-system-fonts', '--in', str(root / 'sample.typ'), expression,
        ], capture_output=True, text=True, timeout=45)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stderr, '')
        return json.loads(result.stdout)

    def test_actual_native_appendix_query_pdf_reference_and_counter(self):
        with tempfile.TemporaryDirectory(prefix='native-appendix-', dir='/tmp') as td:
            root = Path(td)
            source = titles.DRIVER.replace('INSERT', '').replace('LETTER', '1').replace('NEXTCOUNT', '2')
            source = source.replace('ss:appendix', 'app:basic-formulas')
            labels = re.findall(r'<([a-z:-]+)>', source)
            data = self.evaluated(root, source, labels)
            found = data['labelled']['app:basic-formulas']
            self.assertEqual(found['count'], 1)
            self.assertEqual(found['record']['value'], {
                'kind': 'native-heading', 'family': 'heading', 'level': 4, 'numbering': None})
            self.assertEqual(coverage_checks(data, {k: ('sample.typ', 1) for k in labels}, False), [])
            result = titles.HeadingTitleTests().run_typst(root, 'compile')
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stderr, '')
            doc = fitz.open(root / 'sample.pdf')
            self.assertEqual(len(doc), 4)
            self.assertIn('FORWARD Appendix to §49A', doc[0].get_text().replace('\xa0', ' '))
            self.assertIn('BACKWARD Appendix to §49A', doc[3].get_text().replace('\xa0', ' '))
            reader = PdfReader(root / 'sample.pdf')
            dest = reader.named_destinations['app:basic-formulas'].dest_array
            self.assertEqual(dest[0].idnum, reader.pages[2].indirect_reference.idnum)
            self.assertEqual(dest[1], '/XYZ')
            top = float(reader.pages[2].mediabox.height) - float(dest[3])
            self.assertLess(abs(top - (float(found['record']['position']['y'][:-2]) - 10)), .03)
            self.assertFalse(any(m['label'] == '<numbered>' and m['value'].get('level') == 4
                                 for m in data['metadata']))

    def test_actual_wrong_level_numbering_type_duplicate_and_missing_rejected(self):
        cases = {
            'wrong level': '#heading(level:3, numbering:none)[Appendix] <app:sample>',
            'numbered': '#heading(level:4, numbering:"1")[Appendix] <app:sample>',
            'wrong type': '#block[Appendix] <app:sample>',
            'duplicate': '#heading(level:4, numbering:none)[A] <app:sample>\n'
                         '#heading(level:4, numbering:none)[B] <app:sample>',
            'missing': 'No appendix.',
        }
        for name, body in cases.items():
            with self.subTest(name=name), tempfile.TemporaryDirectory(
                    prefix='bad-native-appendix-', dir='/tmp') as td:
                root = Path(td)
                data = self.evaluated(root, body, ['app:sample'])
                findings = coverage_checks(data, {'app:sample': ('sample.typ', 1)}, False)
                self.assertEqual(len(findings), 1, findings)
                self.assertEqual(findings[0]['rule'], 'T012')
                self.assertEqual(findings[0]['severity'], 'error')

    def test_prefix_and_descriptor_contract_does_not_relax_ss(self):
        self.assertIsNone(label_problem('app:basic-formulas'))
        for bad in ('app:49A', 'app:', 'appendix:basic-formulas'):
            self.assertIsNotNone(label_problem(bad))
        value = {'kind': 'native-heading', 'family': 'heading', 'level': 4, 'numbering': None}
        data = {'metadata': [], 'labelled': {'app:sample': {
            'count': 1, 'record': {'value': value, 'position': {'page': 1, 'x': '1pt', 'y': '1pt'}}}}}
        self.assertEqual(coverage_checks(data, {}, False), [])
        for kind in ('numbered', 'unnumbered'):
            mutant = copy.deepcopy(data)
            mutant['labelled']['app:sample']['record']['value']['kind'] = kind
            self.assertEqual(len(coverage_checks(mutant, {}, False)), 1)
        mutant = copy.deepcopy(data)
        del mutant['labelled']['app:sample']['record']['value']['numbering']
        self.assertEqual(len(coverage_checks(mutant, {}, False)), 1)
        mutant = copy.deepcopy(data)
        mutant['labelled']['ss:sample'] = mutant['labelled'].pop('app:sample')
        self.assertEqual(len(coverage_checks(mutant, {}, False)), 1)
        # A native app descriptor cannot cover a coincident numbered object.
        mutant = copy.deepcopy(data)
        mutant['metadata'] = [{'label': '<numbered>', 'value': {
            'kind': 'numbered', 'family': 'prop', 'number': [49, 1]},
            'position': {'page': 1, 'x': '1pt', 'y': '1pt'}}]
        self.assertEqual(len(coverage_checks(mutant, {}, False)), 1)


if __name__ == '__main__':
    unittest.main()
