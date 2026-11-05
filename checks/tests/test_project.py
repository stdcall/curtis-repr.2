from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_indexes import index_checks
from lint_typst import (scan, semantic_checks, label_problem,
    numbering_source_checks, heading_checks, view, MARKUP, CITED, CODE,
    MATH, STRING, COMMENT, coverage_checks, pitfall_checks, layout_checks,
    Exceptions)
from project import editor_settings, stage


class Scanner(unittest.TestCase):
    def test_modes(self):
        text = 'A #idx(16) b $x_1$ "q" // note\n'
        kinds, ends = scan(text)
        self.assertEqual(kinds[0], MARKUP)
        self.assertEqual(kinds[text.index('idx')], CODE)
        self.assertEqual(kinds[text.index('16')], CODE)
        self.assertEqual(kinds[text.index('x_1')], MATH)
        self.assertEqual(kinds[text.index('"q"')], MARKUP)  # a smart quote
        self.assertEqual(kinds[text.index('note')], COMMENT)
        self.assertIn(text.index(' b'), ends)

    def test_content_blocks_are_prose_and_strings_are_code(self):
        text = '#theorem(title: [Lie])[Body $x$ #idx("Term").]\n'
        kinds, _ = scan(text)
        self.assertEqual(kinds[text.index('Lie')], MARKUP)
        self.assertEqual(kinds[text.index('Body')], MARKUP)
        self.assertEqual(kinds[text.index('Term')], STRING)

    def test_statement_lines(self):
        text = '#let summary = [\n  = Title\n  Text.\n]\n#block(summary)\n'
        kinds, _ = scan(text)
        self.assertEqual(kinds[text.index('Title')], MARKUP)
        self.assertEqual(kinds[text.index('summary)')], CODE)

    def test_layout_checks_match_whole_typst_identifiers(self):
        for text, expected in (
                ('#block-matrix(columns: 2, cells: ())\n', 0),
                ('#text-description[Body.] #h-unit(2)\n', 0),
                ('#block[Body #h(1em)]\n', 2),
                ('#text(size: 9pt)[Body.]\n', 1)):
            kinds, _ = scan(text)
            found = layout_checks('f.typ', text, kinds,
                                  Exceptions({}, 'local_markup'))
            self.assertEqual(len(found), expected, text)

class PageLabels(unittest.TestCase):
    @staticmethod
    def problems(labels):
        from build import page_label_problems
        return page_label_problems(labels)

    def test_well_formed(self):
        self.assertEqual(self.problems(['', 'i', 'ii', '1', '2', '']),
                         [])
        self.assertEqual(self.problems(['', '', 'v', 'vi', '1']), [])
        self.assertEqual(self.problems(['', 'iii', 'iv', 'v', '1', '2']), [])

    def test_malformed(self):
        for labels in (['1', '1'], ['i', '1', '3'], ['2', '3'], ['1', 'i'],
                       ['i', 'ii'], ['A-1'], ['1', '552a']):
            self.assertTrue(self.problems(labels), labels)

class Index(unittest.TestCase):
    @staticmethod
    def marks(*paths):
        return [{'value': {'kind': 'index-mark', 'path': list(p)}}
                for p in paths]

    def test_paths(self):
        errors, warnings = index_checks(self.marks(
            ('Element', 'nilpotent'), ('Element', 'semisimple')))
        self.assertEqual((errors, warnings), ([], []))

    def test_spelling_variants_and_empty_index(self):
        errors, _ = index_checks(self.marks(
            ('Element', 'nilpotent'), ('element', 'nilpotent')))
        self.assertEqual(len(errors), 1)
        self.assertEqual(index_checks([], final=False), (
            [], ['the index is empty: no #idx marks in the text']))
        self.assertEqual(len(index_checks([], final=True)[0]), 1)

class BibliographyLint(unittest.TestCase):
    def test_unknown_key_and_missing_number_fail_in_draft(self):
        data = {'headings': [], 'equations': [], 'metadata': [
            {'label': None, 'value': {
                'kind': 'cross-reference', 'target': 'bib:Nope2000',
                'resolved': False, 'position': {'page': 1}}},
        ]}
        found = [f for f in semantic_checks(
            data, {}, ROOT, False, {'bib:Adams1969': ('f.typ', 1)},
            {'bib:Nope2000': ('f.typ', 2), 'bib:Adams1969': ('f.typ', 3)})
            if f['rule'] == 'T016']
        self.assertEqual(len(found), 2)
        self.assertTrue(all(f['severity'] == 'error' for f in found))
        self.assertIn('Nope2000', found[0]['message'] + found[1]['message'])


class SuffixedDisplays(unittest.TestCase):
    def test_variant_label_must_own_the_display_position(self):
        import copy
        position = {'page': 1, 'x': '10pt', 'y': '20pt'}
        record = {'value': {'kind': 'variant', 'family': 'eq',
                           'number': [1, 2], 'suffix': 'a',
                           'base': 'prop:base'}, 'position': dict(position)}
        data = {'headings': [], 'metadata': [], 'equations': [
            {'label': None, 'block': True, 'numbered': True,
             'position': dict(position)}],
            'labelled': {'eq:variant': {'count': 1, 'record': record}}}

        def display_errors(candidate):
            return [f for f in semantic_checks(
                candidate, {}, ROOT, False, {'eq:variant': ('f.typ', 1)})
                if f['rule'] == 'T013']

        self.assertEqual(display_errors(data), [])
        for mutation in ('missing', 'wrong family', 'different position'):
            with self.subTest(mutation=mutation):
                candidate = copy.deepcopy(data)
                found = candidate['labelled']['eq:variant']
                if mutation == 'missing':
                    found['count'] = 0
                elif mutation == 'wrong family':
                    found['record']['value']['family'] = 'prop'
                else:
                    found['record']['position']['y'] = '21pt'
                self.assertEqual(len(display_errors(candidate)), 1)

    def test_named_label_must_own_one_display_and_have_a_name(self):
        import copy
        position = {'page': 1, 'x': '10pt', 'y': '20pt'}
        record = {'value': {'kind': 'unnumbered', 'family': 'eq',
                           'number': None, 'name': '(*)'},
                  'position': dict(position)}
        data = {'headings': [], 'metadata': [], 'equations': [
            {'label': None, 'block': True, 'numbered': True,
             'position': dict(position)}],
            'labelled': {'eq:named': {'count': 1, 'record': record}}}

        def display_errors(candidate):
            return [f for f in semantic_checks(
                candidate, {}, ROOT, False, {'eq:named': ('f.typ', 1)})
                if f['rule'] == 'T013']

        self.assertEqual(display_errors(data), [])
        for mutation in ('missing', 'duplicate', 'wrong family',
                         'different position', 'empty name', 'wrong kind'):
            with self.subTest(mutation=mutation):
                candidate = copy.deepcopy(data)
                found = candidate['labelled']['eq:named']
                if mutation == 'missing':
                    found['count'] = 0
                elif mutation == 'duplicate':
                    found['count'] = 2
                elif mutation == 'wrong family':
                    found['record']['value']['family'] = 'prop'
                elif mutation == 'different position':
                    found['record']['position']['y'] = '21pt'
                elif mutation == 'empty name':
                    found['record']['value']['name'] = ''
                else:
                    found['record']['value']['kind'] = 'ordinary'
                self.assertEqual(len(display_errors(candidate)), 1)

class HeadingNotes(unittest.TestCase):
    def test_multiline_note_keeps_the_heading_label(self):
        text = ('== A title#footnote[\nNote with @sec:elsewhere.\n] '
                '<sec:heading>\n\nParagraph.\n')
        kinds, _ = scan(text)
        markup = view(text, kinds, (MARKUP, CITED))
        self.assertEqual(heading_checks('chapter.typ', text, markup), [])
        missing = text.replace(' <sec:heading>', '')
        kinds, _ = scan(missing)
        markup = view(missing, kinds, (MARKUP, CITED))
        self.assertEqual([x['rule'] for x in
                          heading_checks('chapter.typ', missing, markup)],
                         ['T011'])


class SourceAnchors(unittest.TestCase):
    """T015: the #source(N) anchors, pages of the source edition, stand once
    each and in the order of the pages."""

    @staticmethod
    def anchors(*pages):
        return {'headings': [], 'equations': [], 'metadata': [
            {'label': None, 'value': {'kind': 'source', 'file-page': page,
                                      'position': {'page': 1}}}
            for page in pages]}

    def rules(self, *pages):
        return [f['rule'] for f in semantic_checks(
            self.anchors(*pages), {}, ROOT, True, {}, {})]

    def test_ascending_pages_pass(self):
        self.assertEqual(self.rules(1, 2, 16, 17), [])

    def test_repeated_or_unordered_pages_fail(self):
        self.assertEqual(self.rules(16, 16), ['T015'])
        self.assertEqual(self.rules(17, 16), ['T015'])
        self.assertEqual(self.rules(0), ['T015'])

    def test_anchor_before_display_keeps_the_sentence(self):
        text = 'It follows that\n\n#source(43)\n$\n a = a\n$\n'
        kinds, ends = scan(text)
        self.assertNotIn('T044', [f['rule'] for f in pitfall_checks(
            'content/sample.typ', text, kinds, ends)])

    def test_standalone_anchor_between_prose_still_fails(self):
        text = 'The same statement holds if\n\n#source(43)\n'
        text += 'the group is finite.\n'
        kinds, ends = scan(text)
        self.assertIn('T044', [f['rule'] for f in pitfall_checks(
            'content/sample.typ', text, kinds, ends)])

    def test_multiline_index_call_is_not_an_unfinished_sentence(self):
        text = '#idx(\n  "Tensor product",\n  target: [@sec:tensor],\n)\n'
        text += '\n#source(84)\nLet the algebra have an identity.\n'
        kinds, ends = scan(text)
        self.assertNotIn('T044', [f['rule'] for f in pitfall_checks(
            'content/sample.typ', text, kinds, ends)])

    def test_closed_parenthetical_sentence_before_source_is_complete(self):
        for ending in ('.)', '.”', '?)]', '…”)'):
            for after in ('\nGiven a module.', 'Given a module.'):
                with self.subTest(ending=ending, after=after):
                    text = '(The exact sequences come from $frak(P)(A)$' + ending
                    text += '\n\n#source(43)' + after + '\n'
                    kinds, ends = scan(text)
                    self.assertNotIn('T044', [f['rule'] for f in pitfall_checks(
                        'content/sample.typ', text, kinds, ends)])
        text = 'The statement holds (under the hypothesis)\n\n#source(43)\n'
        text += 'that the group is finite.\n'
        kinds, ends = scan(text)
        self.assertIn('T044', [f['rule'] for f in pitfall_checks(
            'content/sample.typ', text, kinds, ends)])

    def test_emphasized_sentence_before_source_is_complete(self):
        for opening, closing in (('_', '_'), ('*', '*'), ('_*', '*_')):
            for after in ('\nGiven a module.', 'Given a module.'):
                with self.subTest(opening=opening, after=after):
                    text = 'The result is ' + opening + 'valid.' + closing
                    text += '\n\n#source(43)' + after + '\n'
                    kinds, ends = scan(text)
                    self.assertNotIn('T044', [f['rule'] for f in pitfall_checks(
                        'content/sample.typ', text, kinds, ends)])
            text = 'The result ' + opening + 'holds' + closing
            text += '\n\n#source(43)\nif the group is finite.\n'
            kinds, ends = scan(text)
            self.assertIn('T044', [f['rule'] for f in pitfall_checks(
                'content/sample.typ', text, kinds, ends)])


class ProjectContract(unittest.TestCase):
    def test_editor_stage_matches_build(self):
        self.assertIn('--input=stage=' + stage(),
                      editor_settings()['tinymist.typstExtraArgs'])

    def test_required_semantic_prefixes(self):
        for prefix in ('ch', 'sec', 'th', 'def', 'lem', 'prop', 'cor',
                       'exc', 'eq', 'exm', 'fn'):
            self.assertIsNone(label_problem(prefix + ':sample-object'))
        for label in ('th:1.2', 'def:Group', 'eq:', 'fn:', 'bib:smith1962'):
            self.assertIsNotNone(label_problem(label))
        self.assertIsNone(label_problem('bib:Curtis1962'))
        self.assertIsNone(label_problem('bib:vanderKallen1977'))

    def test_note_continuation_marker_belongs_only_to_helpers(self):
        from lint_typst import source_checks
        config = {'chapter_files': r'content/[0-9]{2}-[a-z-]+\.typ'}
        exceptions = {'literal': Exceptions({}, 'literal_references'),
                      'local': Exceptions({}, 'local_layout')}
        text = 'A native paragraph.<note-continuation>\n'
        helper, _, _ = source_checks(
            'content/note-layout.typ', text, config, exceptions)
        self.assertEqual(helper, [])
        chapter, _, _ = source_checks(
            'content/08-example.typ', text, config, exceptions)
        self.assertEqual([x['rule'] for x in chapter], ['T010'])
        self.assertIn('set by a helper', chapter[0]['message'])
        self.assertIsNotNone(label_problem('note-continuation:object'))

    def test_all_numbered_statements_require_labels(self):
        for helper, prefix in (('theorem', 'th'), ('definition', 'def'),
                ('definitions', 'def'),
                ('lemma', 'lem'), ('proposition', 'prop'),
                ('corollary', 'cor'), ('corollary-suffix', 'cor'),
                ('example', 'exm'), ('examples', 'exm'),
                ('remarks', 'rem'), ('lemma-suffix', 'lem'),
                ('theorem-suffix', 'th'), ('numbered-block', 'eq'),
                ('exercise', 'exc')):
            for suffix, expected in (('', ['T012']),
                                     (' <' + prefix + ':sample>', [])):
                text = '#' + helper + '[Body.]' + suffix + '\n'
                kinds, ends = scan(text)
                found = numbering_source_checks('f.typ', text, kinds, ends)
                self.assertEqual([f['rule'] for f in found], expected,
                                 (helper, suffix))

    def test_final_requires_all_chapters_and_sections(self):
        config = {'completeness': {'chapters': 4, 'sections': 37}}
        data = {'headings': [], 'equations': [], 'metadata': []}
        self.assertEqual(semantic_checks(data, config, ROOT, False, {}), [])
        self.assertEqual([f['rule'] for f in
                          semantic_checks(data, config, ROOT, True, {})],
                         ['T019', 'T019'])
        for level, count in ((1, 4), (2, 37)):
            for n in range(1, count + 1):
                data['metadata'].append({'label': None, 'value': {
                    'kind': 'numbered', 'family': 'heading', 'level': level,
                    'number': [n]}, 'position': {'page': n}})
        # Unlabelled numbered objects remain a separate coverage error.
        self.assertFalse(any(f['rule'] == 'T019' for f in
                         semantic_checks(data, config, ROOT, True, {})))
        data['metadata'][-1]['value']['number'] = [91]
        self.assertTrue(any(f['rule'] == 'T019' for f in
                        semantic_checks(data, config, ROOT, True, {})))



class ContinuingVolumeNumbering(unittest.TestCase):
    def test_complete_volume_requires_its_actual_chapter_and_section_ranges(self):
        config = {'completeness': {'chapters': 7, 'sections': 44,
                  'chapter_start': 5, 'section_start': 38}}
        data = {'headings': [], 'equations': [], 'metadata': []}
        for level, first, count in ((1, 5, 7), (2, 38, 44)):
            data['metadata'].extend({'label': None, 'value': {
                'kind': 'numbered', 'family': 'heading', 'level': level,
                'number': [n]}, 'position': {'page': n}}
                for n in range(first, first + count))
        findings = semantic_checks(data, config, ROOT, True, {})
        self.assertFalse(any(f['rule'] == 'T019' for f in findings))
        for row in data['metadata']:
            row['value']['number'][0] -= 4 if row['value']['level'] == 1 else 37
        findings = semantic_checks(data, config, ROOT, True, {})
        self.assertEqual(sum(f['rule'] == 'T019' for f in findings), 2)


class PdfOutline(unittest.TestCase):
    def test_nested_outlines_keep_height_and_inherit_zoom(self):
        import io
        from pypdf import PdfReader, PdfWriter
        from pypdf.generic import Fit, NullObject
        from build import normalize_outline_destinations
        original = PdfWriter()
        original.add_blank_page(width=300, height=500)
        parent = original.add_outline_item('Chapter', 0,
            fit=Fit.xyz(left=23, top=500, zoom=2))
        original.add_outline_item('Section', 0, parent=parent,
            fit=Fit.xyz(left=34, top=217, zoom=1))
        stream = io.BytesIO()
        original.write(stream)
        stream.seek(0)
        reader = PdfReader(stream)
        writer = PdfWriter(reader)
        self.assertEqual(normalize_outline_destinations(
            writer, reader, left=0), 2)
        result = io.BytesIO()
        writer.write(result)
        result.seek(0)
        checked = PdfReader(result)
        chapter, children = checked.outline
        for destination, top in ((chapter, 500), (children[0], 217)):
            values = destination.dest_array
            self.assertEqual(str(values[1]), '/XYZ')
            self.assertEqual(values[2], 0)
            self.assertEqual(values[3], top)
            self.assertIsInstance(values[4], NullObject)
        self.assertNotIn('/OpenAction', checked.trailer['/Root'])
