"""Native references become strictly pinned companion PDF actions."""
import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

from pypdf import PdfReader, PdfWriter
from pypdf.generic import NameObject, NullObject, NumberObject, TextStringObject

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_links import check_links
from build import accessibility_signature
from external_references import (URI_PREFIX, check_external_links,
    rewrite_external_links, validate_catalog)


class ExternalReferences(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix='companion-', dir='/tmp')
        cls.root = root = Path(cls.temporary.name)
        (root / 'content').mkdir()
        (root / 'config').mkdir()
        for name in ('book-style.typ', 'main-defs.typ', 'note-layout.typ',
                     'numbering.typ', 'statements.typ'):
            shutil.copyfile(ROOT / 'content' / name, root / 'content' / name)
        shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
        cls.catalog = {'schema': 1, 'volume': 'I', 'edition': {
            'release': '2026-11-03.7', 'commit': 'a' * 40,
            'filename': 'companion.pdf', 'sha256': 'b' * 64, 'pages': 3},
            'geometry': {'width_pt': 500, 'height_pt': 700}, 'targets': {}}
        for target, number, page in [('i:th:first', [1, 1], 0),
                                     ('i:ss:last', [2, 'B'], 2)]:
            cls.catalog['targets'][target] = {
                'kind': 'numbered', 'family': target.split(':')[1],
                'number': number, 'suffix': '', 'name': None,
                'destination': {'page': page, 'left': 0,
                                'top': 650.0014399999999,
                                'zoom': None}, 'folio': str(page + 1)}
        validate_catalog(cls.catalog)
        (root / 'config/companion.json').write_text(json.dumps(cls.catalog))
        (root / 'sample.typ').write_text('''#import "content/book-style.typ": book-style
#import "content/main-defs.typ": reference-rules, metadata-value
#import "content/statements.typ": *
#show: book-style
#show: reference-rules
#proposition[LOCALOBJECT.] <prop:local>
Local @prop:local. First @i:th:first. Last @i:ss:last[second subsection].
''')
        command = ['typst', '--root', str(root), '--ignore-system-fonts',
                   '--font-path', str(root / 'assets/fonts'), '--input',
                   'external-catalog=config/companion.json']
        # Subcommands precede their options in the real command line.
        def run(subcommand, *args):
            result = subprocess.run([command[0], subcommand, *command[1:],
                *map(str, args)], cwd=root, capture_output=True, text=True,
                timeout=60)
            if result.returncode:
                raise AssertionError(result.stderr)
            return result.stdout
        cls.raw = root / 'raw.pdf'
        run('compile', root / 'sample.typ', cls.raw)
        expression = '''{
          import "/content/main-defs.typ": metadata-value
          query(metadata).map(m => (
            ..metadata-value(m), position: m.location().position()))
        }'''
        cls.metadata = json.loads(run('eval', expression, '--in', root / 'sample.typ'))
        cls.external = [m for m in cls.metadata if m.get('kind') == 'external-reference']
        cls.internal = [m for m in cls.metadata if m.get('kind') == 'cross-reference']
        cls.final = root / 'final.pdf'
        writer = PdfWriter(cls.raw)
        rewrite_external_links(writer, cls.catalog)
        writer.write(cls.final)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def test_actual_native_pdf_and_first_and_last_companion_pages(self):
        report = check_links(self.final, self.internal,
            external_references=self.external, catalog=self.catalog)
        self.assertEqual(report['semantic_references_checked'], 1)
        external = report['external_references']
        self.assertEqual(external['annotations'], 2)
        self.assertEqual([r['page'] for r in external['references']], [0, 2])
        raw, final = PdfReader(self.raw), PdfReader(self.final)
        rewrite_external_links(raw, self.catalog)
        self.assertEqual(accessibility_signature(raw),
                         accessibility_signature(final))
        for before, after in zip(raw.pages, final.pages):
            self.assertEqual(before.get_contents().get_data(), after.get_contents().get_data())
            self.assertEqual(list(before.mediabox), list(after.mediabox))
            self.assertEqual([list(a.get_object()['/Rect']) for a in before['/Annots']],
                             [list(a.get_object()['/Rect']) for a in after['/Annots']])
        text = '\n'.join(p.extract_text() for p in final.pages)
        self.assertIn('(1.1)', text)
        self.assertIn('second subsection', ' '.join(text.split()))
        self.assertNotIn('?', text)

    def test_rejects_corrupt_or_unregistered_remote_actions(self):
        for change in ('file', 'page', 'left', 'height', 'zoom', 'new-window', 'uri'):
            with self.subTest(change=change):
                reader = PdfReader(self.final)
                annotation = next(a.get_object() for p in reader.pages
                    for a in p.get('/Annots', [])
                    if a.get_object().get('/A', {}).get('/S') == '/GoToR')
                action = annotation['/A']
                if change == 'file':
                    action[NameObject('/F')] = TextStringObject('other.pdf')
                elif change == 'page':
                    action['/D'][0] = NumberObject(1)
                elif change == 'left':
                    action['/D'][2] = NullObject()
                elif change == 'height':
                    action['/D'][3] = NumberObject(651)
                elif change == 'zoom':
                    action['/D'][4] = NumberObject(1)
                elif change == 'new-window':
                    action[NameObject('/NewWindow')] = NumberObject(1)
                else:
                    action[NameObject('/S')] = NameObject('/URI')
                    action[NameObject('/URI')] = TextStringObject(URI_PREFIX + 'i:th:unknown')
                with self.assertRaises(AssertionError):
                    check_external_links(reader, self.external, self.catalog)

    def test_rejects_leftover_placeholders_and_orphan_or_duplicate_metadata(self):
        for path, metadata, catalogue in (
            (self.raw, self.external, self.catalog),
            (self.final, self.external[:-1], self.catalog),
            (self.final, self.external + self.external[:1], self.catalog),
            (self.final, self.external, None)):
            with self.subTest(path=path.name, references=len(metadata), catalogue=bool(catalogue)):
                with self.assertRaises(AssertionError):
                    check_external_links(PdfReader(path), metadata, catalogue)
        unknown = PdfReader(self.raw)
        catalogue = copy.deepcopy(self.catalog)
        catalogue['targets'].pop('i:th:first')
        with self.assertRaises(AssertionError):
            rewrite_external_links(unknown, catalogue)
