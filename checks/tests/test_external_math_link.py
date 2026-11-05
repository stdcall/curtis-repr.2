"""Isolated native regression; pass the project root as BOOK_PROJECT.

No companion file is read or evaluated. Only its pinned catalogue is used.
"""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import fitz
from pypdf import PdfReader, PdfWriter

sys.dont_write_bytecode = True
ROOT = Path(os.environ.get('BOOK_TEST_ROOT', Path(__file__).resolve().parents[2]))
OLD = 'link(external-uri(target), box(anchored-first(body, anchor)))'
NEW = 'box(link(external-uri(target), block(anchored-first(body, anchor))))'
FIXTURE = '''#import "content/book-style.typ": book-style
#import "content/statements.typ": proposition
#show: book-style
= Engineering
== Native companion links
#proposition[Local control.] <prop:local-control>
Local @prop:local-control. Plain @i:prop:permutation-hecke-formulas.

$ D in B backslash G "/" B quad
  ("see" #[@i:prop:permutation-hecke-formulas]) $

Adjacent @i:prop:permutation-hecke-formulas@i:prop:permutation-hecke-formulas.
$ #[@i:prop:permutation-hecke-formulas] #[@i:prop:permutation-hecke-formulas] $

Different @i:prop:permutation-hecke-formulas@i:th:schur-zassenhaus.
$ #[@i:prop:permutation-hecke-formulas] #[@i:th:schur-zassenhaus] $

Caption @i:prop:permutation-hecke-formulas[explicit caption].
$ (#[@i:prop:permutation-hecke-formulas[explicit caption]]) $

Inline $x = #[@i:prop:permutation-hecke-formulas]$ and ordinary prose.

Ordinary punctuation (11.34), not a reference.

#pagebreak()
Caption brackets @i:prop:permutation-hecke-formulas[(descriptive caption)].
Styled @i:prop:permutation-hecke-formulas[_italic_ and *bold* caption].
$ #[@i:prop:permutation-hecke-formulas[_italic_ and *bold* caption]] $

Repeated inline $#[@i:prop:permutation-hecke-formulas]#[@i:prop:permutation-hecke-formulas]$.

Local again @prop:local-control. Last plain @i:th:schur-zassenhaus.
'''
EXPR = '''{
  import "/content/main-defs.typ": metadata-value
  query(metadata).map(m => (
    ..metadata-value(m), position: m.location().position()))
}'''


def ownership(reader):
    """Every annotation has exactly one matching native OBJR owner."""
    tree = reader.trailer['/Root']['/StructTreeRoot']
    nums = tree['/ParentTree']['/Nums']
    parents = dict(zip(nums[::2], nums[1::2]))
    count = 0
    actual = set()
    owners = set()
    for page in reader.pages:
        for ref in page.get('/Annots', []):
            obj = ref.get_object()
            parent = parents[obj['/StructParent']].get_object()
            owners.add(parents[obj['/StructParent']].idnum)
            assert parent['/S'] == '/Link'
            kids = parent['/K']
            if not isinstance(kids, list):
                kids = [kids]
            matches = [k for k in kids if isinstance(k, dict) and
                       k.get('/Type') == '/OBJR' and k.get('/Obj') == ref]
            assert len(matches) == 1
            actual.add(ref.idnum)
            count += 1
    referenced = []
    def walk(node):
        node = node.get_object() if hasattr(node, 'get_object') else node
        if isinstance(node, list):
            for child in node:
                walk(child)
        elif isinstance(node, dict):
            if node.get('/Type') == '/OBJR':
                referenced.append(node['/Obj'].indirect_reference.idnum)
            elif '/K' in node:
                walk(node['/K'])
    walk(tree['/K'])
    assert len(referenced) == len(set(referenced)) == count
    assert set(referenced) == actual
    assert len(owners) == count
    return count


class ExternalMathLinks(unittest.TestCase):
    def test_native_links_are_bijective_without_changing_visible_output(self):
        keep = os.environ.get('FIXTURE_OUTPUT')
        temporary = None if keep else tempfile.TemporaryDirectory(
            prefix='external-math-', dir='/tmp')
        base = Path(keep or temporary.name)
        base.mkdir(parents=True, exist_ok=True)
        checker = base / 'external_references.py'
        shutil.copyfile(ROOT / 'scripts/external_references.py', checker)
        spec = importlib.util.spec_from_file_location('fixture_checker', checker)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        catalog = json.loads((ROOT / 'config/external-references.json').read_text())
        module.validate_catalog(catalog)
        raw_source = (ROOT / 'content/main-defs.typ').read_text()
        self.assertEqual(raw_source.count(NEW), 1)
        results = {}
        for variant in ('baseline', 'candidate'):
            root = base / variant
            (root / 'content').mkdir(parents=True, exist_ok=True)
            (root / 'config').mkdir(exist_ok=True)
            for name in ('book-style.typ', 'main-defs.typ', 'note-layout.typ',
                         'numbering.typ', 'statements.typ'):
                shutil.copyfile(ROOT / 'content' / name, root / 'content' / name)
            source = raw_source.replace(NEW, OLD) if variant == 'baseline' else raw_source
            (root / 'content/main-defs.typ').write_text(source)
            (root / 'config/external-references.json').write_text(json.dumps(catalog))
            (root / 'fixture.typ').write_text(FIXTURE)
            options = ['--root', str(root), '--ignore-system-fonts',
                       '--font-path', str(ROOT / 'assets/fonts'), '--input',
                       'external-catalog=config/external-references.json']
            for cmd, args in (
                ('compile', [str(root / 'fixture.typ'), str(root / 'raw.pdf')]),
                ('eval', [EXPR, '--in', str(root / 'fixture.typ')]),
            ):
                proc = subprocess.run(['typst', cmd, *options, *args],
                    capture_output=True, text=True, timeout=60)
                (root / (cmd + '.log')).write_text(proc.stderr)
                self.assertEqual(proc.returncode, 0, proc.stderr)
                self.assertEqual(proc.stderr, '')
                if cmd == 'eval':
                    (root / 'metadata.json').write_text(proc.stdout)
            data = json.loads((root / 'metadata.json').read_text())
            external = [m for m in data if m.get('kind') == 'external-reference']
            self.assertEqual(len(external), 19)
            writer = PdfWriter(root / 'raw.pdf')
            module.rewrite_external_links(writer, catalog)
            writer.write(root / 'checked.pdf')
            reader = PdfReader(root / 'checked.pdf')
            if variant == 'baseline':
                with self.assertRaisesRegex(AssertionError, 'expected one companion link'):
                    module.check_external_links(reader, external, catalog)
            else:
                result = module.check_external_links(reader, external, catalog)
                self.assertEqual(result['annotations'], len(external))
                self.assertEqual(ownership(reader), len(external) + 2)
                (base / 'strict-actions.json').write_text(json.dumps(result, indent=2))
            results[variant] = {'metadata': data, 'external': len(external),
                'annotations': sum(len(p.get('/Annots', [])) for p in reader.pages)}
        self.assertEqual(results['baseline']['metadata'], results['candidate']['metadata'])
        def local_actions(reader):
            pages = {p.indirect_reference.idnum: i for i, p in enumerate(reader.pages)}
            actions = []
            for i, page in enumerate(reader.pages):
                for a in page.get('/Annots', []):
                    a = a.get_object()
                    action = a.get('/A', {})
                    d = a.get('/Dest', action.get('/D'))
                    if action.get('/S') == '/GoToR' or d is None:
                        continue
                    if isinstance(d, str):
                        d = reader.named_destinations[d].dest_array
                    self.assertEqual(str(d[1]), '/XYZ')
                    self.assertIn(str(d[4]), ('NullObject', '0'))
                    actions.append((i, list(a['/Rect']), pages[d[0].idnum],
                                    float(d[2]), float(d[3]), str(d[4])))
            return actions
        self.assertEqual(local_actions(PdfReader(base / 'baseline/checked.pdf')),
                         local_actions(PdfReader(base / 'candidate/checked.pdf')))
        before = fitz.open(base / 'baseline/raw.pdf')
        after = fitz.open(base / 'candidate/checked.pdf')
        self.assertEqual(len(before), 2)
        self.assertEqual(len(before), len(after))
        for i, (a, b) in enumerate(zip(before, after), 1):
            self.assertEqual(a.get_pixmap(dpi=108).samples, b.get_pixmap(dpi=108).samples)
            self.assertEqual(a.get_text(), b.get_text())
            self.assertEqual(a.get_texttrace(), b.get_texttrace())
            self.assertEqual(sorted(before.extract_font(f[0])[3] for f in a.get_fonts()),
                             sorted(after.extract_font(f[0])[3] for f in b.get_fonts()))
            self.assertEqual(b.get_images(), [])
            for span in b.get_texttrace():
                for char in span['chars']:
                    self.assertNotEqual(char[1], 0)
                    self.assertTrue(b.rect.contains(fitz.Rect(char[3])))
            b.get_pixmap(dpi=108).save(base / f'candidate-{i}.png')
        (base / 'results.json').write_text(json.dumps(results, indent=2))
        if temporary:
            temporary.cleanup()


if __name__ == '__main__':
    unittest.main()
