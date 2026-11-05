"""Pinned references to the companion volume, with exact PDF destinations.

The catalogue contains native object numbers from one published edition.
It never supplies local definitions to the language server.
"""
import hashlib
import math
from pathlib import Path
import re

from pypdf import PdfReader
from pypdf.generic import (ArrayObject, DictionaryObject, FloatObject,
                          NameObject, NullObject, NumberObject,
                          TextStringObject)

URI_PREFIX = 'https://book-reference.invalid/volume-i/'


def uri(target):
    return URI_PREFIX + target


def validate_catalog(catalog):
    assert catalog['schema'] == 1 and catalog['volume'] == 'I'
    edition = catalog['edition']
    assert re.fullmatch(r'[0-9a-f]{64}', edition['sha256'])
    assert re.fullmatch(r'[0-9a-f]{40}', edition['commit'])
    assert re.fullmatch(r'\d{4}-\d{2}-\d{2}\.\d+', edition['release'])
    assert re.fullmatch(r'[\w.-]+\.pdf', edition['filename'])
    assert isinstance(edition['pages'], int) and edition['pages'] > 0
    geometry = catalog['geometry']
    assert all(isinstance(v, (int, float)) and math.isfinite(v) and v > 0
               for v in geometry.values())
    assert set(geometry) == {'width_pt', 'height_pt'}
    for target, value in catalog['targets'].items():
        assert re.fullmatch(r'i:[a-z]+:[a-z0-9-]+', target), target
        assert value['family'] == target.split(':')[1], target
        assert value['kind'] in ('numbered', 'variant', 'unnumbered')
        if value['kind'] == 'unnumbered':
            assert value['number'] is None and value['name']
        else:
            assert isinstance(value['number'], list) and value['number']
            assert all((isinstance(n, int) and n > 0) or
                       (isinstance(n, str) and re.fullmatch('[A-Z]', n))
                       for n in value['number'])
        assert re.fullmatch(r'[a-z′]?', value['suffix'])
        dest = value['destination']
        assert set(dest) == {'page', 'left', 'top', 'zoom'}
        assert type(dest['page']) is int
        assert 0 <= dest['page'] < edition['pages'], target
        assert dest['left'] == 0 and dest['zoom'] is None, target
        assert isinstance(dest['top'], (int, float))
        assert math.isfinite(dest['top'])
        assert 0 <= dest['top'] <= geometry['height_pt'], target
    return catalog


def load_catalog(root):
    import json
    from project import settings
    name = settings(root).get('typst_inputs', {}).get('external-catalog')
    if name is None:
        return None
    path = Path(name)
    assert not path.is_absolute() and '..' not in path.parts
    return validate_catalog(json.loads((root / path).read_text()))


def printed_reference(value):
    if value['kind'] == 'unnumbered':
        return value['name']
    number = value['number']
    separator = '' if value['family'] == 'ss' else '.'
    printed = separator.join(map(str, number)) + value['suffix']
    if value['family'] in ('eq', 'th', 'lem', 'prop', 'cor', 'def', 'rem', 'exm'):
        printed = '(' + printed + ')'
    return printed


def description(value):
    return 'Volume I, ' + printed_reference(value)


def remote_action(catalog, target):
    dest = catalog['targets'][target]['destination']
    # Remove subtraction noise before PDF serialization. Five decimal
    # places exceed the precision of the native target position metadata.
    return DictionaryObject({
        NameObject('/S'): NameObject('/GoToR'),
        NameObject('/F'): TextStringObject(catalog['edition']['filename']),
        NameObject('/D'): ArrayObject([
            NumberObject(dest['page']), NameObject('/XYZ'),
            FloatObject(dest['left']), FloatObject(round(dest['top'], 5)),
            NullObject()]),
    })


def rewrite_external_links(document, catalog):
    """Replace only registered placeholder actions; preserve all rectangles.

    The reference renderer emits one compact, indivisible link per reference.
    The independent checker also requires a bijection with its metadata.
    """
    for page in document.pages:
        for item in page.get('/Annots', []):
            annotation = item.get_object()
            action = annotation.get('/A')
            if action is None:
                continue
            action = action.get_object()
            address = action.get('/URI', '')
            if action.get('/S') != '/URI' or not address.startswith(URI_PREFIX):
                continue
            target = address[len(URI_PREFIX):]
            assert catalog is not None and target in catalog['targets'], \
                f'Unregistered companion reference: {target}'
            assert annotation.get('/Subtype') == '/Link'
            annotation[NameObject('/A')] = remote_action(catalog, target)
            annotation[NameObject('/Contents')] = TextStringObject(
                description(catalog['targets'][target]))


def validate_remote_action(action, catalog, target):
    assert catalog is not None and target in catalog['targets']
    expected = remote_action(catalog, target)
    assert set(action) == set(expected), 'Unexpected remote action fields'
    assert action['/S'] == '/GoToR'
    assert action['/F'] == expected['/F'], 'Wrong companion filename'
    actual, wanted = action['/D'], expected['/D']
    assert len(actual) == 5 and actual[1] == '/XYZ'
    assert type(actual[0]) is NumberObject and actual[0] == wanted[0], \
        'Wrong companion physical page (zero based)'
    assert all(not isinstance(actual[n], NullObject) and
               abs(float(actual[n]) - float(wanted[n])) < 0.0001
               for n in (2, 3)), 'Wrong companion coordinates'
    assert isinstance(actual[4], NullObject), 'Companion link sets a zoom'


def check_external_links(reader, references, catalog):
    if catalog is not None:
        validate_catalog(catalog)
    records = []
    for number, page in enumerate(reader.pages, 1):
        height, width = float(page.mediabox.height), float(page.mediabox.width)
        for item in page.get('/Annots', []):
            annotation = item.get_object()
            if annotation.get('/Subtype') != '/Link':
                continue
            action = annotation.get('/A')
            if action is None:
                continue
            action = action.get_object()
            assert not str(action.get('/URI', '')).startswith(URI_PREFIX), \
                'Companion placeholder remains in the PDF'
            if action.get('/S') != '/GoToR':
                continue
            assert '/Dest' not in annotation
            rectangle = [float(n) for n in annotation['/Rect']]
            assert 0 <= rectangle[0] < rectangle[2] <= width
            assert 0 <= rectangle[1] < rectangle[3] <= height
            records.append({'page': number, 'action': action,
                'rectangle': [rectangle[0], height - rectangle[3],
                              rectangle[2], height - rectangle[1]],
                'description': str(annotation.get('/Contents', ''))})
    used = set()
    checked = []
    for reference in references:
        target = reference['target']
        assert catalog is not None and target in catalog['targets'], target
        assert reference['uri'] == uri(target)
        assert reference['edition-sha256'] == catalog['edition']['sha256']
        source = reference['position']
        x, y = (float(source[n].removesuffix('pt')) for n in ('x', 'y'))
        matches = [(n, record) for n, record in enumerate(records)
                   if record['page'] == source['page']
                   and abs(record['rectangle'][0] - x) < 0.03
                   and record['rectangle'][1] - 0.03 <= y
                   <= record['rectangle'][3] + 0.03]
        assert len(matches) == 1, f'{target}: expected one companion link'
        index, record = matches[0]
        assert index not in used, 'Companion link has duplicate metadata'
        used.add(index)
        validate_remote_action(record['action'], catalog, target)
        assert record['description'] == description(catalog['targets'][target])
        checked.append({'target': target, 'from_page': source['page'],
                        **catalog['targets'][target]['destination']})
    assert len(used) == len(records), 'Unregistered or orphan companion link'
    return {'semantic_references_checked': len(checked),
            'annotations': len(records), 'references': checked,
            'edition': catalog['edition'] if catalog else None,
            'viewer_click_test': 'not performed; actual PDF actions checked'}


def check_companion_file(path, catalog):
    """Optional local pairing check; CI does not fetch the companion PDF."""
    path = Path(path)
    assert path.name == catalog['edition']['filename']
    assert hashlib.sha256(path.read_bytes()).hexdigest() == \
        catalog['edition']['sha256'], 'Companion edition does not match'
    assert len(PdfReader(path).pages) == catalog['edition']['pages']
