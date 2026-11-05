"""Check the subject index marks, `#idx(..path)`, placed in the text.

A mark is `metadata((kind: "index-mark", path: ("Element", "nilpotent")))`:
the path of the entry in the index of the book, heading first. The page
numbers come from where the marks stand, so there is nothing to compare with
the printed index; what remains is what free-text marks get wrong on their
own. An older single-term form (`term`, optional `sub`) is still read, so a
change of the helper's signature does not silently empty the index.
"""
from collections import defaultdict
import re


def marks(metadata, kind='index-mark'):
    for item in metadata:
        value = item.get('value', item)
        if isinstance(value, dict) and value.get('kind') == kind:
            yield value, item.get('position') or value.get('position')


def entry_path(value):
    path = value.get('path')
    if path is None and 'term' in value:
        sub = value.get('sub')
        path = [value['term']] + (sub if isinstance(sub, list)
                                  else [sub] if sub else [])
    return path


def spelling_key(level):
    return ' '.join(level.split()).casefold()


def position_key(position):
    return (position['page'],
            float(str(position['y']).removesuffix('pt')),
            float(str(position['x']).removesuffix('pt')))


def notation_scope(value, position, headings, labelled):
    """Use native numbered chapter destinations, not mark placement."""
    if headings is None:
        return None
    chapters = [h for h in headings
                if h.get('level') == 1 and h.get('numbered')]
    if 'chapter-target' in value:
        target = value['chapter-target']
        chapter = next((h for h in chapters
                        if h.get('label') == '<' + target + '>'), None)
        if chapter is None:
            raise ValueError(f'notation has unresolved chapter target {target!r}')
        return chapter['label']
    if 'target' in value:
        target = value['target']
        found = (labelled or {}).get(target, {})
        record = found.get('record')
        if found.get('count') != 1 or not record or not record.get('position'):
            raise ValueError(f'notation has unresolved target {target!r}')
        position = record['position']
    if position is None:
        raise ValueError('notation has no native destination position')
    preceding = [h for h in chapters
                 if position_key(h['position']) <= position_key(position)]
    if not preceding:
        raise ValueError('notation destination has no numbered chapter')
    return max(preceding, key=lambda h: position_key(h['position']))['label']


def index_checks(metadata, *, final=True, kind='index-mark',
                 headings=None, labelled=None):
    """Errors and warnings of the marks; an empty index is an error only in
    the finished book."""
    errors, warnings = [], []
    forms = defaultdict(set)
    meanings = defaultdict(set)
    count = 0
    declared = set()
    related = []
    redirects = defaultdict(set)
    located = set()
    see_related = []
    for value, position in marks(metadata, kind):
        where = f' (PDF page {position["page"]})' if position else ''
        path = entry_path(value)
        if isinstance(path, str):
            path = [path]
        if not isinstance(path, list) or not path:
            errors.append('an index mark carries no path' + where)
            continue
        if not all(isinstance(level, str) and level.strip() for level in path):
            errors.append(f'index path {path!r} has an empty level' + where)
            continue
        if any(level != level.strip() or re.search(r'\s{2,}', level)
               for level in path):
            errors.append(f'index path {path!r} has stray whitespace' + where)
        count += 1
        declared.add(tuple(path))
        if kind == 'index-mark':
            if 'see' in value:
                target = value['see']
                if 'target' in value:
                    errors.append(f'see-only entry {path!r} has a body target' + where)
                if (not isinstance(target, list) or not target or
                        not all(isinstance(level, str) and level.strip()
                                for level in target)):
                    errors.append(f'index entry {path!r} has an empty see path' + where)
                elif any(level != level.strip() or re.search(r'\s{2,}', level)
                         for level in target):
                    errors.append(f'see path {target!r} has stray whitespace' + where)
                elif target == path:
                    errors.append(f'index entry {path!r} refers to itself' + where)
                else:
                    redirects[tuple(path)].add(tuple(target))
                    see_related.append((path, tuple(target), where))
            else:
                located.add(tuple(path))
            targets = value.get('see-also', [])
            if not isinstance(targets, list):
                errors.append(f'index entry {path!r} has invalid see-also paths' + where)
            else:
                for target in targets:
                    if (not isinstance(target, list) or not target or
                            not all(isinstance(level, str) and level.strip()
                                    for level in target)):
                        errors.append(f'index entry {path!r} has an empty see-also path' + where)
                    elif any(level != level.strip() or re.search(r'\s{2,}', level)
                             for level in target):
                        errors.append(f'see-also path {target!r} has stray whitespace' + where)
                    elif target == path:
                        errors.append(f'index entry {path!r} refers to itself' + where)
                    else:
                        related.append((path, tuple(target), where))
        if kind == 'notation-mark':
            meaning = value.get('meaning')
            if not isinstance(meaning, str) or not meaning.strip():
                errors.append(f'notation {path!r} has no explanation' + where)
            else:
                try:
                    scope = notation_scope(value, position, headings, labelled)
                except ValueError as error:
                    errors.append(str(error) + where)
                    scope = None
                meanings[(scope, tuple(path))].add(meaning)
        # A typo in a mark fails nothing by itself: it quietly splits one
        # entry into two that sort next to each other. Catch the near-miss
        # at every level of the path.
        for depth in range(1, len(path) + 1) if kind != 'notation-mark' else ():
            prefix = tuple(path[:depth])
            forms[tuple(spelling_key(p) for p in prefix)].add(prefix)
    for path, targets in redirects.items():
        if len(targets) > 1:
            errors.append(f'index entry {path!r} has conflicting see targets')
        if path in located:
            errors.append(f'index entry {path!r} mixes see and locators')
    if not count:
        (errors if final else warnings).append(
            ('the notation index is empty: no #nidx marks in the text'
             if kind == 'notation-mark' else
             'the index is empty: no #idx marks in the text'))
    for (scope, path), explanations in meanings.items():
        if len(explanations) > 1:
            errors.append(f'notation {path!r} has conflicting explanations')
    reported = set()
    for key, spellings in sorted(forms.items(), key=lambda kv: len(kv[0])):
        if len(spellings) < 2 or any(key[:d] in reported
                                     for d in range(1, len(key))):
            continue
        reported.add(key)
        errors.append('one index entry spelled several ways: '
                      + ', '.join(' / '.join(s) for s in sorted(spellings)))
    for origin, target, where in related:
        if target not in declared:
            (errors if final else warnings).append(
                f'index entry {origin!r} names missing see-also target {list(target)!r}' + where)
    for origin, target, where in see_related:
        if target not in declared:
            (errors if final else warnings).append(
                f'index entry {origin!r} names missing see target {list(target)!r}' + where)
    return errors, warnings
