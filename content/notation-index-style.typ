#import "index-style.typ": index-target, index-text, locator, sort-key
#import "note-layout.typ": without-notes
#import "numbering.typ": numbered-record, record-number

#let notation-entries = context {
  let chapters = query(heading.where(level: 1)).filter(it => (
    it.numbering != none
  ))
  let groups = (:)
  for mark in query(<notation-mark>) {
    let destination = index-target(mark)
    if destination == none { continue }
    let chapter = counter(heading).at(destination).first()
    if "chapter-target" in mark.value {
      let target = mark.value.chapter-target
      let group = numbered-record(label(target))
      if group == none {
        metadata((
          kind: "cross-reference",
          target: target,
          resolved: false,
          printed: "?",
          position: here().position(),
        ))
        continue
      }
      assert(group.value.family == "heading" and group.value.level == 1)
      chapter = record-number(group).first()
    }
    let key = str(chapter)
    let entries = groups.at(key, default: (:))
    let name = mark.value.path.first()
    let entry = entries.at(name, default: (
      name: name,
      meaning: mark.value.meaning,
      at: (),
    ))
    assert(
      entry.meaning == mark.value.meaning,
      message: "Conflicting explanations of notation " + name,
    )
    if entry.at.all(it => it.page() != destination.page()) {
      entry.at.push(destination)
    }
    entries.insert(name, entry)
    groups.insert(key, entries)
  }
  for key in groups.keys().sorted(key: int) {
    let chapter = int(key)
    let title = chapters.find(it => (
      counter(heading).at(it.location()).first() == chapter
    ))
    assert(title != none, message: "A notation mark needs a numbered chapter")
    heading(level: 2, numbering: none)[
      Chapter #chapter: #without-notes(title.body)
    ]
    for entry in groups
      .at(key)
      .values()
      .sorted(key: it => sort-key((it.name,))) {
      block(above: 0pt, below: 0.5em, par(hanging-indent: 1.2em)[
        #index-text(entry.name) — #index-text(entry.meaning),
        #(
          entry
            .at
            .sorted(key: it => it.page())
            .map(it => (
              locator(it, target: "notation-mark")
            ))
            .join([, ])
        )
      ])
    }
  }
}

#let notation-index(preamble: []) = {
  set par(first-line-indent: 0pt, justify: false)
  preamble
  notation-entries
}
