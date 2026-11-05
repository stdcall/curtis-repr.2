#import "numbering.typ": restart-counters, section-counter
#import "statements.typ": numbered-display
#import "main-defs.typ": reference-rules
#import "note-layout.typ": bookmark-title, contains-note, keep-note-runs
#import "note-layout.typ": without-notes
#import "note-layout.typ": heading-above, title-text

#let running-chapter = state("running-chapter", [])
#let running-section = state("running-section", [])
#let preliminary-gap = state("preliminary-gap", false)
#let body-margin = (x: 20mm, top: 21mm, bottom: 20mm)
#let unnumbered-heading-record(it) = context [#metadata((
  kind: "unnumbered",
  family: "heading",
  level: it.level,
  number: none,
  name: title-text(without-notes(it.body)),
))<numbered>]
#let opening-page() = {
  query(heading.where(level: 1))
    .map(it => it.location().page())
    .contains(here().page())
}
#let folio() = text(size: 9pt, counter(page).display())
#let running-header = context {
  if opening-page() or preliminary-gap.get() { return }
  if calc.even(counter(page).get().first()) {
    grid(
      columns: (2em, 1fr, 2em),
      align: (left, center, right),
      folio(), smallcaps(running-chapter.get()), [],
    )
  } else {
    let leading = query(heading.where(level: 2)).find(it => (
      it.numbering != none
        and it.location().page() == here().page()
        and it.location().position().y <= body-margin.top + 0.1pt
    ))
    let section = if leading != none {
      [§ #counter(heading).at(leading.location()).last(). #without-notes(
          leading.body,
        )]
    } else if running-section.get() == [] {
      running-chapter.get()
    } else { running-section.get() }
    grid(
      columns: (2em, 1fr, 2em),
      align: (left, center, right),
      [], smallcaps(section), folio(),
    )
  }
}
#let book-style(body) = {
  set page(
    width: 176mm,
    height: 250mm,
    margin: body-margin,
    header: text(size: 8.5pt, running-header),
    footer: context if opening-page() { align(center, folio()) },
  )
  set text(font: "Libertinus Serif", size: 11pt, lang: "en", region: "us")
  set par(
    justify: true,
    leading: 0.58em,
    first-line-indent: 1.1em,
    spacing: 0.65em,
  )
  // Unfinished prose introduces the next block. The native sticky block is
  // breakable, so a long paragraph retains its ordinary internal page flow.
  show par: it => context {
    if it.at("label", default: none) == <note-continuation> { return it }
    let words(body) = {
      if type(body) == str { return body }
      if type(body) != content { return "" }
      if body.has("text") { return words(body.text) }
      if body.has("children") { return body.children.map(words).join() }
      if body.has("child") { return words(body.child) }
      if body.has("body") { return words(body.body) }
      ""
    }
    let plain = words(it.body).trim()
    if (
      plain != "" and not plain.ends-with(regex("[.!?][\\s\\]\\)\"’”]*$"))
    ) {
      block(above: par.spacing, below: par.spacing, sticky: true, it)
    } else { it }
  }
  show link: set text(fill: black)
  show regex("^-\p{L}"): it => sym.wj + it
  show "–": it => sym.wj + it + sym.wj
  set heading(numbering: (..n) => {
    let numbers = n.pos()
    if numbers.len() == 1 {
      "Chapter " + numbering("1", numbers.first()) + "."
    } else if numbers.len() == 2 {
      "§ " + str(numbers.at(1)) + "."
    } else {
      "§ " + str(numbers.at(1)) + numbering("A", numbers.last()) + "."
    }
  })
  // Deeper native headings also need resolved plain bookmark titles.
  // The specialized rules below supply the same hook for levels 1–3.
  show heading: it => {
    bookmark-title(it)
    it
  }
  show heading.where(level: 1): it => {
    bookmark-title(it)
    pagebreak(weak: true)
    let numbered = it.numbering != none
    running-chapter.update(without-notes(it.body))
    running-section.update([])
    if numbered {
      context {
        let chapter = counter(heading).at(it.location()).first()
        [#metadata((
          kind: "numbered",
          family: "heading",
          level: 1,
          number: (chapter,),
        ))<numbered>]
      }
    }
    if not numbered { unnumbered-heading-record(it) }
    block(width: 100%, above: 12mm, below: 11mm, align(center, {
      set par(first-line-indent: 0pt, justify: false)
      if numbered {
        text(size: 10pt, smallcaps[Chapter #numbering(
            "1",
            counter(heading).at(it.location()).first(),
          )])
        linebreak()
      }
      text(size: 17pt, it.body)
    }))
  }
  show heading.where(level: 2): it => {
    bookmark-title(it)
    if it.numbering != none {
      restart-counters(2)
      context {
        let n = section-counter.get().first()
        [#metadata((
          kind: "numbered",
          family: "heading",
          level: 2,
          number: (n,),
        ))<numbered>]
        running-section.update([§ #n. #without-notes(it.body)])
        block(
          width: 100%,
          above: heading-above(2),
          below: 3.5mm,
          sticky: true,
          align(
            center,
            text(size: 12pt, weight: "semibold")[§ #n. #it.body],
          ),
        )
      }
    } else {
      block(
        width: 100%,
        above: heading-above(2, numbered: false),
        below: 2mm,
        sticky: true,
        strong(it.body),
      )
    }
  }
  show heading.where(level: 3): it => {
    bookmark-title(it)
    if it.numbering == none {
      block(
        width: 100%,
        above: heading-above(3),
        below: 2mm,
        sticky: true,
        align(
          center,
          smallcaps(it.body),
        ),
      )
    } else {
      context {
        let n = numbering("A", counter(heading).at(it.location()).last())
        [#metadata((
          kind: "numbered",
          family: "heading",
          level: 3,
          number: (section-counter.get().first(), n),
        ))<numbered>]
        block(
          width: 100%,
          above: heading-above(3),
          below: 2mm,
          sticky: true,
          emph[§ #section-counter.display()#n. #it.body],
        )
      }
    }
  }
  show heading: set par(first-line-indent: 0pt, justify: false)
  show outline: set par(first-line-indent: 0pt)
  show outline.entry: set block(breakable: false)
  show outline.entry: it => {
    if contains-note(it.body()) {
      link(it.element.location(), it.indented(it.prefix(), {
        without-notes(it.body())
        box(width: 1fr, it.fill)
        it.page()
      }))
    } else { it }
  }
  set math.equation(numbering: none, supplement: none)
  show math.equation: set text(font: "STIX Two Math")
  show math.equation.where(block: false): it => context {
    let ink = measure({
      set text(top-edge: "bounds", bottom-edge: "bounds")
      it
    })
    let equation = if ink.height > 1em.to-absolute() {
      text(top-edge: "bounds", bottom-edge: "bounds", it)
    } else { it }
    // Keep short inline relations intact at line/page boundaries; long
    // equations retain native mathematical line breaking.
    if ink.width <= 12em.to-absolute() { box(equation) } else { equation }
  }

  show math.equation: it => {
    show ":": math.class("punctuation", ":")
    show "∼": math.scripts
    it
  }
  show math.equation.where(block: true): it => {
    if (
      it.has("label")
        and str(it.label).starts-with("eq:")
        and it.numbering == none
    ) {
      numbered-display(it)
    } else { it }
  }
  set table(stroke: 0.4pt, inset: (x: 0.4em, y: 0.45em))
  show table: set align(center)
  show table: set block(breakable: false)
  set table.cell(breakable: false)
  show footnote.entry: it => {
    context metadata((
      kind: "footnote-placement",
      marker-page: it.note.location().page(),
      entry-page: it.location().page(),
    ))
    block(above: 0pt, below: 0pt, breakable: false, it)
  }
  show: reference-rules
  keep-note-runs(body)
}
