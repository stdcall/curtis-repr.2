#import "../book-style.typ": preliminary-gap

#let preface-addendum(body) = block(stroke: 0.4pt, inset: 10pt, body)
// Shared presentation of the notation catalogue.
#let notation-style(body) = {
  set par(first-line-indent: 0pt, justify: false)
  show heading.where(level: 2): it => block(
    above: 0.9em,
    below: 0.5em,
    sticky: true,
    text(weight: "bold", it.body),
  )
  body
}

// Empty leaves have no running head or visible folio, but remain counted.
#let blank-leaf() = page(header: none, footer: none)[#v(1fr)]
#let preliminary-break() = {
  // Title iii is physical page 2 after the uncounted cover. Even physical
  // pages therefore carry odd Roman folios throughout the preliminaries.
  preliminary-gap.update(true)
  pagebreak(weak: true, to: "even")
  preliminary-gap.update(false)
}
