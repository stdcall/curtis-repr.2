#import "numbering.typ": record

// Head-only group series are independent of nested ordinary case lists.
#let case-heading-counter = counter("book-case-heading")
#let case-heading-format = state("book-case-heading-format", "(I)")

#let case-series(body, numbering: "(I)") = context {
  let previous = case-heading-counter.get()
  let previous-format = case-heading-format.get()
  case-heading-counter.update(0)
  case-heading-format.update(numbering)
  body
  case-heading-counter.update(previous)
  case-heading-format.update(previous-format)
}

#let case-heading(body) = {
  case-heading-counter.step()
  text(context {
    let number = case-heading-counter.get().first()
    record("case", tag: number, number-format: case-heading-format.get())
    block(sticky: true, enum(
      numbering: case-heading-format.get(),
      start: number,
      body,
    ))
  })
}
