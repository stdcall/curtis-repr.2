// Chapters are arabic; sections run continuously through the book.
// Statements and numbered displays share the series (section.item).
#let section-counter = counter("book-section")
#let item-counter = counter("book-item")
#let item-offset = state("book-item-offset", 0)
#let exercise-counter = counter("book-exercise")
#let bibliography-counter = counter("book-bibliography")
#let illustration-counter = counter("book-illustration")
#let remark-counter = counter("book-remark")
#let case-counter = counter("book-case")
#let case-number-format = state("case-number-format", "(1)")

// Called between a chapter's introduction and its first section. The
// heading counter keeps the continuous section series across chapters.
#let continue-sections() = context {
  let section = section-counter.get().first()
  counter(heading).update((..numbers) => (numbers.pos().first(), section))
}

#let place-key(location) = (
  counter(heading).at(location).at(0, default: 0),
  section-counter.at(location).first(),
)

#let family-counter(family) = if family == "exc" {
  exercise-counter
} else if family == "case" { case-counter } else if family == "bib" {
  bibliography-counter
} else { item-counter }

// An exceptional section may start its shared series at zero. The native
// counter still counts insertions; the offset belongs to this section.
#let item-series(start: 1) = {
  assert(type(start) == int and start >= 0)
  item-counter.update(0)
  item-offset.update(start - 1)
}

#let restart-counters(level) = if level == 2 {
  section-counter.step()
  item-counter.update(0)
  item-offset.update(0)
  exercise-counter.update(0)
  illustration-counter.update(0)
  remark-counter.update(0)
}

#let object-number(family, location, tag: none, series: none) = {
  let own = if tag != none { tag } else {
    let counting = if series == "illustration" {
      illustration-counter
    } else if (
      series == "remark"
    ) { remark-counter } else {
      family-counter(family)
    }
    (
      counting.at(location).first()
        + if (
          series == none and family not in ("exc", "case", "bib")
        ) { item-offset.at(location) } else { 0 }
    )
  }
  if family in ("bib", "case") { (own,) } else {
    (section-counter.at(location).first(), own)
  }
}

#let numbered-record(target) = {
  if query(target).len() != 1 { return none }
  query(selector(<numbered>).within(target)).at(0, default: none)
}

#let record-number(item) = {
  let value = item.value
  if value.kind in ("hint", "variant") { value.number } else if (
    value.kind == "unnumbered"
  ) {
    none
  } else if value.family == "heading" {
    if value.level == 1 {
      (counter(heading).at(item.location()).first(),)
    } else if value.level == 2 {
      (section-counter.at(item.location()).first(),)
    } else {
      (
        section-counter.at(item.location()).first(),
        numbering("A", counter(heading).at(item.location()).last()),
      )
    }
  } else {
    object-number(
      value.family,
      item.location(),
      tag: value.at("tag", default: none),
      series: value.at("series", default: none),
    )
  }
}

// Plain names are shared by visible references and references inside titles.
// This function returns data only: no links, metadata or contextual content.
#let record-text(target, item) = {
  let prefix = str(target).split(":").first()
  let number = record-number(item)
  let value = item.value
  if value.kind == "unnumbered" { return value.name }
  if prefix == "case" {
    let format = value.at("number-format", default: "(1)")
    return numbering(format.trim(".", at: end, repeat: false), ..number)
  }
  if prefix == "ch" { return numbering("1", ..number) }
  if (
    prefix == "bib"
      or (
        prefix == "exm" and value.at("series", default: none) == "illustration"
      )
  ) {
    return str(number.last())
  }
  if prefix == "ss" { return str(number.first()) + str(number.last()) }
  number.map(str).join(".") + value.at("suffix", default: "")
}

#let record(family, ..flags) = context [#metadata((
  kind: "numbered",
  family: family,
  ..flags.named(),
  number: object-number(
    family,
    here(),
    tag: flags.named().at("tag", default: none),
    series: flags.named().at("series", default: none),
  ),
))<numbered>]
