#import "numbering.typ": numbered-record
#import "note-layout.typ": reference-data

#let source(n, printed: none) = context {
  let folio = if printed != none { str(printed) } else if n <= 16 {
    numbering("i", n + 2)
  } else { str(n - 16) }
  metadata((
    kind: "source",
    file-page: n,
    printed-page: folio,
    position: here().position(),
  ))
}

#let number-text(body) = text(weight: "semibold", style: "normal", body)

// Companion numbers and destinations belong to one pinned published edition.
#let external-catalog-path = sys.inputs.at("external-catalog", default: none)
#let external-catalog = if external-catalog-path == none { none } else {
  json("/" + external-catalog-path)
}
#let external-uri(target) = "https://book-reference.invalid/volume-i/" + target

// Keep a reference's invisible anchor with its first word when it wraps.
#let anchored-first(body, anchor) = {
  let body = if type(body) == str { text(body) } else { body }
  let parts = if body.has("children") { body.children } else { (body,) }
  let first = parts.position(it => (
    it.func() not in ([ ].func(), parbreak, linebreak)
  ))
  assert(first != none, message: "A reference needs visible content")
  let lead = parts.at(first)
  let sequence = [].func()
  let end = first + 1
  let punctuation = ()
  while (
    lead.has("text")
      and lead.text in ("[", "(", "{", "“", "‘")
      and end < parts.len()
      and parts.at(end).func() not in ([ ].func(), parbreak, linebreak)
  ) {
    punctuation.push(lead)
    lead = parts.at(end)
    end += 1
  }
  let anchor = anchor + sequence(punctuation)
  let gap-start = end
  while end < parts.len() and parts.at(end).func() == [ ].func() {
    end += 1
  }
  let trailing = if end > gap-start {
    text("\u{00a0}" * (end - gap-start))
  } else { [] }
  let anchored = if lead.has("text") {
    let word = lead.text.match(regex("^\\S+\\s*"))
    if word == none { box(anchor + lead + trailing) } else {
      if word.end == lead.text.len() {
        box(
          anchor + text(word.text.replace(regex("\\s"), "\u{00a0}")) + trailing,
        )
      } else {
        box(anchor + text(word.text.replace(regex("\\s"), "\u{00a0}")))
        text(lead.text.slice(word.end))
        trailing
      }
    }
  } else if lead.has("children") {
    anchored-first(lead, anchor) + trailing
  } else { box(anchor + lead + trailing) }
  sequence((..parts.slice(0, first), anchored, ..parts.slice(end)))
}

#let external-reference(it, caption) = {
  let target = str(it.target)
  assert(
    external-catalog != none and target in external-catalog.targets,
    message: "Unregistered companion reference: " + target,
  )
  let item = external-catalog.targets.at(target)
  let printed = if item.kind == "unnumbered" { item.name } else if (
    item.family == "ss"
  ) { item.number.map(str).join("") } else {
    item.number.map(str).join(".") + item.suffix
  }
  let body = if caption { it.supplement } else if item.kind == "unnumbered" {
    printed
  } else if (
    item.family in ("eq", "th", "lem", "prop", "cor", "def", "rem", "exm")
  ) {
    [(#number-text(printed))]
  } else { number-text(printed) }
  let anchor = metadata((
    kind: "external-reference",
    target: target,
    uri: external-uri(target),
    printed: printed,
    edition-sha256: external-catalog.edition.sha256,
  ))
  box(link(external-uri(target), block(anchored-first(body, anchor))))
}

#let reference-body(it, caption) = context {
  let target = str(it.target)
  let prefix = target.split(":").first()
  let data = reference-data(it.target, element: it.element)
  let item = data.item
  let unnumbered-heading = data.heading-title
  let unnumbered = item != none and item.value.kind == "unnumbered"
  let illustration = (
    prefix == "exm"
      and item != none
      and (
        item.value.at("series", default: none) == "illustration"
      )
  )
  let pending = not data.resolved
  let printed = data.text
  let body = if caption { it.supplement } else if (
    unnumbered or unnumbered-heading
  ) {
    printed
  } else if (
    prefix
      in (
        "eq",
        "th",
        "lem",
        "prop",
        "cor",
        "def",
        "rem",
      )
      or (prefix == "exm" and not illustration)
  ) { [(#number-text(printed))] } else if prefix == "bib" {
    [\[#number-text(printed)\]]
  } else { number-text(printed) }
  let destination = if pending { none } else if (
    unnumbered-heading or it.element.func() == math.equation
  ) {
    it.element.location()
  } else { item.location() }
  let anchor = {
    if prefix == "bib" {
      metadata((kind: "bibliographic-mention", target: target))
    }
    metadata((
      kind: "cross-reference",
      target: target,
      resolved: not pending,
      printed: printed,
      target-location: destination,
    ))
  }
  let shown = anchored-first(body, anchor)
  if pending { shown } else {
    link(destination, if caption { shown } else { box(shown) })
  }
}

#let reference-rules(body) = {
  show ref: it => {
    let caption = it.supplement not in (auto, none, [])
    if str(it.target).starts-with("i:") {
      external-reference(it, caption)
    } else {
      let shown = reference-body(it, caption)
      if caption { shown } else { box(shown) }
    }
  }
  body
}

#let index-value(path, target) = {
  assert(path.len() > 0)
  let refs(body) = {
    if body.func() == ref { (body.target,) } else if body.has("children") {
      body.children.map(refs).flatten()
    } else if body.has("body") { refs(body.body) } else { () }
  }
  let destination = if target == none { () } else { refs(target) }
  assert(
    target == none or destination.len() == 1,
    message: "An index target must contain one native reference",
  )
  let value = (path: path)
  if target != none { value.insert("target", str(destination.first())) }
  value
}

#let idx(target: none, see: none, see-also: (), ..path) = {
  assert(path.named().len() == 0)
  assert(
    path.pos().len() > 0
      and path.pos().all(level => type(level) == str and level.trim() != ""),
    message: "An index entry needs a nonempty path",
  )
  assert(
    see == none or target == none,
    message: "A see-only entry has no body target",
  )
  let value = (kind: "index-mark", ..index-value(path.pos(), target))
  if see != none {
    assert(
      type(see) == array
        and see.len() > 0
        and see.all(level => type(level) == str and level.trim() != ""),
      message: "A see target is a nonempty index path",
    )
    value.insert("see", see)
  }
  if see-also.len() > 0 {
    assert(
      see-also.all(other => (
        type(other) == array
          and other.len() > 0
          and other.all(level => type(level) == str and level.trim() != "")
      )),
      message: "See-also targets are nonempty index paths",
    )
    value.insert("see-also", see-also)
  }
  [#metadata(value)<index-mark>]
}

// Notation names and their explanations live only beside their definitions.
#let nidx(notation, meaning, target: none, chapter: none) = {
  assert(type(notation) == str and type(meaning) == str)
  let value = (
    kind: "notation-mark",
    meaning: meaning,
    ..index-value((notation,), target),
  )
  if chapter != none {
    let group = index-value((notation,), chapter).target
    assert(
      group.starts-with("ch:"),
      message: "A notation group names a chapter",
    )
    value.insert("chapter-target", group)
  }
  [#metadata(value)<notation-mark>]
}

#let editorial-note-counter = counter("editorial-note")
#let ed-note(body) = {
  metadata((kind: "deferred-footnote", enter: true))
  editorial-note-counter.step()
  context {
    let mark = "*" + str(editorial-note-counter.get().first())
    footnote(numbering: _ => mark)[#body~— _Ed._]
    counter(footnote).update(n => n - 1)
  }
  metadata((kind: "deferred-footnote", enter: false))
}

// Native block matrices with spanning cells and independent partitions.
#let block-matrix(
  columns,
  cells,
  hlines: (),
  vlines: (),
  delimiters: (sym.brace.l, sym.brace.r),
) = {
  let stroke(line, dashed) = if line.at("dashed", default: dashed) {
    (thickness: 0.05em, dash: "dashed")
  } else { (thickness: 0.05em) }
  let matrix = grid(
    columns: columns,
    align: center + horizon,
    column-gutter: 0.5em,
    row-gutter: 0.6em,
    ..hlines.map(it => grid.hline(y: it.at, stroke: stroke(it, false))),
    ..vlines.map(it => grid.vline(x: it.at, stroke: stroke(it, true))),
    ..cells,
  )
  math.lr(delimiters.first() + matrix + delimiters.last())
}

// Native vector diagrams retain their size unless they exceed the column.
// Reflow reserves the scaled height as well as the scaled width.
#let fit-diagram(body) = block(width: 100%, layout(size => {
  let width = measure(body).width
  let factor = if width <= size.width { 100% } else {
    size.width / width * 100%
  }
  align(center, scale(factor, reflow: true, body))
}))

#let Hom = math.op("Hom")
#let End = math.op("End")
#let Aut = math.op("Aut")
#let ker = math.op("ker")
#let im = math.op("im")
#let tr = math.op("tr")
#let rank = math.op("rank")
#let rad = math.op("rad")
#let Irr = math.op("Irr")
#let cf = math.op("cf")
#let char = math.op("char")
#let GL = math.upright("GL")
#let SL = math.upright("SL")
#let lmodule(ring, module) = math.attach(module, bl: ring)

// Resolve audit coordinates only in the final document query, not while a
// reference is being measured for its inline mathematical dimensions.
#let metadata-value(element) = {
  let value = element.value
  if type(value) == dictionary and "target-location" in value {
    let destination = value.remove("target-location")
    value.insert("target-position", if destination != none {
      destination.position()
    })
  }
  value
}
