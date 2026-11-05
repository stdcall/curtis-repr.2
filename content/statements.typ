#import "numbering.typ": (
  case-counter, case-number-format, family-counter, illustration-counter,
  item-counter, item-series, numbered-record, object-number, record,
  record-number, remark-counter,
)
#import "note-layout.typ": contains-note, keep-note-runs

#let number-text(body) = text(weight: "semibold", body)

// Parenthetical comments retain the author's roman text inside a statement.
#let statement-comment(body) = text(style: "normal", body)

// Preserve a deliberately vacant position in the shared statement series.
#let numbering-gap() = item-counter.step()

#let sequence = [].func()
#let join-pieces(pieces) = sequence(
  pieces
    .map(it => {
      if it.func() == sequence and not it.has("label") { it.children } else {
        (it,)
      }
    })
    .flatten(),
)

// Keep only the final native block with its following inline paragraph.
#let keep-closing-block(body) = {
  if body.func() != sequence { return body }
  let pieces = body.children
  let prior = pieces
    .enumerate()
    .rev()
    .find(pair => (
      pair.last().func() == block
        or (pair.last().func() == math.equation and pair.last().block)
    ))
  if prior == none or prior.first() >= pieces.len() - 1 { return body }
  let (index, previous) = prior
  let tail = pieces.slice(index + 1)
  while tail.len() > 0 and tail.first().func() in ([ ].func(), parbreak) {
    tail = tail.slice(1)
  }
  let advertised-block(it) = {
    if type(it) != content { return false }
    if it.func() == metadata and it.value == (kind: "block-opening") {
      true
    } else if it.has("children") {
      it.children.any(advertised-block)
    } else if it.has("child") { advertised-block(it.child) } else if it.has(
      "body",
    ) {
      advertised-block(it.body)
    } else { false }
  }
  if (
    tail.len() == 0
      or tail.any(advertised-block)
      or not tail.all(it => (
        it.func()
          not in (
            parbreak,
            block,
            enum,
            list,
            table,
            grid,
            figure,
            heading,
            align,
            terms,
          )
          and not (it.func() == math.equation and it.block)
      ))
  ) { return body }
  let kept = if previous.func() == block {
    let fields = previous.fields()
    let inner = fields.remove("body")
    let target = fields.remove("label", default: none)
    fields.insert("sticky", true)
    let kept = block(..fields, inner)
    if target != none { kept = [#kept#target] }
    kept
  } else {
    // A show-set rule retains the native equation, numbering and label.
    show math.equation.where(block: true): set block(sticky: true)
    previous
  }
  join-pieces((..pieces.slice(0, index), kept, ..pieces.slice(index + 1)))
}

// Keep a statement's introductory paragraph with its first native block.
// The following block remains breakable; only its opening stays with the lead.
#let keep-opening-block(body) = {
  if body.func() != sequence { return body }
  let children = body.children
  let first = children.position(it => (
    it.func() in (block, enum, list, terms, table, grid, figure, align)
      or (it.func() == math.equation and it.block)
      or (it.func() == metadata and it.value == (kind: "block-opening"))
  ))
  if first == none or first == 0 { return body }
  if (
    children.at(first).func()
      not in (
        block,
        enum,
        list,
        terms,
        table,
        grid,
        figure,
        align,
        metadata,
      )
  ) {
    return body
  }
  let end = first
  while end > 0 and children.at(end - 1).func() in ([ ].func(), parbreak) {
    end -= 1
  }
  let lead = children.slice(0, end)
  // Native sticky movement can detach an already placed footnote entry.
  // Preserve the existing note-run flow for a note-bearing introduction.
  if contains-note(sequence(lead)) { return body }
  // Do not bind multiple introductory paragraphs to a later block.
  if lead.any(it => it.func() in (parbreak, heading, pagebreak, colbreak)) {
    return body
  }
  let kept-end = children
    .enumerate()
    .find(pair => (
      pair.first() > first
        and pair.last().func() == metadata
        and pair.last().value == (kind: "kept-case-list-end")
    ))
  if (
    first + 1 < children.len()
      and children.at(first + 1).func() == metadata
      and children.at(first + 1).value == (kind: "kept-case-list")
      and kept-end != none
  ) {
    let stop = kept-end.first() + 1
    return join-pieces((
      context block(
        above: 0pt,
        below: par.leading,
        breakable: false,
        sequence(children.slice(0, stop)),
      ),
      ..children.slice(stop),
    ))
  }
  join-pieces((
    context block(
      above: 0pt,
      below: par.leading,
      breakable: true,
      sticky: true,
      sequence(lead),
    ),
    ..children.slice(first),
  ))
}

#let prepend-heading(body, head, keep-opening: false) = {
  let flatten(it) = {
    if it.func() == sequence and not it.has("label") {
      it.children.map(flatten).flatten()
    } else { (it,) }
  }
  let pieces = flatten(body)
  // Named lists prepend invisible counter/state updates to their native enum.
  // Inspect the first layout element, preserving that prelude in its order.
  let invisible = (
    [ ].func(),
    parbreak,
    metadata,
    counter("heading-probe").update(0).func(),
    state("heading-probe", 0).update(0).func(),
  )
  let first = pieces.position(it => it.func() not in invisible)
  if first == none { return join-pieces((head, body)) }
  let opening = pieces.at(first)
  let advertised-block = pieces
    .slice(0, first)
    .any(it => (
      it.func() == metadata and it.value == (kind: "block-opening")
    ))
  let block-opening = (
    advertised-block
      or opening.func()
        in (
          block,
          enum,
          list,
          terms,
          table,
          grid,
          figure,
          heading,
          align,
        )
      or (opening.func() == math.equation and opening.block)
  )
  let lead = if block-opening and head != [] {
    context block(above: 0pt, below: par.leading, sticky: true, head)
  } else { head }
  let contents = join-pieces((
    ..pieces.slice(0, first),
    lead,
    ..pieces.slice(first),
  ))
  if keep-opening and not block-opening { keep-opening-block(contents) } else {
    contents
  }
}

#let keep-opening-display(body, paragraph-spacing: false) = {
  if body.func() != sequence { return body }
  let children = body.children
  let first = children.position(it => (
    it.func() == math.equation and it.block
  ))
  if first == none { return body }
  let lead = children.slice(0, first)
  if lead.any(it => (
    it.func() in (parbreak, block, table, list, enum, heading)
  )) {
    return body
  }
  join-pieces((
    context block(
      above: 0pt,
      below: if paragraph-spacing { par.spacing } else { par.leading },
      sticky: true,
      sequence(lead),
    ),
    ..children.slice(first),
  ))
}

#let suffix-base(variant, family, inserted: false) = {
  let refs(it) = {
    if it.func() == ref { (it.target,) } else if it.has("children") {
      it.children.map(refs).flatten()
    } else if it.has("body") { refs(it.body) } else { () }
  }
  let targets = refs(variant)
  assert(
    targets.len() == 1,
    message: "A suffixed object names its base by one native reference",
  )
  let base = numbered-record(targets.first())
  assert(
    base != none
      and (
        base.value.family == family
          or (
            inserted
              and base.value.family
                in (
                  "th",
                  "lem",
                  "prop",
                  "cor",
                  "def",
                  "exm",
                  "rem",
                  "eq",
                )
              and base.value.at("series", default: none) == none
          )
      )
      and base.value.kind != "unnumbered",
    message: "A suffix requires a numbered object from the shared series",
  )
  (target: targets.first(), record: base)
}

// Only explicit kept lists request the existing opening-block attachment.
#let contains-kept-case-list(body) = {
  if type(body) != content { return false }
  if body.func() == metadata and body.value == (kind: "kept-case-list") {
    return true
  }
  if body.has("children") and body.children.any(contains-kept-case-list) {
    return true
  }
  if body.has("child") and contains-kept-case-list(body.child) { return true }
  body.has("body") and contains-kept-case-list(body.body)
}

#let statement(
  kind,
  family,
  body,
  italic: false,
  title: none,
  numbered: true,
  variant: none,
  suffix: "′",
  inserted: false,
) = {
  if inserted {
    assert(
      suffix.match(regex("^[A-Za-z′]$")) != none,
      message: "A suffix is one letter or a prime",
    )
  }
  if numbered and variant == none { family-counter(family).step() }
  let head = context {
    let base = if variant != none {
      suffix-base(variant, family, inserted: inserted)
    }
    if variant != none {
      [#metadata((
        kind: "variant",
        family: family,
        number: record-number(base.record),
        base: str(base.target),
        suffix: suffix,
      ))<numbered>]
    } else if numbered {
      if inserted { record(family, suffix: suffix) } else { record(family) }
    } else {
      [#metadata((
        kind: "unnumbered",
        family: family,
        number: none,
        name: if kind == none { "Statement" } else { kind },
      ))<numbered>]
    }
    let number = if variant != none {
      record-number(base.record).map(str).join(".") + suffix
    } else if numbered {
      (
        object-number(family, here()).map(str).join(".")
          + if inserted { suffix } else { "" }
      )
    }
    let prefix = if numbered { [(#number-text(number)) ] } else { [] }
    let name = if kind != none { smallcaps(kind) } else { [] }
    let title-part = if title != none { [ (#title)] } else { [] }
    let period = if kind != none or title != none { [.] } else { [] }
    text(style: "normal", prefix + name + title-part + period + [ ])
  }
  // Keep note-bearing paragraphs in the outer native page flow. A surrounding
  // breakable block can defer their entries even when the inner run is kept.
  if contains-note(body) or contains-kept-case-list(body) {
    v(0.75em, weak: true)
    set text(style: "italic") if italic
    keep-closing-block(keep-note-runs(prepend-heading(
      body,
      head,
      keep-opening: contains-kept-case-list(body),
    )))
    v(0.6em, weak: true)
  } else {
    block(above: 0.75em, below: 0.6em, breakable: true, {
      set text(style: "italic") if italic
      keep-closing-block(keep-opening-display(
        keep-note-runs(prepend-heading(
          body,
          head,
          keep-opening: true,
        )),
        paragraph-spacing: true,
      ))
    })
  }
}
#let theorem(name: "Theorem", title: none, numbered: true, body) = statement(
  name,
  "th",
  body,
  italic: true,
  title: title,
  numbered: numbered,
)
#let theorem-variant(base, body) = statement(
  "Theorem",
  "th",
  body,
  italic: true,
  variant: base,
)
#let lemma(name: "Lemma", title: none, numbered: true, body) = statement(
  name,
  "lem",
  body,
  italic: true,
  title: title,
  numbered: numbered,
)
#let lemma-suffix(base: none, suffix: "a", name: "Lemma", body) = statement(
  name,
  "lem",
  body,
  italic: true,
  variant: base,
  suffix: suffix,
  inserted: true,
)
#let theorem-suffix(base: none, suffix: "a", name: "Theorem", body) = statement(
  name,
  "th",
  body,
  italic: true,
  variant: base,
  suffix: suffix,
  inserted: true,
)
#let corollary-suffix(base: none, suffix: "a", body) = statement(
  "Corollary",
  "cor",
  body,
  italic: true,
  variant: base,
  suffix: suffix,
  inserted: true,
)
#let reference-list(..entries) = {
  set par(justify: false)
  table(
    columns: (auto, 1fr),
    column-gutter: 1.4em,
    stroke: none,
    align: left,
    inset: (x: 0pt, y: 0.15em),
    ..entries,
  )
}

#let proposition-suffix(base: none, suffix: "a", body) = statement(
  "Proposition",
  "prop",
  body,
  italic: true,
  variant: base,
  suffix: suffix,
  inserted: true,
)
#let proposition(title: none, numbered: true, body) = statement(
  "Proposition",
  "prop",
  body,
  italic: true,
  title: title,
  numbered: numbered,
)
#let claim(body) = statement(none, "prop", body, italic: true)
#let corollary(title: none, numbered: true, body) = statement(
  "Corollary",
  "cor",
  body,
  italic: true,
  title: title,
  numbered: numbered,
)
#let definition(title: none, numbered: true, body) = statement(
  "Definition",
  "def",
  body,
  title: title,
  numbered: numbered,
)
#let definitions(body) = statement("Definitions", "def", body)
#let example(title: none, numbered: true, body) = statement(
  "Example",
  "exm",
  body,
  title: title,
  numbered: numbered,
)
#let illustration(title: none, numbered: true, body) = {
  if numbered { illustration-counter.step() }
  let head = context {
    if numbered { record("exm", series: "illustration") } else {
      [#metadata((
        kind: "unnumbered",
        family: "exm",
        number: none,
        name: "Example",
      ))<numbered>]
    }
    let ordinal = if numbered {
      [ #object-number("exm", here(), series: "illustration").last()]
    } else { [] }
    emph[Example#ordinal.#if title != none [ #title.]] + [~]
  }
  block(above: 0.75em, below: 0.6em, breakable: true, prepend-heading(
    body,
    head,
  ))
}
#let examples(name: "Examples", title: none, numbered: true, body) = statement(
  name,
  "exm",
  body,
  title: title,
  numbered: numbered,
)
#let remark(numbered: false, body) = statement(
  "Remark",
  "rem",
  body,
  numbered: numbered,
)
#let remarks(name: "Remarks", numbered: true, body) = statement(
  name,
  "rem",
  body,
  numbered: numbered,
)
#let exercise-list-heading(body) = heading(
  level: 3,
  numbering: none,
  outlined: false,
  body,
)
#let exercises-heading = exercise-list-heading([Exercises])
#let exercise-heading = exercise-list-heading([Exercise])
#let hint-link(from, number, target) = metadata((
  kind: "hint-link",
  from: from,
  number: number,
  position: here().position(),
  target-position: if target != none { target.position() },
))

// Distinguish a hint already inside the exercise from its following paragraph.
#let contains-inline-hint(body) = {
  if type(body) != content { return false }
  if body.func() == metadata and body.value == (kind: "inline-hint") {
    true
  } else if body.has("children") {
    body.children.any(contains-inline-hint)
  } else if body.has("body") { contains-inline-hint(body.body) } else { false }
}

#let exercise(body) = {
  family-counter("exc").step()
  context {
    let number = object-number("exc", here())
    let hints = query(metadata.where(value: (
      kind: "hint",
      family: "exc",
      number: number,
    )))
    let target = if hints.len() > 0 { hints.first().location() }
    block(
      above: 0.4em,
      below: 0.4em,
      sticky: target != none and not contains-inline-hint(body),
      {
        let words = strong[#number.last().]
        let head = (
          box(context {
            record("exc")
            hint-link("problem", number, target)
            if target == none { words } else { link(target, words) }
          })
            + [ ]
        )
        keep-closing-block(keep-opening-display(prepend-heading(body, head)))
      },
    )
  }
}

// Inline hints retain the authors' bracketed form. The exercise's number
// leads to the first hint; every "Hint" leads back to the exercise.
#let close-hint(body) = {
  let pieces = if body.func() == sequence { body.children } else { (body,) }
  let last = pieces
    .enumerate()
    .rev()
    .find(pair => (
      pair.last().func() not in ([ ].func(), parbreak)
    ))
  if (
    last != none and last.last().func() == math.equation and last.last().block
  ) {
    let (index, equation) = last
    let fields = equation.fields()
    let _ = fields.remove("body")
    let target = fields.remove("label", default: none)
    let closed = math.equation(
      ..fields,
      equation.body + math.upright("]"),
    )
    if target != none { closed = [#closed#target] }
    // Keep a separate last paragraph's tail with the concluding display.
    // The first inline paragraph stays with the hint's inline heading.
    let end = index
    while end > 0 and pieces.at(end - 1).func() in ([ ].func(), parbreak) {
      end -= 1
    }
    let start = end
    while start > 0 {
      let previous = pieces.at(start - 1)
      if (
        previous.func() in (parbreak, block, enum, list, table, heading)
          or (previous.func() == math.equation and previous.block)
      ) { break }
      start -= 1
    }
    if start == end or start == 0 {
      join-pieces((..pieces.slice(0, index), closed))
    } else {
      join-pieces((
        ..pieces.slice(0, start),
        context block(
          above: par.spacing,
          below: par.leading,
          breakable: true,
          sticky: true,
          sequence(pieces.slice(start, end)),
        ),
        closed,
      ))
    }
  } else if last != none and last.last().func() in (enum, list) {
    let (index, listing) = last
    let fields = listing.fields()
    let children = fields.remove("children")
    let target = fields.remove("label", default: none)
    let item = children.pop()
    let item-fields = item.fields()
    let inner = item-fields.remove("body")
    let item-target = item-fields.remove("label", default: none)
    let closed-item = item.func()(close-hint(inner), ..item-fields)
    if item-target != none { closed-item += item-target }
    children.push(closed-item)
    let closed = listing.func()(..fields, ..children)
    if target != none { closed += target }
    join-pieces((..pieces.slice(0, index), closed))
  } else {
    keep-closing-block(body) + [\]]
  }
}

#let hint(problem, body, caption: [Hint:]) = {
  let refs(it) = {
    if it.func() == ref { (it.target,) } else if it.has("children") {
      it.children.map(refs).flatten()
    } else if it.has("body") { refs(it.body) } else { () }
  }
  let targets = refs(problem)
  assert(
    targets.len() == 1 and str(targets.first()).starts-with("exc:"),
    message: "Name the exercise by one native reference",
  )
  text(
    metadata((kind: "inline-hint"))
      + context {
        let found = numbered-record(targets.first())
        let number = if found == none { ("?",) } else { record-number(found) }
        [#metadata((kind: "hint", family: "exc", number: number))<numbered>]
        let head = context {
          let target = if found != none { found.location() }
          hint-link("hint", number, target)
          // A native inline box gives the link its own text bounds instead of
          // the paragraph's taller annotation bounds at an exercise boundary.
          if target == none { emph(caption) } else {
            link(target, box(emph(caption)))
          }
        }
        [\[#head #close-hint(body)]
      },
  )
}
#let proof(body, head: emph[Proof.]) = {
  let contents = keep-opening-display(keep-note-runs(prepend-heading(
    body,
    if head == none {
      []
    } else {
      [#head ]
    },
  )))
  if contains-note(body) {
    // A split enclosing block can defer a note until a later page. Keep
    // note-bearing proofs in the native page flow, with their note runs
    // grouped before layout.
    parbreak()
    contents
    parbreak()
  } else {
    block(above: 0.4em, below: 0.6em, breakable: true, contents)
  }
}

// Named cases retain native list numbering. Their separate counter lets
// references follow an inserted case without changing theorem numbers.
#let native-case-numbering = numbering
#let case-list(
  numbering: "(1)",
  start: 1,
  prefix: "",
  keep-together: false,
  ..items,
) = {
  assert(type(keep-together) == bool, message: "keep-together must be boolean")
  assert(type(prefix) == str, message: "case-list prefix must be a string")
  assert(
    prefix == "" or type(numbering) == str,
    message: "case-list with prefix requires a numbering pattern",
  )
  assert(
    type(start) == int and start >= 1,
    message: "case-list start must be a positive integer",
  )
  // Context hides its resulting enum from structural opening detection.
  metadata((kind: "block-opening"))
  if keep-together { metadata((kind: "kept-case-list")) }
  if items.pos().any(contains-inline-hint) { metadata((kind: "inline-hint")) }
  context {
    let previous = case-counter.get()
    let previous-format = case-number-format.get()
    let listing = if prefix == "" {
      enum(numbering: numbering, start: start, ..items.pos())
    } else {
      enum(
        numbering: (..numbers) => (
          prefix + native-case-numbering(numbering, ..numbers.pos())
        ),
        start: start,
        ..items.pos(),
      )
    }
    let contents = {
      case-counter.update(start - 1)
      case-number-format.update(if type(numbering) == str { numbering } else {
        "(1)"
      })
      listing
      case-counter.update(previous)
      case-number-format.update(previous-format)
    }
    if keep-together {
      block(
        above: par.leading,
        below: par.leading,
        breakable: false,
        contents,
      )
    } else { contents }
  }
  if keep-together { metadata((kind: "kept-case-list-end")) }
}
#let case(body) = {
  case-counter.step()
  text(
    (if contains-inline-hint(body) { metadata((kind: "inline-hint")) })
      + context {
        record("case", number-format: case-number-format.get())
        keep-note-runs(body)
      },
  )
}

#let numbered-display(it, base: none, suffix: "a", name: none) = {
  assert(name == none or base == none, message: "A named display has no base")
  if name == none {
    if base == none { family-counter("eq").step() } else {
      assert(suffix.match(regex("^[a-z′]$")) != none)
    }
  }
  context {
    let variant = if base != none { suffix-base(base, "eq", inserted: true) }
    if name != none {
      [#metadata((
        kind: "unnumbered",
        family: "eq",
        number: none,
        name: name,
      ))<numbered>]
    } else if variant == none { record("eq") } else {
      [#metadata((
        kind: "variant",
        family: "eq",
        number: record-number(variant.record),
        base: str(variant.target),
        suffix: suffix,
      ))<numbered>]
    }
    let number = if name != none { none } else if variant == none {
      object-number("eq", here()).map(str).join(".")
    } else { record-number(variant.record).map(str).join(".") + suffix }
    let tag = if name != none { name } else { [(#number)] }
    let natural = measure(math.equation(math.display(it.body))).width
    let reserve = measure(tag).width + 0.75em.to-absolute()
    layout(size => {
      // Wide displays use the right side of the available line so that
      // the left-hand number remains separate from the mathematical body.
      let alignment = if natural > size.width - 2 * reserve { right } else {
        center
      }
      show math.equation: set align(alignment)
      math.equation(
        block: true,
        numbering: _ => tag,
        number-align: start + horizon,
        it.body,
      )
    })
  }
}

#let single-display(body) = {
  let equations = if body.func() == math.equation { (body,) } else {
    assert(body.has("children"), message: "Expected one mathematical display")
    body.children.filter(it => (
      it.func() not in ([ ].func(), parbreak, linebreak)
    ))
  }
  assert(
    equations.len() == 1 and equations.first().func() == math.equation,
    message: "Expected one mathematical display without surrounding prose",
  )
  equations.first()
}

#let equation-suffix(base: none, suffix: "a", body) = {
  assert(base != none, message: "A suffixed equation requires its base")
  numbered-display(single-display(body), base: base, suffix: suffix)
}

#let named-equation(name: none, body) = {
  assert(name != none and name != [], message: "A named equation needs a name")
  numbered-display(single-display(body), name: name)
}

// Diagrams share the statement/display series. Symmetric number reserves
// keep a natural-width body centred; wider bodies use the remaining width.
#let numbered-block(body) = {
  family-counter("eq").step()
  block(width: 100%, above: 0.6em, below: 0.6em, breakable: false, context {
    record("eq")
    let number = object-number("eq", here()).map(str).join(".")
    let tag = [(#number-text(number))]
    let reserve = measure(tag).width + 0.75em.to-absolute()
    layout(size => {
      if measure(body).width > size.width - 2 * reserve {
        grid(
          columns: (reserve, 1fr),
          align: (left + horizon, right + horizon),
          tag, body,
        )
      } else {
        grid(
          columns: (reserve, 1fr, reserve),
          align: (left + horizon, center + horizon, right + horizon),
          tag, body, [],
        )
      }
    })
  })
}

#let numbered-table(body, introduction: none) = {
  family-counter("eq").step()
  let numbered = block(above: 0.6em, below: 0.6em, breakable: false, {
    context {
      record("eq")
      let number = object-number("eq", here()).map(str).join(".")
      block(below: 0.5em)[(#number-text(number)):]
    }
    block(width: 100%, align(center, body))
  })
  if introduction == none { numbered } else {
    block(above: 0pt, below: 0pt, breakable: false, {
      introduction
      numbered
    })
  }
}

#let bib-item(body, tag: none) = {
  if tag == none { family-counter("bib").step() }
  block(above: 0.35em, below: 0.35em, context {
    record("bib", tag: tag)
    let n = object-number("bib", here(), tag: tag).last()
    prepend-heading(body, [\[#n\] ])
  })
}
#let bib-group(body) = {
  family-counter("bib").update(0)
  heading(level: 2, numbering: none, outlined: false, body)
}
