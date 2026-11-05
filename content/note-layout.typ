#import "numbering.typ": numbered-record, record-text

// Keep each continuous text run containing a footnote together before page
// layout. Preserve styled wrappers and existing label spans.
#let note-boundary(body) = if (
  type(body) == content
    and body.func() == metadata
    and type(body.value) == dictionary
    and body.value.at("kind", default: none) == "deferred-footnote"
) { body.value.enter }
#let contains-note(body) = {
  if type(body) != content { return false }
  if note-boundary(body) == true { return true }
  if body.func() == footnote { return true }
  if body.has("children") and body.children.any(contains-note) { return true }
  if body.has("child") and contains-note(body.child) { return true }
  body.has("body") and contains-note(body.body)
}
#let sequence = [].func()
// Repeated native markers identify their note by its semantic label.
#let note-keys(body) = {
  if type(body) != content { return () }
  if body.func() == footnote {
    if type(body.body) == label { return (str(body.body),) }
    if body.has("label") { return (str(body.label),) }
    return ()
  }
  if body.has("children") { return body.children.map(note-keys).flatten() }
  if body.has("child") { return note-keys(body.child) }
  if body.has("body") { return note-keys(body.body) }
  ()
}
// A kept heading and its first paragraph form one outer block. Its top
// spacing must equal the heading's own spacing, which collapses inside it.
#let heading-above(level, numbered: true) = if level == 2 and numbered {
  5mm
} else { 4mm }
// A title is repeated in running heads and the contents. Its note belongs
// only to the original heading; preserve the remaining styled title text.
#let without-notes(body) = {
  if type(body) != content or not contains-note(body) { return body }
  if body.func() == footnote { return [] }
  if body.func() == sequence {
    let kept = ()
    let depth = 0
    for child in body.children {
      let boundary = note-boundary(child)
      if boundary == true { depth += 1 } else if boundary == false {
        depth -= 1
      } else if depth == 0 { kept.push(without-notes(child)) }
    }
    assert(depth == 0, message: "Unbalanced deferred footnote markers")
    return sequence(kept)
  }
  let fields = body.fields()
  let _ = fields.remove("label", default: none)
  if body.has("child") {
    let child = fields.remove("child")
    let styles = fields.remove("styles")
    return body.func()(without-notes(child), styles, ..fields)
  }
  if body.has("body") {
    let inner = fields.remove("body")
    return body.func()(without-notes(inner), ..fields)
  }
  body
}
// Call from context. Exact target queries can be incomplete on early passes.
// Flattening a title must never emit a second link to its nested reference.
#let reference-value(target, title, element: auto, seen: ()) = {
  assert(target not in seen, message: "Cyclic heading title: " + str(target))
  let element = if element == auto {
    let targets = query(target)
    assert(
      targets.len() <= 1,
      message: "Ambiguous heading title target: " + str(target),
    )
    targets.at(0, default: none)
  } else { element }
  let item = if element != none { numbered-record(target) }
  let heading-title = (
    item == none
      and element != none
      and element.func() == heading
      and element.numbering == none
  )
  let data = if heading-title {
    let title = title(without-notes(element.body), seen: (..seen, target))
    (text: title.text.trim(), resolved: title.resolved)
  } else if item != none {
    (text: record-text(target, item), resolved: true)
  } else { (text: "?", resolved: false) }
  (
    ..data,
    item: item,
    element: element,
    heading-title: heading-title,
    unnumbered: heading-title
      or (
        item != none and item.value.kind == "unnumbered"
      ),
  )
}
// Exact Unicode scripts where available; otherwise preserve plain notation.
#let title-script(value, top: false) = {
  let plain = if top {
    (
      "()+0123456789=ABCDEFGHIJKLMNOPQRTUV"
        + "Wabcdefghijklmnopqrstuvwxyzəβγδθφχ−"
        + "′″‴⁗"
    )
  } else { ("()+0123456789=aehijklmnoprstuvxəβγρ" + "φχ−") }
  let script = if top {
    (
      "⁽⁾⁺⁰¹²³⁴⁵⁶⁷⁸⁹⁼ᴬᴮꟲᴰᴱꟳᴳᴴᴵᴶᴷᴸᴹᴺᴼᴾꟴᴿᵀᵁⱽ"
        + "ᵂᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖ𐞥ʳˢᵗᵘᵛʷˣʸᶻᵊᵝᵞᵟᶿᵠᵡ⁻"
        + "′″‴⁗"
    )
  } else { ("₍₎₊₀₁₂₃₄₅₆₇₈₉₌ₐₑₕᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓₔᵦᵧᵨ" + "ᵩᵪ₋") }
  let mapped = ()
  for char in value.clusters() {
    let index = plain.clusters().position(it => it == char)
    if index == none {
      let prefix = if top { "^" } else { "_" }
      return (
        prefix
          + if value.clusters().len() == 1 { value } else {
            "(" + value + ")"
          }
      )
    }
    mapped.push(script.clusters().at(index))
  }
  mapped.join()
}
#let title-attachment(body, title, seen) = {
  let base = title(body.base, seen: seen)
  let slots = (:)
  for slot in ("b", "t", "bl", "tl", "br", "tr") {
    let value = body.at(slot, default: none)
    if value != none { slots.insert(slot, title(value, seen: seen)) }
  }
  let resolved = base.resolved and slots.values().all(it => it.resolved)
  // Simultaneous smart and explicit right slots need named, lossless notation.
  if ("b" in slots and "br" in slots) or ("t" in slots and "tr" in slots) {
    let args = slots.pairs().map(((name, data)) => name + ": " + data.text)
    return (
      text: "attach(" + base.text + ", " + args.join(", ") + ")",
      resolved: resolved,
    )
  }
  let text = ""
  for slot in ("bl", "tl") {
    if slot in slots {
      text += title-script(slots.at(slot).text, top: slot == "tl")
    }
  }
  text += base.text
  for slot in ("b", "br", "t", "tr") {
    if slot in slots {
      text += title-script(slots.at(slot).text, top: slot in ("t", "tr"))
    }
  }
  (text: text, resolved: resolved)
}
#let title-data(body, seen: ()) = {
  if type(body) == str { return (text: body, resolved: true) }
  if body.func() == math.attach {
    return title-attachment(body, title-data, seen)
  }
  // Plain bookmark strings preserve quote kind without guessing the
  // surrounding language-aware opening or closing glyph.
  if body.func() == smartquote {
    return (text: if body.double { "\"" } else { "'" }, resolved: true)
  }
  if body.func() == math.primes {
    let primes = ("", "′", "″", "‴", "⁗")
    let count = body.count
    return (
      text: primes.at(calc.min(count, 4)) + "′" * calc.max(0, count - 4),
      resolved: true,
    )
  }
  if body.func() == ref {
    let data = reference-value(body.target, title-data, seen: seen)
    let caption = body.fields().at("supplement", default: auto)
    if caption not in (auto, none, []) {
      let title = title-data(caption, seen: seen)
      return (text: title.text, resolved: data.resolved and title.resolved)
    }
    let prefix = str(body.target).split(":").first()
    let text = data.text
    if data.resolved and not data.unnumbered {
      if prefix == "bib" { text = "[" + text + "]" } else if (
        prefix in ("eq", "th", "lem", "prop", "cor", "def", "rem", "exm")
          and data.item.value.at("series", default: none) != "illustration"
      ) { text = "(" + text + ")" }
    }
    return (text: text, resolved: data.resolved)
  }
  if body.has("text") { return title-data(body.text, seen: seen) }
  if body.func() in ([ ].func(), linebreak) {
    return (text: " ", resolved: true)
  }
  if body.has("children") {
    let parts = body.children.map(child => title-data(child, seen: seen))
    return (
      text: parts.map(it => it.text).join(),
      resolved: parts.all(it => it.resolved),
    )
  }
  if body.has("child") { return title-data(body.child, seen: seen) }
  if body.has("body") { return title-data(body.body, seen: seen) }
  panic("Unsupported content in a heading with a note: " + repr(body))
}
#let title-text(body) = title-data(body).text

#let reference-data(target, element: auto) = reference-value(
  target,
  title-data,
  element: element,
)
#let contains-title-reference(body) = {
  if type(body) != content { return false }
  if body.func() == ref { return true }
  if body.has("children") and body.children.any(contains-title-reference) {
    return true
  }
  if body.has("child") and contains-title-reference(body.child) { return true }
  body.has("body") and contains-title-reference(body.body)
}
#let contains-title-attachment(body) = {
  if type(body) != content { return false }
  if body.func() in (math.attach, math.primes) { return true }
  if body.has("children") and body.children.any(contains-title-attachment) {
    return true
  }
  if body.has("child") and contains-title-attachment(body.child) { return true }
  body.has("body") and contains-title-attachment(body.body)
}
#let bookmark-title(it) = if (
  (
    contains-note(it.body)
      or contains-title-reference(it.body)
      or contains-title-attachment(it.body)
  )
    and (it.bookmarked == true or (it.bookmarked == auto and it.outlined))
) {
  context {
    let prefix = if it.numbering == none { "" } else {
      numbering(it.numbering, ..counter(heading).at(it.location())) + " "
    }
    metadata((
      kind: "bookmark-title",
      position: it.location().position(),
      title: prefix + title-text(without-notes(it.body)).trim(),
    ))
  }
}
#let keep-note-runs(body) = {
  if body.has("label") or not contains-note(body) { return body }
  if body.func() != sequence {
    if body.has("child") {
      let fields = body.fields()
      let child = fields.remove("child")
      let styles = fields.remove("styles")
      return body.func()(keep-note-runs(child), styles, ..fields)
    }
    return body
  }
  // Transparent sequences must not make a repeated-note span swallow a
  // complete following proof. Styled and labelled boundaries remain intact.
  let unpack(it) = {
    if it.func() == sequence and not it.has("label") and contains-note(it) {
      it.children.map(unpack).flatten()
    } else { (it,) }
  }
  let children = body.children.map(unpack).flatten()
  let result = ()
  let i = 0
  let empty = [ ].func()
  // Preserve the existing protection of a body's opening note paragraph.
  // Invisible native preludes do not make it a later continuation.
  let first-content = children.position(it => (
    it.func()
      not in (
        empty,
        parbreak,
        metadata,
        counter("note-flow-probe").update(0).func(),
        state("note-flow-probe", 0).update(0).func(),
      )
  ))
  let note-spans = (:)
  for (index, child) in children.enumerate() {
    for key in note-keys(child) {
      let start = note-spans.at(key, default: (index, index)).first()
      note-spans.insert(key, (start, index))
    }
  }
  let boundary(it) = {
    if it.func() == sequence { return it.children.any(boundary) }
    if it.has("child") { return boundary(it.child) }
    (
      it.func()
        in (
          parbreak,
          par,
          block,
          grid,
          table,
          figure,
          list,
          enum,
          terms,
          list.item,
          enum.item,
          terms.item,
          heading,
          pagebreak,
          colbreak,
        )
        or (it.func() == math.equation and it.block)
    )
  }
  while i < children.len() {
    let child = children.at(i)
    let grouped = false
    // A note used in adjacent statements or paragraphs has one entry.
    // Keep the complete span of its markers in the same native page flow.
    let stop = i + 1
    let extended = true
    while extended {
      extended = false
      for span in note-spans.values() {
        if span.first() >= i and span.first() < stop and span.last() >= stop {
          stop = span.last() + 1
          extended = true
        }
      }
    }
    if stop > i + 1 {
      result.push(block(breakable: false, sequence(children.slice(i, stop))))
      i = stop
      grouped = true
    }
    if (
      not grouped
        and child.func() == heading
        and child
          .fields()
          .at(
            "level",
            default: child.fields().at("depth", default: 1),
          )
          in (2, 3)
    ) {
      let start = i + 1
      while (
        start < children.len()
          and (
            children.at(start).func() in (empty, parbreak)
          )
      ) { start += 1 }
      let stop = start
      while stop < children.len() and not boundary(children.at(stop)) {
        stop += 1
      }
      if (
        contains-note(child)
          or contains-note(sequence(children.slice(start, stop)))
      ) {
        let level = child
          .fields()
          .at(
            "level",
            default: child.fields().at("depth", default: 1),
          )
        result.push(block(
          above: heading-above(
            level,
            numbered: child.fields().at("numbering", default: auto) != none,
          ),
          breakable: false,
          sequence(children.slice(i, stop)),
        ))
        i = stop
        grouped = true
      }
    }
    if not grouped and child.func() == math.equation and child.block {
      let stop = i + 1
      while stop < children.len() and not boundary(children.at(stop)) {
        stop += 1
      }
      let tail = sequence(children.slice(i + 1, stop))
      if contains-note(tail) {
        let start = i
        while start > 0 and not boundary(children.at(start - 1)) { start -= 1 }
        let lead = sequence(children.slice(start, i))
        let words(it) = {
          if type(it) == str { return it }
          if type(it) != content { return "" }
          if it.has("text") { return words(it.text) }
          if it.has("children") { return it.children.map(words).join() }
          if it.has("child") { return words(it.child) }
          if it.has("body") { return words(it.body) }
          ""
        }
        let plain = words(lead).trim()
        // Never undo a previously protected heading or repeated-note span.
        let count = i - start
        let intact = (
          result.len() >= count
            and sequence(result.slice(
              result.len() - count,
            ))
              == lead
        )
        if (
          start < i
            and not contains-note(lead)
            and plain != ""
            and intact
            and plain.len() <= 80
            and plain.split(regex("\\s+")).len() <= 12
            and not plain.ends-with(regex("[.!?]$"))
        ) {
          result = result.slice(0, result.len() - (i - start))
          result.push(block(breakable: false, sequence(children.slice(
            start,
            stop,
          ))))
        } else {
          result.push(block(breakable: false, sequence(children.slice(
            i,
            stop,
          ))))
        }
        i = stop
        grouped = true
      }
    }
    if not grouped and not boundary(child) {
      let stop = i + 1
      while stop < children.len() and not boundary(children.at(stop)) {
        stop += 1
      }
      let run = sequence(children.slice(i, stop))
      if contains-note(run) {
        if (
          first-content != none
            and i > first-content
            and stop < children.len()
            and children.at(stop).func() == math.equation
            and children.at(stop).block
        ) {
          // This run continues into a display in the same source paragraph.
          // Preserve native line breaking and avoid a second sticky wrapper.
          // The previous kept block also had no first-line indentation.
          result.push([#par(first-line-indent: 0pt, run)<note-continuation>])
        } else { result.push(block(breakable: false, run)) }
      } else {
        // The whole inspected run has no notes; preserve it and advance once.
        result += children.slice(i, stop)
      }
      i = stop
      grouped = true
    }
    if not grouped {
      result.push(keep-note-runs(child))
      i += 1
    }
  }
  sequence(result)
}
