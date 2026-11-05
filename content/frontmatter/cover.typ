// Wiley Classics cover: all lettering and geometry are vector content.
// The series lettering is supplied as vector outlines.
#let cover() = {
  let W = 176mm
  let H = 250mm
  let gold = rgb("d4b451")
  let cream = rgb("c5b585")
  page(
    width: W,
    height: H,
    margin: 0pt,
    header: none,
    footer: none,
    numbering: none,
    fill: black,
    {
      set text(fill: white, font: "TeX Gyre Heros")
      let centered(y, body, x: 0mm) = place(
        top + left,
        dy: y,
        dx: x,
        block(width: W, align(center, body)),
      )
      // The fine rule is interrupted behind the calligraphic series.
      place(top + left, dy: 17mm, line(length: W, stroke: 0.5pt + cream))
      place(top + center, dy: 9mm, rect(
        width: 114mm,
        height: 17mm,
        fill: black,
        stroke: none,
      ))
      place(top + left, dy: 0mm, image("series.svg", width: W))
      // Both author lines use a freely licensed high-contrast display serif.
      centered(43mm, x: -9mm, scale(x: 94%, reflow: true, {
        set text(font: "Abril Fatface")
        text(size: 114pt)[C]
        text(size: 79pt)[URTIS]
        h(2pt)
        text(font: "Libertinus Serif", weight: "bold", size: 85pt)[&]
      }))
      // Broad gold band and its fine lower edge run behind the large R.
      place(top + left, dy: 103mm, rect(
        width: W,
        height: 4mm,
        fill: gold,
        stroke: none,
      ))
      place(top + left, dy: 108mm, line(length: W, stroke: 0.45pt + gold))
      place(top + left, dx: 45mm, dy: 100mm, rect(
        width: 24mm,
        height: 11mm,
        fill: black,
        stroke: none,
      ))
      place(top + left, dx: 46mm, dy: 79mm, scale(x: 92%, reflow: true, text(
        font: "Abril Fatface",
        size: 114pt,
      )[R]))
      place(top + left, dx: 72mm, dy: 80mm, scale(x: 92%, reflow: true, text(
        font: "Abril Fatface",
        size: 73pt,
      )[EINER]))
      centered(126mm, text(size: 40pt)[Methods of])
      centered(141mm, text(size: 40pt)[Representation Theory])
      centered(162mm, text(size: 20pt)[With Applications to])
      centered(172mm, text(size: 20pt)[Finite Groups and Orders])
      centered(182mm, text(size: 24pt)[Volume II])
    },
  )
}
