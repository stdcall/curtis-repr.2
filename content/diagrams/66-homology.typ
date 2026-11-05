#import "@preview/cetz:0.5.2": canvas, draw
#import "@preview/fletcher:0.5.8": diagram, edge, node

// Every new vertex is the barycentre of its nonempty simplex face.
#let simplex-subdivision() = block(width: 100%, align(center, canvas(
  length: 1mm,
  {
    import draw: *
    set-style(stroke: 0.5pt, content: (
      padding: 1,
      wrap: text.with(top-edge: "bounds", bottom-edge: "bounds"),
    ))
    let height = 14
    let faces = ((0,), (1,), (2,), (0, 1), (0, 2), (1, 2), (0, 1, 2))
    for (panel, width) in (16, 25).enumerate() {
      let offset = panel * 38
      let vertices = (
        (offset, 0),
        (offset + width, 0),
        (offset + width / 2, height),
      )
      let barycentre(face) = range(2).map(axis => (
        face.map(i => vertices.at(i).at(axis)).sum() / face.len()
      ))
      let edges = ()
      if panel == 0 {
        edges = (((0,), (1,)), ((1,), (2,)), ((2,), (0,)))
      } else {
        for a in faces {
          for b in faces {
            if a.len() < b.len() and a.all(i => i in b) {
              edges.push((a, b))
            }
          }
        }
      }
      assert(edges.len() == (if panel == 0 { 3 } else { 12 }))
      for (a, b) in edges { line(barycentre(a), barycentre(b)) }
      content(vertices.at(0), $0$, anchor: "north-east")
      content(vertices.at(1), $1$, anchor: "north-west")
      content(vertices.at(2), $2$, anchor: "south")
      content(
        (offset - 2, height / 2),
        if panel == 0 { $sigma$ } else {
          $op("Sd") sigma$
        },
        anchor: "east",
      )
      if panel == 1 {
        content(barycentre((0, 1)), $01$, anchor: "north")
        content(barycentre((0, 2)), $02$, anchor: "south-east")
        content(barycentre((1, 2)), $12$, anchor: "south-west")
        let center = barycentre((0, 1, 2))
        let base = barycentre((0, 1))
        let label = (base.at(0) + width / 6, -height / 3)
        content(label, $012$, anchor: "north")
        bezier(
          label,
          center,
          (base.at(0) + width / 4, 0),
          (center.at(0) + width / 6, center.at(1) / 2),
          mark: (end: ">"),
        )
      }
    }
  },
)))

#let orbit-universal-triangle() = block(width: 100%, align(center, diagram(
  spacing: (14mm, 12mm),
  node-inset: 2pt,
  node((0, 0), $Z$),
  node((1, 0), $W$),
  node((0.5, 1), $overline(Z)$),
  edge((0, 0), (1, 0), $f$, "->", label-side: left),
  edge((0, 0), (0.5, 1), $pi$, "->", label-side: right),
  edge((0.5, 1), (1, 0), $overline(f)$, "->", label-side: right),
)))
