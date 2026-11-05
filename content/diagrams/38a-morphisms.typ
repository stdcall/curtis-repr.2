#import "@preview/fletcher:0.5.8": diagram, edge, node

#let morphism-square(induction: true) = {
  let vertices = (
    ((0, 0), $F_1 lr((H))$),
    ((1, 0), $F_2 lr((H))$),
    ((0, 1), $F_1 lr((G))$),
    ((1, 1), $F_2 lr((G))$),
  )
  let vertical = if induction {
    (((0, 0), (0, 1), $i_*$, right), ((1, 0), (1, 1), $i_*$, left))
  } else {
    (((0, 1), (0, 0), $i^*$, left), ((1, 1), (1, 0), $i^*$, right))
  }
  let arrows = (
    ((0, 0), (1, 0), $phi_H$, left),
    ((0, 1), (1, 1), $phi_G$, left),
    ..vertical,
  )
  diagram(
    spacing: (16mm, 11mm),
    node-inset: 2pt,
    node-defocus: 0,
    ..vertices.map(v => node(v.at(0), v.at(1))),
    ..arrows.map(e => edge(
      e.at(0),
      e.at(1),
      e.at(2),
      "-|>",
      label-side: e.at(3),
    )),
  )
}
#let frobenius-morphisms = block(width: 100%, align(center, grid(
  columns: 2,
  column-gutter: 14mm,
  align: center,
  morphism-square(), morphism-square(induction: false),
)))
