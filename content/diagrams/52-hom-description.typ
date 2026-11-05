#import "../main-defs.typ": fit-diagram
#import "@preview/fletcher:0.5.8": diagram, edge, node

#let graph(vertices, arrows) = fit-diagram(diagram(
  spacing: (13mm, 13mm),
  node-inset: 2pt,
  node-defocus: 0,
  ..vertices.map(v => node(v.at(0), v.at(1))),
  ..arrows.map(e => edge(
    e.at(0),
    e.at(1),
    e.at(2, default: []),
    "-|>",
    label-side: e.at(3, default: left),
  )),
))

#let triangle(top, lower, target, below: false) = graph(
  (((0, 0), top), ((0, 1), lower), ((1, 1), target)),
  (
    ((0, 0), (0, 1), $op("nr")$, right),
    ((0, 0), (1, 1), $op("Det")$),
    ((0, 1), (1, 1), $f$, if below { right } else { left }),
  ),
)

#let det-reduced-norm-triangle = triangle(
  $A^dot$,
  $C^dot$,
  $op("Hom")_Omega lr((op("ch") G,E^dot))$,
)
#let real-component-det-triangle = triangle(
  $B^dot$,
  $("center of" B)^dot$,
  $op("Hom")_Omega lr((op("ch") G,E_(P_0)^dot))$,
  below: true,
)

#let square(a, b, c, d, horizontal: [], west: [], east: []) = graph(
  (((0, 0), a), ((1, 0), b), ((0, 1), c), ((1, 1), d)),
  (
    ((0, 0), (1, 0), horizontal),
    ((0, 1), (1, 1), horizontal),
    ((0, 0), (0, 1), west, right),
    ((1, 0), (1, 1), east, right),
  ),
)

#let hom-group-induction-square = square(
  $op("Cl") R H$,
  $op("Hom")_Omega lr((op("ch") H,J^* lr((E)))) slash dots.h$,
  $op("Cl") R G$,
  $op("Hom")_Omega lr((op("ch") G,J^* lr((E)))) slash dots.h$,
)
#let det-group-induction-square = square(
  $(K H)^dot$,
  $op("Hom")(op("ch") H,E^dot)$,
  $(K G)^dot$,
  $op("Hom")(op("ch") G,E^dot)$,
  horizontal: $op("Det")$,
)
#let hom-group-restriction-square = square(
  $op("Cl") R G$,
  $op("Hom")_Omega lr((op("ch") G,J^* lr((E)))) slash dots.h$,
  $op("Cl") R H$,
  $op("Hom")_Omega lr((op("ch") H,J^* lr((E)))) slash dots.h$,
  west: $op("res")$,
)
#let det-group-restriction-square = square(
  $K_1(K G)$,
  $op("Hom")(op("ch") G,E^dot)$,
  $K_1(K H)$,
  $op("Hom")(op("ch") H,E^dot)$,
  horizontal: $op("Det")$,
  west: $op("res")$,
)
#let hom-ring-extension-square = square(
  $op("Cl") R G$,
  $op("Hom")_Omega lr((op("ch") G,J^* lr((E)))) slash dots.h$,
  $op("Cl") R' G$,
  $op("Hom")_(Omega') lr((op("ch") G,J^* lr((E)))) slash dots.h$,
)
#let hom-ring-restriction-square = square(
  $op("Cl") R' G$,
  $op("Hom")_(Omega') lr((op("ch") G,J^* lr((E)))) slash dots.h$,
  $op("Cl") R G$,
  $op("Hom")_Omega lr((op("ch") G,J^* lr((E)))) slash dots.h$,
  east: $cal(N)$,
)
