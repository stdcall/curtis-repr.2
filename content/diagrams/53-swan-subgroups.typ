#import "../main-defs.typ": fit-diagram
#import "@preview/fletcher:0.5.8": diagram, edge, node

#let square(a, b, c, d, top: [], west: [], east: []) = fit-diagram(diagram(
  spacing: (14mm, 13mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), a),
  node((1, 0), b),
  node((0, 1), c),
  node((1, 1), d),
  edge((0, 0), (1, 0), top, "-|>"),
  edge((0, 1), (1, 1), "-|>"),
  edge((0, 0), (0, 1), west, "-|>", label-side: right),
  edge((1, 0), (1, 1), east, "-|>", label-side: right),
))

#let swan-fiber-product = square(
  $ZZ G$,
  $ZZ G slash ZZ sigma = Gamma$,
  $ZZ$,
  $overline(ZZ) = ZZ slash n ZZ$,
  top: $f$,
  west: $epsilon$,
)
#let elementary-two-fiber-product = square(
  $ZZ G$,
  $ZZ H$,
  $ZZ H$,
  $k H, quad k=ZZ slash 2 ZZ$,
  top: $f$,
  west: $g$,
)
#let exponent-four-fiber-product = square(
  $ZZ G$,
  $ZZ G_0$,
  $R H$,
  $k G_0$,
)
#let metacyclic-fiber-product = square(
  $ZZ G$,
  $ZZ H$,
  $R compose H$,
  $overline(ZZ) H$,
)
#let normal-subgroup-fiber-product = square(
  $ZZ H$,
  $ZZ H slash ZZ sigma_H$,
  $ZZ$,
  $overline(ZZ)$,
)
#let induced-normal-subgroup-fiber-product = square(
  $ZZ G$,
  $ZZ G slash ZZ G sigma_H$,
  $ZZ(G slash H)$,
  $overline(ZZ)(G slash H)$,
)
#let exercise-fiber-product = square(
  $Lambda$,
  $Lambda'$,
  $Lambda''$,
  $overline(Lambda)$,
  east: $f$,
)
