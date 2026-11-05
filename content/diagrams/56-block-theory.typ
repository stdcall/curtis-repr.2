#import "@preview/fletcher:0.5.8": diagram, edge, node

#let central-character-equivalence = block(width: 100%, align(center, diagram(
  spacing: (10mm, 5mm),
  node((0, 1), $c(A)$),
  node((2, 0), $k'$),
  node((2, 2), $k''$),
  edge((0, 1), (2, 0), $phi$, "-|>"),
  edge((0, 1), (2, 2), $psi$, "-|>", label-side: right),
  edge((2, 0), (2, 2), $sigma$, "-|>", label-side: left),
)))
