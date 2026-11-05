#import "@preview/fletcher:0.5.8": diagram, edge, node

#let brauer-endomorphism-square = block(width: 100%, align(center, diagram(
  spacing: (12mm, 8mm),
  node((0, 0), $c(R G)$),
  node((1, 0), $c(B')$),
  node((0, 1), $E$),
  node((1, 1), $E'$),
  edge((0, 0), (1, 0), $tau$, "-|>"),
  edge((0, 0), (0, 1), $alpha$, "-|>", label-side: right),
  edge((1, 0), (1, 1), $alpha'$, "-|>", label-side: left),
  edge((0, 1), (1, 1), $theta$, "-|>"),
)))
