#import "@preview/fletcher:0.5.8": diagram, edge, node

#let polynomial-k-g-square = block(width: 100%, align(center, diagram(
  spacing: (18mm, 12mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $K_0 lr((R))$),
  node((1, 0), $K_0 lr((R'))$),
  node((0, 1), $G_0 lr((R))$),
  node((1, 1), $G_0 lr((R'))$),
  edge((0, 0), (1, 0), $phi$, "-|>"),
  edge((0, 1), (1, 1), $psi$, "-|>"),
  edge((0, 0), (0, 1), "-|>"),
  edge((1, 0), (1, 1), "-|>"),
)))
