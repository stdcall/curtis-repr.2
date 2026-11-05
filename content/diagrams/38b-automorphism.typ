#import "@preview/fletcher:0.5.8": diagram, edge, node

#let automorphism-morphism = block(width: 100%, align(center, diagram(
  spacing: (13mm, 10mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $M$),
  node((1, 0), $N$),
  node((0, 1), $M$),
  node((1, 1), $N$),
  edge((0, 0), (1, 0), $f$, "-|>", label-side: left),
  edge((0, 1), (1, 1), $f$, "-|>", label-side: left),
  edge((0, 0), (0, 1), $mu$, "-|>", label-side: right),
  edge((1, 0), (1, 1), $nu$, "-|>", label-side: right),
)))
