#import "/content/main-defs.typ": *
#import "@preview/fletcher:0.5.8": diagram, edge, node

#let artin-quotient-square() = align(center, diagram(
  node((0, 0), $G_0(QQ C)$),
  node((1, 0), $G_0(QQ overline(C))$),
  node((0, 1), $G_0(QQ G)$),
  node((1, 1), $G_0(QQ overline(G))$),
  edge((0, 0), (1, 0), "-|>"),
  edge((0, 0), (0, 1), $upright("ind")$, "-|>", label-side: left),
  edge((1, 0), (1, 1), $upright("ind")$, "-|>", label-side: left),
  edge((0, 1), (1, 1), "-|>"),
))
