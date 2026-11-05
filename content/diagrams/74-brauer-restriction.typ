#import "/content/main-defs.typ": *
#import "@preview/fletcher:0.5.8": diagram, edge, node

#align(center, diagram(
  spacing: (12mm, 10mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $B(L slash K)$),
  node((1, 0), $B(L slash F)$),
  node((0, 1), $H^2(frak(G),L^dot)$),
  node((1, 1), $H^2(frak(H),L^dot)$),
  edge((0, 0), (1, 0), $F times.o_K *$, "-|>"),
  edge((0, 0), (0, 1), "-|>"),
  edge((1, 0), (1, 1), "-|>"),
  edge((0, 1), (1, 1), "-|>"),
))
