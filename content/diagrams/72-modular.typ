#import "/content/main-defs.typ": *
#import "@preview/fletcher:0.5.8": diagram, edge, node

#let graph(vertices, arrows) = diagram(
  spacing: (10mm, 10mm),
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
)
#let view(body) = block(width: 100%, align(center, body))

#let decomposition-square = view(graph(
  (
    ((0, 0), $G_0(K G)$),
    ((1, 0), $"ch" G$),
    ((0, 1), $G_0(k G)$),
    ((1, 1), $"Bch" G$),
  ),
  (
    ((0, 0), (1, 0)),
    ((0, 0), (0, 1), $d$),
    ((1, 0), (1, 1), $d'$, right),
    ((0, 1), (1, 1)),
  ),
))

#let cartan-square = view(graph(
  (
    ((0, 0), $K_0(k G)$),
    ((1, 0), $"Pch" G$),
    ((0, 1), $G_0(k G)$),
    ((1, 1), $"Bch" G$),
  ),
  (
    ((0, 0), (1, 0)),
    ((0, 0), (0, 1), $c$),
    ((1, 0), (1, 1), $c'$, right),
    ((0, 1), (1, 1)),
  ),
))

#let projective-lift-square = view(graph(
  (
    ((0, 0), $K_0(k G)$),
    ((1, 0), $"Pch" G$),
    ((0, 1), $G_0(K G)$),
    ((1, 1), $"ch" G$),
  ),
  (
    ((0, 0), (1, 0)),
    ((0, 0), (0, 1), $e$),
    ((1, 0), (1, 1), $e'$, right),
    ((0, 1), (1, 1)),
  ),
))

#let character-cartan-brauer-triangle = view(graph(
  (
    ((0, 0), $"ch" G$),
    ((1, 0), $"Bch" G$),
    ((0.5, 1), $"Pch" G$),
  ),
  (
    ((0, 0), (1, 0), $d'$),
    ((0.5, 1), (0, 0), $e'$),
    ((0.5, 1), (1, 0), $c'$, right),
  ),
))
