#import "../main-defs.typ": GL
#import "@preview/fletcher:0.5.8": diagram, edge, node

#let graph(vertices, arrows, spacing: (10mm, 12mm)) = diagram(
  spacing: spacing,
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
#let square(
  a,
  b,
  c,
  d,
  top: [],
  west: [],
  east: [],
  bottom: [],
  bottom-side: left,
) = graph(
  (((0, 0), a), ((1, 0), b), ((0, 1), c), ((1, 1), d)),
  (
    ((0, 0), (1, 0), top),
    ((0, 0), (0, 1), west, right),
    ((1, 0), (1, 1), east, right),
    ((0, 1), (1, 1), bottom, bottom-side),
  ),
)
#let rows(top, bottom, labels: (:)) = graph(
  top.enumerate().map(p => ((p.at(0), 0), p.at(1)))
    + bottom.enumerate().map(p => ((p.at(0), 1), p.at(1))),
  range(top.len() - 1).map(i => ((i, 0), (i + 1, 0)))
    + range(bottom.len() - 1).map(i => ((i, 1), (i + 1, 1)))
    + range(1, 4).map(i => (
      (i, 0),
      (i, 1),
      labels.at(str(i), default: []),
      right,
    )),
)

#let relative-excision-comparison = graph(
  (
    ((0, 0), $K_1 lr((A))$),
    ((1, 0), $K_1 lr((overline(A)))$),
    ((2, 0), $K_0 lr((A,J))$),
    ((3, 0), $K_0 lr((A))$),
    ((4, 0), $K_0 lr((overline(A)))$),
    ((0, 1), $K_1 lr((B))$),
    ((1, 1), $K_1 lr((overline(B)))$),
    ((2, 1), $K_0 lr((B,J))$),
    ((3, 1), $K_0 lr((B))$),
    ((4, 1), $K_0 lr((overline(B)))$),
  ),
  range(4).map(i => ((i, 0), (i + 1, 0)))
    + range(4).map(i => ((i, 1), (i + 1, 1)))
    + range(5).map(i => (
      (i, 0),
      (i, 1),
      if i == 2 { $theta$ } else { [] },
      right,
    )),
)
#let relative-excision-pullback = view(square(
  $N$,
  $Q$,
  $overline(M)$,
  $overline(Q)$,
  top: $i$,
  west: $h$,
))
#let relative-excision-inclusions = view(square(
  $overline(M)$,
  $overline(N)$,
  $overline(V)$,
  $overline(V)$,
  top: $f$,
  bottom: $f^ast$,
))
#let relative-excision-lift = view(graph(
  (
    ((0, 0), $M$),
    ((1, 0), $subset.eq$),
    ((2, 0), $V$),
    ((0, 1), $N$),
    ((1, 1), $subset.eq$),
    ((2, 1), $V$),
    ((4, 0), $overline(M)$),
    ((5, 0), $subset.eq$),
    ((6, 0), $overline(V)$),
    ((4, 1), $overline(N)$),
    ((5, 1), $subset.eq$),
    ((6, 1), $overline(V)$),
  ),
  (
    ((2, 0), (2, 1), $g$, right),
    ((4, 0), (4, 1), $f$, right),
    ((6, 0), (6, 1), $f^ast$, right),
  ),
  spacing: (4mm, 12mm),
))
#let relative-elementary-kernel = view(rows(
  (
    $1$,
    $E lr((A)) inter GL lr((A,J))$,
    $E lr((A))$,
    $E lr((overline(A)))$,
    $1$,
  ),
  ($1$, $GL lr((A,J))$, $GL lr((A))$, $GL lr((overline(A)))$),
))
#let relative-double-square = square(
  $D$,
  $A$,
  $A$,
  $overline(A)$,
  top: $f$,
  west: $g$,
  east: $f'$,
  bottom: $g'$,
  bottom-side: right,
)
#let relative-double-general-linear = view(square(
  $GL lr((D))$,
  $GL lr((A))$,
  $GL lr((A))$,
  $GL lr((overline(A)))$,
  top: $f$,
  west: $g$,
  east: $g'$,
  bottom: $f'$,
))
#let relative-double-kernel-comparison = view(graph(
  (
    ((0, 0), $1$),
    ((1, 0), $E lr((A,J))$),
    ((2, 0), $GL lr((A,J))$),
    ((3, 0), $K_1^ast lr((A,J))$),
    ((0, 1), $1$),
    ((1, 1), $E lr((D))$),
    ((2, 1), $GL lr((D))$),
    ((3, 1), $K_1 lr((D))$),
    ((4, 1), $1$),
    ((0, 2), $1$),
    ((1, 2), $E lr((A))$),
    ((2, 2), $GL lr((A))$),
    ((3, 2), $K_1 lr((A))$),
    ((4, 2), $1$),
  ),
  range(3).map(i => ((i, 0), (i + 1, 0)))
    + range(4).map(i => ((i, 1), (i + 1, 1)))
    + range(4).map(i => ((i, 2), (i + 1, 2)))
    + (
      ((1, 0), (1, 1), $g_1$, right),
      ((2, 0), (2, 1), $g_2$, right),
      ((3, 0), (3, 1)),
      ((1, 1), (1, 2), $f_1$, right),
      ((2, 1), (2, 2), $f_2$, right),
      ((3, 1), (3, 2), $f_3$, right),
    ),
))
#let relative-finite-general-linear-comparison = view(rows(
  ($1$, $GL_n lr((A,J))$, $GL_n lr((D))$, $GL_n lr((A))$, $1$),
  ($1$, $K_1 lr((A,J))$, $K_1 lr((D))$, $K_1 lr((A))$, $1$),
))
#let relative-finite-quotient-comparison = view(rows(
  (
    $1$,
    $GL_n lr((A,J)) slash E_n lr((A,J))$,
    $GL_n lr((D)) slash E_n lr((D))$,
    $GL_n lr((A)) slash E_n lr((A))$,
    $1$,
  ),
  ($1$, $K_1 lr((A,J))$, $K_1 lr((D))$, $K_1 lr((A))$, $1$),
  labels: ("1": $alpha$, "2": $beta$, "3": $gamma$),
))
#let relative-snake-groups = view(graph(
  (
    ((1, 0), $A$),
    ((2, 0), $B$),
    ((3, 0), $C$),
    ((4, 0), $1$),
    ((0, 1), $1$),
    ((1, 1), $A'$),
    ((2, 1), $B'$),
    ((3, 1), $C'$),
  ),
  (
    ((1, 0), (2, 0), $rho$),
    ((2, 0), (3, 0)),
    ((3, 0), (4, 0)),
    ((0, 1), (1, 1)),
    ((1, 1), (2, 1)),
    ((2, 1), (3, 1), $sigma$),
    ((1, 0), (1, 1), $alpha$, right),
    ((2, 0), (2, 1), $beta$, right),
    ((3, 0), (3, 1), $gamma$, right),
  ),
))
