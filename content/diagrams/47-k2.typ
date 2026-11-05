#import "../main-defs.typ": *
#import "@preview/fletcher:0.5.8": diagram, edge, node
#let graph(vertices, arrows) = diagram(
  spacing: (9mm, 12mm),
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
#let three-rows(rows, vertical-labels: none) = view(graph(
  rows
    .enumerate()
    .map(((j, row)) => row.enumerate().map(((i, item)) => ((i, j), item)))
    .fold((), (result, items) => result + items),
  rows
    .enumerate()
    .map(((j, row)) => range(row.len() - 1).map(i => ((i, j), (i + 1, j))))
    .fold((), (result, items) => result + items)
    + range(2)
      .map(j => range(1, rows.first().len() - 1).map(i => (
        (i, j),
        (i, j + 1),
        if vertical-labels == none { [] } else { vertical-labels.at(j) },
        right,
      )))
      .fold((), (result, items) => result + items),
))
#let universal-central-extension-diagram = view(graph(
  (
    ((0, 0), $1$),
    ((1, 0), $C$),
    ((2, 0), $E$),
    ((3, 0), $G$),
    ((4, 0), $1$),
    ((0, 1), $1$),
    ((1, 1), $C_1$),
    ((2, 1), $E_1$),
    ((3, 1), $G$),
    ((4, 1), $1$),
  ),
  (
    ((0, 0), (1, 0)),
    ((1, 0), (2, 0)),
    ((2, 0), (3, 0), $phi$),
    ((3, 0), (4, 0)),
    ((0, 1), (1, 1)),
    ((1, 1), (2, 1)),
    ((2, 1), (3, 1)),
    ((3, 1), (4, 1)),
    ((2, 0), (2, 1)),
    ((3, 0), (3, 1)),
  ),
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
#let relative-whitehead-three-rows = three-rows(
  (
    ($1$, $E(A,J)$, $GL lr((A,J))$, $K_1 lr((A,J))$, $1$),
    ($1$, $E(D)$, $GL lr((D))$, $K_1 lr((D))$, $1$),
    ($1$, $E(A)$, $GL lr((A))$, $K_1 lr((A))$, $1$),
  ),
  vertical-labels: ($g$, $f$),
)
#let relative-k2-three-rows = three-rows((
  ($1$, $K_2 lr((A,J))$, $op("St") lr((A,J))$, $E(A,J)$, $1$),
  ($1$, $K_2 lr((D))$, $op("St") lr((D))$, $E(D)$, $1$),
  ($1$, $K_2 lr((A))$, $op("St") lr((A))$, $E(A)$, $1$),
))
#let relative-full-k2-three-rows = three-rows((
  (
    $1$,
    $K_2 lr((A,J))$,
    $op("St") lr((A,J))$,
    $GL lr((A,J))$,
    $K_1 lr((A,J))$,
    $1$,
  ),
  ($1$, $K_2 lr((D))$, $op("St") lr((D))$, $GL lr((D))$, $K_1 lr((D))$, $1$),
  ($1$, $K_2 lr((A))$, $op("St") lr((A))$, $GL lr((A))$, $K_1 lr((A))$, $1$),
))
#let relative-steinberg-snake-diagram = view(graph(
  (
    ((1, 0), $op("St") lr((A,J))$),
    ((2, 0), $op("St") lr((A))$),
    ((3, 0), $op("St") lr((overline(A)))$),
    ((4, 0), $1$),
    ((0, 1), $1$),
    ((1, 1), $GL lr((A,J))$),
    ((2, 1), $GL lr((A))$),
    ((3, 1), $GL lr((overline(A)))$),
  ),
  (
    ((1, 0), (2, 0)),
    ((2, 0), (3, 0)),
    ((3, 0), (4, 0)),
    ((0, 1), (1, 1)),
    ((1, 1), (2, 1)),
    ((2, 1), (3, 1)),
    ((1, 0), (1, 1)),
    ((2, 0), (2, 1)),
    ((3, 0), (3, 1)),
  ),
))
#let relative-excision-comparison = view(graph(
  (
    ((0, 0), $1$),
    ((1, 0), $K_2 lr((A,J))$),
    ((2, 0), $op("St") lr((A,J))$),
    ((3, 0), $GL lr((A,J))$),
    ((4, 0), $K_1 lr((A,J))$),
    ((5, 0), $1$),
    ((0, 1), $1$),
    ((1, 1), $K_2 lr((A',J'))$),
    ((2, 1), $op("St") lr((A',J'))$),
    ((3, 1), $GL lr((A',J'))$),
    ((4, 1), $K_1 lr((A',J'))$),
    ((5, 1), $1$),
  ),
  range(2)
    .map(j => range(5).map(i => ((i, j), (i + 1, j))))
    .fold((), (result, items) => result + items)
    + (
      ((1, 0), (1, 1)),
      ((2, 0), (2, 1), $alpha$, right),
      ((3, 0), (3, 1), $psi$, right),
      ((4, 0), (4, 1)),
    ),
))
#let excision-relative-sequences-comparison = view(graph(
  (
    ((0, 0), $K_2 lr((A,J))$),
    ((1, 0), $K_2 lr((A))$),
    ((2, 0), $K_2 lr((overline(A)))$),
    ((3, 0), $K_1 lr((A,J))$),
    ((4, 0), $K_1 lr((A))$),
    ((5, 0), $K_1 lr((overline(A)))$),
    ((0, 1), $K_2 lr((A',J'))$),
    ((1, 1), $K_2 lr((A'))$),
    ((2, 1), $K_2 lr((overline(A)'))$),
    ((3, 1), $K_1 lr((A',J'))$),
    ((4, 1), $K_1 lr((A'))$),
    ((5, 1), $K_1 lr((overline(A)'))$),
  ),
  range(5).map(i => ((i, 0), (i + 1, 0), $alpha_#(i + 1)$))
    + range(5).map(i => ((i, 1), (i + 1, 1), $beta_#(i + 1)$, right))
    + range(6).map(i => ((i, 0), (i, 1), $gamma_#(i + 1)$, right)),
))
#let milnor-fiber-product-square = view(square(
  $A$,
  $A_1$,
  $A_2$,
  $overline(A)$,
  top: $f_1$,
  west: $f_2$,
  east: $g_1$,
  bottom: $g_2$,
))
#let tate-symbol-filtration-comparison = view(graph(
  (
    ((0, 0), $1$),
    ((1, 0), $S_q$),
    ((2, 0), $S_p$),
    ((3, 0), $op("GF") lr((p))^dot$),
    ((4, 0), $1$),
    ((0, 1), $1$),
    ((1, 1), $lr({plus.minus 1}) times dots times op("GF") lr((q))^dot$),
    (
      (2, 1),
      $lr({plus.minus 1}) times dots times op("GF") lr((q))^dot
      times op("GF") lr((p))^dot$,
    ),
    ((3, 1), $op("GF") lr((p))^dot$),
    ((4, 1), $1$),
  ),
  range(2)
    .map(j => range(4).map(i => ((i, j), (i + 1, j))))
    .fold((), (result, items) => result + items)
    + (
      ((1, 0), (1, 1), $tau_q$, right),
      ((2, 0), (2, 1), $tau_p$, right),
      ((3, 0), (3, 1), $1$, right),
    ),
))
#let polynomial-axis-fiber-product = view(square($A$, $F[x]$, $F[y]$, $F$))
