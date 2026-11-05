#import "../main-defs.typ": GL, rad
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
  east-side: right,
) = graph(
  (((0, 0), a), ((1, 0), b), ((0, 1), c), ((1, 1), d)),
  (
    ((0, 0), (1, 0), top),
    ((0, 0), (0, 1), west, right),
    ((1, 0), (1, 1), east, east-side),
    ((0, 1), (1, 1), bottom),
  ),
)
#let rows(top, bottom, vertical, horizontal: ()) = graph(
  top.enumerate().map(v => ((v.at(0), 0), v.at(1)))
    + bottom.enumerate().map(v => ((v.at(0), 1), v.at(1))),
  range(top.len() - 1).map(i => ((i, 0), (i + 1, 0)))
    + range(bottom.len() - 1).map(i => ((i, 1), (i + 1, 1)))
    + vertical.map(v => ((v.at(0), 0), (v.at(0), 1), v.at(1), right))
    + horizontal,
)

#let local-unit-conjugation = view(square(
  $pi_D Delta$,
  $Delta$,
  $pi_D Delta$,
  $Delta$,
  top: $pi_D^(-1)$,
  west: $omega$,
  east: $pi_D omega pi_D^(-1)$,
  bottom: $pi_D^(-1)$,
  east-side: left,
))
#let keating-localization-square = view(square(
  $K_2 lr((D))$,
  $product.co_P K_1 lr((overline(Gamma)_P))$,
  $K_2 lr((D_(P_0)))$,
  $K_1 lr((overline(Gamma)_(P_0)))$,
  top: $theta$,
  bottom: $theta_0$,
))
#let keating-subfield-comparison = view(graph(
  (
    ((0, 0), $K_2 lr((L))$),
    ((1, 0), $product.co_Q K_1 lr((S slash Q))$),
    ((2, 0), $K_1 lr((S))$),
    ((3, 0), $K_1 lr((L))$),
    ((0, 1), $K_2 lr((D))$),
    ((1, 1), $product.co_P K_1 lr((cal(T)_P))$),
    ((2, 1), $K_1 lr((Delta))$),
    ((3, 1), $K_1 lr((D))$),
  ),
  (
    ((0, 0), (1, 0), $theta'$),
    ((1, 0), (2, 0)),
    ((2, 0), (3, 0)),
    ((0, 1), (1, 1), $theta$),
    ((1, 1), (2, 1)),
    ((2, 1), (3, 1)),
    ((0, 0), (0, 1)),
    ((1, 0), (1, 1), $psi$, right),
    ((2, 0), (2, 1)),
    ((3, 0), (3, 1)),
  ),
))
#let hereditary-class-kernel-comparison = view(rows(
  (
    $K_2 lr((A))$,
    $product.co_P K_2 lr((A_P)) slash im K_2 lr((Lambda_P))$,
    $op("Cl")_1 Lambda$,
    $1$,
  ),
  (
    $K_2 lr((A))$,
    $product.co_P K_2 lr((A_P)) slash im K_2 lr((Gamma_P))$,
    $op("Cl")_1 Gamma$,
    $1$,
  ),
  ((0, $1$), (1, []), (2, [])),
))
#let hereditary-localization-comparison = view(graph(
  (
    ((0, 0), $1$),
    ((1, 0), $K_2 lr((A)) slash im K_2 lr((Lambda))$),
    ((2, 0), $K_1 lr((Lambda slash rad Lambda))$),
    ((3, 0), $S K_1 lr((Lambda))$),
    ((4, 0), $1$),
    ((0, 1), $1$),
    ((1, 1), $K_2 lr((A)) slash im K_2 lr((Gamma))$),
    ((2, 1), $K_1 lr((Gamma slash rad Gamma))$),
    ((3, 1), $S K_1 lr((Gamma))$),
    ((4, 1), $1$),
  ),
  (
    ((0, 0), (1, 0)),
    ((1, 0), (2, 0), $theta$),
    ((2, 0), (3, 0)),
    ((3, 0), (4, 0)),
    ((0, 1), (1, 1)),
    ((1, 1), (2, 1), $theta'$),
    ((2, 1), (3, 1)),
    ((3, 1), (4, 1)),
    ((1, 0), (1, 1)),
    ((2, 0), (2, 1)),
    ((3, 0), (3, 1)),
  ),
))
#let full-ideal-relative-comparison = view(square(
  $K_1 lr((Lambda,J))$,
  $K_1 lr((Lambda))$,
  $K_1 lr((Gamma,J))$,
  $K_1 lr((Gamma))$,
  top: $phi$,
  west: $sigma$,
  east: $theta$,
  bottom: $phi'$,
))
#let sk1-finiteness-comparison = view(rows(
  ($1$, $S K_1 lr((Lambda))$, $K_1 lr((Lambda))$, $K_1 lr((A))$),
  ($1$, $S K_1 lr((Lambda'))$, $K_1 lr((Lambda'))$, $K_1 lr((A))$),
  ((1, $theta'$), (2, $theta$), (3, $1$)),
))
#let wall-compact-kernel-comparison = view(graph(
  (
    ((0, 0), $1$),
    ((1, 0), $W_n$),
    ((2, 0), $GL_n lr((Lambda))$),
    ((3, 0), $K_1 lr((A))$),
    ((0, 1), $1$),
    ((1, 1), $S K_1 lr((Lambda))$),
    ((2, 1), $K_1 lr((Lambda))$),
    ((3, 1), $K_1 lr((A))$),
  ),
  (
    ((0, 0), (1, 0)),
    ((1, 0), (2, 0)),
    ((2, 0), (3, 0), $theta$),
    ((0, 1), (1, 1)),
    ((1, 1), (2, 1)),
    ((2, 1), (3, 1)),
    ((1, 0), (1, 1), $alpha$, right),
    ((2, 0), (2, 1), $beta$, right),
    ((3, 0), (3, 1), $1$, right),
  ),
))
#let wall-residue-splitting-comparison = view(graph(
  (
    ((0, 0), $1$),
    ((1, 0), $1+rad Gamma$),
    ((2, 0), $Gamma^dot$),
    ((3, 0), $overline(Gamma)^dot$),
    ((4, 0), $1$),
    ((0, 1), $1$),
    ((1, 1), $V$),
    ((2, 1), $K_1 lr((Lambda))$),
    ((3, 1), $K_1 lr((overline(Lambda)))$),
    ((4, 1), $1$),
  ),
  (
    ((0, 0), (1, 0)),
    ((1, 0), (2, 0)),
    ((2, 0), (3, 0), $gamma$),
    ((3, 0), (4, 0)),
    ((0, 1), (1, 1)),
    ((1, 1), (2, 1)),
    ((2, 1), (3, 1), $lambda$),
    ((3, 1), (4, 1)),
    ((1, 0), (1, 1), $psi$, right),
    ((2, 0), (2, 1), $beta$, right),
    ((3, 0), (3, 1), $delta$, right),
  ),
))
#let order-inclusion-fiber-product = view(square(
  $Lambda$,
  $Lambda slash r Gamma$,
  $Gamma$,
  $Gamma slash r Gamma$,
))
#let canonical-splitting-quotient-comparison = view(graph(
  (
    ((0, 0), $1$),
    ((1, 0), $G$),
    ((2, 0), $A$),
    ((3, 0), $E$),
    ((4, 0), $1$),
    ((0, 1), $1$),
    ((1, 1), $G slash H_i$),
    ((2, 1), $A slash H_i$),
    ((3, 1), $E$),
    ((4, 1), $1$),
  ),
  (
    ((0, 0), (1, 0)),
    ((1, 0), (2, 0), $gamma$),
    ((2, 0), (3, 0), $alpha$),
    ((3, 0), (4, 0)),
    ((0, 1), (1, 1)),
    ((1, 1), (2, 1), $gamma_i$),
    ((2, 1), (3, 1), $alpha_i$),
    ((3, 1), (4, 1)),
    ((1, 0), (1, 1)),
    ((2, 0), (2, 1), $pi_i$, right),
    ((3, 0), (3, 1), $1$, right),
  ),
))
