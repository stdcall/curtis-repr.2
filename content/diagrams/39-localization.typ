#import "@preview/fletcher:0.5.8": diagram, edge, node

#let graph(vertices, arrows, spacing: (12mm, 11mm)) = block(
  width: 100%,
  align(center, diagram(
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
  )),
)

#let decomposition-triangle = graph(
  (
    ((0, 0), $G_0^R lr((R G))$),
    ((1, 0), $G_0 lr((K G))$),
    ((0, 1), $G_0 lr((overline(R) G))$),
  ),
  (
    ((0, 0), (1, 0), $phi$),
    ((0, 0), (0, 1), $gamma$, right),
    ((1, 0), (0, 1), $gamma'$, right),
  ),
)

#let quotient-square = graph(
  (
    ((0, 0), $G_0 lr((overline(R) tilde(G)))$),
    ((1, 0), $G_0 lr((R tilde(G)))$),
    ((0, 1), $G_0 lr((overline(R) G))$),
    ((1, 1), $G_0 lr((R G))$),
  ),
  (
    ((0, 0), (1, 0), $tilde(psi)$),
    ((0, 1), (1, 1), $psi$),
    ((0, 0), (0, 1)),
    ((1, 0), (1, 1)),
  ),
)

#let class-group-comparison = {
  let vertices = (
    ((1, 0), $op("Cl") Lambda$),
    ((2, 0), $G_0^R lr((Lambda))$),
    ((3, 0), $G_0 lr((A))$),
    ((4, 0), $0$),
    ((0, 1), $0$),
    ((1, 1), $op("Cl") Lambda'$),
    ((2, 1), $G_0^R lr((Lambda'))$),
    ((3, 1), $G_0 lr((A))$),
    ((4, 1), $0$),
  )
  graph(
    vertices,
    (
      ((1, 0), (2, 0), $mu$),
      ((2, 0), (3, 0), $phi$),
      ((3, 0), (4, 0)),
      ((0, 1), (1, 1)),
      ((1, 1), (2, 1), $mu'$),
      ((2, 1), (3, 1), $phi'$),
      ((3, 1), (4, 1)),
      ((1, 0), (1, 1), $rho$, right),
      ((2, 1), (2, 0), $alpha$, left),
      ((3, 1), (3, 0), $1$, left),
    ),
    spacing: (7mm, 11mm),
  )
}

#let order-localization-comparison = {
  let rows = (
    (
      $K_1 lr((A))$,
      $G_0^t lr((Lambda'))$,
      $G_0 lr((Lambda'))$,
      $G_0 lr((A))$,
      $0$,
    ),
    (
      $K_1 lr((A))$,
      $G_0^t lr((Lambda))$,
      $G_0 lr((Lambda))$,
      $G_0 lr((A))$,
      $0$,
    ),
  )
  let labels = (($delta'$, $psi'$, $phi'$, []), ($delta$, $psi$, $phi$, []))
  let vertices = rows
    .enumerate()
    .map(((r, row)) => row.enumerate().map(((c, body)) => ((c, r), body)))
    .fold((), (acc, row) => acc + row)
  let horizontal = range(2)
    .map(r => range(4).map(c => ((c, r), (c + 1, r), labels.at(r).at(c))))
    .fold((), (acc, row) => acc + row)
  let vertical = ($1$, $beta$, $alpha$, $1$)
    .enumerate()
    .map(
      ((c, body)) => ((c, 0), (c, 1), body, right),
    )
  graph(vertices, horizontal + vertical, spacing: (7mm, 11mm))
}
