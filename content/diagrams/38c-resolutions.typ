#import "@preview/fletcher:0.5.8": diagram, edge, node

#let graph(vertices, arrows, spacing: (6mm, 7mm)) = diagram(
  spacing: spacing,
  node-inset: 2pt,
  node-defocus: 0,
  ..vertices.map(v => node(v.at(0), v.at(1))),
  ..arrows.map(e => edge(
    e.at(0),
    e.at(1),
    e.at(2, default: []),
    e.at(4, default: "-|>"),
    label-side: e.at(3, default: left),
  )),
)
#let view(body) = block(width: 100%, align(center, body))
#let chain(row, cols) = range(cols - 1).map(c => ((c, row), (c + 1, row)))

#let horseshoe-input = {
  let top = ($0$, $K'$, $P'_n$, $dots$, $P'_0$, $M'$, $0$)
  let bottom = ($0$, $K''$, $P''_n$, $dots$, $P''_0$, $M''$, $0$)
  view(graph(
    (
      ..top.enumerate().map(((c, body)) => ((c, 1), body)),
      ..bottom.enumerate().map(((c, body)) => ((c, 3), body)),
      ((5, 0), $0$),
      ((5, 2), $M$),
      ((5, 4), $0$),
    ),
    (
      ..chain(1, 7),
      ..chain(3, 7),
      ((5, 0), (5, 1)),
      ((5, 1), (5, 2), $f$, left),
      ((5, 2), (5, 3), $g$, left),
      ((5, 3), (5, 4)),
    ),
  ))
}
#let horseshoe-output = {
  let rows = (
    ($0$, $K'$, $P'_n$, $dots$, $P'_0$, $M'$, $0$),
    ($0$, $K$, $P'_n plus.o P''_n$, $dots$, $P'_0 plus.o P''_0$, $M$, $0$),
    ($0$, $K''$, $P''_n$, $dots$, $P''_0$, $M''$, $0$),
  )
  let vertices = rows
    .enumerate()
    .map(((r, row)) => row.enumerate().map(((c, body)) => ((c, r), body)))
    .fold((), (acc, row) => acc + row)
  let vertical = (1, 2, 4)
    .map(c => (
      ((c, 0), (c, 1)),
      ((c, 1), (c, 2)),
    ))
    .fold((), (acc, col) => acc + col)
  let arrows = (
    ..chain(0, 7),
    ..chain(1, 7),
    ..chain(2, 7),
    ..vertical,
    ((5, 0), (5, 1), $f$, left),
    ((5, 1), (5, 2), $g$, left),
  )
  view(graph(vertices, arrows))
}

#let automorphism-lifting = view(graph(
  (
    ((0, 0), $P_0 = P plus.o P$),
    ((1, 0), $M plus.o M$),
    ((2, 0), $M$),
    ((0, 1), $P_0 = P plus.o P$),
    ((1, 1), $M plus.o M$),
    ((2, 1), $M$),
  ),
  (
    ((0, 0), (1, 0), $(f, f)$),
    ((1, 0), (2, 0), $(1, 0)$),
    ((0, 1), (1, 1), $(f, f)$),
    ((1, 1), (2, 1), $(1, 0)$),
    ((0, 0), (0, 1), $pi_0$, right, "--|>"),
    ((1, 0), (1, 1), $(mu, mu^(-1))$, right),
    ((2, 0), (2, 1), $mu$, right),
  ),
  spacing: (12mm, 12mm),
))

#let elementary-action = view(graph(
  (
    ((0, 0), $M$),
    ((1, 0), $plus.o$),
    ((2, 0), $M$),
    ((0, 1), $M$),
    ((1, 1), $plus.o$),
    ((2, 1), $M$),
  ),
  (
    ((0, 0), (0, 1), $1$, right),
    ((0, 0), (2, 1), $alpha$, right),
    ((2, 0), (2, 1), $1$, right),
  ),
  spacing: (2mm, 10mm),
))
#let elementary-lifting = view(graph(
  (
    ((0, 0), $P$),
    ((1, 0), $plus.o$),
    ((2, 0), $P$),
    ((4, 0), $M$),
    ((5, 0), $plus.o$),
    ((6, 0), $M$),
    ((0, 1), $P$),
    ((1, 1), $plus.o$),
    ((2, 1), $P$),
    ((4, 1), $M$),
    ((5, 1), $plus.o$),
    ((6, 1), $M$),
  ),
  (
    ((2, 0), (4, 0), $(f, f)$),
    ((2, 1), (4, 1), $(f, f)$),
    ((0, 0), (0, 1), $1$, right),
    ((0, 0), (2, 1), $theta$, right),
    ((2, 0), (2, 1), $1$, right),
    ((4, 0), (4, 1), $1$, right),
    ((4, 0), (6, 1), $alpha$, right),
    ((6, 0), (6, 1), $1$, right),
  ),
  spacing: (6mm, 14mm),
))

#let automorphism-pullback = view(graph(
  (
    ((2, 0), $0$),
    ((2, 1), $(X, xi)$),
    ((0, 2), $0$),
    ((1, 2), $(X', xi')$),
    ((2, 2), $(Y, eta)$),
    ((3, 2), $(P, pi)$),
    ((4, 2), $0$),
    ((2, 3), $(P', pi')$),
    ((3, 3), $(M, mu)$),
    ((4, 3), $0$),
    ((2, 4), $0$),
  ),
  (
    ((2, 0), (2, 1)),
    ((2, 1), (2, 2)),
    ..chain(2, 5),
    ((2, 2), (2, 3)),
    ((2, 3), (2, 4)),
    ((3, 2), (3, 3), $f$, right),
    ((2, 3), (3, 3), $f'$),
    ((3, 3), (4, 3)),
  ),
  spacing: (6mm, 7mm),
))

#let automorphism-horseshoe = {
  let columns = (
    ($0$, $(X', xi')$, $(P', pi')$, $(M', mu')$, $0$),
    ($0$, $(X_0, xi_0)$, $(P', pi') plus.o (P, pi)$, $(M, mu)$, $0$),
    ($0$, $(X'', xi'')$, $(P, pi)$, $(M'', mu'')$, $0$),
  )
  let vertices = columns
    .enumerate()
    .map(((c, col)) => col.enumerate().map(((r, body)) => ((c + 1, r), body)))
    .fold((), (acc, col) => acc + col)
  let vertical = range(1, 4)
    .map(c => range(4).map(r => (
      (c, r),
      (c, r + 1),
      if r == 2 { ($f'$, $(g f', f)$, $h f$).at(c - 1) } else { [] },
      right,
    )))
    .fold((), (acc, col) => acc + col)
  view(graph(
    (..vertices, ((0, 2), $0$), ((4, 2), $0$), ((0, 3), $0$), ((4, 3), $0$)),
    (
      ..vertical,
      ((0, 2), (1, 2)),
      ((1, 2), (2, 2), $(1, 0)$),
      ((2, 2), (3, 2), $(0, 1)$),
      ((3, 2), (4, 2)),
      ..chain(3, 5),
    ),
    spacing: (7mm, 7mm),
  ))
}
