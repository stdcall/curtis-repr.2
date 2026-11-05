#import "@preview/fletcher:0.5.8": diagram, edge, node

#let lattice-comparison = {
  let rows = (
    ($0$, $L_1$, $M_1$, $N_1$, $0$),
    ($0$, $L_2$, $M_2$, $N_2$, $0$),
  )
  block(width: 100%, align(center, diagram(
    spacing: (9mm, 11mm),
    node-inset: 2pt,
    node-defocus: 0,
    ..rows
      .enumerate()
      .map(((r, row)) => row
        .enumerate()
        .map(
          ((c, body)) => node((c, r), body),
        ))
      .fold((), (acc, row) => acc + row),
    ..range(2)
      .map(r => range(4).map(c => edge(
        (c, r),
        (c + 1, r),
        if c == 1 { if r == 0 { $f_1$ } else { $f_2$ } } else if c == 2 {
          if r == 0 { $g_1$ } else { $g_2$ }
        } else { [] },
        "-|>",
        label-side: left,
      )))
      .fold((), (acc, row) => acc + row),
    ..($lambda$, $mu$, $nu$)
      .enumerate()
      .map(((i, body)) => edge(
        (i + 1, 0),
        (i + 1, 1),
        body,
        "--|>",
        label-side: right,
      )),
  )))
}

#let whitehead-norm-square = block(width: 100%, align(center, diagram(
  spacing: (12mm, 10mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $A^dot slash [A^dot, A^dot]$),
  node((1, 0), $K_1 lr((A))$),
  node((0, 1), $op("nr")_(A slash K) lr((A^dot))$),
  node((1, 1), $op("nr")_(D slash K) lr((D^dot))$),
  edge((0, 0), (1, 0), "-|>"),
  edge((0, 1), (1, 1), "-|>"),
  edge((0, 0), (0, 1), "-|>"),
  edge((1, 0), (1, 1), "-|>"),
)))
