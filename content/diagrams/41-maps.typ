#import "@preview/fletcher:0.5.8": diagram, edge, node

#let cancellation-transvections = block(width: 100%, align(center, diagram(
  spacing: (12mm, 10mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $Lambda plus.o M$),
  node((1, 0), $Lambda plus.o M$),
  node((2, 0), $Lambda plus.o M$),
  node((3, 0), $Lambda plus.o M$),
  edge((0, 0), (1, 0), $mat(1, 0; f, 1)$, "-|>", label-side: left),
  edge((1, 0), (2, 0), $mat(1, g; 0, 1)$, "-|>", label-side: left),
  edge((2, 0), (3, 0), $mat(1, 0; h, 1)$, "-|>", label-side: left),
)))

#let basic-free-summand-diagram = {
  let rows = (
    ($0$, $Lambda$, $Lambda^((n))$, $Lambda^((n-1))$, $0$),
    ($0$, $Lambda x$, $F$, $F slash Lambda x$, $0$),
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
      .map(r => range(4).map(c => edge((c, r), (c + 1, r), "-|>")))
      .fold((), (acc, row) => acc + row),
    ..($alpha$, $beta$, $gamma$)
      .enumerate()
      .map(((i, body)) => edge(
        (i + 1, 0),
        (i + 1, 1),
        body,
        "-|>",
        label-side: right,
      )),
  )))
}
