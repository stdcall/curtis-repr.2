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
#let square(a, b, c, d, east: [], bottom: []) = graph(
  (((0, 0), a), ((1, 0), b), ((0, 1), c), ((1, 1), d)),
  (
    ((0, 0), (1, 0)),
    ((0, 0), (0, 1)),
    ((1, 0), (1, 1), east, right),
    ((0, 1), (1, 1), bottom),
  ),
)
#let class-group-localization-comparison = fit-diagram(graph(
  (
    ((0, 0), $1$),
    ((1, 0), $K_1 lr((A)) slash im K_1 lr((Lambda))$),
    ((2, 0), $K_0 lr((cal(T)))$),
    ((3, 0), $S K_0 lr((Lambda))$),
    ((4, 0), $0$),
    ((0, 1), $1$),
    ((1, 1), $display(product.co_P K_1 lr((A_P)) slash im K_1 lr((Lambda_P)))$),
    ((2, 1), $display(product.co_P K_0 lr((cal(T)_P)))$),
    ((3, 1), $display(product.co_P S K_0 lr((Lambda_P)))$),
    ((4, 1), $0$),
  ),
  (
    ..range(2)
      .map(j => range(4).map(i => ((i, j), (i + 1, j))))
      .fold((), (result, items) => result + items),
    ((1, 0), (1, 1), $alpha$, right),
    ((2, 0), (2, 1), $beta$, right),
    ((3, 0), (3, 1), $gamma$, right),
  ),
))
#let idele-reduced-norm-triangle = view(graph(
  (((0, 0), $J(A)$), ((1, 0), $J K_1 lr((A))$), ((1, 1), $J(C)$)),
  (
    ((0, 0), (1, 0)),
    ((0, 0), (1, 1), $op("nr")$, right),
    ((1, 0), (1, 1), $op("nr")$, right),
  ),
))

#let two-rows(rows, labels, vertical-columns) = fit-diagram(graph(
  rows
    .enumerate()
    .map(((j, row)) => row.enumerate().map(((i, item)) => ((i, j), item)))
    .fold((), (result, items) => result + items),
  range(2)
    .map(j => range(rows.first().len() - 1).map(i => ((i, j), (i + 1, j))))
    .fold((), (result, items) => result + items)
    + vertical-columns
      .enumerate()
      .map(((index, i)) => ((i, 0), (i, 1), labels.at(index), right)),
))
#let higher-class-group-localization-comparison = two-rows(
  (
    (
      $1$,
      $K_2 lr((A)) slash im K_2 lr((Lambda))$,
      $K_1 lr((cal(T)))$,
      $K_1 lr((Lambda))$,
      $K_1 lr((A))$,
    ),
    (
      $1$,
      $display(product.co_P K_2 lr((A_P)) slash im K_2 lr((Lambda_P)))$,
      $K_1 lr((cal(T)))$,
      $display(product_P K_1 lr((Lambda_P)))$,
      $display(product_P K_1 lr((A_P)))$,
    ),
  ),
  ([], [$1$], [], []),
  (1, 2, 3, 4),
)
#let higher-class-group-kernel-comparison = two-rows(
  (
    (
      $1$,
      $K_2 lr((A)) slash im K_2 lr((Lambda))$,
      $K_1 lr((cal(T)))$,
      $S K_1 lr((Lambda))$,
      $1$,
    ),
    (
      $1$,
      $display(product.co_P K_2 lr((A_P)) slash im K_2 lr((Lambda_P)))$,
      $K_1 lr((cal(T)))$,
      $display(product.co_P S K_1 lr((Lambda_P)))$,
      $1$,
    ),
  ),
  ([], [$1$], []),
  (1, 2, 3),
)
#let order-fiber-product-square = view(square(
  $Lambda$,
  $Lambda_1$,
  $Lambda_2$,
  $overline(Lambda)$,
  east: [$g_1$],
  bottom: [$g_2$],
))
#let class-group-maximal-order-triangle = view(graph(
  (
    ((0, 0), $op("Cl") Lambda$),
    ((2, 0), $op("Cl") Lambda'$),
    ((1, 1), $op("Cl") Lambda_1 plus.o op("Cl") Lambda_2$),
  ),
  (((0, 0), (2, 0)), ((0, 0), (1, 1)), ((1, 1), (2, 0))),
))
#let matrix-order-fiber-product-square = view(square(
  $M_n lr((Lambda))$,
  $M_n lr((Lambda_1))$,
  $M_n lr((Lambda_2))$,
  $M_n lr((overline(Lambda)))$,
  east: [$h_1$],
  bottom: [$h_2$],
))
#let matrix-class-kernel-sequence-fork = fit-diagram(graph(
  (
    ((0, 0), $1$),
    ((1, 0), $W$),
    ((2, 0), $GL_n lr((overline(Lambda)))$),
    ((3, 0), $op("Cl") Lambda$),
    ((4, 0), $op("Cl") Lambda_1 plus.o op("Cl") Lambda_2$),
    ((5, 0), $0$),
    ((3, 1), $D(Lambda)$),
    ((4, 1), $D(Lambda_1) plus.o D(Lambda_2)$),
    ((5, 1), $0$),
  ),
  (
    ..range(5).map(i => ((i, 0), (i + 1, 0))),
    ((2, 0), (3, 1)),
    ((3, 1), (4, 1)),
    ((4, 1), (5, 1)),
  ),
))
#let restricted-image-fiber-product-square = view(square(
  $Lambda$,
  $Lambda_1$,
  $Lambda_3$,
  $g_1 lr((Lambda_1))$,
))
#let overorder-ideal-fiber-product-square = view(square(
  $Lambda$,
  $Gamma$,
  $overline(Lambda)$,
  $overline(Gamma)$,
))
#let overorder-class-kernel-sequence-fork = fit-diagram(graph(
  (
    ((0, 0), $K_1 lr((Lambda))$),
    ((1, 0), $K_1 lr((Gamma)) times K_1 lr((overline(Lambda)))$),
    ((2, 0), $K_1 lr((overline(Gamma)))$),
    ((3, 0), $op("Cl") Lambda$),
    ((4, 0), $op("Cl") Gamma$),
    ((5, 0), $0$),
    ((3, 1), $D(Lambda)$),
    ((4, 1), $D(Gamma)$),
    ((5, 1), $0$),
  ),
  (
    ..range(5).map(i => ((i, 0), (i + 1, 0))),
    ((2, 0), (3, 1)),
    ((3, 1), (4, 1)),
    ((4, 1), (5, 1)),
  ),
))
#let full-ideal-localization-comparison = fit-diagram(graph(
  (
    ((0, 0), $K_1 lr((overline(Gamma)))$),
    ((1, 0), $K_0 lr((Lambda))$),
    ((2, 0), $K_0 lr((Gamma))$),
    ((3, 0), $plus.o$),
    ((4, 0), $K_0 lr((overline(Lambda)))$),
    ((5, 0), $K_0 lr((overline(Gamma)))$),
    ((0, 1), $display(product_P K_1 lr((overline(Gamma)_P)))$),
    ((1, 1), $display(product_P K_0 lr((Lambda_P)))$),
    ((2, 1), $display(product_P K_0 lr((Gamma_P)))$),
    ((3, 1), $plus.o$),
    ((4, 1), $display(product_P K_0 lr((overline(Lambda)_P)))$),
    ((5, 1), $display(product_P K_0 lr((overline(Gamma)_P)))$),
  ),
  (
    ((0, 0), (1, 0), $partial$),
    ((1, 0), (2, 0)),
    ((4, 0), (5, 0)),
    ((0, 1), (1, 1), $partial'$),
    ((1, 1), (2, 1)),
    ((4, 1), (5, 1)),
    ((0, 0), (0, 1), $f_1$, right),
    ((1, 0), (1, 1), $f_2$, right),
    ((2, 0), (2, 1), $f_3$, right),
    ((4, 0), (4, 1), $f_4$, right),
    ((5, 0), (5, 1), $f_5$, right),
  ),
))
#let full-ideal-determinant-square = view(graph(
  (
    ((0, 0), $K_1 lr((Gamma))$),
    ((1, 0), $K_1 lr((overline(Gamma)))$),
    ((0, 1), $Gamma^dot$),
    ((1, 1), $overline(Gamma)^dot$),
  ),
  (
    ((0, 0), (1, 0)),
    ((0, 0), (0, 1), $det$, right),
    ((1, 0), (1, 1), $det$, right),
    ((0, 1), (1, 1)),
  ),
))
