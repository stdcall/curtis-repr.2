#import "@preview/fletcher:0.5.8": diagram, edge, node

#let graph(vertices, arrows, spacing: (15mm, 12mm)) = block(
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

#let determinantal-naturality = graph(
  (
    ((0, 0), $K_1 lr((Lambda))$),
    ((1, 0), $K_1 lr((Gamma))$),
    ((0, 1), $K_"det" lr((Lambda))$),
    ((1, 1), $K_"det" lr((Gamma))$),
  ),
  (
    ((0, 0), (1, 0), $phi_*$),
    ((0, 1), (1, 1), $phi'$),
    ((0, 0), (0, 1)),
    ((1, 0), (1, 1)),
  ),
)

#let torsion-presentation-comparison = graph(
  (
    ((0, 0), $0$),
    ((1, 0), $L$),
    ((2, 0), $F slash s t F$),
    ((3, 0), $M$),
    ((4, 0), $0$),
    ((0, 1), $0$),
    ((1, 1), $N$),
    ((2, 1), $F slash s F$),
    ((3, 1), $M$),
    ((4, 1), $0$),
  ),
  (
    ((0, 0), (1, 0)),
    ((1, 0), (2, 0)),
    ((2, 0), (3, 0)),
    ((3, 0), (4, 0)),
    ((0, 1), (1, 1)),
    ((1, 1), (2, 1)),
    ((2, 1), (3, 1)),
    ((3, 1), (4, 1)),
    ((1, 0), (1, 1), $alpha$, right),
    ((2, 0), (2, 1), $beta$, right),
    ((3, 0), (3, 1), $1$, right),
  ),
  spacing: (12mm, 12mm),
)

#let localization-isomorphism-lift = graph(
  (
    ((0, 0), $0$),
    ((1, 0), $P$),
    ((2, 0), $P$),
    ((3, 0), $P slash g' P$),
    ((4, 0), $0$),
    ((0, 1), $0$),
    ((1, 1), $P$),
    ((2, 1), $P$),
    ((3, 1), $P slash s' P$),
    ((4, 1), $0$),
  ),
  (
    ((0, 0), (1, 0)),
    ((1, 0), (2, 0), $g'$),
    ((2, 0), (3, 0)),
    ((3, 0), (4, 0)),
    ((0, 1), (1, 1)),
    ((1, 1), (2, 1), $s'$),
    ((2, 1), (3, 1)),
    ((3, 1), (4, 1)),
    ((1, 0), (1, 1), $gamma_1$, right),
    ((2, 0), (2, 1), $gamma_0$, right),
    ((3, 0), (3, 1), $gamma'$, right),
  ),
  spacing: (12mm, 12mm),
)

#let horseshoe(last, middle) = graph(
  (
    ((0, 0), $P_1$),
    ((1, 0), $P$),
    ((2, 0), $P_2$),
    ((0, 1), $P_1$),
    ((1, 1), $P$),
    ((2, 1), $P_2$),
    ((0, 2), $X_1$),
    ((1, 2), last),
    ((2, 2), $X_2$),
  ),
  (
    ((0, 0), (1, 0)),
    ((1, 0), (2, 0)),
    ((0, 1), (1, 1)),
    ((1, 1), (2, 1)),
    ((0, 2), (1, 2)),
    ((1, 2), (2, 2)),
    ((0, 0), (0, 1), $alpha_1$, right),
    ((1, 0), (1, 1), middle, right),
    ((2, 0), (2, 1), $alpha_2$, right),
    ((0, 1), (0, 2)),
    ((1, 1), (1, 2)),
    ((2, 1), (2, 2)),
  ),
  spacing: (12mm, 11mm),
)

#let boundary-horseshoe-pair = grid(
  columns: (1fr, 1fr),
  gutter: 8mm,
  horseshoe($X$, $gamma$), horseshoe($Y$, $delta$),
)

#let relative-triple-morphism = graph(
  (
    ((0, 0), $M'$),
    ((1, 0), $N'$),
    ((0, 1), $M'_1$),
    ((1, 1), $N'_1$),
  ),
  (
    ((0, 0), (1, 0), $f$),
    ((0, 1), (1, 1), $f_1$),
    ((0, 0), (0, 1), $1 times.o mu$, right),
    ((1, 0), (1, 1), $1 times.o nu$, right),
  ),
)

#let whitehead-field-extension-norm = graph(
  (
    ((0, 0), $K_1(A)$),
    ((1, 0), $C^+$),
    ((0, 1), $K_1(A')$),
    ((1, 1), $(C')^+$),
  ),
  (
    ((0, 0), (1, 0), $op("nr")_(A slash C)$),
    ((0, 1), (1, 1), $op("nr")_(A' slash C')$),
    ((0, 0), (0, 1), $alpha$, right),
    ((1, 0), (1, 1), $beta$, right),
  ),
)
