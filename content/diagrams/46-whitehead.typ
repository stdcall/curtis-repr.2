#import "@preview/fletcher:0.5.8": diagram, edge, node

#let graph(vertices, arrows) = diagram(
  spacing: (10mm, 12mm),
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
#let square(a, b, c, d, top: [], bottom: []) = graph(
  (((0, 0), a), ((1, 0), b), ((0, 1), c), ((1, 1), d)),
  (
    ((0, 0), (1, 0), top),
    ((0, 0), (0, 1)),
    ((1, 0), (1, 1)),
    ((0, 1), (1, 1), bottom),
  ),
)
#let whitehead-image-triangle = graph(
  (
    ((0, 0), $K_1 lr((R)) times G^(a b)$),
    ((1, 0), $K_1 lr((R G))$),
    ((1, 1), $K_1^F lr((R G))$),
  ),
  (((0, 0), (1, 0), $phi$), ((0, 0), (1, 1), $phi'$), ((1, 0), (1, 1))),
)
#let norm-field-extension-square = view(square(
  $K_1 lr((F G))$,
  $C^+$,
  $K_1 lr((E G))$,
  $(E times.o_F C)^+$,
  top: $op("nr")$,
  bottom: $op("nr")$,
))
#let whitehead-extension-augmentation = view(graph(
  (
    ((0, 0), $K_1^F lr((R)) times G^(a b)$),
    ((1, 0), $K_1^F lr((R G))$),
    ((2, 0), $K_1^F lr((R))$),
    ((0, 1), $K_1^E lr((S)) times G^(a b)$),
    ((1, 1), $K_1^E lr((S G))$),
    ((2, 1), $K_1^E lr((S))$),
  ),
  (
    ((0, 0), (1, 0), $phi$),
    ((1, 0), (2, 0), $epsilon_*$),
    ((0, 1), (1, 1), $phi'$),
    ((1, 1), (2, 1), $epsilon'_*$),
    ((0, 0), (0, 1)),
    ((1, 0), (1, 1), $sigma$, right),
    ((2, 0), (2, 1), $sigma'$, right),
  ),
))
#let sk1-splitting-field-square = view(square(
  $K_1 lr((overline(Lambda)))$,
  $K_1 lr((F G))$,
  $K_1 lr((k' times.o_k overline(Lambda)))$,
  $K_1 lr((F' G))$,
  top: $sigma mu$,
  bottom: $sigma' mu'$,
))
#let p-group-transfer-comparison = view(graph(
  (
    ((0, 0), $K_1^F lr((R G))$),
    ((1, 0), $K_1^F lr((R (G slash H')))$),
    ((2, 0), $K_1^F lr((R G^(a b)))$),
    ((0, 1), $K_1^F lr((R H))$),
    ((1, 1), $K_1^F lr((R H^(a b)))$),
  ),
  (
    ((0, 0), (1, 0), $theta$),
    ((1, 0), (2, 0), $theta'$),
    ((0, 0), (0, 1), $bold(N)$, right),
    ((1, 0), (1, 1)),
    ((0, 1), (1, 1), $rho$),
  ),
))
#let quotient-completion-square = view(square(
  $K_1^F lr((R G))$,
  $K_1^F lr((R overline(G)))$,
  $K_1^hat(F) lr((hat(R) G))$,
  $K_1^hat(F) lr((hat(R) overline(G)))$,
  top: $rho_0$,
  bottom: $rho'$,
))
