#import "../main-defs.typ": *
#import "@preview/fletcher:0.5.8": diagram, edge, node

#let graph(vertices, arrows, spacing: (9mm, 12mm)) = diagram(
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
#let square(a, b, c, d, north: [], west: []) = graph(
  (((0, 0), a), ((1, 0), b), ((0, 1), c), ((1, 1), d)),
  (
    ((0, 0), (1, 0), north),
    ((0, 0), (0, 1), west, right),
    ((1, 0), (1, 1)),
    ((0, 1), (1, 1)),
  ),
)
#let cyclic-prime-rim-square = view(square(
  $ZZ C_p$,
  $R$,
  $ZZ$,
  $ZZ slash p tilde.equiv R slash pi$,
  north: $f$,
  west: $g$,
))
#let cyclic-prime-class-kernel-fork = fit-diagram(graph(
  (
    ((0, 0), $1$),
    ((1, 0), $(ZZ C_p)^dot$),
    ((2, 0), $ZZ^dot times R^dot$),
    ((3, 0), $(R slash pi)^dot$),
    ((4, 0), $op("Cl") ZZ C_p$),
    ((5, 0), $op("Cl") ZZ plus.o op("Cl") R$),
    ((6, 0), $0$),
    ((4, 1), $D(ZZ C_p)$),
    ((5, 1), $D(ZZ) plus.o D(R)$),
    ((6, 1), $0$),
  ),
  (
    ((0, 0), (1, 0)),
    ((1, 0), (2, 0)),
    ((2, 0), (3, 0), $h$),
    ((3, 0), (4, 0)),
    ((4, 0), (5, 0)),
    ((5, 0), (6, 0)),
    ((3, 0), (4, 1)),
    ((4, 1), (5, 1)),
    ((5, 1), (6, 1)),
  ),
))
#let cyclotomic-base-prime-square = view(square(
  $R_m C_p$,
  $R_(m p)$,
  $R_m$,
  $R_m slash p tilde.equiv R_(m p) slash pi_p$,
))
#let cyclic-maximal-order-conductor-square = view(square(
  $Lambda$,
  $Lambda'$,
  $Lambda slash n Lambda'$,
  $Lambda' slash n Lambda'$,
))
#let cyclic-conductor-unit-triangle = view(graph(
  (
    ((0, 0), $(Lambda slash n Lambda)^dot$),
    ((0, 1), $(Lambda slash n Lambda')^dot$),
    ((1, 1), $(Lambda' slash n Lambda')^dot$),
  ),
  (
    ((0, 0), (0, 1), $psi$, right),
    ((0, 0), (1, 1), $alpha$, right),
    ((0, 1), (1, 1), $alpha'$),
  ),
  spacing: (12mm, 20mm),
))
#let localized-cyclic-prime-square = view(square(
  $tilde(ZZ) C_p$,
  $tilde(R)_p$,
  $tilde(ZZ)$,
  $tilde(ZZ) slash p tilde.equiv tilde(R)_p slash pi_p$,
))
#let localized-cyclic-squarefree-square = view(square(
  $tilde(ZZ) C_n$,
  $tilde(R)_p C_q$,
  $tilde(ZZ) C_q$,
  $(tilde(ZZ) slash p) C_q tilde.equiv (tilde(R)_p slash pi_p) C_q$,
))
#let metacyclic-prime-fiber-square = view(graph(
  (
    ((0, 0), $Lambda = ZZ G$),
    ((1, 0), $R compose H$),
    ((0, 1), $ZZ H$),
    ((1, 1), $overline(ZZ) H$),
  ),
  (
    ((0, 0), (1, 0), $f_1$),
    ((0, 0), (0, 1), $f_2$, right),
    ((1, 0), (1, 1), $g_1$, right),
    ((0, 1), (1, 1), $g_2$),
  ),
))
#let metacyclic-prime-class-kernel-fork = fit-diagram(graph(
  (
    ((0, 0), $1$),
    ((1, 0), $"image of" (R compose H)^dot$),
    ((2, 0), $(overline(ZZ) H)^dot$),
    ((3, 0), $op("Cl") Lambda$),
    ((4, 0), $op("Cl") S plus.o op("Cl") ZZ H$),
    ((5, 0), $0$),
    ((3, 1), $D(Lambda)$),
    ((4, 1), $D(ZZ H)$),
    ((5, 1), $0$),
  ),
  (
    ..range(5).map(i => ((i, 0), (i + 1, 0))),
    ((2, 0), (3, 1)),
    ((3, 1), (4, 1)),
    ((4, 1), (5, 1)),
  ),
))
#let metacyclic-unit-determinant-square = view(graph(
  (
    ((0, 0), $(R compose H)^dot$),
    ((1, 0), $(overline(ZZ) H)^dot$),
    ((0, 1), $S^dot$),
    ((1, 1), $overline(ZZ)^dot$),
  ),
  (
    ((0, 0), (1, 0)),
    ((0, 1), (1, 1)),
    ((0, 0), (0, 1), $det$, right),
    ((1, 0), (1, 1), $det$, right),
  ),
))
#let dihedral-two-group-fiber-square = view(square(
  $Lambda = ZZ G_n$,
  $Delta = ZZ G_(n - 1)$,
  $Gamma = R compose H$,
  $Delta slash 2 Delta$,
  north: $f_1$,
  west: $f_2$,
))
#let dihedral-cyclotomic-field-chart = fit-diagram(graph(
  (
    ((0, 0), $K$),
    ((1, 0), $R$),
    ((2, 0), $pi_0 = 1 - omega$),
    ((0, 1), $L$),
    ((1, 1), $S$),
    ((2, 1), $pi = (1 - omega)(1 - overline(omega)) = pi_0 overline(pi)_0$),
    ((0, 2), $QQ$),
    ((1, 2), $ZZ$),
    ((2, 2), $2$),
  ),
  (
    ..range(3).map(j => ((0, j), (1, j), [], left, "-")),
    ((0, 0), (0, 1), $2$, right, "-"),
    ((0, 1), (0, 2), $2^(n - 1)$, right, "-"),
    ((1, 0), (1, 1), [], left, "-"),
    ((1, 1), (1, 2), [], left, "-"),
    ((2, 0), (2, 1), [], left, "-"),
    ((2, 1), (2, 2), [], left, "-"),
  ),
))
#let completed-dihedral-fiber-square = view(square(
  $Lambda_2$,
  $Delta_2$,
  $Gamma_2$,
  $Delta_2 slash 2 Delta_2$,
  north: $f_1$,
  west: $f_2$,
))
#let quaternion-eight-fiber-square = view(square(
  $Lambda = ZZ G$,
  $Delta = ZZ H$,
  $Gamma = R plus.o R y$,
  $overline(Delta) = overline(ZZ) H$,
  north: $f_1$,
  west: $f_2$,
))

#let cyclic-prime-square-augmentation-fiber-square = view(square(
  $ZZ G$,
  $Gamma = ZZ[x] slash (Phi_p lr((x)) Phi_(p^2) lr((x)))$,
  $ZZ$,
  $ZZ slash p^2 ZZ$,
))
#let cyclic-prime-square-cyclotomic-fiber-square = view(square(
  $Gamma$,
  $R_2 = ZZ[x] slash (Phi_(p^2) lr((x)))$,
  $R = ZZ[x] slash (Phi_p lr((x)))$,
  $overline(R)$,
))
#let cyclic-p-power-fiber-square = view(square(
  $ZZ G_n$,
  $ZZ G_(n-1)$,
  $R_n$,
  $overline(R)_n tilde.equiv overline(ZZ) G_(n-1)$,
))

#let crossed-product-k1-norm-square = view(graph(
  (
    ((0, 0), $K_1 lr((B))$),
    ((1, 0), $K_1 lr((A))$),
    ((0, 1), $L_0^dot$),
    ((1, 1), $K^dot$),
  ),
  (
    ((0, 0), (1, 0), $theta$),
    ((0, 0), (0, 1), $op("nr")$, right),
    ((1, 0), (1, 1), $op("nr")$, right),
    ((0, 1), (1, 1), $N_(L_0 slash K)$),
  ),
))

#let local-ramification-field-ring-chart = view(graph(
  (
    ((0, 0), $L$),
    ((1, 0), $S$),
    ((2, 0), $frak(P) = pi S$),
    ((3, 0), $overline(S) = S slash frak(P)$),
    ((0, 1), $L_1$),
    ((1, 1), $S_1$),
    ((2, 1), $frak(P)_1 = pi_1 S_1$),
    ((3, 1), $overline(S)_1 = S_1 slash frak(P)_1$),
    ((0, 2), $L_0$),
    ((1, 2), $S_0$),
    ((2, 2), $frak(P)_0 = pi_0 S_0$),
    ((3, 2), $overline(S)_0 = S_0 slash frak(P)_0$),
    ((0, 3), $K$),
    ((1, 3), $R$),
    ((2, 3), $P$),
    ((3, 3), $overline(R) = R slash P$),
  ),
  (
    ((0, 0), (0, 1), [], left, "-"),
    ((0, 1), (0, 2), [], left, "-"),
    ((0, 2), (0, 3), [], left, "-"),
    ((1, 0), (1, 1), [], left, "-"),
    ((1, 1), (1, 2), [], left, "-"),
    ((1, 2), (1, 3), [], left, "-"),
    ((2, 0), (2, 1), [], left, "-"),
    ((2, 1), (2, 2), [], left, "-"),
    ((2, 2), (2, 3), [], left, "-"),
    ((3, 0), (3, 1), [], left, "-"),
    ((3, 1), (3, 2), [], left, "-"),
    ((3, 2), (3, 3), [], left, "-"),
  ),
))

#let tame-crossed-product-reduction-norm-square = view(graph(
  (
    ((0, 0), $Lambda_0^dot$),
    ((1, 0), $S_0^dot$),
    ((0, 1), $overline(Lambda)_0^dot$),
    ((1, 1), $overline(S)_0^dot tilde.equiv overline(S)^dot$),
  ),
  (
    ((0, 0), (1, 0), $op("nr")_(Lambda_0 slash S_0)$),
    ((0, 0), (0, 1)),
    ((1, 0), (1, 1)),
    ((0, 1), (1, 1), $overline(op("nr"))$),
  ),
))

#let wild-crossed-product-reduction-norm-square = view(graph(
  (
    ((0, 0), $Lambda_1^dot$),
    ((1, 0), $S_1^dot$),
    (
      (0, 1),
      $overline(Lambda)_1^dot =
      (Lambda_1 slash frak(P) Lambda_1)^dot$,
    ),
    (
      (1, 1),
      $overline(S)^dot tilde.equiv
      (S_1 slash frak(P)_1)^dot$,
    ),
  ),
  (
    ((0, 0), (1, 0), $op("nr")_(Lambda_1 slash S_1)$),
    ((0, 0), (0, 1)),
    ((1, 0), (1, 1)),
    ((0, 1), (1, 1), $overline(overline(op("nr")))$),
  ),
))

#let local-artin-norm-exact-rows = view(graph(
  (
    ((0, 0), $1$),
    ((1, 0), $N_(L slash F) L^dot$),
    ((2, 0), $F^dot$),
    ((3, 0), $H^"ab"$),
    ((4, 0), $1$),
    ((0, 1), $1$),
    ((1, 1), $N_(L slash K) L^dot$),
    ((2, 1), $K^dot$),
    ((3, 1), $G^"ab"$),
    ((4, 1), $1$),
  ),
  (
    ((0, 0), (1, 0)),
    ((1, 0), (2, 0)),
    ((2, 0), (3, 0), $alpha'$),
    ((3, 0), (4, 0)),
    ((0, 1), (1, 1)),
    ((1, 1), (2, 1)),
    ((2, 1), (3, 1), $alpha$),
    ((3, 1), (4, 1)),
    ((1, 0), (1, 1)),
    ((2, 0), (2, 1), $N_(F slash K)$, right),
    ((3, 0), (3, 1), $i_*$, right),
  ),
))

#let klein-four-fiber-square = view(square(
  $ZZ G$,
  $ZZ H$,
  $ZZ H$,
  $overline(ZZ) H$,
))
#let cyclic-four-fiber-square = view(square(
  $ZZ G$,
  $ZZ[i]$,
  $ZZ H$,
  $overline(ZZ) H$,
))
