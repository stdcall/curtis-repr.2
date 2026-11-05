#import "../main-defs.typ": GL, fit-diagram
#import "@preview/fletcher:0.5.8": diagram, edge, node

#let graph(vertices, arrows, spacing: (14mm, 12mm)) = diagram(
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
#let square(a, b, c, d, top: [], west: [], east: [], bottom: []) = graph(
  (((0, 0), a), ((1, 0), b), ((0, 1), c), ((1, 1), d)),
  (
    ((0, 0), (1, 0), top, left),
    ((0, 0), (0, 1), west, right),
    ((1, 0), (1, 1), east, right),
    ((0, 1), (1, 1), bottom, left),
  ),
)

#let fiber-product-square = square(
  $A$,
  $A_1$,
  $A_2$,
  $overline(A)$,
  top: $f_1$,
  west: $f_2$,
  east: $g_1$,
  bottom: $g_2$,
)
#let ideal-quotient-square = view(square(
  $A slash (I inter J)$,
  $A slash I$,
  $A slash J$,
  $A slash (I+J)$,
))
#let dihedral-integral-square = square(
  $ZZ G$,
  $ZZ[y]$,
  $R circle.small [y]$,
  $overline(ZZ)[y]$,
)
#let dihedral-rational-square = view(square(
  $QQ G$,
  $QQ[y]$,
  $K circle.small [y]$,
  $0$,
))
#let wall-square = view(square($Lambda$, $hat(Lambda)$, $A$, $hat(A)$))
#let projective-base-change-square = square(
  $P$,
  $A_1 times.o_A P = P_1$,
  $P_2 = A_2 times.o_A P$,
  $overline(A) times.o_A P$,
)

#let patching-isomorphism-comparison = fit-diagram(graph(
  (
    ((0, 0), $overline(P)_1 = overline(A) times.o_(A_1) P_1$),
    ((1, 0), $overline(A) times.o_(A_1) A_1 times.o_A M$),
    ((2, 0), $overline(A) times.o_(A_1) A_1 times.o_A N$),
    ((3, 0), $overline(A) times.o_(A_1) Q_1 = overline(Q)_1$),
    ((0, 1), $overline(P)_2 = overline(A) times.o_(A_2) P_2$),
    ((1, 1), $overline(A) times.o_(A_2) A_2 times.o_A M$),
    ((2, 1), $overline(A) times.o_(A_2) A_2 times.o_A N$),
    ((3, 1), $overline(A) times.o_(A_2) Q_2 = overline(Q)_2$),
  ),
  (
    ((0, 0), (1, 0), $1 times.o sigma_1^(-1)$),
    ((1, 0), (2, 0), $1 times.o 1 times.o rho$),
    ((2, 0), (3, 0), $1 times.o tau_1$),
    ((0, 1), (1, 1), $1 times.o sigma_2^(-1)$),
    ((1, 1), (2, 1), $1 times.o 1 times.o rho$),
    ((2, 1), (3, 1), $1 times.o tau_2$),
    ((0, 0), (0, 1), $phi$, right),
    ((1, 0), (1, 1)),
    ((2, 0), (2, 1)),
    ((3, 0), (3, 1), $phi'$, right),
  ),
))
#let patching-free-trivialization = view(graph(
  (
    ((0, 0), $overline(P)_1$),
    ((1, 0), $tilde.equiv$),
    ((2, 0), $overline(A)_1^n$),
    ((0, 1), $overline(P)_2$),
    ((1, 1), $tilde.equiv$),
    ((2, 1), $overline(A)_2^n$),
  ),
  (
    ((0, 0), (0, 1), $kappa$, right),
    ((2, 0), (2, 1), $phi$, right),
  ),
  spacing: (3mm, 10mm),
))
#let general-linear-fiber-square = square(
  $GL_n lr((A))$,
  $GL_n lr((A_1))$,
  $GL_n lr((A_2))$,
  $GL_n lr((overline(A)))$,
)
#let cyclic-prime-fiber-square = view(square(
  $ZZ G$,
  $R$,
  $ZZ$,
  $overline(ZZ)$,
))
#let karoubi-square = view(square($A$, $B$, $S^(-1) A$, $S^(-1) B$))
#let localization-fiber-square = view(square(
  $A$,
  $S^(-1) A$,
  $T^(-1) A$,
  $(S T)^(-1) A$,
))
#let matrix-fiber-square = view(square(
  $M_(2n) lr((A))$,
  $M_(2n) lr((A_1))$,
  $M_(2n) lr((A_2))$,
  $M_(2n) lr((overline(A)))$,
))
#let cusp-fiber-square = view(square(
  $A$,
  $k[x]$,
  $k$,
  $k[x] slash (x^2)$,
))
