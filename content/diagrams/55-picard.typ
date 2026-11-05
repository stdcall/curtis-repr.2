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
    e.at(4, default: "-|>"),
    label-side: e.at(3, default: left),
  )),
)
#let view(body) = block(width: 100%, align(center, body))

#let invertible-bimodule-associativity-squares = fit-diagram(graph(
  (
    ((0, 0), $M times.o_Delta N times.o_Lambda M$),
    ((1, 0), $Lambda times.o_Lambda M$),
    ((0, 1), $M times.o_Delta Delta$),
    ((1, 1), $M$),
    ((3, 0), $N times.o_Lambda M times.o_Delta N$),
    ((4, 0), $Delta times.o_Delta N$),
    ((3, 1), $N times.o_Lambda Lambda$),
    ((4, 1), $N$),
  ),
  (
    ((0, 0), (1, 0)),
    ((0, 0), (0, 1)),
    ((1, 0), (1, 1)),
    ((0, 1), (1, 1)),
    ((3, 0), (4, 0)),
    ((3, 0), (3, 1)),
    ((4, 0), (4, 1)),
    ((3, 1), (4, 1)),
  ),
))

#let normalizer-central-picard-triangle = view(graph(
  (
    ((0, 0), $N(Lambda) slash Lambda^times (K C)^times$),
    ((1, 0), $op("Outcent") Lambda$),
    ((1, 1), $op("Picent") Lambda$),
  ),
  (
    ((0, 0), (1, 0), $rho$),
    ((0, 0), (1, 1), $omega'$, right),
    ((1, 0), (1, 1), $omega$, right),
  ),
))

#let maximal-order-picard-class-snake = fit-diagram(graph(
  (
    ((0, 0), $1$),
    ((1, 0), $op("Cl") R$),
    ((2, 0), $op("LFP")(Lambda)$),
    ((3, 0), $product_P ZZ slash m_P ZZ$),
    ((4, 0), $1$),
    ((0, 1), $1$),
    ((1, 1), $op("Cl")_A R$),
    ((2, 1), $op("Cl") Lambda$),
    ((3, 1), $1$),
  ),
  (
    ((0, 0), (1, 0)),
    ((1, 0), (2, 0)),
    ((2, 0), (3, 0)),
    ((3, 0), (4, 0)),
    ((0, 1), (1, 1)),
    ((1, 1), (2, 1), $sigma$, right),
    ((2, 1), (3, 1)),
    ((1, 0), (1, 1), $t_n$, right),
    ((2, 0), (2, 1), $theta$, right),
    ((3, 0), (3, 1)),
  ),
))

#let matrix-order-picard-class-comparison = fit-diagram(graph(
  (
    ((0, 0), $1$),
    ((1, 0), $op("Outcent") Lambda$),
    ((2, 0), $op("LFP")(Lambda)$),
    ((3, 0), $op("Cl") Lambda$),
    ((0, 1), $1$),
    ((1, 1), $op("Outcent") Gamma$),
    ((2, 1), $op("LFP")(Gamma)$),
    ((3, 1), $op("Cl") Gamma$),
  ),
  (
    ((0, 0), (1, 0)),
    ((1, 0), (2, 0), $omega$),
    ((2, 0), (3, 0), $theta$),
    ((0, 1), (1, 1)),
    ((1, 1), (2, 1), $omega'$),
    ((2, 1), (3, 1), $theta'$),
    ((1, 0), (1, 1), $alpha$, right),
    ((2, 0), (2, 1), $beta$, right),
    ((3, 0), (3, 1), $gamma$, right),
  ),
))

#let matrix-order-picard-class-snake = view(graph(
  (
    ((1, 0), $1$),
    ((2, 0), $op("LFP")(Lambda)$),
    ((3, 0), $op("LFP")(Gamma)$),
    ((4, 0), $1$),
    ((0, 1), $0$),
    ((1, 1), $ker gamma$),
    ((2, 1), $op("Cl") Lambda$),
    ((3, 1), $op("Cl") Gamma$),
  ),
  (
    ((1, 0), (2, 0)),
    ((2, 0), (3, 0), $beta$),
    ((3, 0), (4, 0)),
    ((0, 1), (1, 1)),
    ((1, 1), (2, 1)),
    ((2, 1), (3, 1)),
    ((2, 0), (2, 1), $theta$, right),
    ((3, 0), (3, 1), $theta'$, right),
  ),
))

#let finite-ring-picard-radical-triangle = view(graph(
  (
    ((0, 0), $op("Pic") Lambda/J^n$),
    ((1, 0), $op("Pic") Lambda/J^(n-1)$),
    ((1, 1), $op("Pic") Lambda/J^2$),
  ),
  (
    ((0, 0), (1, 0), $mu$),
    ((0, 0), (1, 1)),
    ((1, 0), (1, 1)),
  ),
))

#let approximate-centralizer-reduction-comparison = fit-diagram(graph(
  (
    ((0, 0), $0$),
    ((1, 0), $(pi X)/(pi^n X)$),
    ((2, 0), $(T^n lr((X))+P X)/(P^n X)$),
    ((3, 0), $(T^n lr((X))+P X)/(P X)$),
    ((4, 0), $0$),
    ((0, 1), $0$),
    ((1, 1), $(pi Lambda)/(pi^n Lambda)$),
    ((2, 1), $(T^n lr((Lambda))+P Lambda)/(P^n Lambda)$),
    ((3, 1), $(T^n lr((Lambda))+P Lambda)/(P Lambda)$),
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
    ((1, 0), (1, 1), $theta_1$, left),
    ((2, 0), (2, 1), $theta_2$, left),
    ((3, 0), (3, 1), $theta_3$, left),
  ),
))

#let group-ring-abelianization-radical-square = view(graph(
  (
    ((0, 0), $Lambda$),
    ((1, 0), $tilde(Lambda)$),
    ((0, 1), $Lambda/J^2$),
    ((1, 1), $tilde(Lambda)/tilde(J)^2$),
    ((0.5, 1), $tilde.equiv$),
  ),
  (
    ((0, 0), (1, 0)),
    ((0, 0), (0, 1)),
    ((1, 0), (1, 1)),
  ),
))

#let dihedral-group-ring-picard-fiber-product = view(graph(
  (
    ((0, 0), $Lambda = ZZ G$),
    ((1, 0), $R compose H = Gamma$),
    ((0, 1), $ZZ H$),
    ((1, 1), $overline(ZZ) H$),
  ),
  (
    ((0, 0), (1, 0)),
    ((0, 0), (0, 1)),
    ((1, 0), (1, 1), $g_2$, left),
    ((0, 1), (1, 1), $g_1$, right),
  ),
))

#let dihedral-picard-class-comparison = view(graph(
  (
    ((0, 0), $op("Cl") C$),
    ((1, 0), $op("Cl") S$),
    ((0, 1), $op("LFP")(Lambda)$),
    ((1, 1), $op("Cl") Lambda tilde.equiv op("Cl") S$),
  ),
  (
    ((0, 0), (1, 0), $phi$),
    ((0, 0), (0, 1), $tau$, right),
    ((1, 0), (1, 1), $t$, right),
    ((0, 1), (1, 1), $theta$),
  ),
))

#let dihedral-center-picard-fiber-product = view(graph(
  (
    ((0, 0), $C$),
    ((1, 0), $S$),
    ((0, 1), $ZZ H$),
    ((1, 1), $overline(ZZ) H$),
  ),
  (
    ((0, 0), (1, 0)),
    ((0, 0), (0, 1)),
    ((1, 0), (1, 1), $g_2$, left),
    ((0, 1), (1, 1), $g_1$, right),
  ),
))

#let dihedral-completed-picard-fiber-product = view(graph(
  (
    ((0, 0), $Lambda_p$),
    ((1, 0), $Gamma_p$),
    ((0, 1), $ZZ_p H$),
    ((1, 1), $overline(ZZ) H$),
  ),
  (
    ((0, 0), (1, 0)),
    ((0, 0), (0, 1)),
    ((1, 0), (1, 1), $g_2$, left),
    ((0, 1), (1, 1), $g_1$, right),
  ),
))

#let central-picard-primary-kernel-reduction = view(graph(
  (
    ((0, 0), $op("Picent") Lambda$),
    ((1, 0), $op("Pic")_R Lambda_n$),
    ((0, 1), $op("Pic")_R Lambda/J^2$),
    ((1, 1), $op("Pic")_R Lambda_n/J_n^2$),
  ),
  (
    ((0, 0), (1, 0)),
    ((0, 0), (0, 1), $f$, right),
    ((1, 0), (1, 1), $g$, left),
    ((0, 1), (1, 1)),
  ),
))
