#import "@preview/fletcher:0.5.8": diagram, edge, node

#let projective-map-factorization = block(width: 100%, align(center, diagram(
  spacing: (10mm, 8mm),
  node((1, 0), $L$),
  node((0, 1), $P$),
  node((1, 1), $M$),
  node((2, 1), $0$),
  edge((1, 0), (0, 1), $mu$, "-|>", label-side: right),
  edge((1, 0), (1, 1), $lambda$, "-|>", label-side: left),
  edge((0, 1), (1, 1), $pi$, "-|>", label-side: right),
  edge((1, 1), (2, 1), "-|>"),
)))

#let green-core-projections = block(width: 100%, align(center, diagram(
  spacing: (11mm, 6mm),
  node((0, 0), $M_H$),
  node((1, 0), $f M$),
  node((2, 0), [and]),
  node((3, 0), $M_H$),
  node((4, 0), $M'$),
  edge((0, 0), (1, 0), $p$, "-|>", shift: 2pt, label-side: left),
  edge((1, 0), (0, 0), $i$, "-|>", shift: 2pt, label-side: left),
  edge((3, 0), (4, 0), $p'$, "-|>", shift: 2pt, label-side: left),
  edge((4, 0), (3, 0), $i'$, "-|>", shift: 2pt, label-side: left),
)))

#let green-trace-quotient-square = diagram(
  spacing: (10mm, 8mm),
  node((0, 0), $(M_H,N_H)_(H slash D) / (M_H,N_H)_(H,cal(X))$),
  node((1, 0), $(M,N)_(G slash D) / (M,N)_(G,cal(X))$),
  node((0, 1), $(M_H,N_H)_(H slash D) / Q$),
  node(
    (1, 1),
    $((M_H,N_H)_(H slash D) + (M_H,N_H)_(H,cal(Y)))
    / (M_H,N_H)_(H,cal(Y))$,
  ),
  edge((0, 0), (1, 0), $t$, "-|>"),
  edge((0, 0), (0, 1), $q$, "-|>", label-side: right),
  edge((1, 0), (1, 1), $r$, "-|>", label-side: right),
  edge((1, 1), (0, 1), $s$, "-|>", label-side: right),
)

#let uniserial-projective-cover-triangle = block(width: 100%, align(
  center,
  diagram(
    spacing: (10mm, 8mm),
    node((1, 0), $P$),
    node((0, 1), $M$),
    node((1, 1), $M slash U$),
    node((2, 1), $0$),
    edge((1, 0), (0, 1), $g$, "-|>", label-side: right),
    edge((1, 0), (1, 1), $f$, "-|>", label-side: left),
    edge((0, 1), (1, 1), $h$, "-|>", label-side: right),
    edge((1, 1), (2, 1), "-|>"),
  ),
))

#let projective-reduction-exact-rows = block(width: 100%, align(center, diagram(
  spacing: (7mm, 8mm),
  node((0, 0), $0$),
  node((1, 0), $N$),
  node((2, 0), $P$),
  node((3, 0), $M$),
  node((4, 0), $0$),
  node((0, 1), $0$),
  node((1, 1), $U$),
  node((2, 1), $Q$),
  node((3, 1), $V$),
  node((4, 1), $0$),
  edge((0, 0), (1, 0), "-|>"),
  edge((1, 0), (2, 0), "-|>"),
  edge((2, 0), (3, 0), "-|>"),
  edge((3, 0), (4, 0), "-|>"),
  edge((0, 1), (1, 1), "-|>"),
  edge((1, 1), (2, 1), "-|>"),
  edge((2, 1), (3, 1), "-|>"),
  edge((3, 1), (4, 1), "-|>"),
  edge((0, 0), (0, 1), "-|>"),
  edge((1, 0), (1, 1), "-|>"),
  edge((2, 0), (2, 1), "-|>"),
  edge((3, 0), (3, 1), "-|>"),
  edge((4, 0), (4, 1), "-|>"),
)))
