#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "@preview/cetz:0.5.2": canvas, draw

#let projective-factor-pullback-diagram() = diagram(
  spacing: (18mm, 12mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $U_1$),
  node((0, 1), $P_1$),
  node((1, 1), $V$),
  node((0, 2), $P_2$),
  node((1, 2), $V$),
  edge((0, 0), (0, 1), $alpha$, "-|>", label-side: right),
  edge((0, 0), (1, 1), $sigma$, "-|>"),
  edge((0, 1), (1, 1), $tau$, "-|>"),
  edge((0, 1), (0, 2), $beta$, "-|>", label-side: right),
  edge((0, 2), (1, 2), $mu$, "-|>"),
  edge((1, 1), (1, 2), $1$, "-|>", label-side: right),
)

#let carlson-resolution-comparison() = {
  let top = ($0$, $L$, $(K G)^((2))$, $(K G)^((2))$, $L$, $0$)
  let bottom = (
    $0$,
    $Omega^2 K times.o L$,
    $W_1 times.o L$,
    $W_0 times.o L$,
    $L$,
    $0$,
  )
  let labels = ($mu_2$, $mu_1$, $mu_0$, $1$)
  diagram(
    spacing: (12mm, 14mm),
    node-inset: 2pt,
    node-defocus: 0,
    ..top.enumerate().map(((i, value)) => node((i, 0), value)),
    ..bottom.enumerate().map(((i, value)) => node((i, 1), value)),
    ..range(5).map(i => edge((i, 0), (i + 1, 0), "-|>")),
    ..range(5).map(i => edge((i, 1), (i + 1, 1), "-|>")),
    ..labels
      .enumerate()
      .map(((i, value)) => edge(
        (i + 1, 0),
        (i + 1, 1),
        value,
        "-|>",
        label-side: left,
      )),
  )
}

#let carlson-extension-pushout() = {
  let top = (
    $0$,
    $Omega^2 K times.o L$,
    $W_1 times.o L$,
    $W_0 times.o L$,
    $L$,
    $0$,
  )
  let bottom = ($0$, $L$, $ast$, $ast$, $L$, $0$)
  diagram(
    spacing: (12mm, 14mm),
    node-inset: 2pt,
    node-defocus: 0,
    ..top.enumerate().map(((i, value)) => node((i, 0), value)),
    ..bottom.enumerate().map(((i, value)) => node((i, 1), value)),
    ..range(5).map(i => edge((i, 0), (i + 1, 0), "-|>")),
    ..range(5).map(i => edge((i, 1), (i + 1, 1), "-|>")),
    edge((1, 0), (1, 1), $zeta times.o 1$, "-|>", label-side: right),
    edge((2, 0), (2, 1), "-|>"),
    edge((3, 0), (3, 1), "-|>"),
    edge((4, 0), (4, 1), $1$, "-|>", label-side: right),
  )
}

#let carlson-kernel-lattice() = canvas(length: 1mm, {
  let vertices = (
    (0, 0),
    (-8, -10.5),
    (8, -10.5),
    (-24, -10.5),
    (-16, -21),
    (0, -21),
    (16, -21),
    (-8, -31.5),
    (8, -31.5),
  )
  let links = (
    (0, 1),
    (0, 2),
    (1, 4),
    (1, 5),
    (2, 5),
    (2, 6),
    (3, 4),
    (4, 7),
    (5, 7),
    (5, 8),
    (6, 8),
  )
  for (a, b) in links {
    draw.line(vertices.at(a), vertices.at(b), stroke: 0.6pt)
  }
  draw.content((2, 0), $a_1=(-(y-1),(x-1))$, anchor: "west")
  draw.content((-26, -10.5), $(N_x,-alpha N_y)=b_1$, anchor: "east")
  draw.content((10, -10.5), $(y-1) a_1$, anchor: "west")
  draw.content((-18, -21), $(y-1) b_1=-(x-1)^2 a_1$, anchor: "east")
  draw.content((18, -21), $(y-1)^2 a_1=(0,(x-1)(y-1)^2)$, anchor: "west")
  draw.content(
    (-10, -31.5),
    $(x-1)^2(y-1) a_1=(-(x-1)^2(y-1)^2,0)$,
    anchor: "east",
  )
  draw.content(
    (6, -35),
    $(x-1)(y-1)^2 a_1=(0,(x-1)^2(y-1)^2)$,
    anchor: "north-west",
  )
})

#let carlson-omega-kernel-lattice() = canvas(length: 1mm, {
  let vertices = (
    (-8, 0),
    (8, 0),
    (-16, -10.5),
    (0, -10.5),
    (16, -10.5),
    (-8, -21),
    (8, -21),
    (24, -21),
    (0, -31.5),
  )
  let links = (
    (0, 2),
    (0, 3),
    (1, 3),
    (1, 4),
    (2, 5),
    (3, 5),
    (3, 6),
    (4, 6),
    (4, 7),
    (5, 8),
    (6, 8),
  )
  for (a, b) in links {
    draw.line(vertices.at(a), vertices.at(b), stroke: 0.6pt)
  }
  draw.content((-10, 0), $c_1=(x-1,alpha N_y)$, anchor: "east")
  draw.content((10, 0), $d_1=(y-1,N_x)$, anchor: "west")
  draw.content(
    (-18, -10.5),
    $(x-1) c_1=((x-1)^2,alpha(x-1) N_y)$,
    anchor: "east",
  )
  draw.content((18, -10.5), $(y-1) d_1$, anchor: "west")
  draw.content((-10, -21), $(x-1)^2 d_1=((x-1)^2(y-1),0)$, anchor: "east")
  draw.content(vertices.at(6), $(x-1)(y-1) d_1$, anchor: "north-west")
  draw.content((26, -23), $(y-1)^2 d_1=(0,N_x N_y)$, anchor: "north-west")
  draw.content(
    (0, -34),
    $(x-1)^2(y-1) d_1=(x-1)(y-1)^2 c_1=(N_x N_y,0)$,
    anchor: "north",
  )
})

#let representation-species-mark-square() = diagram(
  spacing: (22mm, 14mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $CC times.o_ZZ Omega(G)$),
  node((1, 0), $CC^((m))$),
  node((0, 1), $P P(R G)$),
  node((1, 1), $CC^((n))$),
  edge((0, 0), (1, 0), $phi$, "-|>"),
  edge((0, 1), (1, 1), $psi$, "-|>"),
  edge((0, 0), (0, 1), "-|>"),
  edge((1, 0), (1, 1), $rho$, "-|>", label-side: left),
)

#let representation-species-fusion-triangle() = diagram(
  spacing: (18mm, 15mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $A(G)$),
  node((1, 0), $A(H)$),
  node((1, 1), $CC$),
  edge((0, 0), (1, 0), $op("res")$, "-|>"),
  edge((0, 0), (1, 1), $f$, "-|>", label-side: right),
  edge((1, 0), (1, 1), $g$, "-|>", label-side: right),
)

#let relative-splitting-square = {
  let vertices = (
    ((0, 0), $(M_H)^G$),
    ((1, 0), $(N_H)^G$),
    ((0, 1), $M$),
    ((1, 1), $N$),
  )
  let parallel = (
    ((0, 0), (0, 1), $mu$),
    ((0, 1), (0, 0), $i$),
    ((1, 0), (1, 1), $mu'$),
    ((1, 1), (1, 0), $i'$),
  )
  diagram(
    spacing: (18mm, 13mm),
    node-inset: 2pt,
    node-defocus: 0,
    ..vertices.map(v => node(v.at(0), v.at(1))),
    edge((0, 0), (1, 0), $1 times.o f$, "-|>", label-side: left),
    edge((0, 1), (1, 1), $f$, "-|>", label-side: right),
    ..parallel.map(e => edge(
      e.at(0),
      e.at(1),
      e.at(2),
      "-|>",
      shift: 2pt,
      label-side: right,
    )),
  )
}
