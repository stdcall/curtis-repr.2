#import "../main-defs.typ": *
#import "@preview/cetz:0.5.2": canvas, draw
#import "@preview/fletcher:0.5.8": diagram, edge, node

#let representation-square() = align(center, diagram(
  node((0, 0), $V_alpha$),
  node((1, 0), $V_beta$),
  node((0, 1), $W_alpha$),
  node((1, 1), $W_beta$),
  edge((0, 0), (1, 0), $f_e$, "-|>"),
  edge((0, 0), (0, 1), $phi_alpha$, "-|>", label-side: right),
  edge((1, 0), (1, 1), $phi_beta$, "-|>", label-side: left),
  edge((0, 1), (1, 1), $g_e$, "-|>", label-side: right),
))

#let base-change-square() = align(center, diagram(
  node((0, 0), $V_alpha$),
  node((1, 0), $V_beta$),
  node((0, 1), $V_alpha$),
  node((1, 1), $V_beta$),
  edge((0, 0), (1, 0), $f_e$, "-|>"),
  edge((0, 0), (0, 1), $phi_alpha$, "-|>", label-side: right),
  edge((1, 0), (1, 1), $phi_beta$, "-|>", label-side: left),
  edge((0, 1), (1, 1), $f'_e$, "-|>", label-side: right),
  node((2, 0.5), [for each edge $e=(alpha,beta)$.]),
))

// Incidence data and uniform graph coordinates, not raster tracing.
#let graph-view(
  points,
  links,
  filled: false,
  labels: (:),
  gaps: (),
  directed: false,
  curves: (),
  stub: none,
) = canvas(length: 1mm, baseline: (0, 0), {
  import draw: *
  set-style(stroke: 0.5pt, content: (padding: 1.2))
  let pitch = 7
  let at(i) = points.at(i).map(t => pitch * t)
  for (index, (tail, head)) in links.enumerate() {
    let a = at(tail)
    let b = at(head)
    let pair = (tail, head)
    let multiplicity = links.filter(p => p == pair).len()
    if multiplicity > 1 {
      let rank = links.slice(0, index).filter(p => p == pair).len()
      let delta = (rank - (multiplicity - 1) / 2) * 0.5
      let dx = b.at(0) - a.at(0)
      let dy = b.at(1) - a.at(1)
      let norm = calc.sqrt(dx * dx + dy * dy)
      let normal = (-dy / norm, dx / norm)
      a = (a.at(0) + delta * normal.at(0), a.at(1) + delta * normal.at(1))
      b = (b.at(0) + delta * normal.at(0), b.at(1) + delta * normal.at(1))
    }
    if directed {
      let middle = ((a.at(0) + b.at(0)) / 2, (a.at(1) + b.at(1)) / 2)
      line(a, middle, mark: (end: "straight"))
      line(middle, b)
    } else { line(a, b) }
  }
  for (tail, head, rise) in curves {
    let a = at(tail)
    let b = at(head)
    bezier(
      a,
      b,
      (a.at(0), a.at(1) + rise * pitch),
      (b.at(0), b.at(1) + rise * pitch),
    )
  }
  if stub != none {
    let a = at(stub)
    // The D_n source image shows only this short branch stub.
    line(a, (a.at(0), a.at(1) - pitch / 6))
  }
  for (i, point) in points.enumerate() {
    circle(at(i), radius: 0.4, fill: if filled { black } else { white })
    if str(i) in labels {
      let label-data = labels.at(str(i))
      content(at(i), label-data.at(0), anchor: label-data.at(1))
    }
  }
  for point in gaps { content(point.map(t => pitch * t), $dots.h$) }
})

#let kronecker-graph() = canvas(length: 1mm, baseline: (0, 0), {
  import draw: *
  set-style(stroke: 0.5pt)
  let pitch = 12
  for sign in (-1, 1) {
    let height = sign * pitch / 48
    line((0, height), (pitch, height))
    line((pitch / 2 - 1, height), (pitch / 2 + 1, height), mark: (
      end: "straight",
    ))
  }
  for x in (0, pitch) { circle((x, 0), radius: 0.4, fill: white) }
})

#let subspace-graphs() = align(center, [#graph-view(
    (
      (0, 0),
      (1, 0),
      (2, 0),
      (4, 0),
      (5, 0),
      (6, 0),
      (5, -1),
      (8, 0),
      (9, 0),
      (10, 0),
      (9, -1),
      (9, 1),
    ),
    ((0, 1), (2, 1), (3, 4), (5, 4), (6, 4), (7, 8), (9, 8), (10, 8), (11, 8)),
    filled: true,
    directed: true,
  ) etc.])

#let loop-graph() = canvas(length: 1mm, baseline: (0, 0), {
  import draw: *
  arc(
    (0, 0),
    start: 20deg,
    stop: 380deg,
    radius: 1.8,
    anchor: "origin",
    mark: (end: "straight"),
  )
  circle((-1.8, 0), radius: 0.3, fill: black)
})

#let dynkin-first-panels() = align(center, stack(
  [$A_n:$ #graph-view(
      ((0, 0), (1, 0), (2, 0), (4, 0), (5, 0)),
      ((0, 1), (1, 2), (3, 4)),
      gaps: ((3, 0),),
    ) $n$ vertices, $n≥1$],
  [$D_n:$ #graph-view(
      ((0, 0), (1, 0), (2, 0), (4, 0), (5, 0), (6, 0), (5, -1)),
      ((0, 1), (1, 2), (3, 4), (4, 5), (4, 6)),
      gaps: ((3, 0),),
    ) $n$ vertices, $n≥4$],
))

#let exceptional-data(n) = {
  assert((6, 7, 8).contains(n))
  let points = range(n - 1).map(i => (i, 0)) + ((2, -1),)
  let links = range(n - 2).map(i => (i, i + 1)) + ((2, n - 1),)
  assert(points.len() == n and links.len() == n - 1)
  (points, links)
}
#let dynkin-exceptional-panels() = align(center, stack(
  ..(6, 7, 8).map(n => {
    let (points, links) = exceptional-data(n)
    [$E_#n:$ #graph-view(points, links)]
  }),
))

#let forbidden-graph-panels() = align(center, stack(
  dir: ltr,
  graph-view(((0, 0), (1, 0)), ((0, 1), (0, 1)), labels: (
    "0": ($1$, "north"),
    "1": ($1$, "north"),
  )),
  [,],
  graph-view(
    ((0, 0), (1, 0), (2, 0), (4, 0), (5, 0)),
    ((0, 1), (1, 2), (3, 4)),
    gaps: ((3, 0),),
    curves: ((0, 4, 1.25),),
    labels: (
      "0": ($1$, "north"),
      "1": ($1$, "north"),
      "2": ($1$, "north"),
      "3": ($1$, "north"),
      "4": ($1$, "north"),
    ),
  ),
  [,],
  graph-view(
    ((0, 0), (-0.5, 0.5), (0.5, 0.5), (-0.5, -0.5), (0.5, -0.5)),
    ((0, 1), (0, 2), (0, 3), (0, 4)),
    labels: (
      "0": ($2$, "west"),
      "1": ($1$, "south"),
      "2": ($1$, "south"),
      "3": ($1$, "north"),
      "4": ($1$, "north"),
    ),
  ),
  [,],
  graph-view(
    (
      (0, 0),
      (1, 0),
      (2, 0),
      (4, 0),
      (5, 0),
      (-0.5, 0.5),
      (-0.5, -0.5),
      (5.5, 0.5),
      (5.5, -0.5),
    ),
    ((0, 1), (1, 2), (3, 4), (0, 5), (0, 6), (4, 7), (4, 8)),
    gaps: ((3, 0),),
    labels: (
      "0": ($2$, "south"),
      "1": ($2$, "south"),
      "2": ($2$, "south"),
      "3": ($2$, "south"),
      "4": ($2$, "south"),
      "5": ($1$, "south"),
      "6": ($1$, "north"),
      "7": ($1$, "south"),
      "8": ($1$, "north"),
    ),
  ),
))

#let three-arm-graph() = align(center, graph-view(
  (
    (0, 0),
    (-4, 0),
    (-3, 0),
    (-2, 0),
    (-1, 0),
    (1, 0),
    (2, 0),
    (3, 0),
    (5, 0),
    (6, 0),
    (0, 1),
    (1, 1),
    (2, 1),
    (4, 1),
    (5, 1),
  ),
  (
    (0, 4),
    (4, 3),
    (2, 1),
    (0, 5),
    (5, 6),
    (6, 7),
    (8, 9),
    (0, 10),
    (10, 11),
    (11, 12),
    (13, 14),
  ),
  gaps: ((-2.5, 0), (4, 0), (3, 1)),
  labels: (
    "0": ($a$, "north"),
    "1": ($x_1$, "north"),
    "2": ($x_2$, "north"),
    "3": ($x_(p-1)$, "north"),
    "4": ($x_p$, "north"),
    "5": ($y_q$, "north"),
    "6": ($y_(q-1)$, "north"),
    "8": ($y_2$, "north"),
    "9": ($y_1$, "north"),
    "10": ($z_r$, "south"),
    "11": ($z_(r-1)$, "south"),
    "13": ($z_2$, "south"),
    "14": ($z_1$, "south"),
  ),
))
