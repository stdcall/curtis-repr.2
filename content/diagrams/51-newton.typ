#import "@preview/cetz:0.5.2": canvas, draw

#let newton-polygon = block(width: 100%, align(center, canvas({
  import draw: *
  set-style(content: (
    wrap: text.with(top-edge: "bounds", bottom-edge: "bounds"),
  ))
  line((-1.4, 0), (7.3, 0), stroke: 0.5pt)
  line((0, -1.5), (0, 3.9), stroke: 0.5pt)
  line((0, 2.8), (1, 0.8), (3.2, 0.8), (3.6, 1.45), stroke: 1pt)
  line((3.6, 1.45), (4, 2.1), stroke: (thickness: 1pt, dash: "dotted"))
  line((4, 2.1), (4.25, 3.8), stroke: 1pt)
  for point in (
    (0, 2.8),
    (0.72, 2.35),
    (1, 0.8),
    (1.68, 0.8),
    (2.55, 1.6),
    (3.2, 0.8),
    (3.6, 1.45),
    (4, 2.1),
    (4.25, 3.8),
  ) {
    circle(point, radius: 0.045, fill: black, stroke: none)
  }
  content((-0.12, 2.8), $P_0$, anchor: "east")
  content((0.72, 2.55), $P_1$, anchor: "south")
  content((1, 0.65), $P_2$, anchor: "north")
  content((1.68, 0.65), $P_3$, anchor: "north")
  content((2.55, 1.8), $P_4$, anchor: "south")
  content((3.2, 0.65), $P_5$, anchor: "north")
  content((4.38, 3.8), $P_n$, anchor: "west")
})))

#let two-slope-newton-polygon = block(width: 100%, align(center, canvas({
  import draw: *
  set-style(content: (
    wrap: text.with(top-edge: "bounds", bottom-edge: "bounds"),
  ))
  line((-0.8, 0), (3.4, 0), stroke: 0.5pt)
  line((0, 0.45), (0, -1.8), stroke: 0.5pt)
  line((0, 0), (1.65, -1), (2.3, 0), stroke: 1pt)
  for point in ((0, 0), (1.65, -1), (2.3, 0)) {
    circle(point, radius: 0.045, fill: black, stroke: none)
  }
  content((0.08, 0.08), $(0,0)$, anchor: "south-west")
  content((2.3, 0.08), $(n,0)$, anchor: "south")
  content((1.65, -1.15), $(n-m,v(d))$, anchor: "north")
})))
