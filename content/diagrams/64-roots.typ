#import "@preview/cetz:0.5.2": canvas, draw

// Root coordinates are integral coefficients in the simple-root basis.
// Reflection in simple root j subtracts the Cartan pairing in coordinate j.
#let root-orbit(cartan) = {
  let roots = ((1, 0), (0, 1))
  let cursor = 0
  while cursor < roots.len() {
    let root = roots.at(cursor)
    for j in range(2) {
      let pairing = range(2).map(i => root.at(i) * cartan.at(i).at(j)).sum()
      let reflected = range(2).map(i => (
        root.at(i) - if i == j { pairing } else { 0 }
      ))
      if not roots.contains(reflected) { roots.push(reflected) }
    }
    cursor += 1
    assert(roots.len() <= 12)
  }
  roots
}

#let rank-two-data = (
  (
    name: $A_1 times A_1$,
    cartan: ((2, 0), (0, 2)),
    simple: ((1, 0), (0, 1)),
    count: 4,
  ),
  (
    name: $A_2$,
    cartan: ((2, -1), (-1, 2)),
    simple: ((1, 0), (-0.5, calc.sqrt(3) / 2)),
    count: 6,
  ),
  (
    name: $B_2$,
    cartan: ((2, -2), (-1, 2)),
    simple: ((1, -1), (0, 1)),
    count: 8,
  ),
  (
    name: $G_2$,
    cartan: ((2, -1), (-3, 2)),
    simple: ((1, 0), (-1.5, calc.sqrt(3) / 2)),
    count: 12,
  ),
)

#let rank-two-roots() = block(width: 100%, align(center, canvas(length: 1mm, {
  import draw: *
  set-style(stroke: 0.5pt, content: (
    padding: 1.2,
    wrap: text.with(top-edge: "bounds", bottom-edge: "bounds"),
  ))
  let root-unit = 8
  let radius = root-unit * calc.sqrt(3)
  let pitch = 2 * radius + 4
  for (panel, data) in rank-two-data.enumerate() {
    let roots = root-orbit(data.cartan)
    assert(roots.len() == data.count)
    let center-x = panel * pitch
    for root in roots.filter(root => (
      root.at(0) > 0 or (root.at(0) == 0 and root.at(1) > 0)
    )) {
      let projected = range(2).map(k => (
        root-unit
          * range(2).map(i => root.at(i) * data.simple.at(i).at(k)).sum()
      ))
      line(
        (center-x - projected.at(0), -projected.at(1)),
        (center-x + projected.at(0), projected.at(1)),
      )
    }
    content((center-x, -radius - 3), data.name, anchor: "north")
  }
})))

#let path-matrix(rank, weights: (:), branch: none) = {
  let matrix = range(rank).map(i => range(rank).map(j => if i == j { 1 } else {
    2
  }))
  let path-rank = if branch == none { rank } else { rank - 1 }
  for i in range(path-rank - 1) {
    let weight = weights.at(str(i), default: 3)
    matrix.at(i).at(i + 1) = weight
    matrix.at(i + 1).at(i) = weight
  }
  if branch != none {
    matrix.at(branch).at(rank - 1) = 3
    matrix.at(rank - 1).at(branch) = 3
  }
  matrix
}

#let graph-canvas(matrix, positions, labels: (), ellipsis: none) = {
  canvas(length: 1mm, {
    import draw: *
    set-style(stroke: 0.5pt, content: (
      padding: 1.2,
      wrap: text.with(top-edge: "bounds", bottom-edge: "bounds"),
    ))
    assert(matrix.len() == positions.len())
    let pitch = 9
    let coord(index) = positions.at(index).map(value => value * pitch)
    for i in range(matrix.len()) {
      assert(matrix.at(i).at(i) == 1)
      for j in range(i + 1, matrix.len()) {
        assert(matrix.at(i).at(j) == matrix.at(j).at(i))
        if (
          matrix.at(i).at(j) > 2
            and positions.at(i) != none
            and positions.at(j) != none
        ) {
          let left = coord(i)
          let right = coord(j)
          line(left, right)
          if matrix.at(i).at(j) != 3 or labels.len() > 0 {
            content(
              ((left.at(0) + right.at(0)) / 2, (left.at(1) + right.at(1)) / 2),
              [#matrix.at(i).at(j)],
              anchor: "north",
            )
          }
        }
      }
    }
    for i in range(matrix.len()) {
      if positions.at(i) != none {
        circle(coord(i), radius: 0.4, stroke: none, fill: black)
        if labels.len() > 0 {
          content(coord(i), labels.at(i), anchor: "south")
        }
      }
    }
    if ellipsis != none {
      content(ellipsis.map(value => value * pitch), $dots.h$)
    }
  })
}

#let coxeter-example() = block(width: 100%, align(center, graph-canvas(
  path-matrix(3, weights: ("1": 4)),
  ((0, 0), (1, 0), (2, 0)),
  labels: ($s_1$, $s_2$, $s_3$),
)))

// The variable-rank families use a path with an omitted interior run.
// No edge is drawn across that run; the source's ellipsis denotes it.
#let coxeter-crystallographic() = {
  let entries = (
    (
      name: $A_n, quad n>=1$,
      matrix: path-matrix(8),
      positions: ((0, 0), (1, 0), (2, 0), none, none, none, (4, 0), (5, 0)),
      ellipsis: (3, 0),
    ),
    (
      name: $B_n - C_n, quad n>=2$,
      matrix: path-matrix(8, weights: ("6": 4)),
      positions: ((0, 0), (1, 0), (2, 0), none, none, (4, 0), (5, 0), (6, 0)),
      ellipsis: (3, 0),
    ),
    (
      name: $D_n, quad n>=4$,
      matrix: path-matrix(8, branch: 5),
      positions: (
        (0, 0),
        (1, 0),
        (2, 0),
        none,
        (4, 0),
        (5, 0),
        (6, 0),
        (5, -1),
      ),
      ellipsis: (3, 0),
    ),
    (
      name: $E_6$,
      matrix: path-matrix(6, branch: 2),
      positions: ((0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (2, -1)),
    ),
    (
      name: $E_7$,
      matrix: path-matrix(7, branch: 3),
      positions: ((0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (3, -1)),
    ),
    (
      name: $E_8$,
      matrix: path-matrix(8, branch: 4),
      positions: (
        (0, 0),
        (1, 0),
        (2, 0),
        (3, 0),
        (4, 0),
        (5, 0),
        (6, 0),
        (4, -1),
      ),
    ),
    (
      name: $F_4$,
      matrix: path-matrix(4, weights: ("1": 4)),
      positions: ((0, 0), (1, 0), (2, 0), (3, 0)),
    ),
    (
      name: $G_2$,
      matrix: path-matrix(2, weights: ("0": 6)),
      positions: ((0, 0), (1, 0)),
    ),
  )
  block(width: 100%, align(center, grid(
    columns: (auto, auto), align: (right, left),
    column-gutter: 2em, row-gutter: 1em,
    ..entries
      .map(entry => (
        entry.name,
        graph-canvas(entry.matrix, entry.positions, ellipsis: entry.at(
          "ellipsis",
          default: none,
        )),
      ))
      .flatten(),
  )))
}
