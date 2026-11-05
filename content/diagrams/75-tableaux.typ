#import "/content/main-defs.typ": block-matrix

#let tableau(rows, bars: false) = {
  let columns = calc.max(..rows.map(row => row.len()))
  let cells = rows
    .map(row => range(columns).map(i => {
      if i < row.len() { row.at(i) } else { [] }
    }))
    .flatten()
  block-matrix(
    columns,
    cells,
    hlines: if bars {
      range(1, rows.len()).map(i => (at: i))
    } else { () },
    delimiters: ([], []),
  )
}

#let young-diagram(shape) = tableau(shape.map(n => range(n).map(_ => $x$)))
#let first-tableau = (($3$, $1$, $2$), ($4$, $5$), ($7$, $6$), ($8$,))
#let second-tableau = (($8$, $7$, $6$), ($5$, $4$), ($3$, $2$), ($1$,))
#let same-tabloid-tableau = (
  ($2$, $1$, $3$),
  ($5$, $4$),
  ($6$, $7$),
  ($8$,),
)
