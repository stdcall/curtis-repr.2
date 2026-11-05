#import "../main-defs.typ": source

#let dedication-page() = {
  set par(first-line-indent: 0pt, justify: false)
  source(3)
  v(18mm)
  strong(emph[To our sons, \
    David and Peter, \
    Timothy, Daniel, and Robert.])
}

#dedication-page()
