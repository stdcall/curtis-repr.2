#import "../main-defs.typ": source

#let title-page() = {
  set par(first-line-indent: 0pt, justify: false)
  source(1)
  v(18mm)
  text(size: 23pt)[METHODS OF \
    REPRESENTATION THEORY]
  v(4mm)
  text(size: 13pt, weight: "bold")[WITH APPLICATIONS TO FINITE GROUPS AND
    ORDERS]
  v(13mm)
  text(weight: "bold")[CHARLES W. CURTIS]
  linebreak()
  emph[University of Oregon]
  v(5mm)
  text(weight: "bold")[IRVING REINER]
  linebreak()
  emph[University of Illinois at Urbana-Champaign]
  v(15mm)
  text(weight: "bold")[VOLUME II]
  v(1fr)
  text(size: 9pt, weight: "bold")[A WILEY-INTERSCIENCE PUBLICATION]
  linebreak()
  text(size: 10pt, weight: "bold")[JOHN WILEY & SONS, New York · Chichester ·
    Brisbane · Toronto · Singapore]
}

#title-page()
