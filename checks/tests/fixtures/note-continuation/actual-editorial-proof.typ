#import "content/book-style.typ": book-style
#import "content/main-defs.typ": *
#import "content/statements.typ": *
#show: book-style
#set page(header:none,footer:none)
= Engineering chapter
== Engineering section
$ x=x $ <eq:schur-index-character-field-invariance>
#proof[An earlier complete engineering paragraph.

To complete the argument, we show directly that every simple component of $K G$
is split over its center.#ed-note[
  The original reduction argument infers absolute simplicity from the reduced
  character values and then infers an integer multiplicity from its reduction
  modulo $p$. These implications require the following additional argument.
] Put $Lambda=R G$ and $Z=op("Z")(Lambda)$. Since $n$ is a unit of $R$,
$n^(-1)sum_(g in G) g times.o g^(-1)$ is a separability idempotent, and
$a arrow n^(-1)sum_(g in G) g a g^(-1)$ is an $R$-linear projection onto $Z$.
This projection commutes with reduction, so
$ Z slash P Z ≅ op("Z")(overline(R)G). $
The bounded source excerpt ends here.
]
