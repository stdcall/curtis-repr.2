#import "content/book-style.typ": book-style
#import "content/main-defs.typ": *
#import "content/statements.typ": *
#show: book-style
#set page(header:none,footer:none)
= Engineering chapter
== Engineering section
$ x=x $ <eq:schur-index-character-field-invariance>
#proof[An earlier complete engineering paragraph.

  Now let $p$ be any prime, and let $F$ be the field defined in @th:brauer-witt,
  so $d=dim_K F$ is prime to $p$. As shown in any standard
  reference#footnote[See Cassels–Fröhlich~@bib:Cassels1967,
    Huppert~@bib:Huppert1967, or Weiss~@bib:Weiss1969.] on cohomology of groups,
  there exist homomorphisms
  $ "res":B(K) arrow B(F), quad "cor":B(F) arrow B(K), $
The bounded source excerpt ends here.
]

#bib-group[
 #bib-item[Engineering bibliographic target A.]<bib:Cassels1967>
 #bib-item[Engineering bibliographic target B.]<bib:Huppert1967>
 #bib-item[Engineering bibliographic target C.]<bib:Weiss1969>
]
#theorem[Engineering theorem target.]<th:brauer-witt>
