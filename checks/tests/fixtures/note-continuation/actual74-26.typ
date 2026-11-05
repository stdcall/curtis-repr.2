#import "content/book-style.typ": book-style
#import "content/main-defs.typ": *
#import "content/statements.typ": *
#show: book-style
#set page(header:none,footer:none)
= Engineering chapter
== Engineering section
$ x=x $ <eq:schur-index-character-field-invariance>
#theorem[
  Let $zeta$ be an irreducible complex character of a finite group $G$, and let
  $K=QQ(zeta)$. Let#footnote[In general,
    $m_QQ lr((zeta))=m_(QQ(zeta)) lr((zeta))$ by
    @eq:schur-index-character-field-invariance.]
  $ m=m_QQ lr((zeta))=m_K lr((zeta)) $
  be the Schur index of $zeta$. Then
  #case-list(
    numbering: "(i)",
    [#case[$K$ contains all $m$-th roots of $1$.]
      <case:character-field-schur-index-roots-of-unity>],
    [#case[
      Let $P$ and $P'$ be primes of $K$ lying over the same prime $p$ of $QQ$,
      where $p$ is either a rational prime number or $p=infinity$. Then
      $ m_(K_P) lr((zeta))=m_(K_(P')) lr((zeta)), $
      that is, $zeta$ has the same Schur indices over the complete fields $K_P$
      and $K_(P')$.
    ]<case:character-field-uniform-local-schur-indices>],
  )
]<th:character-field-schur-index-roots-local-uniformity>

AFTER @th:character-field-schur-index-roots-local-uniformity.
