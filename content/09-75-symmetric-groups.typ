#import "main-defs.typ": *
#import "note-layout.typ": reference-data
#import "main-defs.typ": number-text as reference-number-text
#import "statements.typ": *
#import "diagrams/75-tableaux.typ": *

== Representations and Characters of the Symmetric Group
<sec:symmetric-group-representations>

=== Specht Modules and Simple $F S_n$-Modules
<ss:specht-modules-simple-symmetric-modules>

Throughout this subsection, $n$ denotes a fixed positive integer. The group of
permutations of the set ${1,2,dots,n}$ will be called the _symmetric group_ and
denoted by $S_n$. The basic facts about cycle decomposition, conjugacy classes,
etc. are assumed (see @bib:CurtisReiner1962[CR], §3).

The conjugacy classes of $S_n$ are parametrized by the _partitions_ of $n$.
These are ordered sets of positive integers $alpha=(a_1,dots,a_r)$ satisfying
the conditions
$ a_1≥a_2≥dots≥a_r>0 quad "and" a_1+dots+a_r=n. $
The integers ${a_i:1≤i≤r}$ are called the _parts_ of $alpha$. Each partition
$alpha$ can be described uniquely by the exponential notation
$ alpha=1^(alpha_1) 2^(alpha_2) dots n^(alpha_n), $
which means that $alpha$ has $alpha_1$ parts equal to $1$, $alpha_2$ parts equal
to $2$, etc., so that $alpha_1+2alpha_2+dots+n alpha_n=n$. For example,
$1 2^2 3$ stands for the partition $3 2 2 1$ of $8$.

The _Young diagram_ $[alpha]$ associated with the partition
$alpha=(a_1,dots,a_r)$ is the set of points in the plane ${(i,j):i,j in ZZ_+}$
satisfying the conditions $1≤i≤r$ and for each $i$, $1≤j≤a_i$. The points
$(i,j)$ are called the nodes of the diagram, and are conveniently drawn as in
the example
$ alpha=1 2^2 3 quad [alpha]=#young-diagram((3, 2, 2, 1)) $
An _$alpha$-tableau_ $T$ is one of the $n!$ arrays obtained filling in the
integers ${1,2,dots,n}$, without repetitions, at the nodes of a Young diagram
$alpha$. For example,

#source(779)
$ T=#tableau(first-tableau) quad "and" quad T'=#tableau(second-tableau) $
are $alpha$-tableaux for the partition $alpha=1 2^2 3$.

For each $alpha$-tableau $T$, we denote by $R(T)$ the subgroup of $S_n$ that
permutes the elements of each row of $T$, and by $C(T)$ the subgroup which
permutes the elements of each column of $T$. We clearly have $R(T) inter C(T)=1$
for each $alpha$-tableau $T$, since the elements of $C(T)$ stabilize the
elements in each fixed column of $T$, while the corresponding statement for the
rows applies to $R(T)$.

The #idx("Sign representation")_sign representation_ of $S_n$ will be denoted by
$epsilon$ (see @def:coxeter-sign-representation). It is the uniquely determined
homomorphism $epsilon:S_n arrow ±1$ such that $epsilon(t)=-1$ for each
transposition $t in S_n$.

The following result was proved in @bib:CurtisReiner1962[CR] (28.15) (using
different notation).#ed-note[
  For the unnormalized element defined below,
  $e(T)^2=frac(n!, dim_QQ Z_alpha)e(T)$. Hence $frac(dim_QQ Z_alpha, n!)e(T)$ is
  a primitive idempotent generating the same left ideal. This follows from the
  simple-ideal calculation in @th:young-symmetrizer-specht-ideal and the regular
  trace.
]

#theorem[
  Set
  $ e(T)=sum_(p in R(T),q in C(T)) epsilon(q)p q $
  in the rational group algebra $QQ S_n$, for each $alpha$-tableau $T$ and each
  partition $alpha$. Then the following statements hold;
  #case-list(
    numbering: "(i)",
    [#case[$e(T)$ is a nonzero scalar multiple of a primitive idempotent in
        $QQ S_n$.]
      <case:young-symmetrizer-primitive-idempotent>],
    [#case[$QQ S_n e(T)$ is an absolutely simple $QQ S_n$-module.]
      <case:young-symmetrizer-absolutely-simple-ideal>],
    [#case[$QQ S_n e(T) ≅ QQ S_n e(T')$, for an $alpha'$-tableau $T'$, if and
      only if $alpha=alpha'$.]<case:young-symmetrizer-partition-isomorphism>],
    [#case[Every simple $QQ S_n$-module is isomorphic to $QQ S_n e(T)$ for some
        $alpha$-tableau $T$ and some partition $alpha$.]
      <case:young-symmetrizer-complete-simple-modules>],
  )
]<th:young-symmetrizer-simple-modules>

In this subsection, we shall give a new proof of this theorem, and improve and
extend it in several important ways. In particular, we shall obtain an explicit
generating set for each simple $QQ S_n$-module, from which a matrix
representation afforded by the module can be calculated. The approach also
yields the simple $F S_n$-modules, for an arbitrary field $F$ of any
characteristic. Except for some minor changes, the entire discussion follows
James~@bib:James1978 (see also James-Kerber~@bib:James1981).

We first require several other concepts and preliminary results concerning them.
We shall make heavy use of two order relations on the set of partitions of $n$.
The first is a partial order, called _dominance_ and denoted by $≽$. We set
$
  alpha≽beta quad "if and only if" quad
  sum_(i=1)^j a_i≥sum_(i=1)^j b_i
$
<eq:partition-dominance-order>
for each $j$, where ${a_i}$ and ${b_i}$ are the parts of $alpha$ and $beta$,
respectively with zeros inserted if necessary. Thus
$ 1 2^2 3≻2^4 quad "and" quad 2^2 4≻1^3 2 3 $

#source(780)
while $2^2 3$ and $1^3 4$ are not comparable with respect to dominance. If
$alpha≽beta$ and $alpha≠beta$, we write $alpha≻beta$.

The second is a total order on the set of partitions of $n$, called
_lexicographic ordering_, and denoted by $≥$. We set $alpha>beta$ if for some
$i≥1$ we have $a_i-b_i$ is positive while all differences (if any) $a_j-b_j$ for
$j<i$ are zero, and ${a_i}$ and ${b_i}$ are the parts of $alpha$ and $beta$,
respectively.

We clearly have
$ alpha≽beta arrow.r.double alpha≥beta, $
but the reverse implication does not always hold.

We next initiate a close study of the permutation action of $S_n$ and its
subgroups on the set of $alpha$-tableaux, for the various partitions of $n$,
which will be denoted by $alpha,beta,gamma,dots$ without further explanation.

Let $alpha$ be a fixed partition of $n$. The group $S_n$ acts on the set of
$alpha$-tableaux ${T}$ in the obvious way, with $x T$ obtained by applying $x$
to each entry in $T$, for each $x in S_n$. The set of $alpha$-tableaux ${T}$ is
clearly a transitive $S_n$-set, and we have
$
  R(x T)=x R(T)x^(-1) quad "and" quad C(x T)=x C(T)x^(-1),
  quad "for" x in S_n
$
<eq:tableau-row-column-conjugation>
where $R(T)$ and $C(T)$ are the groups of row and column permutations defined
previously, for each $alpha$-tableau $T$.

We next define an equivalence relation, denoted by $∼$, on the set of
$alpha$-tableaux. We set
$
  T_1∼T_2 arrow.l.r.double T_1=p T_2
  quad "for some" p in R(T_1).
$
The equivalence class of an $alpha$-tableau $T$ is denoted by $[T]$, and is
called the _$alpha$-tabloid_ with representative $T$. An $alpha$-tabloid can be
viewed as an $alpha$-tableaux with unordered rows. We shall use the notation
$ #tableau(first-tableau, bars: true), $
with bars between the rows, to denote the $alpha$-tabloid represented by the
$alpha$-tableaux
$
  #tableau(first-tableau) quad "and" quad
  #tableau(same-tabloid-tableau) quad "etc."
$
The symmetric group $S_n$ acts on the set of $alpha$-tabloids as follows: we set
$ x[T]=[x T], quad "for" x in S_n, $
#source(781)
for each $alpha$-tabloid $[T]$. The action is well defined, since $[T_1]=[T_2]$
implies that $[x T_1]=[x T_2]$. This is easily proved, since $[T_1]=[T_2]$
implies that $T_1=p T_2$ for some $p in R(T_1)$, and hence
$x T_1=x p x^(-1) dot x T_2$, with $x p x^(-1) in R(x T_1)$ by
@eq:tableau-row-column-conjugation.

The $alpha$-tabloids clearly form a transitive $S_n$-set. The stabilizer of an
$alpha$-tabloid $[T]$ is the row subgroup $R(T)$, for a representative $T$ of
$[T]$. This gives a neat interpretation of the induced permutation modules
$(1_(R(T)))^(S_n)$.

#lemma[
  Let $alpha$ be a fixed partition of $n$, and let $F$ be a field. Let $M_alpha$
  be the vector space over $F$ with a basis identified with the set of
  $alpha$-tabloids $[T]$, and define the action of $S_n$ on $M_alpha$ by the
  rule
  $ x[T]=[x T] $
  for each $x in S_n$ and $alpha$-tabloid $[T]$. Then $M_alpha$ is an
  $F S_n$-module, which affords the permutation representation
  $(1_(R(T)))^(S_n)$, where $R(T)$ is the group of row permutations of any
  $alpha$-tableau $T$.
]<lem:young-tabloid-permutation-module>

The proof is immediate from §~@i:ss:background-group-theory and the remarks
preceding the lemma.

The row subgroups ${R(T)}$ corresponding to the set of $alpha$-tableaux ${T}$,
for a fixed partition $alpha$, form a conjugacy class of subgroups of $S_n$,
called the _Young subgroups_ of type $alpha$. (As an exercise, the reader should
verify that the Young subgroups of type $alpha$ coincide with a conjugacy class
of parabolic subgroups of $S_n$, in the sense of
§~@sec:root-systems-reflection-groups (see also Exercise
@exc:type-a-root-system).) We now have:

#definition[
  #idx("Specht module")
  Let $F$ be a field, and $alpha$ a fixed partition of $n$, with $M_alpha$ the
  permutation module defined in @lem:young-tabloid-permutation-module. For each
  $alpha$-tableau $T$, the _Specht element_ $e_T$ is the element of $M_alpha$
  defined by
  $ e_T=sum_(q in C(T)) epsilon(q)q[T], $
  where $C(T)$ is the group of column permutations of $T$ and $epsilon(q)$ is
  the value of the sign representation $epsilon$ at $q$. The _Specht module_
  $Z_alpha$ is the $F S_n$-submodule of $M_alpha$ generated by the set of Specht
  elements ${e_T}$, corresponding to the set of $alpha$-tableaux ${T}$.
]<def:specht-element-module>

We first note that the Specht element $e_T$ can be expressed as
$ e_T=c(T)[T] $
where $c(T)$ is the element of the group algebra $F S_n$ defined by
$ c(T)=sum_(q in C(T)) epsilon(q)q $
<eq:tableau-signed-column-sum>
and is called the _signed column sum_ associated with the $alpha$-tableau $T$.

#source(782)
#lemma[
  Each Specht module $Z_alpha$ is a cyclic $F S_n$-module, generated by any
  Specht element $e_T$ associated with an $alpha$-tableau $T$.
]<lem:specht-module-cyclic>

#proof[
  Since $S_n$ acts transitively on the set of $alpha$-tableaux, it is sufficient
  to prove that
  $
    x e_T=e_(x T), quad "for" x in S_n,
    quad "and an" alpha"-tableau" T.
  $
  <eq:specht-element-equivariance>
  To prove @eq:specht-element-equivariance, we note that $C(x T)=x C(T)x^(-1)$
  for each $x in S_n$, by @eq:tableau-row-column-conjugation, so that
  $ x c(T)x^(-1)=sum_(q in C(T)) epsilon(q)x q x^(-1)=c(x T). $
  Then
  $ x e_T=x c(T)[T]=x c(T)x^(-1)x[T]=c(x T)[x T]=e_(x T), $
  completing the proof.
]

#definition[
  Let $F$ be a field, and $M_alpha$ a Young module of type $alpha$ (see
  @lem:young-tabloid-permutation-module). Define a bilinear form
  $chevron.l , chevron.r:M_alpha times M_alpha arrow F$ by setting
  $
    chevron.l [T],[T'] chevron.r=cases(
      1 & "if" [T]=[T'],
      0 & "if" [T]≠[T']
    )
  $
  for each pair of $alpha$-tabloids $[T]$ and $[T']$ in $M_alpha$.
]<def:young-tabloid-bilinear-form>

The following two results are straightforward, and are left as exercises for the
reader.

#proposition[
  The bilinear form $chevron.l , chevron.r$ on $M_alpha$, defined by
  @def:young-tabloid-bilinear-form, is symmetric, nondegenerate, and invariant
  under the action of $S_n$ in the sense that
  $chevron.l x t,x t' chevron.r=chevron.l t,t' chevron.r$ for all $x in S_n$ and
  $t,t' in M_alpha$.
]<prop:young-tabloid-form-invariant-nondegenerate>

#proposition[
  Let $F$ be a field, $G$ a finite group, and let $V$ be a f.g. left
  $F G$-module admitting a symmetric, nondegenerate, $G$-invariant bilinear form
  $chevron.l , chevron.r$. Then we have:
  #case-list(
    numbering: "(i)",
    [#case[
      $V$ is self-contragredient, in the sense that there is an isomorphism of
      $F G$-modules $V ≅ V^*$, where $V^*$ denotes the contragredient module.
    ]<case:invariant-form-self-contragredient>],
    [#case[
      Let $W subset.eq V$ be an $F G$-submodule, and set
      $
        W^perp={v in V:chevron.l v,w chevron.r=0
          "for all" w in W}.
      $
      Then $W slash (W inter W^perp)$ is an $F G$-module, which is isomorphic to
      its contragredient module.
    ]<case:invariant-form-radical-quotient-self-dual>],
    [#source(783)
      #case[
        Let ${e_1,dots,e_m}$ be an $F$-basis for $W$, and let
        $Gamma=(chevron.l e_i,e_j chevron.r)_(1≤i,j≤m)$ denote the matrix of the
        restriction $lr(chevron.l, chevron.r |)_W$ of the bilinear form, with
        respect to the basis ${e_i:1≤i≤m}$. Then we have
        $ dim_F W slash (W inter W^perp)="rank" Gamma. $
      ]<case:invariant-form-gram-rank-quotient-dimension>],
  )
]<prop:invariant-bilinear-form-duality-rank>

We can now state the first main result of this subsection, using the properties
#{
  [@prop:young-tabloid-form-invariant-nondegenerate]
}–@prop:invariant-bilinear-form-duality-rank of the bilinear form
$chevron.l , chevron.r$ on $M_alpha$.

#theorem(title: [James~@bib:James1978])[
  #idx("James' Theorem")
  Let $F$ be an arbitrary field, let $alpha$ be a partition of $n$, and let
  $M_alpha$ denote the Young module of type $alpha$. Then the following
  statements hold.
  #case-list(
    numbering: "(i)",
    [#case[
      Let $U subset.eq M_alpha$ be a $F S_n$-submodule of $M_alpha$, and let
      $Z_alpha subset.eq M_alpha$ be the Specht module (see
      @def:specht-element-module). Then we have either $U supset.eq Z_alpha$ or
      $U subset.eq Z_alpha^perp$.
    ]<case:james-specht-submodule-alternative>],
    [#case[
      The quotient $Z_alpha slash (Z_alpha inter Z_alpha^perp)$ is either zero
      or an absolutely simple $F S_n$-module. If it is not zero, then
      $Z_alpha inter Z_alpha^perp$ is the unique maximal submodule of $Z_alpha$,
      and $Z_alpha slash (Z_alpha inter Z_alpha^perp)$ is isomorphic to its
      contragredient.
    ]<case:james-specht-radical-quotient-simple>],
  )
]<th:james-specht-submodule-quotient>

The proof involves a series of lemmas. The first is a variation of a result used
in @bib:CurtisReiner1962[CR] to prove @th:young-symmetrizer-simple-modules (see
@bib:CurtisReiner1962[CR], Lemma 28.11).

#lemma(name: "Basic Combinatorial Lemma")[
  Let $alpha$ and $beta$ be partitions of $n$, and let $T_1$ be an
  $alpha$-tableau and $T_2$ be a $beta$-tableau. Assume that the entries in each
  row of $T_2$ belong to different columns of $T_1$. Then $alpha≽beta$ (see
  @eq:partition-dominance-order).
]<lem:tableau-row-column-dominance>

#proof[
  Let $alpha=(a_1,dots,a_r)$ and $beta=(b_1,dots,b_s)$. Applying the hypothesis
  to the first row of $T_2$, we see that $T_1$ has at least $b_1$ columns, so
  $a_1≥b_1$. Upon replacing $T_1$ by $g T_1$ for a suitable element
  $g in C(T_1)$, we may assume that the elements in the first row of $T_2$ all
  belong to the first row of $T_1$, and that the hypotheses of the lemma are
  satisfied for $T_2$ and the new choice of $T_1$. Since the elements in the
  second row of $T_2$ appear in different columns of $T_1$, it follows that
  either $a_2≥b_2$ or else there are $b_2-a_2$ extra spaces in the first row of
  the new choice of $T_1$ not occupied by elements of the first row of $T_2$. In
  either case, we have $a_1+a_2≥b_1+b_2$, and we may assume that the entries of
  the first two rows of $T_2$ are a subset of the entries of the first two rows
  of $T_1$. The argument is easily continued by induction, and we obtain
  $alpha≽beta$, as required.
]

#lemma[
  Keep the notation of @lem:tableau-row-column-dominance, assume that
  $c(T_1)[T_2]≠0$ in $M_beta$, where $c(T_1)$ is the signed column sum
  @eq:tableau-signed-column-sum of the $alpha$-tableau $T_1$. Then we have
  $alpha≽beta$. Moreover, if $alpha=beta$, then we have
  $ c(T_1)[T_2]=±c(T_1)[T_1]=±e_(T_1), $
  where $e_(T_1)$ is the Specht element @def:specht-element-module in $M_alpha$
  associated with $T_1$.
]<lem:signed-column-sum-tabloid-dominance>

#source(784)
#proof[
  Let ${i,j}$ be two numbers belonging to the same row of $T_2$. Then
  $(1-(i j))[T_2]=0$, and it follows that $i$ and $j$ belong to different
  columns of $T_1$. Otherwise $(i j) in C(T_1)$, and we have $c(T_1)[T_2]=0$
  contrary to the hypothesis, since we have
  $ c(T_1)=u(1-(i j)) $
  where $u in F C(T_1)$ is the alternating sum of coset representatives in
  $C(T_1)$ of the subgroup generated by $(i j)$. This implies that any two
  entries in a row of $T_2$ belong to different columns of $T_1$, and hence
  $alpha≽beta$, by the Basic Combinatorial Lemma
  @lem:tableau-row-column-dominance.

  Now assume $alpha=beta$. Then $[T_2]$ belongs to the $C(T_1)$-orbit of
  $[T_1]$. It follows that $[T_2]=g[T_1]$ for some element $g in C(T_1)$, and we
  obtain
  $
    [T_2]=g[T_1] quad "and" quad
    c(T_1)[T_2]=c(T_1)g[T_1]=epsilon(g)e_(T_1),
  $
  since $g in C(T_1)$ and $e_(T_1)=c(T_1)[T_1]$.
]

#corollary[
  Let $u in M_alpha$, and let $T$ be an $alpha$-tableau. Then $c(T)u$ is a
  multiple of $e_T$.
]<cor:signed-column-sum-specht-line>

#proof[
  By @lem:young-tabloid-permutation-module, $u$ is a linear combination of
  $alpha$-tabloids $[T_j]$, and for each $alpha$-tabloid $[T_j]$, $c(T)[T_j]$ is
  either zero or a multiple of $e_T$, by
  @lem:signed-column-sum-tabloid-dominance.
]

We next introduce the bilinear form
$chevron.l , chevron.r:M_alpha times M_alpha arrow F$ defined in
@def:young-tabloid-bilinear-form, and recall that it is symmetric, nondegenerate
and $S_n$-invariant, by @prop:young-tabloid-form-invariant-nondegenerate. We
also have:

#lemma[
  Let $u,v in M_alpha$ and let $T$ be an arbitrary $alpha$-tableau. Then
  $ chevron.l c(T)u,v chevron.r=chevron.l u,c(T)v chevron.r. $
]<lem:signed-column-sum-self-adjoint>

#proof[
  We have
  $
    chevron.l c(T)u,v chevron.r
    &=sum_(q in C(T)) epsilon(q)chevron.l q u,v chevron.r
    =sum_(q in C(T)) epsilon(q)chevron.l q u,q q^(-1)v chevron.r \
    &=sum_(q in C(T)) epsilon(q)chevron.l u,q^(-1)v chevron.r
    =chevron.l u,c(T)v chevron.r,
  $
  since the form is $S_n$-invariant.
]

We are now in a position to prove part~@case:james-specht-submodule-alternative
of Theorem @th:james-specht-submodule-quotient, which we single out for later
reference.

#lemma(name: "Submodule Lemma")[
  Let $U$ be an $F S_n$-submodule of a Young module $M_alpha$, and let
  $Z_alpha subset.eq M_alpha$ be the Specht submodule of $M_alpha$. Then either
  $Z_alpha subset.eq U$ or $U subset.eq Z_alpha^perp$.
]<lem:specht-submodule-alternative>

#proof[
  Let $u in U$ and let $T$ be an $alpha$-tableau. By
  @cor:signed-column-sum-specht-line, either $c(T)u=0$ or $e_T in U$.
  #source(785)
  Thus if $c(T)u≠0$ for some $alpha$-tableau $T$, we have $Z_alpha subset.eq U$,
  using @cor:signed-column-sum-specht-line and the fact that $Z_alpha$ is a
  cyclic $F S_n$-module generated by an arbitrary Specht element by
  @lem:specht-module-cyclic.

  Next assume that $Z_alpha ⊈ U$. Then $c(T)u=0$ for all $u in U$ and all
  $alpha$-tableaux $T$, by the first part of the proof. Then
  $
    chevron.l c(T)u,[T] chevron.r
    =chevron.l u,c(T)[T] chevron.r=chevron.l u,e_T chevron.r=0
  $
  for each $alpha$-tableau $T$, by @lem:signed-column-sum-self-adjoint, and
  hence $U subset.eq Z_alpha^perp$, completing the proof.
]

#proof(head: emph[Proof of Theorem @th:james-specht-submodule-quotient,
  part~@case:james-specht-radical-quotient-simple.])[
  All the statements in part~@case:james-specht-radical-quotient-simple of
  @th:james-specht-submodule-quotient follow at once from
  part~@case:james-specht-submodule-alternative (which is the Submodule Lemma
  @lem:specht-submodule-alternative) and
  @case:invariant-form-radical-quotient-self-dual[#context {
    reference-number-text(
      "("
        + reference-data(<prop:invariant-bilinear-form-duality-rank>).text
        + reference-data(<case:invariant-form-radical-quotient-self-dual>)
          .text
          .trim(regex("[()]"))
        + ")",
    )
  }], except the fact that $Z_alpha slash (Z_alpha inter Z_alpha^perp)$ is an
  absolutely simple $F S_n$-module if it is different from zero. To settle this
  point, we first note that $Z_alpha$ has a basis consisting of Specht elements
  ${e_(T_i):1≤i≤m}$ for certain $alpha$-tableaux ${T_i}$, by
  @def:specht-element-module. For each pair of basis elements, we have
  $chevron.l e_(T_i),e_(T_j) chevron.r in F_0$, where $F_0$ is the prime field
  in $F$, by @def:young-tabloid-bilinear-form. Thus the matrix
  $Gamma=(chevron.l e_(T_i),e_(T_j) chevron.r)_(1≤i,j≤m)$ of the restriction of
  the bilinear form to $Z_alpha$ has entries in $F_0$, and consequently its rank
  over any field containing $F_0$ is the same as its rank over $F_0$. Now let
  $K$ be a field containing $F$. Letting $Z_alpha^K$ denote
  $K times.o_F Z_alpha$, etc., we note that $Z_alpha^K$ is the Specht submodule
  of the Young module $M_alpha^K$ of type $alpha$, over $K S_n$. Using
  @case:invariant-form-gram-rank-quotient-dimension[#context {
    reference-number-text(
      "("
        + reference-data(<prop:invariant-bilinear-form-duality-rank>).text
        + reference-data(<case:invariant-form-gram-rank-quotient-dimension>)
          .text
          .trim(regex("[()]"))
        + ")",
    )
  }] and the preceding remarks, it follows that
  $
    (Z_alpha slash (Z_alpha inter Z_alpha^perp))^K
    ≅ Z_alpha^K slash (Z_alpha^K inter (Z_alpha^K)^perp),
  $
  <eq:specht-radical-quotient-field-extension>
  where $Z_alpha^K inter (Z_alpha^K)^perp$ is the radical of the bilinear form
  $chevron.l , chevron.r$, extended to $Z_alpha^K$. Since
  $Z_alpha^K slash (Z_alpha^K inter (Z_alpha^K)^perp)$ is a simple
  $K S_n$-module if $Z_alpha slash (Z_alpha inter Z_alpha^perp)≠0$ by the
  preceding discussion, we conclude that
  $Z_alpha slash (Z_alpha inter Z_alpha^perp)$ is absolutely simple by
  @eq:specht-radical-quotient-field-extension, completing the proof.
]

We next turn to the question of the completeness of the set of simple
$F S_n$-modules provided by Theorem @th:james-specht-submodule-quotient. We
first consider the case of a field $F$ of characteristic zero, where it will
turn out that the Specht modules themselves are the simple modules.

#theorem[
  #idx("Specht module")
  The Specht modules ${Z_alpha}$ (over the rational field $QQ$), corresponding
  to the set of partitions ${alpha}$ of $n$, are absolutely simple
  $QQ S_n$-modules, and provide a basic set of simple $QQ S_n$-modules.
]<th:rational-specht-complete-simple-modules>

#proof[
  The bilinear form $chevron.l , chevron.r$ on the Young module $M_alpha$ over
  $QQ S_n$, is clearly positive definite, by @def:young-tabloid-bilinear-form,
  so its restriction to the Specht module $Z_alpha$ is also positive definite,
  for each partition $alpha$. Then we have
  $
    Z_alpha inter Z_alpha^perp=0 quad "and" quad
    M_alpha=Z_alpha plus.o Z_alpha^perp,
  $
  <eq:rational-specht-orthogonal-direct-sum>
  and hence $Z_alpha$ is an absolutely simple $QQ S_n$-module for each partition
  $alpha$, by @th:james-specht-submodule-quotient.
  #source(786)
  The partitions of $n$ are in bijective correspondence with the conjugacy
  classes of $S_n$, and hence with the number of isomorphism classes of simple
  $CC S_n$-modules. The Specht modules ${Z_alpha}$ over $QQ S_n$ are absolutely
  simple by the first part of the proof, and hence provide a basic set of simple
  $QQ S_n$-modules if we can prove that
  $ Z_alpha ≄ Z_beta quad "if" alpha≠beta, $
  <eq:distinct-partition-specht-modules>
  for arbitrary partitions $alpha$ and $beta$. Let $f:Z_alpha arrow Z_beta$ be a
  nonzero homomorphism of $QQ S_n$-modules. By
  @eq:rational-specht-orthogonal-direct-sum, $f$ extends to a nonzero
  homomorphism $tilde(f):M_alpha arrow M_beta$ such that
  $Z_alpha ⊈ ker tilde(f)$. Let $T$ be an $alpha$-tableau; then
  $e_T in.not ker tilde(f)$ by @lem:specht-module-cyclic, so
  $ tilde(f)(e_T)=tilde(f)(c(T)[T])=c(T)tilde(f)([T])≠0. $
  It follows that $c(T)[T']≠0$ for some $beta$-tableau $T'$, and hence
  $alpha≽beta$ by @lem:signed-column-sum-tabloid-dominance. Thus if
  $Z_alpha ≅ Z_beta$ we have $alpha≽beta$ and $beta≽alpha$, and hence
  $alpha=beta$, completing the proof.
]

Continuing with the characteristic zero case, we give a new proof of part of
Theorem @th:young-symmetrizer-simple-modules, based on
@th:james-specht-submodule-quotient. (The remaining assertions of
@th:young-symmetrizer-simple-modules are easily verified and are left to the
reader.)

#theorem[
  Let $T$ be an $alpha$-tableau, and let $I_T$ be the left ideal in $QQ S_n$
  generated by the element
  $ e'=sum_(p in R(T),q in C(T)) epsilon(q)q p, $
  as in @th:young-symmetrizer-simple-modules. Then there is an isomorphism of
  $QQ S_n$-modules
  $ I_T ≅ Z_alpha. $
]<th:young-symmetrizer-specht-ideal>

#proof[
  Let $e_(R(T))=sum_(p in R(T)) p$. Then the left ideal $QQ S_n e_(R(T))$
  affords the permutation representation $(1_(R(T)))^(S_n)$, and hence there is
  an isomorphism of $QQ S_n$-modules
  $ h:QQ S_n e_(R(T)) arrow M_alpha $
  such that $h(e_(R(T)))=[T]$, by @lem:young-tabloid-permutation-module. Since
  the element $e'$ in the statement of the Theorem is given by
  $e'=c(T)e_(R(T))$, we obtain
  $ h(e')=h(c(T)e_(R(T)))=c(T)h(e_(R(T)))=c(T)[T]=e_T. $
  The result now follows from @lem:specht-module-cyclic.
]

#remark(numbered: false)[
  It is worthwhile to compare the descriptions of the simple $QQ S_n$-modules in
  terms of the primitive idempotents obtained by normalizing $e(T)$ (see
  @th:young-symmetrizer-simple-modules) with the approach based on Specht
  modules, in @th:rational-specht-complete-simple-modules. The former provides
  no generating set for a simple module, and hence no explicit formula for the
  $S_n$-action on the module, while the
  #source(787)
  latter does provide a set of generators (the Specht elements) and gives the
  $S_n$-action on them (see @eq:specht-element-equivariance). With further
  discussion, this information can be refined to describe explicitly the
  matrices of the $S_n$-action on a Specht module $Z_alpha$ with respect to a
  suitable basis (see James~@bib:James1978 and James-Kerber~@bib:James1981).
]<rem:specht-generators-matrix-representations>

Our next task is to understand the information contained in Theorem
@th:james-specht-submodule-quotient, for fields $F$ of characteristic $p>0$. We
first require:

#definition[
  Let
  $ alpha=1^(n_1) 2^(n_2) dots r^(n_r) $
  be a partition of $n$, with $n_1$ parts equal to $1$, $n_2$ equal to $2$, etc.
  The partition $alpha$ is called _$p$-regular_ if the numbers $n_j$ satisfy the
  condition
  $ n_j<p quad "for all" j=1,2,dots,r. $
]<def:p-regular-partition>

We then have:

#proposition[
  Let $p$ be a prime number. The number of $p$-regular classes in $S_n$ is equal
  to the number of $p$-regular partitions.
]<prop:p-regular-class-partition-count>

#proof[
  The $p$-regular conjugacy classes in $S_n$ are clearly in bijective
  correspondence with the set of partitions
  $ alpha=1^(n_1) 2^(n_2) dots $
  with property that $n_j=0$ if $p divides j$, that is, no part of $alpha$ is
  divisible by $p$.

  Now consider the formal power series over $QQ$:
  $ P(x)=frac((1-x^p)(1-x^(2 p))dots, (1-x)(1-x^2)dots), $
  and calculate it in two ways, as follows.
  #case-list(
    numbering: "(i)",
    [#case[
      Cancel factors $1-x^(j p)$ in the numerator and denominator. This leaves
      $
        P(x)=product_(p divides.not i) (1-x^i)^(-1)
        =product_(p divides.not i) (1+x^i+x^(2 i)+dots),
      $
      so the coefficient of $x^n$ is the number of partitions of $n$ in which no
      part is divisible by $p$.
    ]<case:p-regular-partition-generating-series-cancellation>],
    [#case[
      For each $j$, divide the term $1-x^(j p)$ in the numerator by $1-x^j$ in
      the denominator. This gives
      $ P(x)=product_(j=1)^infinity (1+x^j+x^(2j)+dots+x^((p-1)j)), $
      #source(788)
      and we see that the coefficient of $x^n$ is equal to the number of
      partitions of $n$ in which no part occurs $p$ or more times.
    ]<case:p-regular-partition-generating-series-geometric>],
  )
  The proposition follows from a comparison of
  parts~@case:p-regular-partition-generating-series-cancellation and
  @case:p-regular-partition-generating-series-geometric.
]

Now let $F$ be a field of characteristic $p$. Let $alpha$ be a partition of $n$,
and let $M_alpha$, $Z_alpha$, $e_T$, $chevron.l , chevron.r$ be the objects
defined earlier in the section. In the following results, integers involved in
calculations in $F$, of course, are taken $"mod" p$, so that $n$ denotes
$n dot 1 in F$, for $n in ZZ$. We also use the convention that $0! =1$.

#proposition[
  Let $alpha=1^(n_1) 2^(n_2) dots r^(n_r)$ be a partition of $n$. Then we have:
  #case-list(
    numbering: "(i)",
    [#case[
      $
        chevron.l e_T,e_(T') chevron.r
        =lr(product_(j=1)^r n_j!)n_(T,T'),
      $
      for all $alpha$-tableaux $T$ and $T'$, and some element $n_(T,T')$
      depending on $T$ and $T'$; and
    ]<case:specht-gram-row-factorial-divisor>],
    [#case[
      $
        product_(j=1)^r (n_j!)^j
        =chevron.l e_(T_0),e_(T'_0) chevron.r
      $
      for some pair of $alpha$-tableaux ${T_0,T'_0}$.
    ]<case:specht-gram-nonzero-p-regular-pair>],
  )
]<prop:specht-gram-row-factorials>

#proof[
  #case-list(
    numbering: "(i)",
    [#case[
      Define an equivalence relation $∼$ on the $alpha$-tabloids, putting
      $[T_1]∼[T_2]$ whenever $[T_1]$ can be obtained from $[T_2]$ by permuting
      rows of equal length. The size of an equivalence class is clearly
      $product_(j=1)^r n_j!$.

      Now assume that an $alpha$-tabloid $[T_1]$ appears with a nonzero
      coefficient $a_1$ in the expression of a Specht element $e_T$ as a linear
      combination of $alpha$-tabloids. It is easily checked that, for all
      tabloids $[T_2]$ in the equivalence class of $[T_1]$, $[T_2]$ appears with
      the nonzero coefficient $epsilon a_1$ in $e_T$, where $epsilon$ is the
      sign of the permutation required to exchange $[T_1]$ and $[T_2]$. The
      proof of part~@case:specht-gram-row-factorial-divisor of
      @prop:specht-gram-row-factorials follows easily from these remarks and the
      definition @def:young-tabloid-bilinear-form of the bilinear form
      $chevron.l , chevron.r$ on $M_alpha$.
    ]<case:specht-gram-row-factorial-divisor-proof>],
    [#case[
      Let $T$ be an $alpha$-tableau, and let $T^*$ be the $alpha$-tableau
      obtained from $T$ by reversing the order of the entries in each row. Let
      $C_0(T)$ denote the subgroup of the group $C(T)$ consisting of elements
      that, independently within each column, permute the entries belonging to
      rows of each fixed length. We clearly have
      $ |C_0(T)|=product_(j=1)^r (n_j!)^j. $
      If $[T']=q[T]$ for some $q in C_0(T)$, then $[T']$ appears in $e_T$ and
      $e_(T^*)$ with the same coefficient. It can also be readily verified that
      all tabloids that appear with nonzero coefficients in $e_T$ and $e_(T^*)$
      are related in this way. Thus we obtain
      $ chevron.l e_T,e_(T^*) chevron.r=product_(j=1)^r (n_j!)^j $
      as required.
    ]<case:specht-gram-reversed-row-pair-proof>],
  )
]

#source(789)
#corollary[
  Let $Z_alpha$ denote the Specht module of type $alpha$, over the group algebra
  $F S_n$. Then
  $ Z_alpha slash (Z_alpha inter Z_alpha^perp)≠0 $
  if and only if $alpha$ is $p$-regular.
]<cor:specht-radical-quotient-p-regular>

#proof[
  Let $alpha$ be $p$-regular; then there exist $alpha$-tableaux $T_0$ and $T'_0$
  such that $chevron.l e_(T_0),e_(T'_0) chevron.r≠0$, by
  @case:specht-gram-nonzero-p-regular-pair[#context {
    reference-number-text(
      "("
        + reference-data(<prop:specht-gram-row-factorials>).text
        + reference-data(<case:specht-gram-nonzero-p-regular-pair>)
          .text
          .trim(regex("[()]"))
        + ")",
    )
  }]. Then $e_(T_0) in.not Z_alpha inter Z_alpha^perp$, and hence
  $Z_alpha slash (Z_alpha inter Z_alpha^perp)≠0$. Conversely, if $alpha$ is not
  $p$-regular, then $chevron.l e_T,e_(T') chevron.r=0$ for all $alpha$-tableau
  $T$ and $T'$, by @case:specht-gram-row-factorial-divisor[#context {
    reference-number-text(
      "("
        + reference-data(<prop:specht-gram-row-factorials>).text
        + reference-data(<case:specht-gram-row-factorial-divisor>)
          .text
          .trim(regex("[()]"))
        + ")",
    )
  }]. Then $Z_alpha subset.eq Z_alpha^perp$, and we obtain
  $Z_alpha slash (Z_alpha inter Z_alpha^perp)=0$, completing the proof.
]

In order to complete the determination of the simple $F S_n$-modules using
Theorem @th:james-specht-submodule-quotient, we will, of course, use
@i:cor:brauer-number-simple-modules, which asserts that the number of
isomorphism classes of simple $F S_n$-modules is equal to the number of
$p$-regular conjugacy classes. We also require:

#lemma[
  Let $alpha$ and $beta$ be partitions of $n$, and assume that $alpha$ is
  $p$-regular. Let $U$ be an $F S_n$-submodule of $M_beta$, and let
  $f:Z_alpha arrow M_beta slash U$ be a nonzero homomorphism of $F S_n$-modules.
  Then $alpha≽beta$.
]<lem:p-regular-specht-quotient-dominance>

#proof[
  (Peel~@bib:Peel1975.) (Notice that the result is simply an adaptation, for
  nonsemisimple modules, of the last part of the proof of
  @th:rational-specht-complete-simple-modules.) Let $T$ be an $alpha$-tableau,
  and let $T^*$ be the $alpha$-tableau obtained by reversing the order of the
  entries of the rows of $T$. By @cor:signed-column-sum-specht-line, we have
  $ c(T)e_(T^*)=a e_T, $
  <eq:p-regular-specht-column-nonzero-scalar>
  where
  $
    a=chevron.l [T],c(T)e_(T^*) chevron.r
    =chevron.l c(T)[T],e_(T^*) chevron.r
    =chevron.l e_T,e_(T^*) chevron.r≠0
  $
  by @lem:signed-column-sum-self-adjoint and @prop:specht-gram-row-factorials,
  using the fact that $alpha$ is $p$-regular. Since
  $f:Z_alpha arrow M_beta slash U$ is different from zero, there exists an
  $alpha$-tableau $T$ such that $f(e_T)≠0$ in $M_beta slash U$. Apply $f$ to
  @eq:p-regular-specht-column-nonzero-scalar, and obtain
  $ c(T)f(e_(T^*))=a f(e_T)≠0 quad "in" M_beta slash U. $
  It follows that $c(T)m in.not U$ for some $m in M_beta$, and hence
  $alpha≽beta$ by Lemma @lem:signed-column-sum-tabloid-dominance, completing the
  proof.
]

#theorem[
  Let $F$ be an arbitrary field of characteristic $p>0$. For a partition
  $alpha$, we have
  $
    Z_alpha slash (Z_alpha inter Z_alpha^perp)≠0 arrow.l.r.double
    alpha "is" p"-regular".
  $
  #source(790)
  For two $p$-regular partitions $alpha$ and $beta$, we have
  $
    Z_alpha slash (Z_alpha inter Z_alpha^perp)
    ≅ Z_beta slash (Z_beta inter Z_beta^perp) arrow.l.r.double alpha=beta.
  $
  The modules
  $ {Z_alpha slash (Z_alpha inter Z_alpha^perp):alpha p"-regular"} $
  are absolutely simple, and form a basic set of simple $F S_n$-modules.
]<th:modular-specht-complete-simple-modules>

#proof[
  The first statement is Corollary @cor:specht-radical-quotient-p-regular. For
  the second statement, assume we have
  $
    Z_alpha slash (Z_alpha inter Z_alpha^perp)
    ≅ Z_beta slash (Z_beta inter Z_beta^perp)
  $
  for $p$-regular partitions $alpha$ and $beta$. Since
  $Z_alpha slash (Z_alpha inter Z_alpha^perp)$ and
  $Z_beta slash (Z_beta inter Z_beta^perp)$ are submodules of
  $M_alpha slash (Z_alpha inter Z_alpha^perp)$ and
  $M_beta slash (Z_beta inter Z_beta^perp)$, respectively, we can apply Lemma
  @lem:p-regular-specht-quotient-dominance and obtain $alpha≽beta$ and
  $beta≽alpha$. Then $alpha=beta$, and the second statement is proved.

  Now let $E supset F$ be a splitting field for $S_n$. By Theorem
  @th:james-specht-submodule-quotient and the first part of the proof, the
  modules
  $ {Z_alpha^E slash (Z_alpha^E inter (Z_alpha^E)^perp):alpha p"-regular"} $
  <eq:modular-specht-splitting-field-basic-set>
  are simple $E S_n$-modules, and no two of them are isomorphic. By
  @prop:p-regular-class-partition-count and @i:cor:brauer-number-simple-modules,
  it follows that the modules @eq:modular-specht-splitting-field-basic-set form
  a basic set of simple $E S_n$-modules. It is now a standard argument to show
  that the modules
  ${Z_alpha slash (Z_alpha inter Z_alpha^perp):alpha p"-regular"}$ form a basic
  set of simple $F S_n$-modules. Let $V$ be an arbitrary simple $F S_n$-module.
  Then
  $ "Hom"_(E S_n) (V^E,(Z_alpha slash (Z_alpha inter Z_alpha^perp))^E)≠0 $
  for some $p$-regular partition $alpha$, because the modules in
  @eq:modular-specht-splitting-field-basic-set form a basic set. Then
  $ "Hom"_(F S_n) (V,Z_alpha slash (Z_alpha inter Z_alpha^perp))≠0 $
  by @i:eq:hom-field-extension, and hence
  $V ≅ Z_alpha slash (Z_alpha inter Z_alpha^perp)$, since
  $Z_alpha slash (Z_alpha inter Z_alpha^perp)$ is an absolutely simple
  $F S_n$-module, by @th:james-specht-submodule-quotient and the first part of
  the proof. This fact, together with what has been shown, completes the proof
  of the theorem.
]

=== Solomon's Theorem and the Irreducible Characters of $S_n$
<ss:solomon-symmetric-group-characters>

Let $G$ be a finite group. As usual, we let $"ch" QQ G$ denote the subring of
$"ch" G$ generated by characters afforded by $QQ G$-modules. We shall denote by
$"ch"' QQ G$ the subring of $"ch" G$ generated by the set of rational-valued
characters; then we have
#source(791)
$ "ch" QQ G≤"ch"' QQ G≤"ch" G. $
In this subsection, we shall prove a theorem of Solomon~@bib:Solomon1974 on the
relation between $"ch"' QQ G$ and the $ZZ$-submodules of $"ch"' QQ G$ generated
by permutation characters defined by certain families of subgroups, for an
arbitrary finite group $G$. This result has several applications, including a
new proof of an extension to $"ch"' QQ G$ of the #idx(
  "Artin Induction Theorem",
)Artin Induction Theorem @i:th:artin-induction-explicit-coefficients, and a
theorem of Frobenius on the characters of the symmetric group $S_n$. In
§~@ss:hecke-sign-steinberg, it was shown how Frobenius's theorem can be used to
decompose $(1_B)^G$, for the groups $G=GL_n lr((F_q))$.

We begin with some general considerations. Let $G$ be a finite group, and let
$A$ be a mapping from $G$ to the set of subgroups of $G$ such that the following
conditions are satisfied:
#case-list(
  numbering: "(i)",
  [#case[$x in A(x)$;]<case:solomon-subgroup-map-extensive>],
  [#case[$y in A(x) arrow.r.double A(y)≤A(x)$; and]
    <case:solomon-subgroup-map-monotone>],
  [#case[$attach(A(x), tl: y)=A(attach(x, tl: y))$,]
    <case:solomon-subgroup-map-equivariant>],
)
for all $x,y in G$. Let $cal(A)$ denote the family of subgroups ${A(x):x in G}$.

A good example to keep in mind is the mapping $A$ that assigns to each $x in G$
the cyclic group $chevron.l x chevron.r$ generated by $x$. It is easily verified
that the mapping $A:x arrow A(x)=chevron.l x chevron.r$ satisfies the axioms.
The family of subgroups $cal(A)$, in this case, is the family of all cyclic
subgroups of $G$.

Returning to a general mapping $A$ satisfying parts~#{
  [@case:solomon-subgroup-map-extensive]
}–@case:solomon-subgroup-map-equivariant, we define an equivalence relation
$∼_A$ on $G$, setting $x∼_A y$ whenever $A(x)=_G A(y)$, where $=_G$, as usual,
denotes conjugacy in $G$. The equivalence classes relative to $∼_A$ are called
_$A$-classes_, and we let $"ch"_(cal(A)) G$ denote the subring of $"ch"' QQ G$
consisting of virtual rational valued characters that are constant on the
$A$-classes, where $"ch"' QQ G$ is the ring of rational-valued characters of
$G$.

We next define another $ZZ$-submodule of $"ch"' QQ G$:
$ P(G,cal(A))=lr({sum_(x in G) ZZ(1_(A(x)))^G}). $
Now let ${chevron.l x_1 chevron.r,dots,chevron.l x_t chevron.r}$ be a set of
representative of the conjugacy classes of cyclic subgroups of $G$. Let
$frak(G)=upright("Gal")(QQ(epsilon) slash QQ)$, where $epsilon$ is a primitive
$n$-th root of $1$, $n=|G|$. Then $frak(G)$ permutes the set $X="Irr" G$
consisting of the absolutely irreducible characters of $G$, and also permutes
the set $Y$ consisting of $G$-conjugacy classes (see
§~@i:ss:witt-berman-induction). By @i:th:brauer-permutation-lemma and the proof
of @i:cor:brauer-conjugacy-orbits, these permutation actions of $frak(G)$ both
have the same number of orbits, and this number is equal to the number $t$ of
conjugacy classes of cyclic subgroups, by Exercise
@i:exc:rational-simple-modules-cyclic-subgroups. Let ${X_1,dots,X_t}$ and
${Y_1,dots,Y_t}$ denote the $frak(G)$-orbits on the sets $X="Irr" G$ and $Y$,
respectively, and choose notation so that the $G$-conjugacy class $frak(C)_i$
containing $x_i$ belongs to $Y_i$, for $1≤i≤t$. Let
$ a_i=|X_i|, quad b_i=|Y_i|, quad "for" 1≤i≤t, $
#source(792)
and set
$ v=(a_1 dots a_t)^(-1)b_1 dots b_t. $

#theorem(title: [Solomon~@bib:Solomon1974])[
  #idx("Solomon's Theorem")
  Let $G$ be a finite group, and let ${A(x):x in G}$ be a family of subgroups
  satisfying the conditions
  @case:solomon-subgroup-map-extensive–@case:solomon-subgroup-map-equivariant.
  Then we have:
  #case-list(
    numbering: "(i)",
    [#case[
      $P(G,cal(A)) subset.eq "ch"_(cal(A)) G$, and the index
      $|"ch"_(cal(A)) G:P(G,cal(A))|$ is finite.
    ]<case:solomon-permutation-character-finite-index>],
    [#case[
      The exponent of the quotient group $("ch"_(cal(A)) G) slash P(G,cal(A))$
      divides $|G|$.
    ]<case:solomon-permutation-character-quotient-exponent>],
    [#case[
      Assume, for all $x,y in G$, that $A(x)=_G A(y)$ implies
      $chevron.l x chevron.r=_G chevron.l y chevron.r$. Then $P(G,cal(A))$ is of
      finite index in $"ch"' QQ G$, and we have
      $
        |"ch"' QQ G:P(G,cal(A))|^2
        =v product_(i=1)^t |N_i:A_i|^2 |C_i|^(-1),
      $
      where
      $
        A_i=A(x_i), quad N_i=N_G lr((A_i)), quad C_i=C_G lr((x_i)),
        quad 1≤i≤t.
      $
    ]<case:solomon-permutation-character-index-formula>],
  )
]<th:solomon-subgroup-permutation-character-induction>

#proof[
  Parts~@case:solomon-permutation-character-finite-index and
  @case:solomon-permutation-character-quotient-exponent. Let $H≤G$. It is clear
  that, for all $x in G$,
  $ |H|(1_H)^G lr((x))="card"{g in G:attach(x, tl: g)=g x g^(-1) in H}. $
  Suppose $x∼_A y$; then $A(x)=attach(A(y), tl: g)$ for some $g in G$. By the
  axioms
  @case:solomon-subgroup-map-extensive–@case:solomon-subgroup-map-equivariant,
  we obtain, for each $z in G$,
  $
    attach(x, tl: h) in A(z)
    arrow.l.r.double attach(A(x), tl: h)≤A(z)
    arrow.l.r.double attach(A(y), tl: h g)≤A(z)
    arrow.l.r.double attach(y, tl: h g) in A(z),
  $
  for all $h in G$. It follows that
  $
    (1_(A(z)))^G lr((x))=(1_(A(z)))^G lr((attach(y, tl: g)))
    =(1_(A(z)))^G lr((y)),
  $
  and we have proved that $P(G,cal(A)) subset.eq "ch"_(cal(A)) G$.

  We next observe that if $chevron.l x chevron.r=_G chevron.l y chevron.r$, then
  $A(x)=_G A(y)$ by
  @case:solomon-subgroup-map-extensive–@case:solomon-subgroup-map-equivariant,
  and hence $x∼_A y$. Therefore we may choose a subset of ${x_1,dots,x_t}$ as
  representatives of the $A$-classes. By renumbering, we may assume that
  ${x_1,dots,x_s}$ is a cross section of the $A$-classes, and that
  $ A(x_i)≤_G A(x_j) arrow.r.double i≤j, quad "for" 1≤i,j≤s. $
  Let us set
  $ alpha_(k i)=(1_(A(x_k)))^G lr((x_i)), quad 1≤i,k≤s; $
  then we have
  $ alpha_(k i)=|G||frak(C)_i inter A(x_k)||A(x_k)|^(-1)|frak(C)_i|^(-1), $
  by Exercise @i:exc:induced-character-centralizer.

  #source(793)
  Suppose $alpha_(k i)≠0$. Then $frak(C)_i inter A(x_k)≠nothing$, so
  $attach(x_i, tl: y) in A(x_k)$ for some $y in G$. Then
  $attach(A(x_i), tl: y)≤A(x_k)$ by the axioms
  @case:solomon-subgroup-map-extensive–@case:solomon-subgroup-map-equivariant,
  and hence $i≤k$. Therefore the $s times s$ matrix $(alpha_(k i))$ is
  triangular. If $attach(x_i, tl: y) in A(x_i)$ for some $y in G$, then
  $attach(A(x_i), tl: y)≤A(x_i)$, and hence $y in N_i=N_G lr((A(x_i)))$.
  Conversely, if $y in N_i$, then $attach(x_i, tl: y)$ belongs to
  $attach(A(x_i), tl: y)=A(x_i)$. This shows that the diagonal elements of the
  matrix $(alpha_(k i))$ are given by
  $ alpha_(i i)=|N_i:A_i|, quad 1≤i≤s. $
  <eq:solomon-permutation-character-diagonal>
  Now let $frak(X)_i$ be the $A$-class of $x_i$, for $1≤i≤s$, and let $lambda_i$
  denote its characteristic function, so $lambda_i lr((x))=1$ if $x∼_A x_i$ and
  is zero otherwise. Then we obtain
  $
    (1_(A(x_j)))^G & =sum_(i=1)^s (1_(A(x_j)))^G lr((x_i))lambda_i
                     =sum_(i=1)^s alpha_(j i)lambda_i \
                   & =sum_(i=1)^(j-1) alpha_(j i)lambda_i+alpha_(j j)lambda_j
                     in P(G,cal(A)),
  $
  using the fact that the matrix $(alpha_(j i))$ is triangular. Since
  $alpha_(j j)=|N_j:A_j|$ by @eq:solomon-permutation-character-diagonal, for
  $1≤j≤s$, it follows by induction that#ed-note[
    The commuting right action of $N_G lr((A_j)) slash A_j$ on $G slash A_j$ is
    free, hence free on the $x_i$-fixed cosets. Thus $alpha_(j j)$ divides every
    $alpha_(j i)$. Multiply the triangular relation by $frac(|G|, alpha_(j j))$
    and subtract the earlier terms
    $sum_(i<j) frac(alpha_(j i), alpha_(j j))|G|lambda_i$ to obtain the
    induction.
  ]
  $ |G|lambda_j in P(G,cal(A)) quad "for" 1≤j≤s. $
  If $phi in "ch"_(cal(A)) G$, then $phi$ is constant on the $A$-classes, so
  $ |G|phi=sum_(j=1)^s phi(x_j)|G|lambda_j in P(G,cal(A)), $
  completing the proof of parts~@case:solomon-permutation-character-finite-index
  and @case:solomon-permutation-character-quotient-exponent.

  Part~@case:solomon-permutation-character-index-formula. By the hypothesis of
  part~@case:solomon-permutation-character-index-formula, we have $s=t$.
  Moreover, $P(G,cal(A))$ is of finite index in $"ch"' QQ G$, by
  part~@case:solomon-permutation-character-finite-index. Indeed let $xi_j$
  denote the sum of the characters in the $frak(G)$-orbit $X_j$, for $1≤j≤t$.
  Then ${xi_1,dots,xi_t}$ is a $ZZ$-basis of $"ch"' QQ G$, and
  $"ch"' QQ G="ch"_(cal(A)) G$, by the proof of
  @i:th:field-character-conjugacy-classes. For each $k$, $1≤k≤t$, let
  $frak(Y)_k$ be the set consisting of all elements of $G$ whose conjugacy class
  belongs to the $frak(G)$-orbit $Y_k$. If $x in frak(C)_k$, then
  $xi_j lr((x))=xi_j lr((x_k))$, for $1≤j≤t$, by
  @i:th:field-character-conjugacy-classes. We also note that $frak(Y)_k$ is the
  union of $b_k$ conjugacy classes, all of cardinality $|G:C_k|$. On the other
  hand, each character $xi_j$ is the sum of $a_j$ distinct absolutely
  irreducible characters, for $1≤j≤t$. By the orthogonality relations
  @i:prop:class-function-orthonormal-basis, we obtain
  $
    a_i delta_(i j)=(xi_i,xi_j)
    =|G|^(-1)sum_(x in G) xi_i lr((x))xi_j lr((x^(-1)))
    =sum_(k=1)^t b_k |C_k|^(-1)xi_i lr((x_k))xi_j lr((x_k)).
  $
  <eq:galois-character-orbit-sum-orthogonality>
  Here we have used the fact that $xi_j lr((x^(-1)))=xi_j lr((x))$, since $xi_j$
  is a rational-valued character. Next, define $t times t$ matrices
  $
    upright(bold(A))=(alpha_(i j)), quad upright(bold(B))=(xi_i lr((x_j))),
    quad upright(bold(D))=(a_i delta_(i j)),
    quad upright(bold(E))=(b_i |C_i|^(-1)delta_(i j)),
  $
  #source(794)
  where $alpha_(i j)=(1_(A(x_i)))^G lr((x_j))$ as in
  parts~@case:solomon-permutation-character-finite-index and
  @case:solomon-permutation-character-quotient-exponent. By
  @eq:galois-character-orbit-sum-orthogonality, we have
  $
    upright(bold(D))=upright(bold(B))upright(bold(E))
    attach(upright(bold(B)), tl: t).
  $
  Taking determinants, we obtain
  $
    v^(-1) product_(i=1)^t |C_i|=(det upright(bold(B)))^2,
    quad "where" v=(product a_i)^(-1)(product b_i) quad "as above".
  $
  <eq:character-orbit-sum-determinant>
  Since $(1_(A(x_k)))^G in "ch"' QQ G$, we may write
  $
    (1_(A(x_k)))^G=sum_(j=1)^t c_(k j)xi_j,
    quad "with" c_(k j) in ZZ, quad 1≤j,k≤t.
  $
  Using the facts that ${(1_(A(x_1)))^G,dots,(1_(A(x_t)))^G}$ and
  ${xi_1,dots,xi_t}$ are $ZZ$-bases for $P(G,cal(A))$ and $"ch"' QQ G$,
  respectively, we obtain
  $ |"ch"' QQ G:P(G,cal(A))|=abs(det upright(bold(C))), $
  where $upright(bold(C))=(c_(k j))$ as above. We also have
  $
    abs(det upright(bold(A)))
    =abs(det upright(bold(C)))abs(det upright(bold(B)))
    =|"ch"' QQ G:P(G,cal(A))|abs(det upright(bold(B))),
  $
  <eq:permutation-character-index-change-of-basis>
  by the formula expressing the characters $(1_(A(x_k)))^G$ in terms of the
  ${xi_j}$ and the definition of the matrices $upright(bold(A))$ and
  $upright(bold(B))$. Since $upright(bold(A))$ is a triangular matrix whose
  diagonal entries are ${|N_i:A_i|:1≤i≤t}$, by
  @eq:solomon-permutation-character-diagonal, we obtain the desired formula for
  the index $|"ch"' QQ G:P(G,cal(A))|$ by comparing
  @eq:character-orbit-sum-determinant and
  @eq:permutation-character-index-change-of-basis. This completes the proof of
  the theorem.
]

#remark(numbered: false)[
  In case $A(x)=chevron.l x chevron.r$ for $x in G$,
  parts~@case:solomon-permutation-character-finite-index and
  @case:solomon-permutation-character-quotient-exponent of the preceding theorem
  give another proof of the #idx("Artin Induction Theorem")Artin Induction
  Theorem @i:th:artin-induction-explicit-coefficients. For yet another proof,
  see @bib:CurtisReiner1962[CR] (39.1).
]<rem:solomon-artin-induction-cyclic-subgroups>

We conclude this section with the following application of Solomon's Theorem to
the characters of $S_n$. We recall from the discussion following Lemma
@lem:young-tabloid-permutation-module that the Young subgroups of type $alpha$
are the row subgroups ${R(T)}$, as $T$ ranges over the set of $alpha$-tableaux,
and that they form a conjugacy class of subgroups of $S_n$, for each partition
$alpha$. We now have:

#theorem(title: [Frobenius])[
  #idx("Frobenius' Theorem")
  Let $cal(A)$ be the family of Young subgroups of $S_n$ of type $alpha$, for
  all partitions $alpha$. Then
  $ "ch" QQ S_n=P(S_n,cal(A)). $
]<th:frobenius-young-permutation-character-basis>

#proof[
  (Solomon~@bib:Solomon1974.) If $x in S_n$, let $alpha_i=alpha_i lr((x))$
  denote the number of $chevron.l x chevron.r$-orbits
  #source(795)
  in $Omega={1,dots,n}$ of cardinality $i$, and write the cycle multiplicity
  vector as
  $ alpha=alpha(x)=(alpha_1 lr((x)),dots,alpha_n lr((x))). $
  <eq:symmetric-group-cycle-count-partition>
  Let $f(alpha)$ and $g(alpha)$ be the positive integers defined by
  $
    f(alpha)=alpha_1! dots alpha_n!,
    quad g(alpha)=1^(alpha_1)2^(alpha_2) dots n^(alpha_n),
  $
  where we set $alpha_i! =1$ if $alpha_i=0$. Let $A(x)$ be the subgroup of $S_n$
  defined by
  $ A(x)={y in S_n:y Delta_i=Delta_i "for each" i} $
  where ${Delta_i}$ are the $chevron.l x chevron.r$-orbits in $Omega$. Then
  $A(x)$ is clearly a Young subgroup of type $1^(alpha_1)dots n^(alpha_n)$, the
  decreasing partition encoded by the multiplicity vector in
  @eq:symmetric-group-cycle-count-partition, and the map $x arrow A(x)$
  satisfies the axioms
  @case:solomon-subgroup-map-extensive–@case:solomon-subgroup-map-equivariant.
  We also have $A(x)=_G A(y) arrow.r.double alpha(x)=alpha(y)$, and hence
  $
    A(x)=_G A(y) arrow.r.double
    chevron.l x chevron.r=_G chevron.l y chevron.r.
  $
  By Theorem @th:rational-specht-complete-simple-modules, we have
  $"ch"' QQ G="ch" QQ G$. Thus we may apply Theorem
  @th:solomon-subgroup-permutation-character-induction to calculate the index
  $ |"ch" QQ S_n:P(S_n,cal(A))|, $
  where $cal(A)$ is the family of subgroups ${A(x):x in S_n}$, and Frobenius's
  Theorem will follow if we can show that the index is $1$.

  We first compute $|N(A(x)):A(x)|$, where $N(A(x))=N_(S_n) lr((A(x)))$. If
  $y in N(A(x))$ then
  $ x y Delta_i=y y^(-1)x y Delta_i=y Delta_i $
  for each $chevron.l x chevron.r$-orbit $Delta_i subset.eq Omega$, since
  $y^(-1)x y in A(x)$. Then $y Delta_i$ is stable under the action of $x$ and is
  an $chevron.l x chevron.r$-orbit. Moreover, $|y Delta_i|=|Delta_i|$ for each
  $i$, and hence $y$ permutes the set of $alpha_i$ orbits of cardinality $i$,
  for each $i$. Therefore we obtain a homomorphism
  $
    theta:N(A(x)) arrow S_(alpha_1) times S_(alpha_2)
    times dots times S_(alpha_n).
  $
  If $Delta={k_1,dots,k_i}$ and $Delta'={k'_1,dots,k'_i}$ are two $x$-orbits of
  cardinality $i$, then we may choose $y in S_n$ that interchanges $k_j$ and
  $k'_j$ for $j=1,dots,i$ and fixes the remaining elements of $Omega$. Then
  $y in N(A(x))$, and $y$ interchanges $Delta$ and $Delta'$ and fixes the
  remaining orbits. Since the symmetric groups ${S_(alpha_j)}$ are generated by
  transpositions, it follows that the homomorphism $theta$ is surjective. Its
  kernel consists of the elements $y in S_n$ such that $y Delta_i=Delta_i$ for
  each $i$, and this is the subgroup $A(x)$. We have proved that
  $ |N(A(x)):A(x)|=f(alpha). $

  #source(796)
  Letting $C(x)$ denote the centralizer of $x$ in $S_n$, it is easily proved
  that
  $ |C(x)|=f(alpha)g(alpha). $
  Before we can apply Theorem
  @th:solomon-subgroup-permutation-character-induction, we calculate the integer
  $v=(a_1 dots a_t)^(-1)b_1 dots b_t$, where $a_i=|X_i|$ and $b_i=|Y_i|$ and
  $X_i$ is a $frak(G)$-orbit in $"Irr" G$ and $Y_i$ is a $frak(G)$-orbit in the
  conjugacy classes of $S_n$. But in the case of $S_n$, we have $a_i=1$ for all
  $i$, since the irreducible characters are rational valued (see Theorem
  @th:rational-specht-complete-simple-modules or §~@i:ss:witt-berman-induction)
  and it is easily checked that the cardinalities $b_i=|Y_i|$ are all $1$. Thus
  $v=1$, and Solomon's Theorem
  @th:solomon-subgroup-permutation-character-induction implies that
  $ |"ch" QQ S_n:P(S_n,cal(A))|^2=product_alpha f(alpha)g(alpha)^(-1), $
  where the product is taken over all $n$-tuples $alpha=(alpha_1,dots,alpha_n)$
  of nonnegative integers such that $alpha_1+2alpha_2+dots+n alpha_n=n$. The
  Frobenius Theorem, that $"ch" QQ S_n=P(S_n,cal(A))$, is a consequence of the
  following combinational result.

  #lemma[$product_alpha f(alpha)=product_alpha g(alpha).$]
  <lem:partition-factorial-power-product>

  #proof[
    For $n in ZZ$, let $Lambda(n)$ be the set of partitions of $n$, with the
    conventions that $Lambda(0)$ consists of a single partition and $Lambda(n)$
    is empty if $n<0$. Let
    $ Lambda=union.big_(n in ZZ) Lambda(n). $
    If $lambda in Lambda$ and $i$ is a positive integer, we let
    $alpha_i lr((lambda))$ be the number of parts of $lambda$ of cardinality
    equal to $i$.

    Let $j$ be a positive integer, which will remain fixed throughout the rest
    of the discussion. If $lambda in Lambda$, let $S_j lr((lambda))$ be the set
    of partitions in $Lambda$ obtained by deleting from $lambda$ any positive
    integral number of parts of size $j$. If $lambda in Lambda(n)$ and
    $mu in S_j lr((lambda))$, then $mu in Lambda(n-j k)$ for some $k=1,2,dots$.
    Conversely, if $mu in Lambda(n-j k)$, then by adjoining $k$-parts of size
    $j$ to $mu$, we obtain an element of $Lambda(n)$. This shows that
    $
      union.big_(lambda in Lambda(n)) S_j lr((lambda))
      =union.big_(k≥1) Lambda(n-j k).
    $
    Now let $lambda,lambda' in Lambda(n)$ and assume that
    $S_j lr((lambda)) inter S_j lr((lambda'))≠nothing$. Let
    $mu in S_j lr((lambda)) inter S_j lr((lambda'))$. Then
    $alpha_k lr((lambda))=alpha_k lr((lambda'))=alpha_k lr((mu))$ for $k≠j$.
    Since $lambda$ and $lambda'$ are both partitions of $n$, this forces
    $alpha_j lr((lambda))=alpha_j lr((lambda'))$, and hence $lambda=lambda'$.
    Thus we have
    $
      sum_(lambda in Lambda(n)) |S_j lr((lambda))|
      =sum_(k≥1) |Lambda(n-j k)|.
    $
    <eq:partition-fixed-size-deletion-count>
    Now let $lambda in Lambda$ and let $T_j lr((lambda))$ be the set of
    partitions obtained from $lambda$ by omitting $j$ parts of the same size. If
    $alpha_k lr((lambda))<j$ for all $k=1,2,dots$, then $T_j lr((lambda))$ is
    empty. If $lambda in Lambda(n)$ and $mu in T_j lr((lambda))$, then
    $mu in Lambda(n-j k)$ for some $k=1,2,dots$. Conversely, if
    $mu in Lambda(n-j k)$,
    #source(797)
    we can adjoin $j$ parts of size $k$ to $mu$, to obtain an element of
    $Lambda(n)$. Therefore
    $
      union.big_(lambda in Lambda(n)) T_j lr((lambda))
      =union.big_(k≥1) Lambda(n-j k).
    $
    Now suppose $T_j lr((lambda)) inter T_j lr((lambda'))≠nothing$ for
    $lambda,lambda' in Lambda(n)$, and let
    $mu in T_j lr((lambda)) inter T_j lr((lambda'))$. Then there exist positive
    integers $i$ and $i'$ such that
    $
      alpha_i lr((mu))=alpha_i lr((lambda))-j, quad
      alpha_k lr((mu))=alpha_k lr((lambda)) quad "for" k≠i \
      alpha_(i') lr((mu))=alpha_(i') lr((lambda'))-j, quad
      alpha_k lr((mu))=alpha_k lr((lambda')) quad "for" k≠i'.
    $
    Since $lambda$ and $lambda'$ are both partitions of the same integer, we
    have
    $
      i j+sum_(k≥1) k alpha_k lr((mu)) & =sum_(k≥1) k alpha_k lr((lambda))
                                         =sum_(k≥1) k alpha_k lr((lambda')) \
                                       & =i'j+sum_(k≥1) k alpha_k lr((mu)).
    $
    Then $i=i'$ and $lambda=lambda'$. This proves that
    $
      sum_(lambda in Lambda(n)) |T_j lr((lambda))|
      =sum_(k≥1) |Lambda(n-j k)|.
    $
    <eq:partition-fixed-multiplicity-deletion-count>
    Upon comparing @eq:partition-fixed-multiplicity-deletion-count and
    @eq:partition-fixed-size-deletion-count, we obtain
    $
      sum_(lambda in Lambda(n)) |S_j lr((lambda))|
      =sum_(lambda in Lambda(n)) |T_j lr((lambda))|.
    $
    This implies that
    $
      sum_(lambda in Lambda(n)) alpha_j lr((lambda))
      =sum_(lambda in Lambda(n)) sum_(i:alpha_i lr((lambda))≥j) 1.
    $
    <eq:partition-size-multiplicity-double-count>
    Since this holds for $j=1,2,dots$, the assertion of the lemma follows. This
    is shown by noting that the left side of
    @eq:partition-size-multiplicity-double-count, suitably interpreted, is the
    contribution of $j$ to $product g(alpha)$, while the right side is the
    contribution of $j$ to $product f(alpha)$. This completes the proof of
    @lem:partition-factorial-power-product.
  ]
]

By Theorem @th:rational-specht-complete-simple-modules, every irreducible
character afforded by a simple $CC S_n$-module belongs to $"ch" QQ S_n$. Since
$S_n$ is a Coxeter group of type $A_(n-1)$, and the Young subgroups of $S_n$
coincide with the parabolic subgroups defined by a Coxeter system of type
$A_(n-1)$ in $S_n$, we obtain the following result (see the remark following
@prop:parabolic-permutation-character-isometry).

#corollary[
  Let $(W,S)$ be a finite Coxeter system of type $A_n$, and let
  $zeta in "Irr" W$. Then there exist integers ${n_J:J subset.eq S}$ such that
  $ zeta=sum_(J subset.eq S) n_J (1_(W_J))^W. $
]<cor:type-a-parabolic-permutation-character-generation>

#source(798)
For related results concerning other types of Coxeter groups, see
Mayer~@bib:Mayer1975, Solomon~@bib:Solomon1974, and Tokuyama~@bib:Tokuyama1984.
