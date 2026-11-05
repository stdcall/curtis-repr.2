#import "main-defs.typ": *
#import "statements.typ": *

== Algebras of Finite Representation Type
<sec:roiter-brauer-thrall-theorem>

In this section, $K$ denotes an arbitrary field, and $A$ a f.d. $K$-algebra. Our
objective is to prove a theorem of Roiter~@bib:Roiter1968a, which asserts that
if the composition lengths (or dimensions over $K$) of the f.g. indecomposable
left $A$-modules are bounded, then the number of isomorphism classes of
indecomposable left $A$-modules is finite. This result settled the long-standing
conjecture of Brauer–Thrall for f.d. $K$-algebras. The corresponding result was
proved by Auslander~@bib:Auslander1974a for artinian rings. The fact that the
Brauer–Thrall conjecture holds for group algebras of finite groups was proved
earlier by D.~Higman~@bib:Higman1954 (see @bib:CurtisReiner1962[CR] §64, and
§~@sec:cyclic-defect-blocks above.)
#idx(
  "Roiter's Theorem",
  target: [@th:roiter-yamagata-finite-representation-type],
)
#idx(
  "Brauer-Thrall conjecture",
  target: [@th:roiter-yamagata-finite-representation-type],
)

We shall give a new proof of Roiter's theorem for f.d. $K$-algebras, which is
#source(847)due to Yamagata~@bib:Yamagata1978, and is based on the theory of
$A R$-sequences (from §~@ss:auslander-reiten-finite-dimensional-algebras).
Yamagata's approach also describes a procedure for constructing indecomposable
left $A$-modules from the simple modules, using the theory of $A R$-sequences,
for f.d. $K$-algebras $A$ of finite representation type. The result is not as
explicit, however, as the construction of the indecomposable $K G$-modules in a
block with a cyclic defect group, by Janusz~@bib:Janusz1969 and
Kupisch~@bib:Kupisch1968, @bib:Kupisch1969 (see also Feit~@bib:Feit1982, Chapter
VII). We remark also that Yamagata's theorems are all established for artinian
rings, while our approach is restricted to f.d. $K$-algebras, since we have only
proved the existence of $A R$-sequences in that case (in
§~@ss:auslander-reiten-finite-dimensional-algebras).

We begin with some preliminary remarks. It is assumed that all left $A$-modules
$M$ under consideration are f.g., over the given f.d. $K$-algebra $A$. The
composition length of $M$ is denoted by $c(M)$, and its isomorphism class by
$(M)$.
#nidx("$lambda(M)=c(M)$", "composition length of $M$")
The set of isomorphism classes of f.g. indecomposable $A$-modules is denoted by
$upright("Ind") A$. The algebra $A$ is said to have #idx(
  "Finite representation type",
)_finite representation type_ if $upright("Ind") A$ is a finite set, and
_bounded representation type_ if the set of composition lengths
${c(M):(M) in upright("Ind") A}$ is bounded.

Let $(M) in upright("Ind") A$. We recall from §~@sec:auslander-reiten-sequences
that an $A R$-sequence for $M$ (or _Auslander–Reiten sequence_) is a nonsplit
ses
$ 0 arrow N arrow E arrow^f M arrow 0, $
<eq:almost-split-sequence-recalled>
#idx("AR-sequence", target: [@eq:almost-split-sequence-recalled])
with $N$ indecomposable, and having the universal mapping property that each
homomorphism of $A$-modules $g:X arrow M$, which is not a split surjection,
factors through $E$. The existence and uniqueness of $A R$-sequences, for all
nonprojective indecomposable modules over a f.d. $K$-algebra $A$, was proved in
§~@ss:auslander-reiten-finite-dimensional-algebras.

The preceding discussion does not apply to a projective indecomposable
$A$-module $M$. In this case, however, $rad M$ is the unique maximal submodule
of $M$, and the inclusion map $f:rad M arrow M$ has the universal property that
each homomorphism of $A$-modules $g:X arrow M$, which is not a split surjection,
factors through $rad M$.

Thus we are led to define an _almost-split homomorphism_ $(E,f)$, for an
indecomposable $A$-module $M$, to be a homomorphism of $A$-modules $f:E arrow M$
such that either
#case-list(
  numbering: "(a)",
  [#case[
    $M$ is not projective and
    $ 0 arrow ker f arrow E arrow^f M arrow 0 $
    is an $A R$-sequence for $M$, or
  ]<case:almost-split-nonprojective-homomorphism>],
  [#case[
    $M$ is projective, $E=rad M$, and $f$ is the inclusion map.
  ]<case:almost-split-projective-homomorphism>],
)
As we have pointed out, each almost-split homomorphism $f:E arrow M$ has the
universal property that homomorphisms $g:X arrow M$, which are not split
surjections, factor through $E$. In particular, $E$ is uniquely determined, up
to isomorphism, in both cases.

Now let ${M_i:i in I}$ be a family of indecomposable left $A$-modules, possibly
with repetitions, indexed by a set $I$. The family is called _noetherian_ if for
each #source(848)sequence of nonisomorphisms
$
  M_(i_1) arrow^(f_(i_1)) M_(i_2) arrow^(f_(i_2)) M_(i_3) arrow dots
  quad (i_j in I),
$
there exists an integer $n$ such that $f_(i_n) dots f_(i_2) f_(i_1)=0$. The
family is called _conoetherian_ if, for each sequence of nonisomorphisms
$
  dots arrow M_(j_3) arrow^(g_(j_2)) M_(j_2) arrow^(g_(j_1)) M_(j_1)
  quad (j_i in I),
$
there exists an integer $m>0$ such that $g_(j_1) g_(j_2) dots g_(j_m)=0$.

The first result holds for families of modules over artinian rings.

#lemma(title: [Harada–Sai~@bib:Harada1970])[
  Let $A$ be an artinian ring, and ${M_i:i in I}$ a family of f.g.
  indecomposable left $A$-modules whose composition lengths are bounded above.
  Then the family ${M_i:i in I}$ is noetherian and conoetherian.
]<lem:harada-sai-bounded-length-families>

#proof[
  By hypothesis there exists an integer $N>0$ such that $c(M_i)<N$ for all
  $i in I$. Let us first consider a sequence of nonisomorphisms
  $ M_(i_1) arrow^(f_(i_1)) M_(i_2) arrow^(f_(i_2)) M_(i_3) arrow dots. $
  <eq:indecomposable-nonisomorphism-chain>
  Then any sequence of $N+1$ or more consecutive maps
  ${f_(i_p),dots,f_(i_(p+N))}$ contains at least one map with a nonzero kernel.
  Therefore, in order to prove the noetherian condition, it is sufficient to
  consider a sequence @eq:indecomposable-nonisomorphism-chain in which
  $ker f_(i_j)≠0$ for all $j$. This reduction is accomplished by taking a
  suitable subsequence of the index set in
  @eq:indecomposable-nonisomorphism-chain, and replacing the maps by products of
  consecutive ones. By a second reduction of this type, we may assume that the
  composition lengths ${c(M_(i_j))}$ of the modules occurring in
  @eq:indecomposable-nonisomorphism-chain are constant.

  In this situation, we shall prove that there exists an integer $n_0$ such that
  $f_(i_(n_0)) dots f_(i_1)=0$. This is a consequence of the following general
  argument. Consider a sequence of f.g. indecomposable modules ${M_i}$, all
  having the same composition length, and homomorphisms ${h_i}$,
  $ M_1 arrow^(h_1) M_2 arrow^(h_2) M_3 arrow dots $
  such that $ker h_i≠0$ for all $i$. Then there exists an integer $q>0$ such
  that $c(M_i)=q$ for all $i$. For the purposes of this argument, let
  $ Pi(i, j)=h_(j+i-1) dots h_(j+1) h_j, quad "for all" i "and" j. $
  We shall prove, by induction on $m$, that, for $0≤m≤q-1$, we have
  $ c(Pi(2^m, 1) M_1)≤q-m-1. $
  <eq:harada-sai-composite-length-bound>

  #source(849)
  We first note that $c(h_1(M_1))≤q-1$ since $ker h_1≠0$, which proves
  @eq:harada-sai-composite-length-bound in case $m=0$. Now assume that, for some
  $m$ with $0≤m≤q-2$, $c(Pi(2^m, 1) M_1)≤q-m-1$ for any sequence as above. Then
  $c(Pi(2^(m+1), 1) M_1)≤q-m-1$. If the inequality is strict, then
  @eq:harada-sai-composite-length-bound follows, since $q-m-2=q-(m+1)-1$. Thus
  we must rule out the possibility that $c(Pi(2^(m+1), 1) M_1)=q-m-1$. If this
  occurs, then the restriction of the map $Pi(2^m, 2^m+1)$ to
  $Pi(2^m, 1) M_1 subset.eq M_(2^m+1)$ is injective. On the other hand,
  $ c(Pi(2^m, 2^m+1) M_(2^m+1))≤q-m-1 $
  by the induction hypothesis, and we obtain
  $ Pi(2^m, 2^m+1) M_(2^m+1)=Pi(2^m, 2^m+1) Pi(2^m, 1) M_1 $
  by comparing composition lengths. It follows that
  $ M_(2^m+1)=Pi(2^m, 1) M_1 plus.o ker Pi(2^m, 2^m+1), $
  contrary to the assumption that the modules ${M_i}$ are indecomposable. This
  completes the proof of @eq:harada-sai-composite-length-bound. At $m=q-1$ the
  bound is zero. Hence the assertion that $f_(i_(n_0)) dots f_(i_1)=0$ for some
  $n_0$ follows from @eq:harada-sai-composite-length-bound. It follows that the
  family ${M_i:i in I}$ is noetherian.

  We next consider a sequence of nonisomorphisms
  $ dots arrow M_(j_3) arrow^(g_(j_2)) M_(j_2) arrow^(g_(j_1)) M_(j_1). $
  By the first part of the proof, it follows that for some block of consecutive
  terms, we have
  $ g_(j_r) dots g_(j_(r+s))=0. $
  This shows that the family is conoetherian, and completes the proof of the
  lemma.
]

For the rest of this section, we return to the situation where $A$ is a f.d.
$K$-algebra.

#lemma[
  Let $M$ be an indecomposable left $A$-module, and let $f:E arrow M$ be an
  almost split homomorphism. Let $E=plus.o.big_(i=1)^m E_i$, with each $E_i$
  indecomposable, and let $epsilon_i:E_i arrow E$ be the injection associated
  with the direct sum decomposition, for $1≤i≤m$. Then $f epsilon_i$ is not an
  isomorphism, for each $i$, $1≤i≤m$.
]<lem:almost-split-components-nonisomorphisms>

#proof[
  Suppose, to the contrary, that $f epsilon_i:E_i arrow M$ is an isomorphism.
  Then $f$ is surjective. Moreover, setting $g_i=f epsilon_i$,
  $epsilon_i g_i^(-1)$ is a map from $M arrow E$ such that
  $f epsilon_i g_i^(-1)$ is the identity map on $M$. Thus $f$ is a split
  surjection, which is impossible for an almost-split homomorphism $f$.
]

Now let $M$ be an arbitrary indecomposable $A$-module. We shall define, for
#source(850)each integer $n≥0$, a finite set $bold(E)_n lr((M))$ of isomorphism
classes of indecomposable modules, as follows:
#case-list(
  numbering: "(i)",
  keep-together: true,
  [#case[
    $bold(E)_0 lr((M))={(M)}$;
  ]<case:ar-predecessor-level-zero>],
  [#case[
    $(X) in bold(E)_(n+1) lr((M))$, for an indecomposable module $X$, if and
    only if there exists an almost-split homomorphism $f:E arrow Y$ such that
    $
      (Y) in bold(E)_n lr((M)) quad "and" X divides E.
      #box[#footnote[As usual, $X divides E$ means that $X$ is isomorphic to a
        direct summand of $E$.]]
    $
  ]<case:ar-predecessor-successor-level>],
)
The finiteness of the $bold(E)_n lr((M))$ follows from the fact that if
$f:E arrow Y$ is an almost split homomorphism, then $E$ is determined, up to
isomorphism, by $Y$.

The main theorem, which settles the Brauer–Thrall conjecture, is stated as
follows.

#theorem[
  #idx(
    "Yamagata's Theorem",
    target: [@th:roiter-yamagata-finite-representation-type],
  )
  Let $A$ be a f.d. $K$-algebra, and let ${S_1,dots,S_n}$ be a basic set of
  simple left $A$-modules. Then the following statements are equivalent.
  #case-list(
    numbering: "(i)",
    [#case[
      $A$ is of finite representation type.
    ]<case:roiter-finite-representation-type>],
    [#case[
      $A$ is of bounded representation type.
    ]<case:roiter-bounded-representation-type>],
    [#case[
      The family of f.g. indecomposable $A$-modules satisfies the noetherian and
      conoetherian conditions.
    ]<case:roiter-chain-termination>],
    [#case[
      There exists a positive integer $m$ such that
      $ upright("Ind") A=union.big_(1≤i≤n,0≤j≤m) bold(E)_j lr((S_i)). $
    ]<case:roiter-finite-almost-split-generation>],
  )
]<th:roiter-yamagata-finite-representation-type>

#proof[
  If $n=0$, then $A=0$. In this case all four statements hold, taking $m=1$ for
  the empty union. We may therefore assume $n>0$.

  The implication @case:roiter-finite-representation-type $==>$
  @case:roiter-bounded-representation-type is clear from the definitions. The
  implication @case:roiter-bounded-representation-type $==>$
  @case:roiter-chain-termination follows from
  Lemma~@lem:harada-sai-bounded-length-families, while the fact that
  @case:roiter-finite-almost-split-generation $==>$
  @case:roiter-finite-representation-type is a consequence of the finiteness of
  the sets $bold(E)_j lr((S_i))$, for all $i$ and $j$.

  Thus it is sufficient to prove that @case:roiter-chain-termination $==>$
  @case:roiter-finite-almost-split-generation. For each simple module $S_i$,
  $1≤i≤n$, and each integer $j≥1$, we shall define a finite set
  $bold(H)_j lr((S_i))$ consisting of nonisomorphisms $h_j:M_j arrow M_(j-1)$,
  where $(M_j)$ and $(M_(j-1))$ are certain isomorphism classes in
  $bold(E)_j lr((S_i))$ and $bold(E)_(j-1) lr((S_i))$, respectively. We first
  choose, for each $j$, a fixed set of representatives ${M_j}$ of the
  isomorphism classes in $bold(E)_j lr((S_i))$. For each module $M_(j-1)$, with
  $(M_(j-1)) in bold(E)_(j-1) lr((S_i))$, choose a fixed almost-split
  homomorphism $f_j:E_j arrow M_(j-1)$ and a decomposition
  $E_j=plus.o.big_(t=1)^r X_t$ into indecomposable summands, including
  repetitions. For each $t$, let $M_j$ be the fixed representative of $(X_t)$,
  choose an isomorphism $alpha_t:M_j arrow X_t$, and let
  $epsilon_t:X_t arrow E_j$ be the summand inclusion. Include the map
  $h_j=f_j epsilon_t alpha_t:M_j arrow M_(j-1)$ in $bold(H)_j lr((S_i))$ for
  every $t$. If two representative modules $M_j$ and $M_(j-1)$ are not related
  in this way, include the zero map $M_j arrow M_(j-1)$. The set
  $bold(H)_j lr((S_i))$ consists of all these maps, for all targets $M_(j-1)$
  and all summand copies in the chosen decompositions. Each map
  $h_j in bold(H)_j lr((S_i))$ is a nonisomorphism, by
  Lemma~@lem:almost-split-components-nonisomorphisms. Moreover,
  $bold(H)_j lr((S_i))$ is finite, since the sets $bold(E)_j lr((S_i))$ and
  $bold(E)_(j-1) lr((S_i))$ and each chosen decomposition are finite.
  #ed-note[The universal property factors a map through the whole direct sum; it
    does not allow one to prescribe which isomorphic summand supplies a nonzero
    component. A single chosen inclusion for an isomorphism class can therefore
    miss a nonzero factorization component.]

  We next let $A_(i,r)$, $r=1,2,dots$, denote the finite set consisting of all
  nonzero products ${h_1 dots h_r:h_j in bold(H)_j lr((S_i)),
    1≤j≤r, "and" h_1 dots h_r≠0}$. We also need to consider
  #source(851)
  the family $F_i$ consisting of the maps ${theta_(i,r):r=1,2,dots}$, where
  $theta_(i,r)$ is the map from $A_(i,r)$ to the power set of $A_(i,r+1)$ such
  that $theta_(i,r) lr((a_r))$ is the set of all nonzero products $a_r h_(r+1)$,
  with $h_(r+1) in bold(H)_(r+1) lr((S_i))$, for each element $a_r in A_(i,r)$.

  If, for some positive integer $r$, $A_(i,r)$ is empty, then it follows that
  $h_1 dots h_r=0$ for all elements $h_j in bold(H)_j lr((S_i))$, $1≤j≤r$. On
  the other hand, if all the sets $A_(i,r)$ are nonempty, then they provide an
  example of a _König graph_, according to the following definition.

  A _König graph_ ${A_r,F:r=0,1,2,dots}$ consists of a countable family of
  finite non-empty sets ${A_r}$ and a set of mappings
  $F={theta_r:r=0,1,2,dots}$, where each $theta_r$ is a map from $A_r$ to the
  power set of $A_(r+1)$. A _path_ in the graph is a finite or infinite sequence
  ${a_0,a_1,a_2,dots}$ such that $a_0 in A_0$, and
  $a_i in theta_(i-1) lr((a_(i-1)))$ for each $i≥1$. We have:

  #lemma(title: [Osofsky~@bib:Osofsky1966])[
    If the König graph ${A_r,F}$ has arbitrarily long paths, then it has a path
    of infinite length.
  ]<lem:konig-infinite-path>

  #proof(head: [Proof of @lem:konig-infinite-path.])[
    The result is known as König's Graph Theorem. Call an element $a_r in A_r$
    _special_ if there exist arbitrarily long paths containing $a_r$. For
    convenience, define another set $A_(-1)={a_(-1)}$, and define
    $theta_(-1) in F$ such that $theta_(-1) lr((a_(-1)))=A_0$. Then $a_(-1)$ is
    special, by hypothesis. Assume $a_r$ is special, for some $a_r in A_r$. If
    no element of the finite set $theta_r lr((a_r))$ is special, then there is
    an upper bound on the lengths of all paths through each of these elements.
    The maximum of these upper bounds is clearly an upper bound on lengths of
    all paths through $a_r$, contradicting the assumption that $a_r$ is special.
    It follows that some element of $theta_r lr((a_r))$ is special. We then
    obtain a path of infinite length by selecting a special element
    $a_0 in theta_(-1) lr((a_(-1)))$, and for each $r$, choosing a special
    element $a_r in theta_(r-1) lr((a_(r-1)))$. This proves the lemma.
  ]

  We apply the preceding lemma to the König graph ${A_(i,r),F_i}$, in case all
  the sets $A_(i,r)$ are nonempty. If the graph contains arbitrarily long paths,
  then there is an infinite path, by the lemma, and this contradicts the
  hypothesis @case:roiter-chain-termination, that the family of all
  indecomposable $A$-modules satisfies the conoetherian condition. It follows
  that in all cases, whether some set $A_(i,r)$ is empty or not, that there
  exists an integer $m_i>0$ such that $h_1 dots h_(m_i)=0$ for all products of
  elements $h_j in bold(H)_j lr((S_i))$, $1≤j≤m_i$. Let us set
  $m=max{m_i:1≤i≤n}$, and let
  $ bold(E)=union.big_(1≤i≤n,0≤j≤m) bold(E)_j lr((S_i)). $
  We have to prove that $bold(E)=upright("Ind") A$. Suppose, to the contrary,
  that $(M) in.not bold(E)$, for some indecomposable $A$-module $M$. Since the
  isomorphism classes of the simple modules are all in $bold(E)$, $M$ is not
  simple, and there exists a nonprojective simple module $S_i$, for $1≤i≤n$, and
  a nonzero nonsplit homomorphism $g:M arrow S_i$. Then there exists an
  almost-split homomorphism $f_1:E_1 arrow S_i$, as in the first part of the
  proof. Moreover, the homomorphism $g:M arrow S_i$ factors through $E_1$. It
  follows that there exists a representative $M_1$ of an isomorphism class in
  $bold(E)_1 lr((S_i))$ such
  #source(852)
  that $M_1 divides E_1$, and maps $g_1:M arrow M_1$ and $h_1:M_1 arrow S_i$
  such that $h_1 g_1≠0$, and $h_1 in bold(H)_1 lr((S_i))$. Then $g_1$ is a
  nonzero nonsplit nonisomorphism from $M$ to $M_1$, since $(M) in.not bold(E)$.
  Continuing with $g_1$ instead of $g$, it follows that there exists an
  almost-split homomorphism $f_2:E_2 arrow M_1$, and the map $g_1:M arrow M_1$
  factors through $E_2$, so that $g_1=f_2 phi$, for some map $phi:M arrow E_2$.
  Then $h_1 g_1≠0$ implies that $h_1 f_2 phi≠0$. Using the same reasoning as in
  the first step, we obtain an indecomposable module $M_2 divides E_2$, and maps
  $g_2:M arrow M_2$ and $h_2:M_2 arrow M_1$, such that
  $h_2 in bold(H)_2 lr((S_i))$ and $h_1 h_2 g_2≠0$. The argument can be
  repeated, and yields elements $h_j in bold(H)_j lr((S_i))$, $1≤j≤m$, such that
  $h_1 h_2 dots h_m≠0$, contrary to the definition of $m$. This proves that
  $(M) in bold(E)$, so $upright("Ind") A=bold(E)$, and the implication
  @case:roiter-chain-termination $==>$
  @case:roiter-finite-almost-split-generation is proved. This completes the
  proof of the theorem.
]

#remarks(numbered: false)[
  A criterion for a $K$-algebra to have finite representation type, which was
  shown by Janusz~@bib:Janusz1969 to hold for all group algebras of finite
  representation type, was obtained by Curtis–Jans~@bib:CurtisJans1965.
]<rem:finite-type-curtis-jans-criterion>
