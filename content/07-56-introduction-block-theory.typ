#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/56-block-theory.typ": *

== Introduction to Block Theory <sec:introduction-block-theory>

=== Background and Notation for Block Theory <ss:block-theory-background>

#idx("p-modular system")
Throughout this chapter, $G$ denotes a finite group and $p$ a rational prime
number. A _p-modular system_ $(K,R,k)$ consists of a d.v.r. $R$ with quotient
field $K$, maximal ideal $frak(p)=pi R$, and residue class field
$k=R slash frak(p)$ of characteristic $p$. One example to keep in mind is that
where $K$ is an algebraic number field and $R$ is the valuation ring of some
discrete valuation on $K$. As another example, we may choose $K$ to be the
completion of an algebraic number field with respect to a non-archimedean
valuation, and $R$ the valuation ring of $K$ (see
§~@i:ss:valuations-completions).

In order to keep the chapter reasonably self-contained, we shall review in this
subsection some of the concepts related to a $p$-modular system, especially
those connected with lifting idempotents. Other results from earlier chapters
will be recalled later, when needed.

#idx("Sufficiently large")
As in §~@i:ss:modular-splitting-fields, a field is called _sufficiently large_
relative to $G$ if it contains the $m$-th roots of unity, where $m$ is the
exponent of $G$. Such a field is a splitting
#source(424)
field for $G$ and all of its subgroups, by Theorem
@i:th:sufficiently-large-field-splits-group. We have seen in
§~@i:ss:modular-brauer-characters that if $(K,R,k)$ is a $p$-modular system with
$"char" K=0$ and $K$ sufficiently large, then also $k$ is sufficiently large,
and Brauer characters of $k G$-modules can be defined. We shall use these
characters later in this chapter.

The centers of the group algebras $K G$, $R G$, and $k G$, associated with a
$p$-modular system, will be of particular importance in block theory. We denote
these centers by
$ c(K G), quad c(R G), quad c(k G), $
respectively. By @i:lem:class-sums-center, each of these centers has a basis
over $K,R,k$, respectively, consisting of the class sums
$ C_i=sum_(x in cal(C)_i) x, $
where
${cal(C)_i}$
are the conjugacy classes in $G$.

Throughout this chapter, let bars denote “reduction mod $frak(p)$”. Thus, for
$a in R G$ let $overline(a) in k G$ denote its image under the canonical
surjection $R G -> k G$. Likewise, for each $R G$-module $M$ we put
$overline(M)=M slash frak(p)M$, and let $m mapsto overline(m)$ under the map
$M -> overline(M)$. Using this notation, we have at once an important connection
between the centers of the above group algebras:

#lemma[
  There is a surjective homomorphism $c(R G) -> c(k G)$, given by
  $ sum a_i C_i mapsto sum overline(a)_i overline(C)_i, quad a_i in R. $
] <lem:group-ring-center-reduction>

Let us now review some facts about idempotents, starting with a $p$-modular
system $(K,R,k)$ and an $R$-order $A$. (By definition, $A$ is an $R$-algebra
with a finite $R$-basis.) We shall be particularly interested in the cases where
$ A=R G quad "or" quad A=c(R G), $
but for the moment we do not make this assumption.
#nidx("$rad A$", "radical of A")
Let $rad A$ denote the Jacobson radical of $A$ (see
§~@i:ss:radicals-basic-definitions), and set $overline(A)=A slash frak(p)A$, a
f.d. $k$-algebra. We then have (see @i:prop:finite-algebra-local-base-radical
and @i:prop:semilocal-module-radical):

#proposition[
  Let $A$ be an $R$-order. Then
  $
    frak(p) A subset.eq rad A, quad
    A slash rad A tilde.equiv overline(A) slash rad overline(A).
  $
  Further, $A slash rad A$ is a semisimple artinian ring, and
  $ rad M=(rad A)M $
  for all f.g. left $A$-modules $M$.
] <prop:order-radical-reduction>
#source(425)

An _idempotent_ $e in A$ is a nonzero element such that $e^2=e$. Two idempotents
$e$ and $e'$ are _orthogonal_ if $e e'=e'e=0$. An idempotent $e$ is _primitive_
if it cannot be expressed as a sum of two orthogonal idempotents, or
equivalently, if and only if the left ideal $A e$ is indecomposable. By
@i:lem:idempotent-corner-endomorphisms and
@i:cor:indecomposable-endomorphism-idempotents, this is equivalent to the
assertion that the ring $e A e$ has no idempotents except $e$. These definitions
and remarks apply also to f.d. algebras over $K$ or $k$.

We wish to describe the connection between idempotents in $A$ and those in
$overline(A)$, under either of two restrictive hypotheses, each of which
provides a satisfactory basis for the development of much of block theory.

#definition[
  A $p$-modular system $(K,R,k)$ is _admissible_ (for block theory, relative to
  $A$) if either
  #enum(
    numbering: "(a)",
    [$R$ is complete in the $frak(p)$-adic topology, or],
    [$"char" K=0$ and the $K$-algebra $K times.o_R A$ is a split semisimple
      $K$-algebra (that is, a direct sum of full matrix algebras over $K$).],
  )
  In case $A=R G$, we say that $(K,R,k)$ is _admissible for G_.
] <def:admissible-modular-system>
#idx("Admissible p-modular system", target: [@def:admissible-modular-system])
#idx("p-modular system", target: [@def:admissible-modular-system])

Before imposing this hypothesis, we recall from §~@i:ss:krull-schmidt-azumaya
that the K-S-A Theorem (“Krull-Schmidt-Azumaya”) states that (under certain
hypotheses) f.g. $A$-modules have unique decompositions into indecomposable
summands (unique up to isomorphism). As usual, an _A-lattice_ means a left
$A$-module which is f.g. and projective over $R$ (and hence $R$-free with a
finite basis, since $R$ is a d.v.r.).

#proposition[
  Let $(K,R,k)$ be an admissible $p$-modular system for the $R$-order $A$. Then
  we have:
  #enum(
    numbering: "(i)",
    [Each idempotent $alpha in overline(A)$ can be lifted to $A$, that is,
      $alpha=overline(a)$ for some idempotent $a in A$.],
    [Each idempotent in $A slash rad A$ can be lifted to $A$.],
    [An idempotent $e in A$ is primitive if and only if $e A e$ is a local
      ring.],
    [An idempotent $e in A$ is primitive if and only if $overline(e)$ is
      primitive in $overline(A)$.],
    [There is a decomposition
      $ 1=e_1+dots+e_m $
      into primitive orthogonal idempotents $e_i in A$. Such a decomposition
      gives a corresponding decomposition
      $ overline(1)=overline(e)_1+dots+overline(e)_m $
      in $overline(A)$. Conversely, every such decomposition of
      $overline(1) in overline(A)$ lifts to a decomposition of $1 in A$.],
    [The K-S-A Theorem holds for $A$-lattices.],
  )
] <prop:admissible-order-idempotent-lifting>
#source(426)
#proof(head: emph[Sketch of Proof.])[
  All of the above assertions have been proved explicitly in §§~@i:sec:radicals,
  @i:sec:idempotents-krull-schmidt-projective-covers, when $R$ is complete in
  the $frak(p)$-adic topology. We shall recall some of the main points, and also
  discuss the case where $"char" K=0$ and $K A$ is split semisimple.

  (i) For $R$ complete, the result holds by @i:th:lifting-idempotents. In the
  second case, use Exercise @i:exc:split-order-idempotent-lifting.

  (ii) By @prop:order-radical-reduction, there is a surjection
  $
    overline(A) -> overline(A) slash rad overline(A) tilde.equiv A slash rad A.
  $
  Since $overline(A)$ is artinian, every idempotent of
  $overline(A) slash rad overline(A)$ lifts to $overline(A)$, by
  @i:th:lifting-idempotents. We then use (i) to lift to $A$.

  (iii) We have already noted that $e$ is primitive if and only if $e A e$
  contains no idempotents other than $e$, while $e A e$ is local if and only if
  $e A e slash rad(e A e)$ is a division ring (see §~@i:ss:local-rings). Thus,
  if $e A e$ is local, $e$ is clearly primitive. Now let $e$ be primitive. In
  case hypothesis @def:admissible-modular-system(a) holds, $e A e$ is a local
  ring by @i:prop:indecomposable-local-endomorphism-ring. In case (b), $e A e$
  is an order in the $K$-algebra $e K A e$, and $e K A e$ is also a split
  semisimple $K$-algebra by standard results in
  §~@i:sec:semisimple-rings-modules. Thus, we can apply parts (i) and (ii) to
  $e A e$, and conclude that idempotents can be lifted from
  $e A e slash rad(e A e)$ to $e A e$. Since we have assumed $e$ primitive, so
  that $e A e$ has no nontrivial idempotents, the same holds for
  $e A e slash rad(e A e)$. It follows that $e A e$ is a local ring, as
  required.

  (iv) The homomorphism
  $ e A e -> overline(e A e)=e A e slash frak(p)e A e $
  is surjective, and by @prop:order-radical-reduction we have
  $
    e A e slash rad(e A e) tilde.equiv
    overline(e A e) slash rad overline(e A e).
  $
  Thus $e A e$ is local if and only if $overline(e A e)$ is local, and the
  result follows from (iii).

  (v) The existence of a decomposition of 1 follows from the fact that $A$ is a
  noetherian ring. The remaining remarks follow from (iv) (see the proof of
  @i:th:lifting-idempotents).

  (vi) The result is @i:th:krull-schmidt-azumaya when $R$ is complete, while
  under hypothesis (b) it is a special case of Heller’s Theorem
  @i:th:heller-completion-krull-schmidt.
]

#proposition[
  Let $A$ be a commutative $R$-order.
  #enum(
    numbering: "(i)",
    [The primitive idempotents in $A$ form a finite set
      ${c_1,dots,c_n}$
      and satisfy the conditions
      $ 1=c_1+dots+c_n, quad c_j c_i=0 quad "for" i!=j. $],
    [If $(K,R,k)$ is admissible for $A$, the natural map $A -> overline(A)$
      induces a bijection of primitive idempotents.],
  )
] <prop:commutative-order-primitive-idempotents>
#source(427)

#remark(numbered: false)[
  Both conditions also hold for commutative algebras over $K$ or $k$.
]

#proof[
  Let $1=c_1+dots+c_n$ be a decomposition of 1 as a sum of primitive orthogonal
  idempotents; then
  $ A=A c_1 plus.o dots plus.o A c_n $
  is a decomposition of $A$ into indecomposable ideals. For an arbitrary
  primitive idempotent $e in A$ we have an orthogonal decomposition
  $ e=e c_1+dots+e c_n, $
  so $e=e c_i$ for some $i$, and $e c_j=0$ for $j!=i$. But $c_i$ is primitive,
  and $c_i=c_i e+c_i lr((1-e))$, so $c_i=c_i e=e$, which proves (i). Assertion
  (ii) follows from @prop:admissible-order-idempotent-lifting.
]

Now let $A$ be an arbitrary $R$-order, and assume $(K,R,k)$ admissible for $A$.
Then $A slash rad A$ is artinian, and every idempotent in $A slash rad A$ lifts
to $A$. Thus, by definition, $A$ is a _semiperfect ring_ (see
§~@i:ss:projective-covers), and every f.g. $A$-module has a projective cover, by
@i:cor:semiperfect-projective-cover-properties. By virtue of the isomorphism
$ A slash rad A tilde.equiv overline(A) slash rad overline(A), $
the simple $A$-modules can be identified with the simple $overline(A)$-modules.

#idx("Principal indecomposable module (P.I.M.)")
#idx("Indecomposable projective module", see: (
  "Principal indecomposable module (P.I.M.)",
))
Let $cal(P)(A)$ and $cal(P)(overline(A))$ denote the categories of f.g.
projective modules over $A$ and $overline(A)$, respectively. The indecomposable
modules in $cal(P)(A)$ and $cal(P)(overline(A))$ are called _principal
indecomposable modules_ (notation: P.I.M.), or also _indecomposable projective
modules_. Up to isomorphism, each P.I.M. $P in cal(P)(A)$ has the form $P=A e$,
with $e$ a primitive idempotent in $A$, and conversely each such $A e$ is a
P.I.M. A corresponding statement holds for P.I.M.’s in $cal(P)(overline(A))$.
Further, for each P.I.M. $P in cal(P)(A)$, we have shown in
@i:cor:projective-cover-radical-quotient that $P slash rad P$ is a simple
module, and $P$ is its projective cover. Moreover, $overline(P)$ is a P.I.M. in
$cal(P)(overline(A))$, and
$overline(P) slash rad overline(P) tilde.equiv P slash rad P$, so $overline(P)$
is a projective $overline(A)$-cover of the simple module $P slash rad P$.

Now let $A=R G$, where $(K,R,k)$ is admissible for $G$. The above remarks show
that there is an isomorphism of projective class groups
$ K_0 lr((R G)) tilde.equiv K_0 lr((k G)), $
where $K_0(A)$ denotes the Grothendieck group of the category $cal(P)(A)$, as in
@i:def:ring-grothendieck-projective-groups. By
@i:prop:semiperfect-projective-class-basis we have
$
  K_0 lr((R G))=plus.o.big_(i=1)^r ZZ[P_i]
  quad "and" quad K_0 lr((k G))=plus.o.big_(i=1)^r ZZ[U_i],
$
#source(428)
where the
${P_i}$
are a basic set of P.I.M.’s in $cal(P)(R G)$, the
${U_i}$
are a corresponding set in $cal(P)(k G)$, and the notation is such that
$overline(P)_i=U_i$, $1<=i<=r$. For more details, see
@i:prop:projective-cover-summary and
@i:th:projective-class-reduction-isomorphism.

=== Definition of $p$-Blocks for a Finite Group $G$
<ss:finite-group-p-block-definition>

Let $G$ be a finite group, and let $(K,R,k)$ be an arbitrary $p$-modular system.
By @prop:commutative-order-primitive-idempotents, the central primitive
idempotents in $R G$ form a finite set ${b_1,dots,b_t}$, and satisfy the
conditions
$
  1=b_1+dots+b_t, quad b_i b_j=0, quad i!=j, quad "and"
  R G=R G b_1 plus.o dots plus.o R G b_t.
$ <eq:group-ring-block-decomposition>

It is evident that for each $i$, $1<=i<=t$, $R G b_i$ is an indecomposable
two-sided ideal with identity element $b_i$, and the decomposition
@eq:group-ring-block-decomposition is the unique expression of $R G$ as a direct
sum of indecomposable two-sided ideals.

#idx("Block idempotents")
#idx("Block ideals")
The central primitive idempotents in $R G$ are called the _block idempotents_ of
$R G$, and the indecomposable two-sided ideals $B_i=R G b_i$, for $1<=i<=t$, are
called the _block ideals_ of $R G$.

#idx("p-Blocks")
#idx("Block", see: ("p-Blocks",))
A _p-block_ $upright(sans(B))_i^R$ _of RG-modules_ is the category of all f.g.
left $B_i$-modules, for some block ideal $B_i=R G b_i$, $1<=i<=t$. Since $B_i$
is a two-sided ideal in $R G$ with identity element $b_i$, the objects of the
$p$-block $upright(sans(B))_i^R$ are precisely the f.g. left $R G$-modules $M$
such that $b_i M=M$.

Let $M$ be an arbitrary f.g. $R G$-module; then
$ M=b_1 M plus.o dots plus.o b_t M $
by @eq:group-ring-block-decomposition, and the summand $b_i M$ is an
$R G$-module belonging to the $p$-block $upright(sans(B))_i^R$. In particular,
each f.g. indecomposable $R G$-module $M$ belongs to a unique $p$-block
$upright(sans(B))_i^R$, namely, the $p$-block $upright(sans(B))_i^R$ such that
$b_i M!=0$.

The preceding discussion applies equally well to $k G$. Denoting the block
idempotents of $k G$ by ${beta_1,dots,beta_u}$, we now have
$ k G=k G beta_1 plus.o dots plus.o k G beta_u, $
the unique decomposition of $k G$ into indecomposable two-sided ideals, called
the _block ideals_ of $k G$. Each block idempotent $beta_i$ defines a _p-block_
$upright(sans(B))_i^k$ _of kG-modules_, consisting of all f.g. left
$k G$-modules $V$ such that $beta_i V=V$, or equivalently, the category of all
f.g. left $k G beta_i$-modules.

The most important applications of block theory occur in the case where the
blocks of $k G$-modules correspond bijectively to the blocks of $R G$-modules.
This need not hold for an arbitrary $p$-modular system, but there is such a
bijection whenever $(K,R,k)$ is admissible for $G$, by
@lem:group-ring-center-reduction and
@prop:commutative-order-primitive-idempotents(ii). It should be pointed out that
if hypothesis @def:admissible-modular-system(b) holds for $K G$, then $K G$ is a
direct sum of full matrix algebras over $K$, and so its center $c(K G)$ is a
direct sum of copies
#source(429)
of $K$, and is also a split semisimple $K$-algebra. _Thus, if_ $(K,R,k)$ _is
admissible for_ $G$, _then it is admissible for both_ $R G$ _and_ $c(R G)$, _in
the sense of Definition_ @def:admissible-modular-system.

#proposition[
  Let the $p$-modular system $(K,R,k)$ be admissible for $G$. Then reduction mod
  $frak(p)$ defines a surjection $c(R G) -> c(k G)$, which, in turn, sets up a
  bijection
  $ b_i mapsto overline(b)_i=beta_i, quad 1<=i<=t, $
  between the set of all block idempotents
  ${b_1,dots,b_t}$
  of $R G$ and the corresponding set
  ${beta_1,dots,beta_t}$
  in $k G$.
] <prop:admissible-block-idempotent-reduction>
#idx(
  "Admissible p-modular system",
  target: [@prop:admissible-block-idempotent-reduction],
)

This is clear from the preceding remarks. We now introduce a simpler notation.

#definition[
  Let $(K,R,k)$ be an admissible $p$-modular system for $G$, and let
  ${b_1,dots,b_t}$
  be the block idempotents of $R G$. Each $b_i$ defines a _p-block_
  $upright(sans(B))_i$ _of G_, consisting of all f.g. $R G$-modules,
  $K G$-modules, and $k G$-modules on which $b_i$ acts as the identity, together
  with their trace functions and Brauer characters. (Here, $b_i$ acts on
  $k G$-modules via the homomorphism $b_i mapsto overline(b)_i=beta_i$, and on
  $K G$-modules via the inclusion $b_i in R G subset.eq K G$.) We use the
  notation
  $
    M in upright(sans(B))_i, quad zeta in upright(sans(B))_i,
    quad psi in upright(sans(B))_i, quad "etc.,"
  $
  to indicate that a module $M$, a $K$-character $zeta$, or a Brauer character
  $psi$ of a $k G$-module belong to the block $upright(sans(B))_i$.
] <def:p-block-finite-group>
#nidx("$upright(sans(B))$", "p-block of G", target: [@def:p-block-finite-group])

#remarks(numbered: false)[
  #enum(
    numbering: "(i)",
    [It is clear that a $p$-modular system $(K,R,k)$, with $"char" K=0$ and $K$
      sufficiently large relative to $G$, is admissible for an arbitrary
      subgroup $H$ of $G$, so the $p$-blocks of $H$ are defined by the block
      idempotents in $R H$, using @def:p-block-finite-group. Of course, a main
      problem is the relation between $p$-blocks of $G$ and $p$-blocks of
      subgroups of $G$.],
    [By a previous remark, each indecomposable $R G$-module belongs to a unique
      $p$-block. In particular, each P.I.M. $P in cal(P)(R G)$ belongs to a
      unique $p$-block. If $P=R G e$ for some primitive idempotent $e$, then
      $P in upright(sans(B))_i$ implies that $b_i P=P$, and hence
      $P subset.eq B_i$, where $B_i$ is the block ideal $R G b_i$. It follows
      that each block ideal $B_i$ is a direct sum of P.I.M.’s belonging to the
      block $upright(sans(B))_i$.],
  )
]

#examples[
  Let $(K,R,k)$ be a $p$-modular system with $"char" K=0$ and $K$ sufficiently
  large relative to $G$. Proofs of the results below are left as exercises.
  #enum(
    numbering: "(i)",
    [If $G$ is a $p'$-group, then $|G|^(-1) in R$, so by
      @i:prop:group-character-orthogonality-idempotents(ii) the central
      primitive idempotents in $K G$ all belong to $R G$, and hence are the
      block idempotents. In this case, $R G$ is a maximal order in $K G$, by
      @i:prop:group-ring-maximality, and the block ideals in $R G$ are maximal
      orders in the Wedderburn components of $K G$. If $P$ is a P.I.M. in $R G$,
      then $K P$ is a simple $K G$-module, and $overline(P)$ is a simple
      $k G$-module. Two
      #source(430)
      P.I.M.’s in $R G$ belong to the same $p$-block if and only if they are
      isomorphic. Evidently, in this situation, $p$-blocks have little to
      contribute to the representation theory of $G$.],
    [Now assume that $G$ is a $p$-group. In this case, $R G$ is a local ring by
      @i:cor:p-group-ring-local-base, so 1 is the only block idempotent, and
      there is only one $p$-block.],
  )
] <exm:prime-to-p-and-p-group-blocks>

=== A Criterion for P.I.M.’s to Belong to the Same $p$-Block
<ss:pim-block-linkage>

Let $G$ be a finite group, and $(K,R,k)$ an arbitrary $p$-modular system. We
shall investigate the distribution of P.I.M.’s of $k G$ and $R G$ into blocks.
One of the earliest results of block theory is the following criterion, due to
Brauer–Nesbitt (@bib:Brauer1937, §6), for two P.I.M.’s in $cal(P)(k G)$ to be
summands of the same block ideal in $k G$.

#definition[
  Two P.I.M.’s $U$ and $U'$ in $cal(P)(k G)$ are said to be _linked_ if and only
  if there is a sequence of P.I.M.’s
  ${U_1,dots,U_m}$
  in $cal(P)(k G)$ such that $U_1=U$, $U_m=U'$, and for each $i$, $1<=i<=m-1$,
  $U_i$ and $U_(i+1)$ have a composition factor in common.
] <def:linked-principal-indecomposable-modules>
#idx("Linked", target: [@def:linked-principal-indecomposable-modules])
#idx(
  "p-Blocks",
  "and P.I.M.'s",
  target: [@def:linked-principal-indecomposable-modules],
)
#idx(
  "Principal indecomposable module (P.I.M.)",
  target: [@def:linked-principal-indecomposable-modules],
)

The relation of linkage clearly is an equivalence relation on the set of all
P.I.M.’s in $cal(P)(k G)$, while the simpler condition of relating two P.I.M.’s
if they have a composition factor in common is not. The concept of linkage,
incidentally, has proved useful in other categories of modules (see
Humphreys–Jantzen @bib:Humphreys1978 and Donkin @bib:Donkin1980 for the theory
of blocks of rational $G$-modules, for a semisimple algebraic group $G$).

The main result about linkage classes holds for P.I.M.’s in $k G$, for an
arbitrary field $k$ of characteristic $p>0$. We recall that, by
@prop:commutative-order-primitive-idempotents, the central primitive idempotents
in $k G$ form a finite set ${beta_1,dots,beta_u}$. Moreover, we have
$ k G=k G beta_1 plus.o dots plus.o k G beta_u, $
<eq:modular-group-algebra-block-decomposition>
and this is the unique decomposition of $k G$ as a direct sum of indecomposable
two-sided ideals, called _block ideals_, as in
§~@ss:finite-group-p-block-definition.

We now have the following result (see @bib:CurtisReiner1962[CR] §55 for the
corresponding theorem for artinian rings).

#theorem[
  Each block ideal in $k G$ is the direct sum of all indecomposable projective
  left ideals belonging to one linkage class (see
  @def:linked-principal-indecomposable-modules). Thus two P.I.M.’s are linked if
  and only if they are isomorphic to direct summands of a single block ideal in
  $k G$. In particular, no two distinct block ideals of $k G$ have a composition
  factor in common.
] <th:block-ideals-linkage-classes>

The proof is based on the following important method for identifying composition
factors.

#lemma[
  Let $A$ be a left artinian ring, let $A e$ be a P.I.M. generated by
  #source(431)
  a primitive idempotent $e$, and let $F$ be the simple module
  $A e slash (rad A)e$. A f.g. left $A$-module $M$ has a composition factor
  isomorphic to $F$ if and only if $e M!=0$.
] <lem:primitive-idempotent-composition-factor>
#proof[
  (See Exercise @i:exc:idempotent-multiplicities for the case of a semisimple
  ring $A$.) From §~@i:ss:finiteness-conditions, $M$ has a composition series
  $ M=M_0>M_1>dots>M_s>M_(s+1)=0. $
  Since $e$ is idempotent, it follows that $e M!=0$ if and only if
  $e(M_i slash M_(i+1))!=0$ for some $i$, $0<=i<=s$.

  We now prove that $e(M_i slash M_(i+1))!=0$ if and only if
  $F tilde.equiv M_i slash M_(i+1)$. To show this, let $W$ be the simple module
  $M_i slash M_(i+1)$, and suppose $e W!=0$. Then $e w!=0$ for some $w in W$,
  and hence $W=A e w$, since $W$ is a simple module. Then the obvious
  homomorphism $A e -> A e w$ defines an isomorphism $F tilde.equiv W$, since
  $rad A e$ is the unique maximal submodule of $A e$. Conversely, if
  $A e slash rad A e tilde.equiv W$, there is a nonzero homomorphism
  $f:A e -> W$. Then $f(e)!=0$ since $f(A e)=A f(e)$, and $f(e) in e W$,
  completing the proof.
]

#proof(head: emph[Proof of @th:block-ideals-linkage-classes.])[
  Each indecomposable projective left ideal in $k G$ is generated by a primitive
  idempotent (see §~@ss:block-theory-background). Let
  ${B_1,dots,B_v}$
  be left ideals in $k G$, each of which is the sum of all indecomposable
  projective left ideals belonging to a single linkage class. We first prove
  that $B_i B_j=0$ if $i!=j$. Otherwise, there exist indecomposable projective
  left ideals $k G e$ and $k G f$, belonging to different linkage classes, such
  that $(k G e)(k G f)!=0$, which is impossible by Lemma
  @lem:primitive-idempotent-composition-factor. It follows that the ideals
  ${B_i}_(1<=i<=v)$
  are two-sided ideals, and that $k G=B_1 plus.o dots plus.o B_v$. Since the
  decomposition @eq:modular-group-algebra-block-decomposition is the unique
  expression of $k G$ as a direct sum of indecomposable two-sided ideals, each
  ideal $B_i$ is a direct sum of certain of the block ideals ${k G beta_j}$.

  We now prove that the decompositions are the same. By the definition of the
  ideals ${B_i}$, it is sufficient to prove that if $e$ and $e'$ are primitive
  idempotents of $k G$ such that $k G e$ and $k G e'$ have a common composition
  factor, and if $k G e subset.eq k G beta_j$, then also
  $k G e' subset.eq k G beta_j$. But if $k G e' subset.eq k G beta_l$, with
  $l!=j$, then $beta_l$ acts as 1 on every composition factor of $k G e'$, and
  as 0 on every composition factor of $k G e$. This contradicts the hypothesis
  that $k G e$ and $k G e'$ have a common composition factor, and completes the
  proof that each $B_i$ is a block ideal.
]

#corollary[
  Let $G$ be a finite group, and let $(K,R,k)$ be an admissible $p$-modular
  system for $G$. Then the following conditions concerning two P.I.M.’s $P$ and
  $P'$ in $cal(P)(R G)$ are equivalent:
  #enum(
    numbering: "(i)",
    [$P$ and $P'$ belong to the same $p$-block of $G$.],
    [$overline(P)$ and $overline(P)'$ belong to the same $p$-block of $G$.],
    [$overline(P)$ and $overline(P)'$ belong to the same linkage class of left
      $k G$-modules (according to Definition
      @def:linked-principal-indecomposable-modules).],
  )
] <cor:projective-lattice-block-linkage>
#proof[
  Let
  ${b_1,dots,b_t}$
  be the block idempotents of $c(R G)$. By @def:p-block-finite-group,
  ${overline(b)_i}$
  are
  #source(432)
  the block idempotents of $c(k G)$, and it follows that (i) and (ii) are
  equivalent. Since $overline(P)$ and $overline(P)'$ are P.I.M.’s in
  $cal(P)(k G)$ by the discussion at the end of §~@ss:block-theory-background,
  (ii) and (iii) are also equivalent, by Theorem
  @th:block-ideals-linkage-classes.
]

=== Central Characters and Blocks of $K G$-Modules
<ss:central-characters-blocks>

In §~@ss:finite-group-p-block-definition, the $p$-blocks of $G$ were defined in
terms of the block idempotents of $R G$ (and $k G$). For applications to
character theory, it is essential to know the distribution of simple
$K G$-modules and their characters among the $p$-blocks. A solution to this
problem, in principle, is provided by the connection between $p$-blocks and
representations of the centers of $R G$ and $k G$.

#definition[
  Let $A$ be f.d. algebra over a field $k$. A _central character_ of $A$ is a
  surjective homomorphism of $k$-algebras
  $ phi:c(A) -> k' $
  from the center of $A$ to a finite extension field $k'$ of $k$. Two central
  characters
  $ phi:c(A) -> k', quad psi:c(A) -> k'' $
  are said to be _equivalent_ if there is a $k$-isomorphism of fields
  $sigma:k' -> k''$ such that the diagram
  #central-character-equivalence
  commutes.
] <def:central-character-finite-algebra>
#idx("Central character", target: [@def:central-character-finite-algebra])

Evidently, equivalence of central characters is an equivalence relation.

#proposition[
  Let $G$ be a finite group, and $k$ a field. Let
  ${beta_1,dots,beta_u}$
  be the block idempotents in $c(k G)$.
  #enum(
    numbering: "(i)",
    [For each block idempotent $beta_i$, let
      $
        frak(m)_i=rad c(k G)+c(k G)(1-beta_i),
        quad "and" quad k_i=c(k G) slash frak(m)_i.
      $
      Then $frak(m)_i$ is a maximal ideal in $c(k G)$, $k_i$ is a finite
      extension field of $k$, and the natural map
      $ psi_i:c(k G) -> c(k G) slash frak(m)_i=k_i $
      is a central character of $k G$ with the property that
      $ psi_i lr((beta_i))=1 quad "and" quad psi_i lr((beta_j))=0 "if" i!=j. $],
    [Every central character $psi:c(k G) -> k'$ is equivalent to exactly one of
      the central characters $psi_i$ defined in (i).],
  )
] <prop:modular-central-characters-block-idempotents>
#source(433)
#proof[
  (i) For each $i$, $beta_i$ is a primitive idempotent in the commutative
  $k$-algebra $c(k G)$, and $rad c(k G)beta_i$ is the unique maximal submodule
  of $c(k G)beta_i$, by @i:cor:indecomposable-projective-top. It follows that
  $frak(m)_i$ is a maximal ideal in $c(k G)$. Then $k_i=c(k G) slash frak(m)_i$
  is a finite extension field of $k$, and the natural map $psi_i:c(k G) -> k_i$
  has the required properties.

  (ii) Let $psi:c(k G) -> k'$ be any central character. Then $frak(m)=ker psi$
  is a maximal ideal in $c(k G)$, and $k' tilde.equiv c(k G) slash frak(m)$. Now
  $ c(k G)=c(k G)beta_1 plus.o dots plus.o c(k G)beta_u $
  is the unique decomposition of $c(k G)$ as a direct sum of indecomposable
  ideals. For some $i$, $beta_i in.not frak(m)$, so
  $c(k G)beta_i+frak(m)=c(k G)$, and hence
  $
    c(k G) slash frak(m) tilde.equiv
    c(k G)beta_i slash (c(k G)beta_i inter frak(m))
  $
  by an isomorphism theorem. Then $c(k G)beta_i inter frak(m)$ coincides with
  the unique maximal submodule $rad c(k G)beta_i$ of $c(k G)beta_i$. A similar
  argument shows that $c(k G)(1-beta_i) subset.eq frak(m)$, and it follows that
  $frak(m)=frak(m)_i$. Since $k' tilde.equiv c(k G) slash frak(m)$, it follows
  that there exists an isomorphism of $k$-algebras $sigma:k' -> k_i$ such that
  $sigma compose psi=psi_i$, completing the proof.
]

Let $R$ be a d.v.r. with maximal ideal $frak(p)$ and residue class field
$k=R slash frak(p)$. By @prop:order-radical-reduction we have
$ c(R G) slash rad c(R G) tilde.equiv c(k G) slash rad c(k G). $
Then the simple $c(R G)$-modules can be identified with the simple
$c(k G)$-modules, and these correspond to the central characters of $k G$. Thus
we are led to:

#definition[
  Let $R$ be a d.v.r. with residue class field $k=R slash frak(p)$. A _central
  character_ $lambda$ of $R G$ is a surjective homomorphism of $R$-algebras
  $lambda:c(R G) -> k'$, where $k'$ is a finite extension field of $k$, and $k'$
  is viewed as an $R$-algebra via the natural map from $R$ to $k$. Equivalence
  of central characters of $R G$ is defined as in
  @def:central-character-finite-algebra.
] <def:central-character-group-order>
#idx("Central character", target: [@def:central-character-group-order])

#proposition[
  Let $nu:c(R G) -> c(k G)$ be the natural surjection (see
  @lem:group-ring-center-reduction).
  #enum(
    numbering: "(i)",
    [For each central character $psi$ of $R G$, $ker psi supset.eq ker nu$, and
      there exists a unique central character $xi$ of $k G$ such that
      $ psi=xi compose nu. $],
    [The correspondence defined in (i) is a bijection, preserving the relation
      of equivalence, from the set of central characters of $R G$ to the set of
      central characters of $k G$.],
  )
] <prop:central-character-reduction-bijection>
#source(434)
#proof[
  Let $psi$ be a central character of $R G$. Then $ker psi$ is a maximal ideal
  of $c(R G)$, so $ker psi supset.eq rad c(R G) supset.eq frak(p)c(R G)=ker nu$,
  by @prop:order-radical-reduction, and therefore the first statement follows.
  The proof of the second statement is left as an exercise for the reader.
]

#remark(numbered: false)[
  The equivalence classes of central characters of $R G$ do not correspond
  bijectively with the block idempotents of $R G$ as in
  @prop:modular-central-characters-block-idempotents unless some additional
  hypotheses are satisfied, such as the completeness of $R$. The reason is that
  $rad c(R G)b_i$ is not necessarily maximal in $c(R G)b_i$, for a block
  idempotent $b_i$, so the ideals $frak(m)_i$ defined as in
  @prop:modular-central-characters-block-idempotents are not necessarily maximal
  in $c(R G)$. This difficulty does not arise if $(K,R,k)$ is a $p$-modular
  system which is admissible for $G$, since, in that case, $c(R G)$ is a
  semiperfect ring. Thus we have
]

#proposition[
  Let $(K,R,k)$ be a $p$-modular system which is admissible for $G$. Then the
  following sets are in bijective correspondence, defined by
  @prop:modular-central-characters-block-idempotents and
  @prop:central-character-reduction-bijection:
  #enum(
    numbering: "(i)",
    [The $p$-blocks
      ${upright(sans(B))_i}$
      of $G$;],
    [The equivalence classes of central characters of $R G$;],
    [The equivalence classes of central characters of $k G$.],
  )
  A central character $psi$ of $R G$ (and its equivalence class) corresponds to
  a $p$-block $upright(sans(B))_i$ if and only if $psi(b_i)=1$ and $psi(b_j)=0$,
  $j!=i$, where
  ${b_i}$
  are the block idempotents in $R G$. A similar statement applies to central
  characters of $k G$.
] <prop:blocks-central-character-bijection>
#idx(
  "p-Blocks",
  "and central characters",
  target: [@prop:blocks-central-character-bijection],
)

A sharper statement holds when $k$ is a splitting field for $G$, that is,
$k G slash rad k G$ is a split semisimple $k$-algebra.

#proposition[
  Let $(K,R,k)$ be a $p$-modular system such that $"char" K=0$ and $K$ is
  sufficiently large relative to $G$. Then $(K,R,k)$ is admissible for $G$, and
  the following statements hold.
  #enum(
    numbering: "(i)",
    [Each central character $psi_i$ of $k G$ (as in
      @prop:modular-central-characters-block-idempotents(i)) gives a
      homomorphism of $k$-algebras $psi_i:c(k G) -> k$; in other words, the
      fields
      ${k_i}$
      all coincide with $k$.],
    [Let $psi:c(k G) -> k'$ be an arbitrary central character of $G$. Then
      $k'=k$, and $psi$ coincides with exactly one of the central characters
      $psi_i$.],
    [Let $upright(bold(F))$ be an irreducible $k$-representation of $G$. Then
      for each $a in c(k G)$,
      $ upright(bold(F))(a)=psi(a) upright(bold(I)) quad "with" psi(a) in k, $
      and the map $a mapsto psi(a)$ is a central character of $k G$.],
    [Two irreducible $k$-representations $upright(bold(F))$ and
      $upright(bold(F))'$ of $G$ belong to the same $p$-block if and only if the
      central characters $psi$ and $psi'$ corresponding to them, as in part
      (iii), coincide.],
  )
] <prop:split-modular-central-characters>
#proof[
  We begin with part (iii). Since $K$ is sufficiently large, $k$ is a splitting
  #source(435)
  field for $G$ by @i:cor:modular-system-sufficiently-large-fields, and the
  commuting algebra of the set of matrices
  ${upright(bold(F))(x):x in G}$
  is $k dot upright(bold(I))$. Thus if $a in c(k G)$,
  $upright(bold(F))(a)=psi(a) upright(bold(I))$ with $psi(a) in k$, and (iii) is
  proved. Each central character $psi$ defined as in part (iii) is equivalent to
  one of the central characters $psi_i$, by
  @prop:modular-central-characters-block-idempotents(ii), and, in this case, we
  clearly have $k_i=k$ and $psi=psi_i$—equivalence becomes equality.

  Now let $psi_j$ be an arbitrary central character associated with a block
  idempotent $beta_j$ of $k G$. Then $psi_j$ is the central character
  corresponding, as in (iii), to any irreducible $k$-representation
  $upright(bold(F))$ belonging to the block $upright(sans(B))_j$, by the first
  part of the proof, and it follows that $k_j=k$. The rest of the proof is
  immediate from these remarks.
]

We are now in a position to discuss the $p$-blocks of $K G$-modules, for a
$p$-modular system $(K,R,k)$ such that $"char" K=0$, and $K$ is sufficiently
large relative to $G$. The $p$-modular system is admissible for $G$, and the
natural map $R G -> k G$ defines a bijection
$ b_i arrow.l.r overline(b)_i, quad 1<=i<=t $
from the block idempotents of $R G$ to those of $k G$, by
@prop:admissible-block-idempotent-reduction.

We wish to reorganize the character table data for $K$-characters and Brauer
characters of $k G$-modules, summarized in @i:def:character-table-data and
@i:def:brauer-character-table-data, in terms of the $p$-blocks of $G$. We begin
by discussing the principles on which this organization is based.

Each irreducible $K$-character $zeta in op("Irr") G$ defines a central character
$omega:c(K G) -> K$, as follows: let $Z$ be a simple $K G$-module affording the
character $zeta$, and let $upright(bold(Z))$ be an irreducible matrix
representation of $K G$ afforded by $Z$. Then
$ upright(bold(Z))(C_i)=omega(C_i) upright(bold(I)) $
and (see §~@i:ss:character-table) $omega$ is a central character of $K G$, such
that
$ omega(C_i)=|cal(C)_i|zeta(x_i) slash zeta(1), quad "where" x_i in cal(C)_i, $
<eq:ordinary-central-character-values>
and $C_i$ is the class sum associated with the class $cal(C)_i$. By
@i:prop:central-character-values-integral we have
$omega(C_i) in "alg. int." {K}$ for each $i$, and hence $omega(C_i) in R$. We
now define
$
  overline(omega):c(k G) -> k quad "by"
  overline(omega)(overline(C)_i)=overline(omega(C_i))
  quad "for each" i.
$
<eq:reduced-ordinary-central-character>
If the multiplication of class sums is given by
$ C_i C_j=sum c_(i j k) C_k, quad c_(i j k) in ZZ, $
then by @i:eq:central-character-multiplicativity we obtain
$
  omega(C_i)omega(C_j)=sum c_(i j k)omega(C_k),
  quad "and" quad
  overline(omega)(overline(C)_i)overline(omega)(overline(C)_j)
  =sum overline(c)_(i j k)overline(omega)(overline(C)_k).
$
It follows that $overline(omega):c(k G) -> k$ is a central character of $k G$.
#source(436)

Now let $upright(sans(B))_i$ be the $p$-block defined by the block idempotent
$b_i$. Then $Z in upright(sans(B))_i$ if and only if $b_i$ acts as 1 on $Z$, or
equivalently,
$ omega(b_i)=1, quad omega(b_j)=0 quad "for" j!=i. $
Therefore $Z in upright(sans(B))_i$ if and only if $overline(omega)=psi_i$,
where $psi_i$ is the central character of $c(k G)$ associated with
$overline(b)_i$ as in @prop:blocks-central-character-bijection. We have thus
proved:

#proposition[
  Let $Z$ and $Z'$ be simple $K G$-modules, and $omega,omega'$ the corresponding
  central characters of $K G$. Then $Z$ and $Z'$ belong to the same $p$-block if
  and only if $overline(omega)=overline(omega)'$, where
  ${overline(omega),overline(omega)'}$
  are the central characters of $k G$ defined in
  @eq:reduced-ordinary-central-character.
] <prop:ordinary-block-reduced-central-character>

#corollary(title: [Brauer–Nesbitt @bib:Brauer1941])[
  Two irreducible $K$-characters
  ${zeta,zeta'}$
  of $G$ belong to the same $p$-block if and only if
  $
    |cal(C)|zeta(x) slash zeta(1)
    equiv |cal(C)|zeta'(x) slash zeta'(1) (mod frak(p))
  $
  for each conjugacy class $cal(C)$, and each $x in cal(C)$.
] <cor:block-central-character-congruence>
#idx(
  "p-Blocks",
  "congruence criterion",
  target: [@cor:block-central-character-congruence],
)

The preceding result gives the distribution of the irreducible characters into
$p$-blocks for any finite group $G$ whose character table is known.

Another description of the $p$-blocks of $K$-characters is easily obtained as
follows. Let $op("Irr") G= {zeta^1,dots,zeta^s}$, and for each $i$, let $e_i$ be
the central primitive idempotent in $K G$ defined by $zeta^i$. Thus (see
@i:prop:group-character-orthogonality-idempotents)
$ e_i=zeta^i lr((1)) |G|^(-1) sum_(x in G) zeta^i lr((x^(-1)))x. $
Because of the factor $|G|^(-1)$, the idempotents $e_i$ usually do not belong to
$R G$. On the other hand, each block idempotent $b in c(R G)$ belongs to
$c(K G)$, and hence can be expressed uniquely as a sum of the central
idempotents ${e_i}_(1<=i<=s)$. Therefore we obtain

#proposition[
  Let $upright(sans(B))$ be a $p$-block of $G$, defined by the block idempotent
  $b in R G$. Then, letting $e_i$ be the central idempotent associated with
  $zeta^i in op("Irr") G$,
  $ b=sum_(zeta^i in upright(sans(B))) e_i $
  is the expression of $b$ as a sum of central primitive idempotents in $K G$.
] <prop:block-idempotent-ordinary-components>

#examples(name: [Organization of $p$-Blocks of Characters])[
  The distribution among the $p$-blocks of simple $K G$-modules and
  $k G$-modules, and their characters and Brauer characters, of course leads to
  information about the decomposition matrix and the Cartan matrix (see
  §~@i:sec:cartan-brauer-triangle). Keeping $(K,R,k)$ as in the preceding two
  results, let us number the simple $K G$-modules and their characters
  $ {Z_1,dots,Z_s}, quad {zeta^1,dots,zeta^s} $
  #source(437)
  so that the first $x_1$ of them belong to the block $upright(sans(B))_1$, the
  next $x_2$ to $upright(sans(B))_2$, etc. As in @i:def:character-table-data, we
  let $zeta^1=1_G$ be the principal (or trivial) character, and call the
  $p$-block
  #idx("p-Blocks", "principal")
  #idx("Principal p-block")
  #nidx(
    "$upright(sans(B))_1$",
    "principal p-block containing the trivial character",
  )
  $upright(sans(B))_1$ containing $1_G$ the _principal p-block_ of $G$. We also
  number the simple $k G$-modules
  ${F_1,dots,F_r}$
  and their Brauer characters
  ${phi^1,dots,phi^r}$
  in a similar manner. Finally the P.I.M.’s
  ${U_1,dots,U_r}$
  of $k G$ and their Brauer characters
  ${eta^1,dots,eta^r}$
  are arranged so that $F_i=U_i slash rad U_i$, $1<=i<=r$. For each block
  idempotent $b in R G$, we know that $overline(b)$ is a block idempotent in
  $k G$, and clearly $overline(b)U_i!=0$ if and only if $overline(b)F_i!=0$.
  Thus the P.I.M.’s
  ${U_i}$
  are distributed among the blocks in the same way as the ${F_i}$.

  If $M_i$ is a full $R G$-lattice in $Z_i$, and $Z_i in upright(sans(B))$, then
  the block idempotent $b$ of $upright(sans(B))$ acts as the identity on $M_i$.
  Then $overline(b)=id$ on $overline(M)_i$, and it follows that all the
  composition factors of $overline(M)_i$ belong to $upright(sans(B))$. Let
  $ d:G_0 lr((K G)) -> G_0 lr((k G)) $
  be the _decomposition map_ (see @i:def:decomposition-map-matrix), so by
  @i:eq:decomposition-coefficients we have
  $ d[Z_i]=sum_(j=1)^r d_(i j)[F_j], quad 1<=i<=s, $
  where $upright(bold(D))=(d_(i j))$ is the _decomposition matrix_. By the way
  we have ordered the modules, the decomposition matrix has the form
]
<exm:block-character-organization>
$
  upright(bold(D))=mat(
    delim: "[", upright(bold(D))_1^(x_1 times y_1), , 0;
    , dots.down, ; 0, , upright(bold(D))_t^(x_t times y_t)
  )
$
<eq:block-decomposition-matrix>
with zeros except for the diagonal blocks ${upright(bold(D))_i}_(1<=i<=t)$,
where each diagonal block describes the decomposition map for $K$-characters
belonging to a given block.

The _Cartan map_ (see @i:def:cartan-homomorphism-matrix)
$ c:K_0 lr((k G)) -> G_0 lr((k G)) $
is defined by the $r times r$ _Cartan matrix_ $upright(bold(C))=(c_(i j))$,
where
$ c[U_i]=sum_(j=1)^r c_(i j)[F_j], quad 1<=i<=r. $
Then because of the arrangement of the P.I.M.’s
${U_i}$
and the simple modules
${F_j}$
according to blocks, the Cartan matrix also has a block decomposition
$
  upright(bold(C))=mat(
    delim: "[", upright(bold(C))_1^(y_1 times y_1), , ;
    , dots.down, ; , , upright(bold(C))_t^(y_t times y_t)
  )
$
<eq:block-cartan-matrix>
#source(438)
with zeros except for the diagonal blocks ${upright(bold(C))_i}$. Each diagonal
block describes the action of the Cartan map on the P.I.M.’s belonging to a
given block. Using the basic result @i:cor:cartan-decomposition-gram-matrix that
$upright(bold(C))=attach(upright(bold(D)), tl: t) upright(bold(D))$, we obtain
$
  upright(bold(C))_i=attach(upright(bold(D))_i, tl: t) upright(bold(D))_i,
  quad 1<=i<=t.
$
#numbering-gap()

=== The Defect of a Block <ss:block-defect>

We continue the investigation of $p$-blocks of characters in $op("Irr") G$. As
in §~@ss:central-characters-blocks, $(K,R,k)$ denotes a $p$-modular system, such
that $"char" K=0$ and $K$ is sufficiently large relative to $G$. We shall define
a nonnegative integer associated with each block, called its _defect_. This
concept was introduced by Brauer–Nesbitt @bib:Brauer1941; it relates the degrees
of the characters in a $p$-block to properties of the block idempotents in $R G$
and $k G$. In §~@sec:defect-groups-blocks, we shall define a $p$-subgroup of $G$
associated with each $p$-block, called the _defect group_ of the block, whose
order is $p^d$, where $d$ is the defect.

We shall follow the organization of modules, characters, etc. in terms of the
$p$-blocks ${upright(sans(B))_1,dots,upright(sans(B))_t}$, defined by the block
idempotents ${b_1,dots,b_t}$, as described in @exm:block-character-organization.
Since $(K,R,k)$ is an admissible $p$-modular system,
${overline(b)_1,dots,overline(b)_t}$
are the block idempotents in $k G$, by @def:p-block-finite-group.

We shall often use the $p$-adic valuation $v_p$, defined on the rational field
$QQ$ (see §~@i:sec:dedekind-domains). Thus, for $a in ZZ$, $v_p lr((a))$ is the
exponent to which $p$ appears in the prime factorization of $a$, and we have
$v_p lr((a slash b))=v_p lr((a))-v_p lr((b))$, for $a,b in ZZ$, $b!=0$. Let us
set
$
  z_i=zeta^i lr((1))=dim_K Z_i, quad
  f_j=phi^j lr((1))=dim_k F_j, quad
  u_j=eta^j lr((1))=dim_k U_j,
$
where $1<=i<=s$, $1<=j<=r$. We also put
$
  |G|=g, quad e=v_p lr((g)), quad
  G_(p')= {"all" p"-regular elements of" G}.
$

#definition[
  The _defect_ $d_j$ of the $p$-block $upright(sans(B))_j$ is the integer
  defined by the formula
  $ d_j=e-min {v_p lr((z_i)):Z_i in upright(sans(B))_j}. $
] <def:block-defect>
#idx("Defect of p-block", target: [@def:block-defect])
#idx("p-Blocks", "defect of", target: [@def:block-defect])

Since $z_i divides g$ for each $i$ by
@i:prop:character-degree-divides-group-order, it follows that the defect of a
block is always a nonnegative integer. A restatement of the definition is:
$
  p^(e-d_j) divides z_i quad "for all" Z_i in upright(sans(B))_j,
  quad "but" quad p^(e-d_j+1) divides.not z_i
  quad "for some" Z_i in upright(sans(B))_j.
$

In the extreme case of defect zero, we have:

#proposition[
  Let $upright(sans(B))_j$ be a $p$-block of defect zero. Then
  $upright(sans(B))_j$ contains exactly one simple $K G$-module $Z$, exactly one
  simple $k G$-module $F$, and exactly one P.I.M. $U$. The contributions
  $upright(bold(D))_j$ and $upright(bold(C))_j$ to the decomposition matrix and
  the Cartan
  #source(439)
  matrix, respectively, are given by
  $ upright(bold(D))_j=(1), quad upright(bold(C))_j=(1). $
  Moreover, $zeta(x)=0$ for all $p$-irregular $x in G$, where $zeta$ is the
  character afforded by $Z$.
] <prop:defect-zero-block-singletons>
#idx("p-Blocks", "of defect zero", target: [@prop:defect-zero-block-singletons])
#proof[
  Let $Z$ be a simple $K G$-module belonging to $upright(sans(B))_j$, and let
  the primitive idempotent associated with $Z$ be
  $ e=zeta(1)|G|^(-1)sum_(x in G) zeta(x^(-1))x, $
  as in @i:prop:group-character-orthogonality-idempotents. Since
  $upright(sans(B))_j$ has defect zero, it follows that $e in R G$, and hence
  $Z$ is the only simple module in $upright(sans(B))_j$, by
  @prop:block-idempotent-ordinary-components. The rest of the proof follows from
  @i:prop:defect-zero-character-projective-simple. We recall the argument, and
  give a new proof of a crucial step. There exists an indecomposable projective
  $R G$-module $P_i$, with $K$-character $tau_i$, such that $Z$ is a direct
  summand of $K times.o_R P_i$. Then $e P_i!=0$, and hence $e P_i=P_i$. Thus
  $tau_i=a zeta$ for some positive integer $a$, and it follows that $zeta$
  vanishes on $p$-irregular elements, by
  @i:th:projective-characters-supported-p-regular. Then $zeta=sum_j b_j tau_j$
  for some integers $b_j$, by @i:th:projective-characters-supported-p-regular,
  and it follows that $a=1$ and $tau_i=zeta$. Then
  $e R G=P_i plus.o dots plus.o P_i$, and hence
  $overline(e)k G=overline(P)_i plus.o dots plus.o overline(P)_i$, where
  $overline(e)$ is a block idempotent in $k G$, and $overline(P)_i$ is an
  indecomposable projective $k G$-module. Since the block ideal $overline(e)k G$
  contains only one P.I.M., it follows that the block $upright(sans(B))_j$
  contains only one simple $k G$-module
  $F_i=overline(P)_i slash rad overline(P)_i$. Now consider the decomposition
  map, applied to $[Z]=[K times.o P_i]$. Since $tau_i=zeta$, and
  $tau_i=sum_(l=1)^s d_(l i)zeta^l$ by
  @i:th:projective-characters-supported-p-regular, we obtain $d_(l i)=1$ if
  $zeta=zeta^l$ and $d_(m i)=0$ if $m!=l$. Since the block $upright(sans(B))_j$
  contains only one simple $k G$-module, it follows that
  $upright(bold(D))_j=(1)$, and hence $overline(P)_i$ is a simple $k G$-module,
  completing the proof. (This discussion gives a more conceptual version of the
  proof of @bib:CurtisReiner1962[CR] (86.3), which used the orthogonality
  relations for the coefficients of the matrix representation affording $zeta$.)
]

At the other extreme, the principal block $upright(sans(B))_1$ contains the
trivial character $1_G$, and hence has defect $e$, where $p^e=|G|_p$. Of course,
there may be other blocks of defect $e$. A criterion for irreducible characters
to belong to the principal block is easily derived from
@prop:ordinary-block-reduced-central-character (see the Exercises).

Returning to the general discussion, we next characterize the defect in terms of
the degrees of the simple $k G$-modules.

#proposition[
  The defect $d_j$ of the $p$-block $upright(sans(B))_j$ satisfies the equation
  $ d_j=e-min {v_p lr((f_i)):F_i in upright(sans(B))_j}. $
] <prop:block-defect-brauer-degrees>
#proof[
  By @i:cor:decomposition-matrix-primitive-columns, the $s times r$ matrix
  $overline(upright(bold(D)))$ has rank $r$. It follows that for each block
  $upright(sans(B))_j$, the $x_j times y_j$ matrix
  $overline(upright(bold(D)))_j$ has rank $y_j$. On the other hand, we have
  $ zeta^i|_(G_(p'))=sum_(l=1)^r d_(i l)phi^l, quad 1<=i<=s, $
  #source(440)
  by @i:eq:ordinary-brauer-decomposition. Upon evaluating both sides at 1 for
  the characters belonging to $upright(sans(B))_j$, we obtain
  $
    mat(delim: "[", z_(j_1); dots.v; z_(j_(x_j)))
    =upright(bold(D))_j mat(delim: "[", f_(j_1); dots.v; f_(j_(y_j))),
  $
  where
  ${z_(j_1),dots,z_(j_(x_j))}$
  and
  ${f_(j_1),dots,f_(j_(y_j))}$
  are the degrees of the characters $zeta^i in upright(sans(B))_j$ and
  $phi^i in upright(sans(B))_j$, respectively. Since
  $overline(upright(bold(D)))_j$ has rank $y_j$, it follows that
  $
    v_p lr((op("G.C.D.")(z_(j_1),dots,z_(j_(x_j)))))
    =v_p lr((op("G.C.D.")(f_(j_1),dots,f_(j_(y_j))))).
  $
  Then by @def:block-defect,
  $
    e-d_j=min {v_p lr((z_i)):Z_i in upright(sans(B))_j}
    =min {v_p lr((f_i)):F_i in upright(sans(B))_j},
  $
  completing the proof.
]

Restating the preceding results, we have:

#corollary[
  The defect $d_j$ of $upright(sans(B))_j$ is characterized as follows:
  $
    d_j & = "smallest integer" (>=0) "such that"
          p^(e-d_j) divides z_i "for all" Z_i in upright(sans(B))_j, \
        & = "smallest integer" (>=0) "such that"
          p^(e-d_j) divides f_i "for all" F_i in upright(sans(B))_j.
  $
] <cor:block-defect-degree-divisibility>

We next find connections between the defect $d_j$ of $upright(sans(B))_j$ and
the coefficients of the block idempotent $b_j in c(R G)$. We shall write
$ b_j=sum_(m=1)^s a_(j m) C_m, quad "where" a_(j m) in R; $
<eq:block-idempotent-class-sum-coefficients>
then $overline(b)_j=sum_(m=1)^s overline(a)_(j m)overline(C)_m$ is the
corresponding block idempotent in $c(k G)$, by
@prop:commutative-order-primitive-idempotents. For each block
$upright(sans(B))_j$, there is a central character $psi_j:c(k G) -> k$,
characterized by the conditions (see
@prop:modular-central-characters-block-idempotents)
$ psi_j lr((overline(b)_j))=1, quad psi_j lr((overline(b)_l))=0, quad l!=j. $
Moreover, each simple $K G$-module $Z$ is associated with a central character
$omega$, defined by @eq:ordinary-central-character-values, and we have
$ overline(omega)=psi_j arrow.l.r.double Z in upright(sans(B))_j, $
by @prop:ordinary-block-reduced-central-character.

We also require the character table data, as summarized in
@i:def:brauer-character-table-data and §~@i:ss:brauer-character-orthogonality.
In particular, the conjugacy classes are arranged so that
$cal(C)_1,dots,cal(C)_r$ are the $p'$-classes. The value of a character $zeta^i$
on an element of the class $cal(C)_j$ is given by
#source(441)
$zeta_j^i$, while $zeta_(j*)^i$ denotes $zeta^i lr((x^(-1)))$, $x in cal(C)_j$.
Similar notations are used for the Brauer characters $phi^i$ and $eta^i$,
$1<=i<=r$.

#proposition[
  The coefficients of the block idempotent $b_j=sum a_(j m)C_m$ in $c(R G)$ are
  given by
  $ a_(j m)=g^(-1)sum_(Z_i in upright(sans(B))_j) z_i zeta_(m*)^i $
  while for $p$-regular classes $cal(C)_m$, we also have
  $ a_(j m)=g^(-1)sum_(F_l in upright(sans(B))_j) u_l phi_(m*)^l. $
] <prop:block-idempotent-character-coefficients>
#idx(
  "Block idempotents",
  "coefficients of",
  target: [@prop:block-idempotent-character-coefficients],
)
#proof[
  The first formula is immediate from
  @prop:block-idempotent-ordinary-components. Using the first formula, we have,
  for a $p$-regular class $cal(C)_m$,
  $
    a_(j m) & =g^(-1)sum_(Z_i in upright(sans(B))_j) z_i zeta_(m*)^i
              =g^(-1)sum_(Z_i in upright(sans(B))_j) z_i
              lr((sum_(F_l in upright(sans(B))_j) d_(i l)phi_(m*)^l)) \
            & =g^(-1)sum_(F_l in upright(sans(B))_j)
              lr((sum_(Z_i in upright(sans(B))_j) d_(i l)z_i))phi_(m*)^l \
            & =g^(-1)sum_(F_l in upright(sans(B))_j) u_l phi_(m*)^l
  $
  since
  $
    (eta_j^i)=upright(bold(C))(phi_j^i)
    =attach(upright(bold(D)), tl: t)upright(bold(D))(phi_j^i)
    =attach(upright(bold(D)), tl: t)(zeta_j^i)
  $
  by @i:eq:brauer-character-matrix-identities and
  @i:cor:cartan-decomposition-gram-matrix. This completes the proof.
]

#definition[
  The _defect_ $delta_i$ of the conjugacy class $cal(C)_i$ of $G$ is the
  nonnegative integer
  $ delta_i=e-v_p lr((h_i)) quad "where" h_i=|cal(C)_i|. $
  If $x in cal(C)_i$, then $h_i=|G:C_G lr((x))|$, and thus
  $delta_i=v_p lr((|C_G lr((x))|))$, $x in cal(C)_i$.
] <def:conjugacy-class-defect>
#idx("Defect of conjugacy class", target: [@def:conjugacy-class-defect])

The next result includes Osima’s theorem that the block idempotents in $c(R G)$
are supported on the $p$-regular classes, and relates the coefficients of the
block idempotents in $c(k G)$ to the class defects $delta_j$.

#proposition[
  Let $b_j=sum a_(j m)C_m$ be a block idempotent in $R G$ belonging to a block
  $upright(sans(B))_j$ of defect $d_j$. The coefficients satisfy the conditions:
  #enum(
    numbering: "(i)",
    [$a_(j m)=0$ for each $p$-irregular class $cal(C)_m$, and],
    [$overline(a)_(j m)=0$ for each $p$-regular class $cal(C)_m$ such that
      $delta_m>d_j$.],
  )
] <prop:block-idempotent-support-class-defect>
#idx("Osima's Theorem", target: [@prop:block-idempotent-support-class-defect])

The proof of the first part is based on a lemma:
#source(442)

#lemma[
  For all $p$-irregular $x in G$ and $p$-regular $y in G$ we have
  $ sum_(Z_i in upright(sans(B))_j) zeta^i lr((x))zeta^i lr((y))=0. $
] <lem:block-mixed-character-orthogonality>
#proof[
  Let $upright(bold(Z))=(zeta_j^i)^(s times r)$ be the matrix of character
  values of the $zeta^i in op("Irr") G$ on the $p$-regular classes. Since $x$ is
  $p$-irregular, we have
  $ (zeta^1 lr((x)),dots,zeta^s lr((x)))upright(bold(Z))=0 $
  by the second orthogonality relation
  @i:prop:first-second-character-orthogonality. The same formula holds with
  $upright(bold(D))$ in place of $upright(bold(Z))$, since
  $upright(bold(Z))=upright(bold(D))upright(bold(Phi))$ and $upright(bold(Phi))$
  is invertible. Using the distribution of the characters $zeta^i$ into blocks,
  together with the resulting decomposition @eq:block-decomposition-matrix of
  the decomposition matrix $upright(bold(D))$, it follows that for each $l$ such
  that $phi^l in upright(sans(B))_j$, we have
  $ sum_(Z_i in upright(sans(B))_j) zeta^i lr((x))d_(i l)=0. $
  Therefore, after multiplying by $phi^l lr((y))$ and summing on $l$, we obtain
  the desired formula, since
  $ zeta^i lr((y))=sum_(F_l in upright(sans(B))_j) d_(i l)phi^l lr((y)). $
]

#proof(head: emph[Proof of @prop:block-idempotent-support-class-defect.])[
  (i) This result follows at once by setting $y=1$ in
  @lem:block-mixed-character-orthogonality and applying the first formula for
  the coefficients $a_(j m)$ in @prop:block-idempotent-character-coefficients.

  (ii) Assume $delta_m>d_j$, let $Z_i in upright(sans(B))_j$, and let $omega^i$
  be the central character of $K G$ corresponding to $Z_i$, as in
  @eq:ordinary-central-character-values. Then
  $ omega^i lr((C_m))=h_m zeta_m^i slash z_i in R, $
  and it follows that $zeta_m^i in frak(p)$, because
  $
    v_p lr((z_i slash h_m))=v_p lr((z_i))-v_p lr((h_m))
    >=(e-d_j)-(e-delta_m)=delta_m-d_j>0.
  $
  Since $overline(upright(bold(D)))_j$ has rank $y_j$ (as we noted in the proof
  of @prop:block-defect-brauer-degrees), and
  $upright(bold(Z))=upright(bold(D))upright(bold(Phi))$, it follows that
  $phi_m^i in frak(p)$ for all $F_i in upright(sans(B))_j$. But
  $v_p lr((u_i slash g))>=0$ by Exercise
  @i:exc:projective-degree-p-part-divisibility, so $u_i slash g in R$, and hence
  (using @prop:block-idempotent-character-coefficients),
  $ a_(j m)=g^(-1)sum_(F_l in upright(sans(B))_j) u_l phi_(m*)^l in frak(p), $
  completing the proof.
]

#remark(numbered: false)[
  #idx("p-Blocks", "congruence criterion")
  We can now give a more useful version of the congruence criterion
  @cor:block-central-character-congruence. Namely, $zeta$ and $zeta'$ belong to
  the same $p$-block if and only if the condition
  @cor:block-central-character-congruence holds for all $p$-regular $x$. The
  proof, based on @prop:block-idempotent-support-class-defect(i), is left as an
  exercise.
]
#source(443)

In the course of the proof of @prop:block-idempotent-support-class-defect, we
used the important fact that
$
  v_p lr((u_i))>=v_p lr((g))=e quad
  "for each P.I.M." U_i, quad 1<=i<=r,
$
<eq:projective-block-degree-divisibility>
by Exercise @i:exc:projective-degree-p-part-divisibility. The next result shows
that this inequality cannot be improved, for P.I.M.’s belonging to a given
block.

#corollary[
  Each $p$-block $upright(sans(B))_j$ contains a P.I.M. $U_i$ such that
  $ v_p lr((u_i))=e. $
] <cor:block-projective-degree-minimum>
#idx(
  "Principal indecomposable module (P.I.M.)",
  target: [@cor:block-projective-degree-minimum],
)
#proof[
  Suppose $v_p lr((u_i))>e$ for all P.I.M.’s $U_i in upright(sans(B))_j$. Then
  $v_p lr((u_i slash g))>0$ for each $U_i in upright(sans(B))_j$, and we obtain
  $overline(b)_j=0$ by @prop:block-idempotent-support-class-defect(i) and
  @prop:block-idempotent-character-coefficients, contrary to the fact that
  $overline(b)_j$ is a block idempotent in $c(k G)$.
]

The main result of this subsection is the following theorem, which asserts that
the defect of a block is equal to the defect of certain conjugacy classes. These
classes are determined from the coefficients of the corresponding block
idempotent in $k G$.

#theorem[
  Let $upright(sans(B))_j$ be a block of defect $d_j$, with block idempotent
  $b_j=sum a_(j m)C_m$. Let $psi_j$ be the corresponding central character of
  $k G$. Then the following statements hold.
  #enum(
    numbering: "(i)",
    [$psi_j lr((overline(b)_j))
      =sum_(1<=m<=r,delta_m=d_j) overline(a)_(j m)psi_j lr((overline(C)_m))
      =1$;],
    [$overline(b)_j=sum_(1<=m<=r,delta_m<=d_j) overline(a)_(j m)overline(C)_m$;
      and],
    [$psi_j lr((overline(a)_(j m)overline(C)_m))!=0$ for some $p$-regular class
      $cal(C)_m$ of defect $d_j$.],
  )
] <th:block-defect-central-character-criterion>
#proof[
  This result follows easily from the preceding discussion, as soon as we
  establish one further point, namely: for each class $cal(C)_m$ of defect
  $delta_m$,
  $ psi_j lr((overline(C)_m))=0 quad "whenever" delta_m<d_j. $
  <eq:central-character-vanishes-smaller-defect>
  To prove this, choose $Z_i in upright(sans(B))_j$ such that
  $v_p lr((z_i))=e-d_j$. Then $overline(omega)^i=psi_j$, and we have
  $ omega^i lr((C_m))=h_m zeta_m^i slash z_i. $
  Moreover,
  $
    v_p lr((h_m slash z_i))=v_p lr((h_m))-v_p lr((z_i))
    =(e-delta_m)-(e-d_j)=d_j-delta_m>0,
  $
  so $omega^i lr((C_m)) in frak(p)$. Thus $psi_j lr((overline(C)_m))=0$, as
  required.

  The rest of the proof is left as an exercise for the reader.
]

#corollary[
  A simple $K G$-module $Z_i$ belongs to a $p$-block of defect $d$ if and only
  if the following conditions are satisfied:
  #source(444)
  #enum(
    numbering: "(i)",
    [$omega_i lr((C_m)) in frak(p)$ whenever $delta_m<d$, $1<=m<=r$; and],
    [$omega_i lr((C_l)) in.not frak(p)$ for some $p$-regular class $cal(C)_l$ of
      defect $d$.],
  )
] <cor:ordinary-character-block-defect-criterion>

#exercises-heading

All the exercises are stated with reference to a $p$-modular system $(K,R,k)$
such that $"char" K=0$ and $K$ is sufficiently large relative to $G$.

#exercise[
  Prove that $c(k G) slash rad c(k G)$ is a split semisimple $k$-algebra.
] <exc:modular-center-split-semisimple-quotient>
#hint([@exc:modular-center-split-semisimple-quotient])[
  Use @prop:split-modular-central-characters.
]

#exercise[
  Let $G$ be a direct product, $G=G_1 times G_2$. Prove that
  $c(k G) tilde.equiv c(k G_1) times.o c(k G_2)$, and that every central
  character of $k G$ can be expressed as a product $psi=psi_1 times.o psi_2$,
  where $psi_1$ and $psi_2$ are central characters of $k G_1$ and $k G_2$,
  respectively.
] <exc:direct-product-central-characters>
#hint([@exc:direct-product-central-characters])[
  Use Exercise @exc:modular-center-split-semisimple-quotient and
  @i:th:outer-tensor-separable.
]

#exercise[
  Prove that if $beta_1$ is a block idempotent of $k G_1$ and $beta_2$ is a
  block idempotent of $k G_2$, then $beta_1 times.o beta_2$ is a block
  idempotent of $k(G_1 times G_2) tilde.equiv k G_1 times.o k G_2$.
] <exc:direct-product-modular-block-idempotents>
#hint([@exc:direct-product-modular-block-idempotents])[
  Use @prop:blocks-central-character-bijection.
]

#exercise[
  Prove the assertion of Exercise @exc:direct-product-modular-block-idempotents
  for block idempotents of $R G$.
] <exc:direct-product-integral-block-idempotents>

#exercise[
  Let
  ${zeta_(1 1),dots,zeta_(1 m_1)}$
  and
  ${zeta_(2 1),dots,zeta_(2 m_2)}$
  be $p$-blocks of $K$-characters of $G_1$ and $G_2$, respectively. Prove that
  ${zeta_(1 i) dot zeta_(2 j):1<=i<=m_1,1<=j<=m_2}$
  is a $p$-block of $K$-characters of $G_1 times G_2$.
] <exc:direct-product-ordinary-character-blocks>
#hint([@exc:direct-product-ordinary-character-blocks])[
  Use @prop:block-idempotent-ordinary-components together with the preceding
  exercises.
]

#exercise[
  Determine the $p$-blocks of $K$-characters, and their defects, for a finite
  abelian group $G$.
] <exc:finite-abelian-group-blocks>
#hint([@exc:finite-abelian-group-blocks])[
  Use the examples at the end of §~@ss:finite-group-p-block-definition, and the
  preceding exercises.
]

#exercise[
  Let $omega:c(K G) -> K$ be a central character of $K G$ associated with an
  irreducible $K$-character $zeta$ (see @eq:ordinary-central-character-values).
  Prove that $zeta$ belongs to the principal block if and only if
  $omega(C) equiv |cal(C)| (mod frak(p))$ for each class sum
  $C=sum_(x in cal(C)) x$. Use this to determine the $K$-characters belonging to
  the principal $p$-block in the symmetric groups $S_3$, $S_4$, $S_5$ for
  $p=2,3,5$, using their character tables (see Volume I, end of
  §~@i:ss:character-table).
] <exc:principal-block-central-character-test>

#exercise[
  Prove that if a $p$-block of $k G$-modules contains a P.I.M. which is a simple
  $k G$-module, then the block has defect zero.
] <exc:simple-projective-block-defect-zero>
#hint([@exc:simple-projective-block-defect-zero])[
  Use @prop:block-defect-brauer-degrees and
  @eq:projective-block-degree-divisibility.
]

#exercise[
  Let $zeta$ be an irreducible $K$-character of $G$ such that $zeta(x)=0$ for
  all $p$-irregular $x in G$. Prove that $zeta$ belongs to a $p$-block of defect
  zero.
] <exc:irreducible-p-singular-vanishing-defect-zero>

#exercise[
  Fill in the details of the following alternative proof of
  @prop:defect-zero-block-singletons. Let $upright(sans(B))_j$ have defect zero,
  let $Z$ be a simple $K G$-module in $upright(sans(B))_j$, and let $e$ be the
  primitive central idempotent in $K G$ associated with
  #source(445)
  $Z$. Then $e in R G$, since $upright(sans(B))_j$ has defect zero. We may write
  $
    K G=plus.o.big M_(n_i) lr((K)), quad Gamma=plus.o.big Gamma_i,
    quad Gamma_i tilde.equiv M_(n_i) lr((R)),
  $
  with $Gamma$ a maximal $R$-order in $K G$. By
  @i:th:jacobinski-conductor-formula, $plus.o.big (g slash n_i)Gamma_i$ is the
  largest $Gamma$-ideal in $R G$. If $Z$ is a simple $M_(n_i) lr((K))$-module,
  then $n_i=zeta(1)$, and we deduce that $Gamma_i subset.eq R G$. Therefore
  $Gamma_i=R G dot e$, so the $R$-block ideal $B_j tilde.equiv M_(n_i) lr((R))$.
  It follows that
  $
    Z tilde.equiv K^((n_i)), quad P tilde.equiv R^((n_i)),
    quad overline(P) tilde.equiv k^((n_i)) tilde.equiv F_i tilde.equiv U_i,
  $
  where $P$ is the unique P.I.M. belonging to $upright(sans(B))_j$. The
  remaining assertions of @prop:defect-zero-block-singletons are now clear, with
  the last statement following as in Step 1 of the proof of
  @i:th:projective-lattice-character-image.
] <exc:defect-zero-block-maximal-order-proof>




