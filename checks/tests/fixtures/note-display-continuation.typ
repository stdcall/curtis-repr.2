#import "content/book-style.typ": book-style
#import "content/main-defs.typ": *
#import "content/statements.typ": *
#show: book-style
#set page(header:none,footer:none)
#block(height:150mm)[ENGINEERING PRESSURE]
#proof[
#case-list(numbering: "Step 1.", [#case[
      This time we shall assume that $G = N_G lr((Y))$, and will prove that
      $upright(sans(B))$ is a uniserial block, containing exactly $e$ simple
      modules and $e abs(D)$ indecomposable modules, where $e$ is the inertial
      index.

      In this case, $C_G lr((Y)) ⊴ G$, so $upright(sans(B))$ covers a unique
      conjugacy class of blocks of $C_G lr((Y))$, all with defect group $D$.
      This follows from Theorem 61.2, using the
      fact that $D <= C_G lr((Y))$ to calculate the defect groups. By
      Step 2, each of these blocks is
      uniserial, and contains exactly one simple module and $abs(D)$
      indecomposable modules.

      Our first objective is to prove that $upright(sans(B))$ is a uniserial
      block. Let $upright(sans(B))_0$ be a uniserial block of $C_G lr((Y))$ with
      defect group $D$ covered by $upright(sans(B))$ and let
      $T_0 = op("Stab")_G b_0$, where $b_0$ is the block idempotent of
      $upright(sans(B))_0$. Then $C_G lr((Y)) ⊴ T_0$, and we have

      $ abs(T_0 colon C_G lr((Y))) equiv.not 0 (mod p) $
      <eq:cyclic-defect-inertia-quotient-prime-to-p>

      by 61.5. Moreover, $upright(sans(B))_0$
      is covered by a unique block $tilde(upright(sans(B)))_0$ of $T_0$. Letting
      $B_0$ and $tilde(B)_0$ denote the block ideals of $upright(sans(B))_0$ and
      $tilde(upright(sans(B)))_0$, respectively, we have

      $
        rad tilde(B)_0 = tilde(B)_0(rad B_0) = (rad B_0) tilde(B)_0
      $ <eq:cyclic-defect-inertia-block-radical>

      by Exercise~62.6, because of
      62.47. Since $B_0$ is uniserial,
      we have $rad B_0 = u B_0 = B_0 u$ for some element $u in B_0$ by
      62.26, and hence the same is true for
      $tilde(B)_0$ because of 62.48. It
      follows that $tilde(upright(sans(B)))_0$ is also a uniserial block, by
      62.26.

      Since $B_0$ is a uniserial block containing a unique simple module,
      $T_0 = op("Stab")_G b_0$ coincides with the stabilizer of each
      indecomposable module in $upright(sans(B))_0$. This follows easily from
      the fact that the isomorphism class of an indecomposable module in
      $upright(sans(B))_0$ is determined by its composition length. Then
      $U^G = op("ind")_(T_0)^G U$ is an indecomposable module in
      $upright(sans(B))$ for each indecomposable module $U$ in
      $tilde(upright(sans(B)))_0$, by
      18.14. Moreover, $U$ is uniserial,
      and $F^G$ is a simple module for each composition factor $F$ of $U$. It
      follows that $U^G$ is also uniserial. Indeed, the conjugates of $b_0$
      indexed by $G slash T_0$ are orthogonal. A submodule of $U^G$ is the
      direct sum of its components under these idempotents, and all components
      are translates of its $b_0$-component, a $T_0$-submodule of $U$. Thus
      induction identifies the entire submodule lattices, and preserves
      uniseriality.#ed-note[
        Exactness alone does not preserve uniseriality: restriction from
        $k[t] slash (t^2)$-modules to $k$-spaces is exact and preserves simple
        modules, but sends the regular module to a nonuniserial two-dimensional
        space. The inertia hypothesis is essential; compare
        18.14.
      ]

      We can now complete the proof that $upright(sans(B))$ is a uniserial
      block. Each indecomposable module $M$ in $upright(sans(B))$ is
      $(G,D)$-projective, and hence $(G,C_G lr((Y)))$-projective, since
      $C_G lr((Y)) >= D$. Then $M divides V^G$ for some indecomposable module
      $V$ in $upright(sans(B))_0$, and it follows easily from
      18.14 that in fact
      $M tilde.equiv U^G$ for some indecomposable module $U$ in
      $tilde(upright(sans(B)))_0$. Then $M$ is uniserial by the preceding
      discussion, and we have proved that $upright(sans(B))$ is uniserial.

      It remains to count the simple and indecomposable modules.#ed-note[
        A nilpotent kernel alone does not ensure that a block remains primitive:
        the principal block of $k S_3$ in characteristic three maps onto both
        blocks of $k C_2$. The centrality hypothesis in
        62.46 is essential to its argument.
      ] Put $q=abs(D)$, $J=rad B$, $C_0=C_G lr((Y))$, and let $I$ be the
      augmentation ideal of $k Y$. If $U$ is a P.I.M. of $B_0$, it is free over
      $k Y$. Multiplication by $y-1$, for $Y=chevron.l y chevron.r$, has kernel
      of dimension $dim_k U slash p$. Since $U$ is uniserial of length $q$ with
      one simple type, $I U=(rad B_0)^(q slash p)U$. Hence
      $I B_0=(rad B_0)^(q slash p)$. The $T_0$-stable idempotent $b_0$ acts as
      identity on its unique covering block; uniqueness also follows from
      61.2(iv), since $C_(T_0) lr((D))<=C_0$. By
      62.48 the same equality holds in
      $tilde(B)_0$. The orthogonal conjugate idempotents give the matrix algebra
      identification
      $ B tilde.equiv M_(abs(G colon T_0)) lr((tilde(B)_0)), $
      which carries the $G$-stable ideal $I B$ to the matrix ideal generated by
      $I tilde(B)_0$. Consequently
      $ I B=J^(q slash p) subset.eq J^2, $
      since $q>p$.

      Let $tau:k G arrow k(G slash Y)$ be the quotient map. Then
      #source(538)
      $tau(b)$ is a block idempotent. To see this, a central decomposition of
      $B slash I B$ lifts to orthogonal idempotents $e,f$ in $B$. Its
      cross-corners lie in $J^2$, and $e J f=e J e dot e J f+e J f dot f J f$.
      Iteration and nilpotence of $J$ give $e J f=f J e=0$. Thus the lifted
      idempotents are central, contradicting the indecomposability of $B$.

      Write $overline(G)=G slash Y$, $overline(D)=D slash Y$. For every
      $p$-subgroup $P>=Y$, $P$ centralizes $Y$. In a coset $x Y$ centralizing
      $P slash Y$, if $x$ does not centralize $Y$, conjugation by $Y$ is
      transitive on that coset; otherwise the commutator homomorphism
      $P arrow Y$ is trivial or onto. As in
      62.46, central coefficient sums therefore
      give $tau sigma_P lr((b))=sigma_(P slash Y)tau(b)$. Since $Y$ is central
      in $C_G lr((P))$, nonzero Brauer idempotents survive this quotient. Thus
      the quotient block has defect $overline(D)$.

      Since $Y<=D$, $N_(overline(G)) lr((overline(D)))=N_G lr((D)) slash Y$. To
      compare inertial indices, put $C=C_G lr((D))$, $N=N_G lr((D))$, and choose
      the canonical block idempotent $c$ of $k C$ below $b$. Let
      $S=op("Stab")_N c$, and let $C^*$ be the preimage in $N$ of
      $C_(overline(G)) lr((overline(D)))$. The group $C^* slash C$ embeds in the
      kernel of $op("Aut") D arrow op("Aut") lr((D slash Y))$ and is a
      $p$-group. Since $S slash C$ has order $e$ prime to $p$, $S inter C^*=C$.
      The central-$Y$ block bijection in $k C$ shows that the
      $C^* slash C$-orbit of $tau(c)$ is free. Its orbit sum is one block
      idempotent of $k(C^* slash Y)$: the orthogonal idempotent matrix
      construction identifies its algebra with a matrix algebra over
      $k(C slash Y)tau(c)$. Its stabilizer in $N slash Y$ is $C^* S slash Y$.
      Since $sigma_D lr((b))c=c$, Brauer compatibility puts this orbit block
      below $sigma_(overline(D))(tau(b))$. Thus it is the canonical block below
      $tau(b)$, by 58.11. The quotient
      inertial index is therefore $abs(C^* S colon C^*)=abs(S colon C)=e$.

      Induction on $abs(G)$ now gives $e$ simple modules in $B slash I B$, and
      hence in $B$, since $I B subset.eq J$. Let $l$ be the common composition
      length of the P.I.M.'s of the symmetric uniserial algebra $B$, and let
      $F_1,dots,F_e$ be its simple modules. A nonzero P.I.M. $P$ is free over
      $k Y$, so $I P!=0$ and $l>q slash p$. Summing dimensions over one basic
      set of P.I.M.'s gives $l sum_i dim_k F_i$. Their quotients by $I$ have
      length $q slash p$, so their dimensions sum to
      $(q slash p)sum_i dim_k F_i$; at each radical depth the simple types are
      permuted, by 62.29. Each
      P.I.M. is free over $k Y$, so the first sum is $p$ times the second.
      Therefore $l=q$, and $B$ has $e q$ indecomposable modules by
      62.25. This completes the
      proof of Step 3.

] <case:fragment>])
]
AFTER @case:fragment.
