#import "content/book-style.typ": book-style
#import "content/main-defs.typ": *
#import "content/statements.typ": *
#show: book-style
#set page(header:none,footer:none)
#block(height:170mm)[ENGINEERING PRESSURE]
#proof[
 The final step of the preceding argument is
 $ [f]=[g]-[s]=[g]+[gamma]-[s]-[delta] in im i_1, $
 which completes the proof that $ker partial subset.eq im i_1$. This
 establishes the exactness of the Localization Sequence.
]
#corollary[
  Let $S$ be a multiplicative subset of the commutative ring $R$, let $Lambda$
  be an $R$-algebra which is $S$-torsionfree and is a left noetherian
  ring,#footnote[This hypothesis certainly holds if $Lambda$ is f.g./$R$ and $R$
    is noetherian.] and set $Lambda' = S^(-1) Lambda$. Then the sequence
  $
    K_1 lr((Lambda)) -> K_1 lr((Lambda')) -> K_0 lr((cal(T)))
    -> K_0 lr((Lambda)) -> K_0 lr((Lambda'))
  $
  is exact, where $cal(T)$ is the category of all f.g. $S$-torsion
  $Lambda$-modules of finite homological dimension over $Lambda$.
] <cor:algebra-whitehead-localization>

AFTER The corollary is @cor:algebra-whitehead-localization.
