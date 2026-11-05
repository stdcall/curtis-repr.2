#import "content/book-style.typ": book-style
#import "content/main-defs.typ": *
#import "content/statements.typ": *
#show: book-style
#set page(header:none,footer:none)
#set page(width:156mm)
#block(height:150mm)[ENGINEERING PRESSURE]
#theorem[
  Let $M$ be a simple $CC G$-module, affording the character $mu$.
  #case-list(
    keep-together: true,
    numbering: "(i)",
    [#case[
      If $M$ does not admit a nonzero $G$-invariant bilinear form, then $mu$ is
      not real-valued, and $M$ has no $RR$-form. Call $M$ _unitary_ in this
      case.
      #idx("Unitary CG-module")
    ]<case:unitary-simple-complex-module>],
    [#case[
      If $M$ admits a nonzero $G$-invariant bilinear form, then this form is
      unique up to scalar multiples. It is nondegenerate, and is either
      symmetric or skew-symmetric. If the form is symmetric, then $mu$ is
      real-valued, and $M$ has an $RR$-form. We call $M$ _orthogonal_ in this
      case (since $M$ affords a real representation of $G$ by orthogonal
      transformations).
      #idx("Orthogonal CG-module")

      If the form is skew-symmetric, then $mu$ is real-valued, but $M$ has no
      $RR$-form. We call $M$ _symplectic_, since $M$ affords a representation of
      $G$ by symplectic transformations.#footnote[
        A _symplectic transformation_ on a vector space over a field is a linear
        map preserving a nondegenerate skew-symmetric bilinear form on the
        vector space.
      ]
      #idx("Symplectic CG-module")
      #idx("Symplectic character")
    ]<case:orthogonal-symplectic-simple-complex-module>],
  )
]<th:simple-complex-module-form-types>

AFTER @th:simple-complex-module-form-types.
