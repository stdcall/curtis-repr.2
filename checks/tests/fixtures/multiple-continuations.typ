#import "content/book-style.typ": book-style
#import "content/main-defs.typ": *
#import "content/statements.typ": *
#show: book-style
#set page(header: none, footer: none)
= Engineering <ch:continuations>
== Native Note Continuations <sec:continuations>
#proposition[
  #case-list(prefix: "Case ", numbering: "1.", start: 2,
    [#case[
      FIRSTCONT The first observation has a note.#ed-note[
        FIRSTENTRY This explanation belongs to the first observation.
      ] Its argument continues through the following native display:
      $ x + y = z. $ <eq:first-continuation>
      This is still the author's continuing paragraph.

      SECONDCONT A separate paragraph has an author note.#footnote[
        SECONDENTRY This independent explanation belongs to the second
        observation.
      ] The same paragraph also continues through a native display:
      $ z - y = x. $ <eq:second-continuation>
      Its conclusion remains in the same formal case. FIRSTEND
    ] <case:first-continuation>],
    [#case[SECONDCASE The next assertion has no note.]
      <case:second-continuation>],
  )
] <prop:continuations>
#case-list(
  [#case[RESET The next ordinary case-list starts at one.]
    <case:continuation-reset>],
)
The references are Case~@case:first-continuation,
Case~@case:second-continuation, @case:continuation-reset,
@eq:first-continuation, and @eq:second-continuation.
