#import "content/book-style.typ": book-style
#import "content/main-defs.typ": *
#import "content/statements.typ": *
#show: book-style
#set page(header:none,footer:none)
#set page(width:176mm)
#block(height:135mm)[ENGINEERING PRESSURE]
PREVIOUS prose has another note.#footnote[PREVIOUSENTRY A distinct preceding note.]
#theorem[
 Opening assertion for the native cases.
 #case-list(keep-together:true,numbering:"1.",prefix:"Case ",start:3,
 [#case[The first native case concludes.]<case:first>],
 [#case[
  A continuation paragraph begins the argument.

  FIRSTREPEAT The author note is here.#footnote[REPEATENTRY The one labelled entry.]<fn:repeat>
  SECONDREPEAT The same author note is used again.#footnote(<fn:repeat>)
  A different clarification follows.#ed-note[EDITENTRY The editorial note.]
 ]<case:second>],
 )
]<th:control>
AFTER Case~@case:first and Case~@case:second; theorem @th:control.
#case-list([#case[The following list resets.]<case:reset>])
Reset @case:reset.
