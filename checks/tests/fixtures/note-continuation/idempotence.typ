#import "content/book-style.typ": book-style
#import "content/main-defs.typ": *
#import "content/statements.typ": *
#show: book-style
#set page(header:none,footer:none)
= Engineering chapter
== Engineering section
$ x=x $ <eq:schur-index-character-field-invariance>
#import "content/note-layout.typ": keep-note-runs
#let input = [An opening paragraph.

A later native continuation has a note.#footnote[The complete native note.]
It continues to the display
$ a=b, $
and then concludes.]
#let once = keep-note-runs(input)
#let twice = keep-note-runs(once)
#metadata((kind:"idempotence", equal:once==twice, once:repr(once), twice:repr(twice)))
#twice
