# Source conventions

The main file includes ordinary Typst chapter and section files.
Chapters 5–11 and Sections 38–81 continue the first volume. The heading
and section counters begin at 4 and 37 before Chapter 5.
Lettered subsections are native level-three headings.
An unnumbered appendix within a lettered subsection uses a native
`heading(level: 4, numbering: none)` with a literal `<app:semantic-name>`
label immediately after it. This family requires exactly one such heading;
it does not create a numbered object or advance the subsection counter.
Its native `@app:semantic-name` reference prints the complete computed title
and links to the appendix itself. A reference inside the title remains native,
for example `Appendix to §@ss:basic-formulas`. Do not prepend another § to
a reference that prints this complete title. The `ss:` family remains
reserved for native level-three subsection headings.

Statements and displayed equations share the series `(section.item)`.
An exceptional series starting at zero uses `#item-series(start: 0)`
after its section heading. The native counter still counts every object;
the section offset resets at the next heading. Inserted lettered statements
use a suffix helper with a native reference to their base object.
When the first actual statement already has a letter, use
`theorem-suffix(suffix: "A")[…] <th:first>` without a base. It advances
the shared series once. A following `theorem-suffix(base: [@th:first],
suffix: "B")[…]` reuses that number; the next ordinary object advances
normally. A statement suffix is one uppercase or lowercase letter or a prime.
An author's symbolic display uses `named-equation(name: [$(ast)$])[$ … $]`
with a literal `<eq:…>` label. Its native reference prints the symbol;
the display does not advance the shared numerical series.
Exercises have their own counter within each section. Every numbered
object has a literal semantic label immediately after it; references use
native `@label` syntax.
A formal case list can continue after an ordinary paragraph with
`case-list(start: n, ...)`. Its visible and referenced case numbers start
together at n; an independent list starts at 1 by default. For literal names,
use `case-list(prefix: "Case ", numbering: "1.", ...)` or
`case-list(prefix: "Problem ", numbering: "I.", ...)`. The string prefix
affects the native item label; the numbering pattern stays numerical.
Write the word separately in a reference, for example `Case~@case:target`.
Named lemmas and theorems use the `name` argument;
unnumbered remarks use `remark(numbered: false)`, and an unnumbered example uses
`example(numbered: false)`.
Use `definitions` for an author's plural heading; it counts as one item in
the definition family.

Author hints retain their positions, including several hints within one
exercise. Its number links to the first hint; every hint links back to the
exercise. Use `exercise-heading` for a singular heading and
`exercises-heading` for a plural one.
An original footnote called more than once uses a semantic `<fn:…>` label
and native `footnote(<fn:…>)` calls. Keep every marker on its entry's page.
The label belongs to the native footnote itself. The shared note passage
stays together across statement and proof boundaries.
Footnote entries remain unbroken, including long editorial notes beside
author notes; their whole text stays on the marker's page.

Use native mathematical attachments; separate an external argument from
an index, for example `f_i lr((x))`. Lists use native `enum` items.
Layout rules belong to the common style, never to individual passages.
Ordinary statement blocks keep their introductory paragraph with the first
item of a following native list, diagram block or displayed equation. Statements
with notes retain their native outer paragraph flow so that complete entries
stay on their marker pages.
Matrices needing cell spans or different separator strokes use the common
`block-matrix(columns, cells, hlines: (), vlines: (), delimiters: …)`.
Use native `grid.cell` spans and line records with `at` and optional `dashed`;
pass the source's delimiters explicitly.
Native diagrams wider than the text column use `fit-diagram` around the
unwrapped diagram content. It scales uniformly only when needed and uses
native reflow to reserve the resulting size. Keep diagram data and labels
unchanged, and inspect the actual scaled output for readability.

Bibliographic descriptions are stored only in `references.bib` and
`editorial.bib`. The printing file supplies author groups, the original
year labels, and literal semantic labels. Page backlinks are computed
from mentions in the text, including notes, excluding the bibliography
itself. Index entries come only from `idx` marks next to their semantic
targets, and their page numbers are computed at build time.
An author's related-entry instruction uses `see-also: (("Target entry",),)`
on its ordinary `idx` mark. Each target is an existing index path, with one
string per nested level. The generated link reaches the target's index row;
the entry's page locators still reach the underlying definition. Repeated
relations are deduplicated, and final checks reject missing target paths.
A see-only redirect uses `idx("Author term", see: ("Target",))`. It has no
body locator or semantic `target`; its `see` path must name an exact existing
index entry. The generated link reaches that entry's index row.
Notation entries use `nidx("$symbol$", "meaning", target: [@def:object])`;
they form a separate index, grouped by the target's numbered chapter.
Names and explanations occur only in these marks. Both indexes use the
actual target for their page number and link, even when a mark occurs later.
An entry grouped by the author under another chapter uses a native group
reference, for example `chapter: [@ch:class-groups]`. Its page locator still
uses the definition target; no chapter number is typed into the mark.
Numerical citations use ordinary computed `@bib:Key` references, followed
by their external locators in prose. A descriptive caption such as `CR`
or `MO` may replace the number; never repeat a year tag by hand in a caption.
Editorial citations identify a section, theorem, lemma, proposition or
exercise whenever possible. Use a page locator only for unnumbered material.
Bibliography keys retain surname particles, for example `vanderKallen1977`.

References to Volume I use native namespaced labels such as
`@i:th:krull-schmidt-azumaya`. The catalogue in
`config/external-references.json` pins the companion edition, native object
numbers and physical PDF destinations. The `external-catalog` Typst input
is shared by CLI and editor settings. Finalization converts the registered
links to PDF remote actions that preserve zoom; checks require an exact
match between those actions, catalogue entries and reference metadata.
The companion PDF must match the catalogue checksum. Its references are
checked separately from the language server's local definition jumps.

The added cover is outside printed pagination. The title, publication
leaf, dedication and blank verso occupy iii–vi; the preface begins vii.
Contents continue the Roman series. Their pages reflow
freely; a counted blank verso is inserted only when needed before a new
preliminary part on an odd folio.
This edition displays a folio on every Contents page; the original's last
two Contents pages omit their visible folios but remain counted.
The half-title and its blank verso precede Chapter 5; the main
text restarts at Arabic 1. Hidden folios continue the page count.

Only the book with editorial notes and its separate corrections PDF are
produced. Fonts are supplied with their licenses in `assets/fonts`.

The native tool versions are pinned in `config/project.json`. Tinymist
0.15.12-rc1 includes the [dynamic-import analysis memory fix][import-fix].
Use the official release archive for the platform and verify its checksum.
A separate executable directory can be selected with `BOOK_TOOL_PATH` in
the local `.env`; `just` prepends it to the command search path.
`BOOK_CACHE_DIR` selects an optional build cache directory.
Run `just check` for the complete PDF and native-navigation checks.

[import-fix]: https://github.com/Myriad-Dreamin/tinymist/pull/2761
