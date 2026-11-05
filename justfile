# Machine settings such as LEAN_MATHLIB may be kept in a local .env file.
set dotenv-load

python := env("PYTHON", "python3")
tool_path := env("BOOK_TOOL_PATH", "")
export PATH := if tool_path == "" { env("PATH") } else {
    tool_path + ":" + env("PATH")
}

default: build

# Validated PDF, with cached no-op when source files have not changed.
build:
    {{python}} scripts/project.py build

# CI gate: format, lint, PDF links/layout, tests, corrections.
check:
    {{python}} scripts/project.py check

# Formatter check, source rules and the evaluated document (T000-T099).
lint:
    {{python}} scripts/project.py lint

# Format the Typst sources in place (Typstyle with the Tinymist settings).
fmt:
    {{python}} scripts/project.py fmt

# Unit tests: corrections schema, labels, bibliography, numbering, lint rules.
test:
    {{python}} scripts/project.py test

# The reader's list of corrections: build/curtis-repr.2.corrections.pdf
corrections:
    {{python}} scripts/project.py corrections

# Remove build/ and the configured build cache.
clean:
    {{python}} scripts/project.py clean

# Advisory prose check (Harper); dictionary and rules shared with VS Code.
check-prose:
    {{python}} scripts/check_prose.py

# Validate the PDF exported by the editor using the same Python setting.
editor-prepare:
    {{python}} scripts/project.py editor-prepare

editor-finish:
    {{python}} scripts/project.py editor-finish

# Exact algebra and finite-group checks with the installed SageMath.
check-sage:
    {{python}} scripts/check_sage.py

# Compile and audit declarations using the pinned Lean environment.
check-lean:
    {{python}} checks/lean/check_axioms.py
