# V1 Structured Diff Layer

The V1 layer adds a structured, line-oriented diff model for agent edits. It is
implemented in the `VersionControl` namespace and integrated with the existing
repository foundation in `VersionControl.Basic`.

## Architecture

The implementation separates edit content from version history:

- A `Diff` describes one agent's proposed edits to one file.
- A `Hunk` describes one edit operation over a half-open line range.
- `History.lean` records linear commit metadata separately from the JSON diff.

The JSON format stores edits. Commit history is handled separately.

## Modules

- `VersionControl/Defns.lean` defines the V1 datatypes, JSON instances,
  validation predicates, hunk ordering, and executable schema checks.
- `VersionControl/JsonParse.lean` provides `parseDiffJson`, `parseDiff`, and
  `diffAsJson`.
- `VersionControl/Semantics.lean` defines base-checked diff application and
  inverse-diff helpers.
- `VersionControl/Conflict.lean` defines hunk and diff conflict predicates plus
  executable conflict flags.
- `VersionControl/History.lean` models linear push histories and nearest common
  parent splits.
- `VersionControl/FullMerge.lean` connects replay, residual diffs, conflict
  witnesses, and pairwise merge checks.

## Validation Model

The schema checks enforce:

- agent identifiers start at `1`
- file paths are non-empty
- hunk sequence numbers start at `1`
- ranges are 1-indexed and half-open
- `insert`, `delete`, and `replace` hunks have matching `before` and `after`
  shapes
- hunks within a diff are pairwise non-overlapping

The base checks also verify that:

- `base_line_count` matches the supplied base file
- each hunk's `before` lines match the corresponding slice of the base file

The base-alignment check prevents stale edits from being applied to the wrong
file contents.

## Conflict Model

Two hunks conflict when they target overlapping old-line ranges or when they are
same-point inserts with different inserted text. Identical edits are treated as
compatible.

The code defines both logical predicates and Boolean checks. The Boolean checks
are proved equivalent to the logical predicates.

## Build

The V1 layer uses Lean `v4.30.0-rc2` and mathlib `v4.30.0-rc2`.

```sh
lake build
```

For the full technical write-up, including type definitions, implementation
notes, checked theorem inventory, and open work, see
`docs/V1_TECHNICAL_REPORT.tex`.

## Open Work

- Add a monadic pipeline for parsing, validation, conflict checks, and merge
  checks.
- Add explicit invalid-input flags for JSON parse failures, schema failures,
  and base-alignment failures.
- Add explicit merge-conflict flags. The core already returns conflict
  witnesses, but callers still need a clear flag to report.
- Add commit-graph history support if branch and merge commits are needed.
- Add a timestamp parser if Lean must reject invalid date-time strings.
