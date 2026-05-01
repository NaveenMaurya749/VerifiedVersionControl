
namespace VersionControl

namespace Diff

def checkAgainstBase (diff : Diff) (base : BaseFile) : Except String Unit := do
  diff.checkSchema
  match diff.newContent with
  | some _ =>
    -- Binary replacement: no line-count or hunk checks needed
    pure ()
  | none =>
    -- Text diff: verify base line count and hunk alignment
    if diff.base_line_count = base.length then
      pure ()
    else
      .error "declared base_line_count does not match the supplied base file"
    for hunk in diff.diffs do
      if hunk.before = slice base hunk.range then
        pure ()
      else
        .error s!"base drift detected at hunk {hunk.seq}"

end Diff

/--
Extracts the unchanged lines between two hunk application points.
Only meaningful for text content.
-/
def unchangedSegment (base : BaseFile) (cursor nextStart : Nat) : List String :=
  match base with
  | .text lines => (lines.drop (cursor - 1)).take (nextStart - cursor)
  | .binary _   => []

def applyOrderedHunks (base : BaseFile) : Nat → List Hunk → Except String BaseFile
  | cursor, [] =>
      match base with
      | .text lines => .ok (.text (lines.drop (cursor - 1)))
      | .binary _   => .ok base
  | cursor, hunk :: rest =>
      if _ : ¬ hunk.range.wellFormed base.length then
        .error s!"invalid range for hunk {hunk.seq}"
      else if _ : hunk.range.start < cursor then
        .error s!"overlapping or unsorted hunk sequence at hunk {hunk.seq}"
      else if _ : hunk.before ≠ slice base hunk.range then
        .error s!"base drift detected at hunk {hunk.seq}"
      else if _ : ¬ hunk.opMatchesShape then
        .error s!"operation shape mismatch at hunk {hunk.seq}"
      else do
        let tail ← applyOrderedHunks base hunk.range.stop rest
        -- tail is a Content but we need to prepend lines to it
        match tail with
        | .text tailLines =>
            let prefix := unchangedSegment base cursor hunk.range.start
            pure (.text (prefix ++ hunk.after ++ tailLines))
        | .binary _ =>
            .error s!"internal error: binary tail in text hunk application"

/--
Apply a single hunk to a base file.
-/
def applyHunk (hunk : Hunk) (base : BaseFile) : Except String BaseFile :=
  applyOrderedHunks base 1 [hunk]

/--
The main diff application function. Branches on whether the diff
is a binary replacement or a structured text diff.
-/
def applyDiff (diff : Diff) (base : BaseFile) : Except String BaseFile := do
  diff.checkAgainstBase base
  match diff.newContent with
  | some newContent =>
      -- Binary path: whole-file replacement, no hunk machinery
      return newContent
  | none =>
      -- Text path: apply sorted hunks
      applyOrderedHunks base 1 diff.sortedHunks

-- ============================================================
-- Theorems
-- ============================================================

@[simp, grind =] theorem applyDiff_empty
    (file : String) (hFile : file ≠ "") (base : BaseFile) :
    applyDiff
      { agent := 1
        file
        timestamp := "2026-01-01T00:00:00Z"
        base_line_count := base.length
        diffs := []
        newContent := none } base = .ok base := by
  simp [applyDiff, Diff.checkAgainstBase, Diff.checkSchema, hFile,
    Diff.sortedHunks, Diff.pairwiseSeparated, applyOrderedHunks]
  cases base <;> simp [applyOrderedHunks]

@[simp, grind =] theorem applyHunk_insert_at_start
    (line : String) (lines : List String) :
    applyHunk
        { seq := 1
          op := .insert
          range := { start := 1, stop := 1 }
          before := []
          after := [line] }
        (.text lines) =
      .ok (.text (line :: lines)) := by
  simp [applyHunk, applyOrderedHunks, unchangedSegment, slice,
    Range.wellFormed, Range.width, Hunk.opMatchesShape, Range.isInsert]

-- ============================================================
-- Inversion (unchanged from before)
-- ============================================================

def invertOp (op : Op) : Op :=
  match op with
  | .insert  => .delete
  | .delete  => .insert
  | .replace => .replace

def invertHunk (h : Hunk) : Hunk :=
  { h with before := h.after, after := h.before, op := invertOp h.op }

def hunkLineDelta (h : Hunk) : Int :=
  Int.ofNat h.after.length - Int.ofNat h.before.length

def inverseRangeOnPatched (delta : Int) (h : Hunk) : Range :=
  let start := Int.toNat (Int.ofNat h.range.start + delta)
  { start, stop := start + h.after.length }

def invertOrderedHunks : Int → List Hunk → List Hunk
  | _, [] => []
  | delta, h :: rest =>
      let inverse :=
        { h with
            op    := invertOp h.op
            range := inverseRangeOnPatched delta h
            before := h.after
            after  := h.before }
      inverse :: invertOrderedHunks (delta + hunkLineDelta h) rest

def resultLineCount (diff : Diff) : Nat :=
  Int.toNat <|
    diff.sortedHunks.foldl
      (fun total h => total + hunkLineDelta h)
      (Int.ofNat diff.base_line_count)

def invertDiff (d : Diff) : Diff :=
  { d with
      base_line_count := resultLineCount d
      diffs           := invertOrderedHunks 0 d.sortedHunks
      newContent      := none }

@[simp, grind =] theorem invertHunk_involution (h : Hunk) :
    invertHunk (invertHunk h) = h := by
  cases h with
  | mk _ op _ _ _ => cases op <;> rfl

end VersionControl
