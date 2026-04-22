import VersionControl.Defns

namespace VersionControl

namespace Diff

def checkAgainstBase (diff : Diff) (base : BaseFile) : Except String Unit := do
  diff.checkSchema
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

def unchangedSegment (base : BaseFile) (cursor nextStart : Nat) : List String :=
  (base.drop (cursor - 1)).take (nextStart - cursor)

def applyOrderedHunks (base : BaseFile) : Nat → List Hunk → Except String BaseFile
  | cursor, [] => .ok (base.drop (cursor - 1))
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
        pure (unchangedSegment base cursor hunk.range.start ++ hunk.after ++ tail)

def applyHunk (hunk : Hunk) (base : BaseFile) : Except String BaseFile :=
  applyOrderedHunks base 1 [hunk]

def applyDiff (diff : Diff) (base : BaseFile) : Except String BaseFile := do
  diff.checkAgainstBase base
  applyOrderedHunks base 1 diff.sortedHunks

@[simp, grind =] theorem applyDiff_empty (file : String) (hFile : file ≠ "") (base : BaseFile) :
    applyDiff
      { agent := 1
        file
        timestamp := "2026-01-01T00:00:00Z"
        base_line_count := base.length
        diffs := [] } base = .ok base := by
  simp [applyDiff, Diff.checkAgainstBase, Diff.checkSchema, hFile,
    Diff.sortedHunks, Diff.pairwiseSeparated, applyOrderedHunks]

@[simp, grind =] theorem applyHunk_insert_at_start (line : String) (base : BaseFile) :
    applyHunk
        { seq := 1
          op := .insert
          range := { start := 1, stop := 1 }
          before := []
          after := [line] }
        base =
      .ok (line :: base) := by
  simp [applyHunk, applyOrderedHunks, unchangedSegment, slice, Range.wellFormed,
    Range.width, Hunk.opMatchesShape, Range.isInsert]

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
            op := invertOp h.op
            range := inverseRangeOnPatched delta h
            before := h.after
            after := h.before }
      inverse :: invertOrderedHunks (delta + hunkLineDelta h) rest

def resultLineCount (diff : Diff) : Nat :=
  Int.toNat <|
    diff.sortedHunks.foldl
      (fun total h => total + hunkLineDelta h)
      (Int.ofNat diff.base_line_count)

def invertDiff (d : Diff) : Diff :=
  { d with
      base_line_count := resultLineCount d
      diffs := invertOrderedHunks 0 d.sortedHunks }

@[simp, grind =] theorem invertHunk_involution (h : Hunk) : invertHunk (invertHunk h) = h := by
  cases h with
  | mk _ op _ _ _ =>
      cases op <;> rfl

end VersionControl
