import Mathlib.Tactic
import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson.Basic
import Init.Data.List.Sort.Basic
import VersionControl.Basic

open Lean

namespace VersionControl

abbrev BaseFile := Content

inductive Op where
  | insert
  | delete
  | replace
  deriving Repr, DecidableEq, Inhabited, BEq, FromJson, ToJson

structure Range where
  start : Nat
  stop  : Nat
  deriving Repr, DecidableEq, Inhabited, BEq

namespace Range

def width (r : Range) : Nat :=
  r.stop - r.start

def isInsert (r : Range) : Prop :=
  r.start = r.stop

def wellFormed (r : Range) (baseLineCount : Nat) : Prop :=
  1 ≤ r.start ∧ r.start ≤ r.stop ∧ r.stop ≤ baseLineCount + 1

def overlaps (left right : Range) : Prop :=
  left.start < right.stop ∧ right.start < left.stop

def pointInsertCollision (left right : Range) : Prop :=
  left.isInsert ∧ right.isInsert ∧ left.start = right.start

@[simp, grind =] theorem overlaps_comm (left right : Range) :
    left.overlaps right ↔ right.overlaps left := by
  unfold Range.overlaps
  aesop

@[simp, grind =] theorem width_eq_zero_of_isInsert {r : Range} (h : r.isInsert) :
    r.width = 0 := by
  unfold Range.isInsert Range.width at *
  omega

@[grind =] theorem isInsert_iff_width_eq_zero {r : Range} (hle : r.start ≤ r.stop) :
    r.isInsert ↔ r.width = 0 := by
  unfold Range.isInsert Range.width
  omega

end Range

instance (r : Range) (baseLineCount : Nat) : Decidable (r.wellFormed baseLineCount) := by
  unfold Range.wellFormed
  infer_instance

instance : FromJson Range where
  fromJson?
    | Json.arr values =>
        match values.toList with
        | [startJson, stopJson] => do
            let start : Nat ← fromJson? startJson
            let stop  : Nat ← fromJson? stopJson
            pure { start, stop }
        | _ => .error "range must be a two-element integer array"
    | _ => .error "range must be encoded as a JSON array"

instance : ToJson Range where
  toJson r :=
    Json.arr #[toJson r.start, toJson r.stop]

def slice (base : BaseFile) (range : Range) : List String :=
  match base with
  | .text lines => (lines.drop (range.start - 1)).take range.width
  | .binary _ => []  -- Binary files don't support slicing

@[simp, grind =] theorem slice_of_insert (base : BaseFile) {range : Range} (h : range.isInsert) :
    slice base range = [] := by
  rcases range with ⟨start, stop⟩
  change start = stop at h
  subst stop
  cases base <;> simp [slice, Range.width]

structure Hunk where
  seq : Nat
  op : Op
  range : Range
  before : List String
  after : List String
  deriving Repr, DecidableEq, Inhabited, BEq, FromJson, ToJson

namespace Hunk

def opMatchesShape (h : Hunk) : Prop :=
  match h.op with
  | .insert =>
      h.range.isInsert ∧ h.before = [] ∧ h.after ≠ []
  | .delete =>
      h.range.start < h.range.stop ∧ h.before.length = h.range.width ∧ h.after = []
  | .replace =>
      h.range.start < h.range.stop ∧ h.before.length = h.range.width ∧ h.after ≠ []

def baseAligned (base : BaseFile) (h : Hunk) : Prop :=
  h.before = slice base h.range

def schemaWellFormed (baseLineCount : Nat) (h : Hunk) : Prop :=
  1 ≤ h.seq ∧
    1 ≤ h.range.start ∧
    h.range.start ≤ h.range.stop ∧
    h.range.stop ≤ baseLineCount + 1 ∧
    h.opMatchesShape

def wellFormed (base : BaseFile) (h : Hunk) : Prop :=
  1 ≤ h.seq ∧
    h.range.wellFormed base.length ∧
    h.baseAligned base ∧
    h.opMatchesShape

def compareByRange (left right : Hunk) : Bool :=
  if left.range.start = right.range.start then
    left.range.stop ≤ right.range.stop
  else
    left.range.start ≤ right.range.start

instance (h : Hunk) : Decidable h.opMatchesShape := by
  unfold Hunk.opMatchesShape Range.isInsert
  cases h.op <;> infer_instance

def checkSchema (baseLineCount : Nat) (h : Hunk) : Except String Unit := do
  if h.seq = 0 then
    .error "hunk seq must be >= 1"
  else if h.range.start = 0 then
    .error s!"hunk {h.seq} must start at line 1 or later"
  else if h.range.start > h.range.stop then
    .error s!"hunk {h.seq} has range start after range stop"
  else
    pure ()
  if h.range.stop > baseLineCount + 1 then
    .error s!"hunk {h.seq} ends past the declared base line count"
  else
    pure ()
  if h.opMatchesShape then
    pure ()
  else
    .error s!"hunk {h.seq} has an op/before/after shape mismatch"

@[simp, grind =] theorem opMatchesShape_insert {range : Range} {after : List String}
    (hAfter : after ≠ []) :
    ({ seq := 1, op := .insert, range, before := [], after } : Hunk).opMatchesShape ↔
      range.isInsert := by
  simp [opMatchesShape, hAfter]

end Hunk

structure Diff where
  agent : Agent
  file : File
  timestamp : String
  base_line_count : Nat
  diffs : List Hunk
  newContent : Option Content  -- For binary file replacement
  deriving Repr, DecidableEq, Inhabited, BEq

instance : FromJson Diff where
  fromJson? json := do
    let agent           : Agent       ← json.getObjValAs? (α := Nat)         "agent"
    let file            : File        ← json.getObjValAs? (α := String)      "file"
    let timestamp       : String      ← json.getObjValAs? (α := String)      "timestamp"
    let base_line_count : Nat         ← json.getObjValAs? (α := Nat)         "base_line_count"
    let diffs           : List Hunk   ← json.getObjValAs? (α := List Hunk)   "diffs"
    let newContent      : Option Content ← json.getObjValAs? (α := Option Content) "newContent"
    pure { agent, file, timestamp, base_line_count, diffs, newContent }

instance : ToJson Diff where
  toJson diff :=
    Json.mkObj <|
      [ ("agent", toJson diff.agent)
      , ("file", toJson diff.file)
      , ("timestamp", toJson diff.timestamp)
      , ("base_line_count", toJson diff.base_line_count)
      , ("diffs", toJson diff.diffs)
      , ("newContent", toJson diff.newContent)
      ]

namespace Diff

def metadataWellFormed (diff : Diff) : Prop :=
  1 ≤ diff.agent ∧ diff.file ≠ ""

def sortedHunks (diff : Diff) : List Hunk :=
  diff.diffs.mergeSort Hunk.compareByRange

def pairwiseSeparated (hunks : List Hunk) : Prop :=
  List.Pairwise
      (fun (left right : Hunk) =>
        (left.range.stop ≤ right.range.start ∨ right.range.stop ≤ left.range.start) ∧
          ¬ left.range.pointInsertCollision right.range)
      hunks

instance (left right : Hunk) : Decidable
    ((left.range.stop ≤ right.range.start ∨ right.range.stop ≤ left.range.start) ∧
      ¬ left.range.pointInsertCollision right.range) := by
  unfold Range.pointInsertCollision Range.isInsert
  infer_instance

instance (hunks : List Hunk) : Decidable (pairwiseSeparated hunks) := by
  unfold pairwiseSeparated
  infer_instance

def schemaWellFormed (diff : Diff) : Prop :=
  diff.metadataWellFormed ∧
    match diff.newContent with
    | some _ => diff.diffs.isEmpty ∧ diff.base_line_count = 0
    | none =>
        pairwiseSeparated diff.sortedHunks ∧
        ∀ h ∈ diff.diffs, h.schemaWellFormed diff.base_line_count

def wellFormed (base : BaseFile) (diff : Diff) : Prop :=
  diff.metadataWellFormed ∧
    match diff.newContent with
    | some _ =>
        diff.diffs.isEmpty ∧ diff.base_line_count = 0
    | none =>
        diff.base_line_count = base.length ∧
        pairwiseSeparated diff.sortedHunks ∧
        ∀ h ∈ diff.diffs, h.wellFormed base

def checkSchema (diff : Diff) : Except String Unit := do
  if diff.agent = 0 then
    .error "agent must be >= 1"
  else if diff.file = "" then
    .error "file must be non-empty"
  else
    pure ()
  match diff.newContent with
  | some _ =>
      if diff.diffs.isEmpty ∧ diff.base_line_count = 0 then
        pure ()
      else
        .error "binary diffs must have empty hunks and base_line_count = 0"
  | none =>
      for h in diff.diffs do
        h.checkSchema diff.base_line_count
      if pairwiseSeparated diff.sortedHunks then
        pure ()
      else
        .error "diff hunks must be pairwise non-overlapping"

@[simp, grind =] theorem sortedHunks_nil :
    ({ agent := 1, file := "x", timestamp := "2026-01-01T00:00:00Z",
       base_line_count := 0, diffs := [] } : Diff).sortedHunks = [] := by
  simp [sortedHunks]

end Diff

end VersionControl
