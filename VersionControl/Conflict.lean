import Mathlib.Tactic
import VersionControl.Defns

namespace VersionControl

def identicalChange (left right : Hunk) : Prop :=
  left.range = right.range ∧ left.before = right.before ∧ left.after = right.after

def pointInsertConflict (left right : Hunk) : Prop :=
  left.range.isInsert ∧
    right.range.isInsert ∧
    left.range.start = right.range.start ∧
    left.after ≠ right.after

def hunksConflict (left right : Hunk) : Prop :=
  ¬ identicalChange left right ∧
    (left.range.overlaps right.range ∨ pointInsertConflict left right)

def diffsConflict (left right : Diff) : Prop :=
  ∃ h₁ ∈ left.diffs, ∃ h₂ ∈ right.diffs, hunksConflict h₁ h₂

def compatible (left right : Diff) : Prop :=
  ∀ h₁ ∈ left.diffs, ∀ h₂ ∈ right.diffs, ¬ hunksConflict h₁ h₂

instance (left right : Hunk) : Decidable (identicalChange left right) := by
  unfold identicalChange
  infer_instance

instance (left right : Range) : Decidable (left.overlaps right) := by
  unfold Range.overlaps
  infer_instance

instance (left right : Hunk) : Decidable (pointInsertConflict left right) := by
  unfold pointInsertConflict Range.isInsert
  infer_instance

def hunkConflictFlag (left right : Hunk) : Bool :=
  (!(decide (identicalChange left right))) &&
    (decide (left.range.overlaps right.range) || decide (pointInsertConflict left right))

def diffConflictFlag (left right : Diff) : Bool :=
  left.diffs.any fun h₁ => right.diffs.any fun h₂ => hunkConflictFlag h₁ h₂

@[simp, grind =] theorem identicalChange_comm {left right : Hunk} :
    identicalChange left right ↔ identicalChange right left := by
  unfold identicalChange
  aesop

@[grind →] theorem not_hunksConflict_of_identicalChange {left right : Hunk}
    (hIdentical : identicalChange left right) :
    ¬ hunksConflict left right := by
  intro hConflict
  exact hConflict.1 hIdentical

@[simp, grind =] theorem pointInsertConflict_comm {left right : Hunk} :
    pointInsertConflict left right ↔ pointInsertConflict right left := by
  constructor
  · rintro ⟨hLeftInsert, hRightInsert, hSameStart, hDifferentAfter⟩
    refine ⟨hRightInsert, hLeftInsert, hSameStart.symm, ?_⟩
    intro hEq
    exact hDifferentAfter hEq.symm
  · rintro ⟨hRightInsert, hLeftInsert, hSameStart, hDifferentAfter⟩
    refine ⟨hLeftInsert, hRightInsert, hSameStart.symm, ?_⟩
    intro hEq
    exact hDifferentAfter hEq.symm

@[grind =] theorem hunksConflict_comm {left right : Hunk} :
    hunksConflict left right ↔ hunksConflict right left := by
  unfold hunksConflict
  simp [identicalChange_comm, Range.overlaps_comm]

@[grind .] theorem identical_hunks_not_conflict (hunk : Hunk) :
    ¬ hunksConflict hunk hunk := by
  exact not_hunksConflict_of_identicalChange ⟨rfl, rfl, rfl⟩

@[grind =] theorem hunkConflictFlag_eq_true_iff {left right : Hunk} :
    hunkConflictFlag left right = true ↔ hunksConflict left right := by
  simp [hunkConflictFlag, hunksConflict]

@[grind =] theorem hunkConflictFlag_eq_false_iff {left right : Hunk} :
    hunkConflictFlag left right = false ↔ ¬ hunksConflict left right := by
  grind

@[grind =] theorem diffConflictFlag_eq_true_iff {left right : Diff} :
    diffConflictFlag left right = true ↔ diffsConflict left right := by
  simp [diffConflictFlag, diffsConflict, hunkConflictFlag_eq_true_iff]

@[grind =] theorem diffConflictFlag_eq_false_iff {left right : Diff} :
    diffConflictFlag left right = false ↔ ¬ diffsConflict left right := by
  grind

@[grind →] theorem flagged_implies_real_conflict {left right : Diff}
    (hFlag : diffConflictFlag left right = true) :
    diffsConflict left right := by
  grind

@[grind →] theorem real_conflict_implies_flagged {left right : Diff}
    (hConflict : diffsConflict left right) :
    diffConflictFlag left right = true := by
  grind

@[grind →] theorem separated_hunks_not_conflict {left right : Hunk}
    (hSeparated :
      left.range.stop ≤ right.range.start ∨ right.range.stop ≤ left.range.start)
    (hNoInsertCollision : ¬ pointInsertConflict left right) :
    ¬ hunksConflict left right := by
  unfold hunksConflict Range.overlaps
  grind

@[grind =] theorem identical_hunks_not_flagged (hunk : Hunk) :
    hunkConflictFlag hunk hunk = false := by
  grind

@[grind →] theorem same_point_equal_insert_not_conflict {left right : Hunk}
    (hLeftInsert : left.range.isInsert)
    (hRightInsert : right.range.isInsert)
    (hSameStart : left.range.start = right.range.start)
    (hBeforeLeft : left.before = [])
    (hBeforeRight : right.before = [])
    (hSameAfter : left.after = right.after) :
    ¬ hunksConflict left right := by
  rcases left with ⟨_, _, ⟨leftStart, leftStop⟩, leftBefore, leftAfter⟩
  rcases right with ⟨_, _, ⟨rightStart, rightStop⟩, rightBefore, rightAfter⟩
  change leftStart = leftStop at hLeftInsert
  change rightStart = rightStop at hRightInsert
  change leftStart = rightStart at hSameStart
  subst leftStop
  subst rightStop
  subst rightStart
  apply not_hunksConflict_of_identicalChange
  refine ⟨rfl, ?_, hSameAfter⟩
  exact hBeforeLeft.trans hBeforeRight.symm

@[grind =] theorem same_point_equal_insert_not_flagged {left right : Hunk}
    (hLeftInsert : left.range.isInsert)
    (hRightInsert : right.range.isInsert)
    (hSameStart : left.range.start = right.range.start)
    (hBeforeLeft : left.before = [])
    (hBeforeRight : right.before = [])
    (hSameAfter : left.after = right.after) :
    hunkConflictFlag left right = false := by
  grind

@[simp, grind =] theorem diffsConflict_comm {left right : Diff} :
    diffsConflict left right ↔ diffsConflict right left := by
  constructor
  · rintro ⟨h₁, h₁_mem, h₂, h₂_mem, hConflict⟩
    exact ⟨h₂, h₂_mem, h₁, h₁_mem, (hunksConflict_comm.mp hConflict)⟩
  · rintro ⟨h₂, h₂_mem, h₁, h₁_mem, hConflict⟩
    exact ⟨h₁, h₁_mem, h₂, h₂_mem, (hunksConflict_comm.mp hConflict)⟩

@[grind =] theorem compatible_iff_not_diffsConflict {left right : Diff} :
    compatible left right ↔ ¬ diffsConflict left right := by
  simp [compatible, diffsConflict]

@[grind .] theorem compatible_empty_left (diff : Diff) :
    compatible
      { agent := 1
        file := diff.file
        timestamp := diff.timestamp
        base_line_count := diff.base_line_count
        diffs := []
        newContent := none } diff := by    -- ← add this line
  simp [compatible]

@[grind .] theorem compatible_empty_right (diff : Diff) :
    compatible diff
      { agent := 1
        file := diff.file
        timestamp := diff.timestamp
        base_line_count := diff.base_line_count
        diffs := []
        newContent := none } := by         -- ← add this line
  simp [compatible]

@[grind =] theorem compatible_comm {left right : Diff} :
    compatible left right ↔ compatible right left := by
  grind

end VersionControl
