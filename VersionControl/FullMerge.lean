import Mathlib.Tactic
import VersionControl.Defns
import VersionControl.Semantics
import VersionControl.History
import VersionControl.Conflict

namespace VersionControl

def mergeArtifactAgent : Agent := 1

def mergeArtifactTimestamp : String := "2026-04-22T00:00:00Z"

abbrev MergeM (α : Type) := Except String α

inductive MergeResult where
  | clean    (merged : Diff)       : MergeResult
  | conflict (witness : List Hunk) : MergeResult
  deriving Repr, Inhabited, DecidableEq

def replayFromCommon (common : BaseFile) (residual : PushHistory) : MergeM BaseFile :=
  residual.foldlM (fun b s => applyDiff s.diff b) common

@[simp, grind =] theorem replayFromCommon_nil (base : BaseFile) :
    replayFromCommon base [] = .ok base := rfl

@[grind =] theorem replayFromCommon_append (base : BaseFile) (h1 h2 : PushHistory) :
    replayFromCommon base (h1 ++ h2) =
      (replayFromCommon base h1 >>= fun mid => replayFromCommon mid h2) := by
  simp [replayFromCommon, List.foldlM_append]

def residualDiffs (history : PushHistory) : List Diff :=
  history.map (·.diff)

def conflictWitnesses (leftDiffs rightDiffs : List Diff) : List Hunk :=
  let leftConflicting := (leftDiffs.map (fun ld =>
    ld.diffs.filter (fun h1 =>
      rightDiffs.any (fun rd => rd.diffs.any (fun h2 => hunkConflictFlag h1 h2))))).flatten
  let rightConflicting := (rightDiffs.map (fun rd =>
    rd.diffs.filter (fun h2 =>
      leftDiffs.any (fun ld => ld.diffs.any (fun h1 => hunkConflictFlag h1 h2))))).flatten
  leftConflicting ++ rightConflicting

def dedupeIdenticalSortedHunks : List Hunk → List Hunk
  | [] => []
  | [h] => [h]
  | h1 :: h2 :: rest =>
      if identicalChange h1 h2 then
        dedupeIdenticalSortedHunks (h1 :: rest)
      else
        h1 :: dedupeIdenticalSortedHunks (h2 :: rest)

def mergedDiffFrom (common : BaseFile) (leftDiffs rightDiffs : List Diff) : Diff :=
  let fileName :=
    match leftDiffs.head? with
    | some diff => diff.file
    | none =>
        match rightDiffs.head? with
        | some diff => diff.file
        | none => "merged"
  let allHunks :=
    ((leftDiffs.map (·.diffs)).flatten ++ (rightDiffs.map (·.diffs)).flatten)
      |>.mergeSort Hunk.compareByRange
      |> dedupeIdenticalSortedHunks
  let mergedHunks := List.mapIdx (fun i h => { h with seq := i + 1 }) allHunks
  -- A clean merge result is a constructed artifact diff. Since `Diff` carries
  -- exactly one agent and one timestamp, merged artifacts use canonical
  -- metadata here instead of pretending the merge has a single input author.
  { agent := mergeArtifactAgent
    file := fileName
    timestamp := mergeArtifactTimestamp
    base_line_count := common.length
    diffs := mergedHunks }

@[simp] theorem residualDiffs_nil : residualDiffs [] = [] := rfl

@[simp] theorem residualDiffs_cons (step : PatchStep) (rest : PushHistory) :
    residualDiffs (step :: rest) = step.diff :: residualDiffs rest := rfl

def threeWayCheck (common : BaseFile) (left right : PushHistory) : MergeM (Option MergeResult) := do
  let _ ← replayFromCommon common left
  let _ ← replayFromCommon common right
  let lds := residualDiffs left
  let rds := residualDiffs right
  if lds.any (fun ld => rds.any (fun rd => diffConflictFlag ld rd)) then
    return some (.conflict (conflictWitnesses lds rds))
  else
    return some (.clean (mergedDiffFrom common lds rds))

theorem threeWayCheck_of_conflictFlag_true
    (common : BaseFile) (left right : PushHistory)
    (leftFile rightFile : BaseFile)
    (hLeft : replayFromCommon common left = .ok leftFile)
    (hRight : replayFromCommon common right = .ok rightFile)
    (hConflict :
      (residualDiffs left).any (fun ld =>
        (residualDiffs right).any (fun rd => diffConflictFlag ld rd)) = true) :
    threeWayCheck common left right =
      .ok (some (.conflict (conflictWitnesses (residualDiffs left) (residualDiffs right)))) := by
  simp [threeWayCheck, hLeft, hRight, hConflict]
  rfl

theorem threeWayCheck_of_conflictFlag_false
    (common : BaseFile) (left right : PushHistory)
    (leftFile rightFile : BaseFile)
    (hLeft : replayFromCommon common left = .ok leftFile)
    (hRight : replayFromCommon common right = .ok rightFile)
    (hConflict :
      (residualDiffs left).any (fun ld =>
        (residualDiffs right).any (fun rd => diffConflictFlag ld rd)) = false) :
    threeWayCheck common left right =
      .ok (some (.clean (mergedDiffFrom common (residualDiffs left) (residualDiffs right)))) := by
  simp [threeWayCheck, hLeft, hRight, hConflict]
  rfl

def reconstructAncestor (initialFile : BaseFile) (left right : PushHistory) : MergeM BaseFile :=
  replayFromCommon initialFile (left.take (sharedStepCount left right))

def fullMerge (initialFile : BaseFile) (left right : PushHistory) :
    MergeM (Option MergeResult) := do
  match splitAtNearestCommonParent? left right with
  | none =>
      return none
  | some split =>
      let ancestor ← reconstructAncestor initialFile left right
      threeWayCheck ancestor split.leftResidual split.rightResidual

def nWayCompatible.aux (d : Diff) : List Diff → Bool
  | [] => true
  | d2 :: rest => !diffConflictFlag d d2 && nWayCompatible.aux d rest

@[simp, grind =] theorem nWayCompatible_aux_nil (d : Diff) :
    nWayCompatible.aux d [] = true := rfl

@[simp, grind =] theorem nWayCompatible_aux_cons (d d2 : Diff) (rest : List Diff) :
    nWayCompatible.aux d (d2 :: rest) =
      (!diffConflictFlag d d2 && nWayCompatible.aux d rest) := rfl

def nWayCompatible : List Diff → Bool
  | [] => true
  | d :: rest => nWayCompatible.aux d rest && nWayCompatible rest

@[simp, grind =] theorem nWayCompatible_nil : nWayCompatible [] = true := rfl

@[simp, grind =] theorem nWayCompatible_cons (d : Diff) (rest : List Diff) :
    nWayCompatible (d :: rest) = (nWayCompatible.aux d rest && nWayCompatible rest) := rfl

@[simp, grind =] theorem nWayCompatible_singleton (d : Diff) : nWayCompatible [d] = true := by
  simp

def PairwiseCompatible : List Diff → Prop
  | [] => True
  | d :: rest => (∀ d', d' ∈ rest → compatible d d') ∧ PairwiseCompatible rest

@[simp] theorem PairwiseCompatible_nil : PairwiseCompatible [] := by
  trivial

@[simp] theorem PairwiseCompatible_cons {d : Diff} {rest : List Diff} :
    PairwiseCompatible (d :: rest) ↔
      (∀ d', d' ∈ rest → compatible d d') ∧ PairwiseCompatible rest := by
  rfl

theorem nWayCompatible_aux_eq_true_iff (d : Diff) :
    ∀ rest, nWayCompatible.aux d rest = true ↔ ∀ d', d' ∈ rest → compatible d d'
  | [] => by
      simp [nWayCompatible.aux, compatible]
  | d2 :: rest => by
      simp [nWayCompatible.aux, nWayCompatible_aux_eq_true_iff,
        compatible_iff_not_diffsConflict, diffConflictFlag_eq_false_iff]

@[grind =] theorem nWayCompatible_eq_true_iff :
    ∀ ds, nWayCompatible ds = true ↔ PairwiseCompatible ds
  | [] => by
      simp [nWayCompatible, PairwiseCompatible]
  | d :: rest => by
      simp [nWayCompatible, PairwiseCompatible, nWayCompatible_aux_eq_true_iff,
        nWayCompatible_eq_true_iff]

@[grind →] theorem nWayCompatible_sound {ds : List Diff} (h : nWayCompatible ds = true) :
    PairwiseCompatible ds := by
  exact (nWayCompatible_eq_true_iff ds).mp h

@[grind →] theorem nWayCompatible_complete {ds : List Diff} (h : PairwiseCompatible ds) :
    nWayCompatible ds = true := by
  exact (nWayCompatible_eq_true_iff ds).mpr h

def ValidMerge (diffs : List Diff) : Prop :=
  2 ≤ diffs.length ∧ PairwiseCompatible diffs

@[simp] theorem validMerge_iff (diffs : List Diff) :
    ValidMerge diffs ↔ 2 ≤ diffs.length ∧ PairwiseCompatible diffs := by
  rfl

@[grind =] theorem validMerge_iff_flag (diffs : List Diff) :
    ValidMerge diffs ↔ 2 ≤ diffs.length ∧ nWayCompatible diffs = true := by
  rw [validMerge_iff, nWayCompatible_eq_true_iff]

@[grind →] theorem validMerge_of_flag {diffs : List Diff}
    (hLen : 2 ≤ diffs.length) (hFlag : nWayCompatible diffs = true) :
    ValidMerge diffs := by
  exact ⟨hLen, nWayCompatible_sound hFlag⟩

@[grind →] theorem flag_of_validMerge {diffs : List Diff} (hValid : ValidMerge diffs) :
    nWayCompatible diffs = true := by
  exact nWayCompatible_complete hValid.2

@[grind →] theorem validMerge_has_two_or_more {diffs : List Diff} (hValid : ValidMerge diffs) :
    2 ≤ diffs.length := by
  exact hValid.1

@[grind →] theorem split_ne_none_of_shared_nonempty {h1 h2 : PushHistory}
    (h : sharedCommitPath h1 h2 ≠ []) :
    splitAtNearestCommonParent? h1 h2 ≠ none := by
  grind

@[grind →] theorem common_parent_exists_for_two {h1 h2 : PushHistory}
    (_ : validHistory h1) (_ : validHistory h2)
    (hShared : sharedCommitPath h1 h2 ≠ []) :
    splitAtNearestCommonParent? h1 h2 ≠ none := by
  grind

end VersionControl
