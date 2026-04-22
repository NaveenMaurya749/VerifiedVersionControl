import VersionControl.Defns

namespace VersionControl

-- A commit id is a short string name such as "init" or "a1".
abbrev CommitId := String

structure PatchStep where
  baseCommit : CommitId
  newCommit  : CommitId
  diff       : Diff
  deriving Repr, DecidableEq, Inhabited

abbrev PushHistory := List PatchStep

namespace PatchStep

def wellFormed (step : PatchStep) : Prop :=
  step.baseCommit ≠ "" ∧
    step.newCommit ≠ "" ∧
    step.diff.metadataWellFormed

end PatchStep

def commitPath : PushHistory → List CommitId
  | [] => []
  | step :: rest => step.baseCommit :: (step :: rest).map PatchStep.newCommit

def distinctCommitIds (history : PushHistory) : Prop :=
  (commitPath history).Nodup

def validHistory : PushHistory → Prop
  | [] => True
  | [step] => step.wellFormed ∧ distinctCommitIds [step]
  | step₁ :: step₂ :: rest =>
      step₁.wellFormed ∧
        step₁.newCommit = step₂.baseCommit ∧
        step₁.diff.file = step₂.diff.file ∧
        validHistory (step₂ :: rest) ∧
        step₁.baseCommit ∉ commitPath (step₂ :: rest)

def commonPrefix {α : Type} [DecidableEq α] : List α → List α → List α
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys =>
      if x = y then
        x :: commonPrefix xs ys
      else
        []

def sharedCommitPath (left right : PushHistory) : List CommitId :=
  commonPrefix (commitPath left) (commitPath right)

def sharedStepCount (left right : PushHistory) : Nat :=
  (sharedCommitPath left right).length - 1

structure CommonParentSplit where
  sharedCommits : List CommitId
  ancestorCommit : CommitId
  leftResidual : PushHistory
  rightResidual : PushHistory
  deriving Repr, DecidableEq, Inhabited

def splitAtNearestCommonParent? (left right : PushHistory) : Option CommonParentSplit :=
  match (sharedCommitPath left right).getLast? with
  | none => none
  | some ancestor =>
      some
        { sharedCommits  := sharedCommitPath left right
          ancestorCommit := ancestor
          leftResidual   := left.drop (sharedStepCount left right)
          rightResidual  := right.drop (sharedStepCount left right) }

@[simp, grind =] theorem commitPath_nil :
    commitPath ([] : PushHistory) = [] := rfl

@[simp, grind =] theorem commitPath_singleton (step : PatchStep) :
    commitPath [step] = [step.baseCommit, step.newCommit] := rfl

@[grind →] theorem validHistory_distinctCommitIds :
    ∀ {history : PushHistory}, validHistory history → distinctCommitIds history
  | [], _ => by
      simp [distinctCommitIds, commitPath]
  | [step], h => h.2
  | step₁ :: step₂ :: rest, h => by
      rcases h with ⟨_, hChain, _, hTail, hFresh⟩
      have hTailDistinct : distinctCommitIds (step₂ :: rest) :=
        validHistory_distinctCommitIds hTail
      simpa [distinctCommitIds, commitPath, hChain] using
        List.nodup_cons.mpr ⟨hFresh, hTailDistinct⟩

@[grind =] theorem split_none_of_sharedCommitPath_eq_nil {left right : PushHistory}
    (hShared : sharedCommitPath left right = []) :
    splitAtNearestCommonParent? left right = none := by
  simp [splitAtNearestCommonParent?, hShared]

@[grind =] theorem split_eq_some_of_sharedCommitPath {left right : PushHistory}
    (hShared : sharedCommitPath left right ≠ []) :
    splitAtNearestCommonParent? left right =
      some
        { sharedCommits  := sharedCommitPath left right
          ancestorCommit := (sharedCommitPath left right).getLast hShared
          leftResidual   := left.drop (sharedStepCount left right)
          rightResidual  := right.drop (sharedStepCount left right) } := by
  have hLast :
      (sharedCommitPath left right).getLast? =
        some ((sharedCommitPath left right).getLast hShared) := by
    grind
  simp [splitAtNearestCommonParent?, hLast, sharedStepCount]

@[grind →] theorem validHistory_tail {step : PatchStep} {rest : PushHistory}
    (h : validHistory (step :: rest)) : validHistory rest := by
  cases rest with
  | nil => trivial
  | cons _ _ =>
      simp [validHistory] at h ⊢
      grind

@[grind .] theorem validHistory_drop : ∀ (n : Nat) (h : PushHistory),
    validHistory h → validHistory (h.drop n)
  | 0, _, hv => hv
  | _ + 1, [], _ => trivial
  | n + 1, _ :: rest, hv => validHistory_drop n rest (validHistory_tail hv)

@[grind →] theorem validHistory_leftResidual {left right : PushHistory}
    (hLeft : validHistory left)
    {split : CommonParentSplit}
    (hSplit : splitAtNearestCommonParent? left right = some split) :
    validHistory split.leftResidual := by
  unfold splitAtNearestCommonParent? at hSplit
  cases hAnc : (sharedCommitPath left right).getLast? with
  | none =>
      simp [hAnc] at hSplit
  | some ancestor =>
      have hEq :
          { sharedCommits := sharedCommitPath left right
            ancestorCommit := ancestor
            leftResidual := left.drop (sharedStepCount left right)
            rightResidual := right.drop (sharedStepCount left right) } = split := by
        simpa [hAnc, Option.some.injEq] using hSplit
      subst split
      grind

@[grind →] theorem validHistory_rightResidual {left right : PushHistory}
    (hRight : validHistory right)
    {split : CommonParentSplit}
    (hSplit : splitAtNearestCommonParent? left right = some split) :
    validHistory split.rightResidual := by
  unfold splitAtNearestCommonParent? at hSplit
  cases hAnc : (sharedCommitPath left right).getLast? with
  | none =>
      simp [hAnc] at hSplit
  | some ancestor =>
      have hEq :
          { sharedCommits := sharedCommitPath left right
            ancestorCommit := ancestor
            leftResidual := left.drop (sharedStepCount left right)
            rightResidual := right.drop (sharedStepCount left right) } = split := by
        simpa [hAnc, Option.some.injEq] using hSplit
      subst split
      grind

end VersionControl
