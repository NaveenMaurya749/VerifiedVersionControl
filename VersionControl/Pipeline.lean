import Mathlib
import VersionControl.Defns
import VersionControl.JsonParse
import VersionControl.Semantics
import VersionControl.Conflict
import VersionControl.FullMerge
import VersionControl.Filesystem
import VersionControl.ErrorOutput

namespace VersionControl

/-!
# Pipeline

A monadic pipeline that sequences the five commit stages:
  1. JSON parsing        (PipelineM Diff)
  2. Schema validation   (PipelineM Diff)
  3. Base alignment      (PipelineM (Diff × BaseFile))
  4. Conflict check      (PipelineM Diff)
  5. Apply to disk       (PipelineM Unit)

`PipelineM` is `ExceptT AgentError IO`.
Each stage either passes its output to the next stage,
or short-circuits with a typed, stage-tagged `AgentError`.
-/

-- ============================================================
-- 1. The monad
-- ============================================================

/--
`PipelineM α` is an IO action that either produces an `α`
or fails with a structured `AgentError` carrying the stage
at which failure occurred.
-/
abbrev PipelineM := ExceptT AgentError IO

/--
Lift a pure `Except String` computation into `PipelineM`,
tagging any error string with the given stage.
-/
def liftExcept (stage : RejectionStage) : Except String α → PipelineM α
  | .ok a    => pure a
  | .error s => throw { stage, message := s }

/--
Lift an `IO` action into `PipelineM`, catching any IO exception
and tagging it with the given stage.
-/
def liftIO' (stage : RejectionStage) (action : IO α) : PipelineM α :=
  ExceptT.mk do
    try
      return .ok (← action)
    catch e =>
      return .error { stage, message := toString e }

-- ============================================================
-- 2. Stages
-- ============================================================

/-- Stage 1: Parse raw JSON into a `Diff`. -/
def parseDiffM (jsonStr : String) : PipelineM Diff :=
  liftExcept .JsonParse (parseDiff jsonStr)

/-- Stage 2: Check schema — agent id, file name, hunk ranges,
    op shapes, pairwise non-overlap. -/
def checkSchemaM (diff : Diff) : PipelineM Diff := do
  liftExcept .SchemaCheck (diff.checkSchema)
  return diff

/-- Stage 3: Load the file from disk and verify that the diff's
    `before` lines match what is actually on disk. -/
def loadAndAlignM (diff : Diff) (path : File) : PipelineM (Diff × BaseFile) := do
  let base ← liftIO' .FilesystemError (loadBaseFile path)
  liftExcept .BaseAlignment (diff.checkAgainstBase base)
  return (diff, base)

/-- Stage 4: Reject if the diff conflicts with any pending diff
    from another agent. -/
def checkConflictsM (diff : Diff) (pending : List Diff) : PipelineM Diff := do
  let conflicts := pending.filterMap fun p =>
    if diffConflictFlag diff p then
      some { stage   := .ConflictCheck
             message := s!"Conflicts with agent {p.agent}'s pending diff on '{p.file}'" }
    else none
  match conflicts with
  | []     => return diff
  | e :: _ => throw e

/-- Stage 5: Write the validated diff to disk. -/
def applyDiffM (diff : Diff) (path : File) : PipelineM Unit :=
  liftIO' .FilesystemError do
    match ← applyDiffToFile path diff with
    | .ok ()   => pure ()
    | .error e => throw (IO.userError e)

-- ============================================================
-- 3. The full pipeline
-- ============================================================

/--
`runCommitPipeline` sequences all five stages.
Each stage either passes its output forward or stops
with a typed `AgentError`.
This replaces the manual if/match chain in `AgentInterface`.
-/
def runCommitPipeline
    (jsonStr : String)
    (pending : List Diff)
    (path    : File)
    : PipelineM Unit := do
  let diff         ← parseDiffM jsonStr
  let diff         ← checkSchemaM diff
  let (diff, _)   ← loadAndAlignM diff path
  let diff         ← checkConflictsM diff pending
  applyDiffM diff path

/--
Run the pipeline and wrap the result as an `AgentResponse`.
This is the replacement for the old `submitCommit`.
-/
def runPipeline
    (_agentId : Agent)
    (jsonStr : String)
    (pending : List Diff)
    (path    : File)
    : IO AgentResponse := do
  match ← runCommitPipeline jsonStr pending path with
  | .ok ()   => return AgentResponse.ok
  | .error e => return AgentResponse.rejectMany [e]

-- ============================================================
-- 4. Merge pipeline
-- ============================================================

/--
Wrap `fullMerge` in `PipelineM` so merge errors carry
a typed stage rather than a raw string.
-/
def runMergePipeline
    (initialFile : BaseFile)
    (left right  : PushHistory)
    : PipelineM (Option MergeResult) :=
  liftExcept .FilesystemError (fullMerge initialFile left right)

-- ============================================================
-- 5. Theorems
-- ============================================================

-- liftExcept is definitionally transparent for both cases
@[simp] theorem liftExcept_ok (stage : RejectionStage) (a : α) :
    liftExcept stage (.ok a) = (pure a : PipelineM α) := rfl

@[simp] theorem liftExcept_error (stage : RejectionStage) (s : String) :
    liftExcept stage (.error s) =
      (throw { stage, message := s } : PipelineM α) := rfl

/--
`parseDiffM` succeeds with `d` iff `parseDiff` succeeds with `d`.
-/
theorem parseDiffM_ok_of_ok {s : String} {d : Diff}
    (h : parseDiff s = .ok d) :
    parseDiffM s = pure d := by
  simp [parseDiffM, h]

/--
`parseDiffM` fails iff `parseDiff` returns an error.
The failure is tagged with the `JsonParse` stage.
-/
theorem parseDiffM_error_of_error {s : String} {msg : String}
    (h : parseDiff s = .error msg) :
    parseDiffM s = throw { stage := .JsonParse, message := msg } := by
  simp [parseDiffM, h]

/--
If JSON is malformed, the pipeline short-circuits immediately
at the `JsonParse` stage — no file is read, no disk is touched.
-/
theorem pipeline_fails_on_bad_json
    {jsonStr : String} {pending : List Diff} {path : File} {msg : String}
    (h : parseDiff jsonStr = .error msg) :
    runCommitPipeline jsonStr pending path =
      throw { stage := .JsonParse, message := msg } := by
  unfold runCommitPipeline parseDiffM liftExcept
  simp [h]

/--
If schema validation fails, the pipeline stops at `SchemaCheck` —
the file is never read.
-/
theorem pipeline_fails_on_bad_schema
    {jsonStr : String} {pending : List Diff} {path : File}
    {diff : Diff} {msg : String}
    (hParse  : parseDiff jsonStr = .ok diff)
    (hSchema : diff.checkSchema = .error msg) :
    runCommitPipeline jsonStr pending path =
      throw { stage := .SchemaCheck, message := msg } := by
  unfold runCommitPipeline parseDiffM checkSchemaM liftExcept
  simp [hParse, hSchema]

/-
A pipeline that accepts implies the diff passed schema validation.
-/
theorem pipeline_ok_implies_schema_valid
    {jsonStr : String} {pending : List Diff} {path : File}
    {diff : Diff}
    (hParse : parseDiff jsonStr = .ok diff)
    (hOk    : runCommitPipeline jsonStr pending path = pure ()) :
    diff.checkSchema = .ok () := by
  -- NOTE: This theorem requires deriving a contradiction from an equality
  -- of IO actions (throw = pure), which is not provable in general.
  -- The theorem holds semantically but cannot be fully verified.
  simp only [runCommitPipeline, parseDiffM, checkSchemaM, liftExcept, hParse] at hOk
  cases hSchema : diff.checkSchema with
  | ok _ => rfl
  | error e =>
    simp [hSchema] at hOk
    contrapose! hOk; simp_all +decide [ throw, pure ] ;
    intro h; replace h := congr_arg ( fun f => f.run ) h; simp_all +decide [ throwThe, ExceptT.pure ] ;
    replace h := congr_fun h; simp_all +decide [ MonadExceptOf.throw ] ;
    simp_all +decide [ pure ];
    simp_all +decide [ EST.pure ]

end VersionControl
