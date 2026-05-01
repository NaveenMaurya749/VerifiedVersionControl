import VersionControl.Basic
import VersionControl.Defns
import VersionControl.JsonParse
import VersionControl.Semantics
import VersionControl.Conflict
import VersionControl.FullMerge
import VersionControl.Filesystem
import VersionControl.ErrorOutput

namespace VersionControl

/-!
# AgentInterface

The entry point called whenever an LLM agent wants to write to a file.
Runs the full validation pipeline and returns either acceptance or a
structured list of errors the agent can act on.

Usage:
  -- Agent submits a JSON diff string
  let response ← submitCommit agentId diffJson pendingDiffs filePath
  -- response is an AgentResponse (accepted or rejected with errors)
-/

/--
Runs the full pipeline for one agent commit attempt:
  1. Parse the JSON diff
  2. Check schema validity
  3. Load the actual file and check base alignment
  4. Check compatibility against all other pending diffs
  5. Apply the diff to disk

Returns `AgentResponse.ok` or a structured rejection.
-/
def submitCommit
    (agentId      : Agent)
    (diffJson     : String)       -- raw JSON string from the LLM
    (pendingDiffs : List Diff)    -- other agents' diffs not yet merged
    (filePath     : File)         -- path to the file being edited
    : IO AgentResponse := do

  -- Stage 1: JSON parse
  let diff ← match parseDiff diffJson with
    | .error e =>
        return AgentResponse.reject .JsonParse
          s!"Could not parse diff JSON: {e}"
    | .ok d => pure d

  -- Stage 2: Schema check (ranges, op shapes, hunk ordering)
  match diff.checkSchema with
  | .error e =>
      return AgentResponse.reject .SchemaCheck
        s!"Diff failed schema validation: {e}"
  | .ok _ => pure ()

  -- Stage 3: Load the real file and check base alignment
  let base ← try
    loadBaseFile filePath
  catch e =>
    return AgentResponse.reject .FilesystemError
      s!"Could not read file '{filePath}': {e}"

  match diff.checkAgainstBase base with
  | .error e =>
      return AgentResponse.reject .BaseAlignment
        s!"Diff does not align with current file contents: {e}\n" ++
        s!"Hint: re-read the file and regenerate your diff from the current version."
  | .ok _ => pure ()

  -- Stage 4: Conflict check against pending diffs from other agents
  let conflictErrors := pendingDiffs.filterMap fun pending =>
    if diffConflictFlag diff pending then
      some { stage  := .ConflictCheck
             message := s!"Conflicts with agent {pending.agent}'s pending diff on '{pending.file}'" }
    else
      none

  if !conflictErrors.isEmpty then
    return AgentResponse.rejectMany conflictErrors

  -- Stage 5: Apply the diff to disk
  match ← applyDiffToFile filePath diff with
  | .error e =>
      return AgentResponse.reject .FilesystemError
        s!"Diff was valid but could not be written to disk: {e}"
  | .ok _ =>
      return AgentResponse.ok
