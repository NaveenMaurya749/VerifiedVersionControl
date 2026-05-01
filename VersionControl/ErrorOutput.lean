import Lean
import VersionControl.Defns

namespace VersionControl

/-!
# ErrorOutput

Structured error type returned to agents when a commit is rejected.
Designed to be serializable to JSON so an LLM can parse and act on it.
-/

/--
The stage at which the agent's request was rejected.
Lets the agent know how far its diff got before failing.
-/
inductive RejectionStage where
  | JsonParse        -- diff JSON was malformed
  | SchemaCheck      -- diff structure was invalid (bad ranges, op shapes, etc.)
  | BaseAlignment    -- diff's before-lines didn't match the actual file
  | ConflictCheck    -- diff conflicts with another agent's pending diff
  | FilesystemError  -- IO error reading/writing the file
  deriving Repr, DecidableEq, Inhabited, BEq

instance : ToString RejectionStage where
  toString
    | .JsonParse       => "json_parse"
    | .SchemaCheck     => "schema_check"
    | .BaseAlignment   => "base_alignment"
    | .ConflictCheck   => "conflict_check"
    | .FilesystemError => "filesystem_error"

/--
A single error message with the stage it came from.
-/
structure AgentError where
  stage   : RejectionStage
  message : String
  deriving Repr, DecidableEq, Inhabited

instance : ToString AgentError where
  toString e := s!"[{e.stage}] {e.message}"

/--
The full response sent back to an agent when their commit is rejected.
Contains the list of all errors found, in pipeline order.
-/
structure AgentResponse where
  accepted : Bool
  errors   : List AgentError  -- empty if accepted = true
  deriving Repr, Inhabited

instance : ToString AgentResponse where
  toString r :=
    if r.accepted then
      "ACCEPTED"
    else
      "REJECTED:\n" ++ (r.errors.map toString |> String.intercalate "\n")

open Lean in
instance : ToJson AgentError where
  toJson e := Json.mkObj
    [ ("stage",   toJson e.stage.toString)
    , ("message", toJson e.message) ]

open Lean in
instance : ToJson AgentResponse where
  toJson r := Json.mkObj
    [ ("accepted", toJson r.accepted)
    , ("errors",   toJson r.errors) ]

namespace AgentResponse

def ok : AgentResponse :=
  { accepted := true, errors := [] }

def reject (stage : RejectionStage) (msg : String) : AgentResponse :=
  { accepted := false
    errors   := [{ stage, message := msg }] }

def rejectMany (errs : List AgentError) : AgentResponse :=
  { accepted := false, errors := errs }

end AgentResponse

end VersionControl
