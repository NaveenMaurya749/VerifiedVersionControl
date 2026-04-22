import VersionControl.Defns

open Lean

namespace VersionControl

def parseDiffJson (json : Json) : Except String Diff :=
  fromJson? json

def parseDiff (text : String) : Except String Diff := do
  let json ← Json.parse text
  parseDiffJson json

def diffAsJson (diff : Diff) : Json :=
  toJson diff

@[grind =] theorem parseDiff_eq_parseDiffJson (text : String) :
    parseDiff text = (do
      let json ← Json.parse text
      parseDiffJson json) := by
  rfl

@[grind =] theorem parseDiffJson_eq_fromJson (json : Json) :
    parseDiffJson json = (fromJson? json : Except String Diff) := by
  rfl

end VersionControl
