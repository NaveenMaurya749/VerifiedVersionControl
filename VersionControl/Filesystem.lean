import Lean
import VersionControl.Basic
import VersionControl.Defns
import VersionControl.Semantics

namespace VersionControl

/-!
# Filesystem Layer

Bridges the OS (real files as ByteArray) and the VCS logic layer
(Content / BaseFile / Diff). Provides:
  1. Low-level binary read/write
  2. Smart read → Content (text or binary)
  3. Content → write back to disk
  4. applyDiffToFile: read a file, apply a Diff, write it back
-/

-- ============================================================
-- 1. Low-level binary I/O
-- ============================================================

def readBinaryFile (path : File) : IO ByteArray := do
  try
    IO.FS.readBinFile path
  catch e =>
    throw (IO.userError s!"VCS read error at {path}: {e}")

def writeBinaryFile (path : File) (content : ByteArray) : IO Unit := do
  try
    IO.FS.writeBinFile path content
  catch e =>
    throw (IO.userError s!"VCS write error at {path}: {e}")

-- ============================================================
-- 2. ByteArray ↔ Content conversion
-- ============================================================

/--
Converts a ByteArray to `Content`. If valid UTF-8, produces `Content.text`
with the file split into lines. Otherwise produces `Content.binary`.
This is the bridge from raw OS bytes into the VCS type system.
-/
def bytesToContent (bytes : ByteArray) : Content :=
  match String.fromUTF8? bytes with
  | some s => Content.text (s.splitOn "\n")
  | none   => Content.binary bytes.data.toList

/--
Converts `Content` back to a ByteArray for writing to disk.
-/
def contentToBytes : Content → ByteArray
  | Content.text lines => (String.intercalate "\n" lines).toUTF8
  | Content.binary data => { data := data.toArray }

-- ============================================================
-- 3. High-level Content I/O
-- ============================================================

/--
Reads a file from disk and returns it as `Content`.
Text files become `Content.text (lines)`, binary files become
`Content.binary (bytes)`. This is what agents call to get a
`BaseFile` they can pass to `applyDiff`.
-/
def readContent (path : File) : IO Content := do
  let bytes ← readBinaryFile path
  return bytesToContent bytes

/--
Writes `Content` back to disk. Inverse of `readContent`.
-/
def writeContent (path : File) (c : Content) : IO Unit := do
  writeBinaryFile path (contentToBytes c)

-- ============================================================
-- 4. Applying a Diff to a file on disk
-- ============================================================

/--
The main operation: reads a file, applies a structured `Diff` to it,
and writes the result back. Returns an error string if the diff
fails to apply (schema error, base drift, binary file, etc.).

This is where Bhoris's diff tracker meets the real filesystem.
-/
def applyDiffToFile (path : File) (diff : Diff) : IO (Except String Unit) := do
  let base ← readContent path
  match applyDiff diff base with
  | .error e =>
      return .error s!"Failed to apply diff to {path}: {e}"
  | .ok newContent =>
      writeContent path newContent
      return .ok ()

/--
Reads a file and returns it as a `BaseFile` (= `Content`),
ready to be passed to `Diff.checkAgainstBase` or `applyDiff`.
-/
def loadBaseFile (path : File) : IO BaseFile :=
  readContent path

-- ============================================================
-- 5. Repository I/O: load/save a whole Repository from disk
-- ============================================================

/--
Loads a list of file paths into a `Repository` (a partial map
File → Option Content). Files that fail to read are mapped to `none`.
-/
def loadRepository (paths : List File) : IO Repository := do
  let mut entries : List (File × Option Content) := []
  for path in paths do
    try
      let c ← readContent path
      entries := entries ++ [(path, some c)]
    catch _ =>
      entries := entries ++ [(path, none)]
  let map := entries
  return fun f => (map.find? (fun e => e.1 == f)).bind (·.2)

/--
Writes all `some` entries of a Repository back to disk.
Files mapped to `none` are skipped.
-/
def saveRepository (repo : Repository) (paths : List File) : IO Unit := do
  for path in paths do
    match repo path with
    | none => pure ()
    | some c => writeContent path c

end VersionControl
