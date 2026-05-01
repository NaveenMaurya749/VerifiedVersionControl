import Lean
import VersionControl.Basic

namespace VersionControl

/-!
# Filesystem Layer

This module handles the raw interaction between the VCS logic and the OS.
It supports both text-based I/O (for diffing) and binary I/O (for assets/binaries),
ensuring that the VCS does not corrupt non-text files.
-/

def readBinaryFile (path : File) : IO ByteArray := do
  try
    IO.FS.readBinFile path
  catch e =>
    throw (IO.userError s!"VCS Filesystem Error: Failed to read binary file at {path}: {e}")

def writeBinaryFile (path : File) (content : ByteArray) : IO Unit := do
  try
    IO.FS.writeBinFile path content
  catch e =>
    throw (IO.userError s!"VCS Filesystem Error: Failed to write binary file at {path}: {e}")

def stringToBytes (s : String) : ByteArray :=
  s.toUTF8  -- was: s.encodeUtf8

def bytesToString (b : ByteArray) : Except String String :=
  match String.fromUTF8? b with  -- was: b.decodeUtf8
  | some s => .ok s
  | none   => .error "Binary data detected: File is not valid UTF-8 text."

def isBinaryFile (path : File) : IO Bool := do
  try
    let bytes ← readBinaryFile path
    let sample : ByteArray := bytes.extract 0 1024  -- was: bytes.take 1024
    return (ByteArray.findIdx? sample (· == 0)).isSome  -- was: sample.any (· == 0)
  catch _ =>
    return true

inductive FileContent where
  | Text   (s : String)
  | Binary (b : List UInt8)

def readFileSmart (path : File) : IO FileContent := do
  let bytes ← readBinaryFile path
  match bytesToString bytes with
  | .ok s    => return FileContent.Text s
  | .error _ => return FileContent.Binary bytes.data.toList

end VersionControl
