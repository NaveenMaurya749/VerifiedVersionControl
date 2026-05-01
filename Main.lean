import VersionControl.AgentInterface
import VersionControl.ErrorOutput
import VersionControl.JsonParse

open VersionControl

def main : IO Unit := do
  IO.println "=== VerifiedVersionControl Demo ==="
  IO.println ""

  -- Set up the shared file
  IO.FS.writeFile "demo.txt" "line one\nline two\nline three"
  IO.println "Initial file (demo.txt):"
  IO.println (← IO.FS.readFile "demo.txt")
  IO.println ""

  -- ── SCENARIO 1: Agent 1 makes a clean edit ──────────────────
  IO.println "--- Scenario 1: Agent 1 edits line 2 ---"
  let agent1Diff := "{
    \"agent\": 1,
    \"file\": \"demo.txt\",
    \"timestamp\": \"2026-05-01T00:00:00Z\",
    \"base_line_count\": 3,
    \"diffs\": [{
      \"seq\": 1,
      \"op\": \"replace\",
      \"range\": [2, 3],
      \"before\": [\"line two\"],
      \"after\": [\"line two - AGENT 1 WAS HERE\"]
    }],
    \"newContent\": null
  }"
  let r1 ← submitCommit 1 agent1Diff [] "demo.txt"
  IO.println s!"Result: {r1}"
  IO.println "File now:"
  IO.println (← IO.FS.readFile "demo.txt")
  IO.println ""

  -- ── SCENARIO 2: Agent 2 uses stale base ─────────────────────
  IO.println "--- Scenario 2: Agent 2 tries stale diff (old 'line two' is gone) ---"
  let agent2Stale := "{
    \"agent\": 2,
    \"file\": \"demo.txt\",
    \"timestamp\": \"2026-05-01T00:01:00Z\",
    \"base_line_count\": 3,
    \"diffs\": [{
      \"seq\": 1,
      \"op\": \"replace\",
      \"range\": [2, 3],
      \"before\": [\"line two\"],
      \"after\": [\"line two - agent 2 attempt\"]
    }],
    \"newContent\": null
  }"
  let r2 ← submitCommit 2 agent2Stale [] "demo.txt"
  IO.println s!"Result: {r2}"
  IO.println ""

  -- ── SCENARIO 3: Two agents conflict on the same line ────────
  IO.println "--- Scenario 3: Agents 2 and 3 both target line 3 (conflict) ---"

  let agent3Pending := "{
    \"agent\": 3,
    \"file\": \"demo.txt\",
    \"timestamp\": \"2026-05-01T00:02:00Z\",
    \"base_line_count\": 3,
    \"diffs\": [{
      \"seq\": 1,
      \"op\": \"replace\",
      \"range\": [3, 4],
      \"before\": [\"line three\"],
      \"after\": [\"line three - AGENT 3 VERSION\"]
    }],
    \"newContent\": null
  }"
  let agent3Diff := match parseDiff agent3Pending with
    | .ok d  => d
    | .error _ => default

  let agent2Fresh := "{
    \"agent\": 2,
    \"file\": \"demo.txt\",
    \"timestamp\": \"2026-05-01T00:03:00Z\",
    \"base_line_count\": 3,
    \"diffs\": [{
      \"seq\": 1,
      \"op\": \"replace\",
      \"range\": [3, 4],
      \"before\": [\"line three\"],
      \"after\": [\"line three - AGENT 2 VERSION\"]
    }],
    \"newContent\": null
  }"
  let r3 ← submitCommit 2 agent2Fresh [agent3Diff] "demo.txt"
  IO.println s!"Result: {r3}"
  IO.println ""

  IO.println "Final file state:"
  IO.println (← IO.FS.readFile "demo.txt")
