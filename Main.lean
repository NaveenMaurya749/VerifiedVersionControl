import VersionControl.AgentInterface
import VersionControl.ErrorOutput

open VersionControl

def main : IO Unit := do
  IO.println "=== VerifiedVersionControl Demo ==="
  IO.println ""

  -- A hardcoded diff JSON simulating Agent 1 making a text edit
  let diffJson := "{
    \"agent\": 1,
    \"file\": \"demo.txt\",
    \"timestamp\": \"2026-05-01T00:00:00Z\",
    \"base_line_count\": 3,
    \"diffs\": [{
      \"seq\": 1,
      \"op\": \"replace\",
      \"range\": [2, 3],
      \"before\": [\"line two\"],
      \"after\": [\"line two - edited by agent 1\"]
    }],
    \"newContent\": null
  }"

  -- Write a demo file first so there's something to edit
  IO.FS.writeFile "demo.txt" "line one\nline two\nline three\n"
  IO.println "Created demo.txt with 3 lines."
  IO.println ""

  -- Agent 1 submits their diff, no pending diffs from other agents
  IO.println "Agent 1 submitting diff..."
  let response ← submitCommit 1 diffJson [] "demo.txt"
  IO.println s!"Result: {response}"
  IO.println ""

  -- Show the file after the edit
  let after ← IO.FS.readFile "demo.txt"
  IO.println "demo.txt after agent 1's commit:"
  IO.println after

  -- Now simulate a conflict: Agent 2 tries to edit the same line
  -- but with stale base content (the old "line two" is gone)
  IO.println "Agent 2 submitting conflicting diff (stale base)..."
  let staleDiff := "{
    \"agent\": 2,
    \"file\": \"demo.txt\",
    \"timestamp\": \"2026-05-01T00:01:00Z\",
    \"base_line_count\": 3,
    \"diffs\": [{
      \"seq\": 1,
      \"op\": \"replace\",
      \"range\": [2, 3],
      \"before\": [\"line two\"],
      \"after\": [\"line two - edited by agent 2\"]
    }],
    \"newContent\": null
  }"
  let response2 ← submitCommit 2 staleDiff [] "demo.txt"
  IO.println s!"Result: {response2}"
