namespace VersionControl

abbrev File := String     -- Filepath 
abbrev Content := String  -- Contents as a string
abbrev AgentID := Nat     -- Identifiers for local agents 

-- A partial map from filepaths to content
-- (We can change this later to refer an actual filesystem)
abbrev Repository := File → Option Content

structure System where
  (origin : Repository)
  (agents : Agent → Repository)

inductive Timeline (σ : System) where
| origin  : Timeline σ
| agentic : Agent → Timeline σ

-- Changes to a filepath, currently only rewrite supported
def Diff := File → Option Content

inductive Commit (author : Agent) where
| update (changes : Diff) : Commit author 

inductive Action (σ : System) where
| commit (author : Agent) : Commit author → Action σ 
| merge  (source : Timeline σ) (dest : Timeline σ) : Action σ

def push {σ : System} (source : Timeline σ) : Action σ :=
  Action.merge source Timeline.origin 

def pull {σ : System} (destination : Timeline σ) : Action σ :=
  Action.merge Timeline.origin destination

inductive safeAction (σ : System) where

-- This implementation is subject to change
def executeChanges : Repository → Diff → Repository :=
  fun ρ δ ↦ (fun f ↦ if δ f ≠ none then δ f else ρ f)

def executeAction {σ : System} (_ : safeAction σ) : IO Unit := 
  println! "Hello, world!"

end VersionControl
