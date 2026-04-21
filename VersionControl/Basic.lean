namespace VersionControl

abbrev File := String     -- Filepath 
abbrev Content := String  -- Contents as a string
abbrev Agent := Nat     -- Identifiers for local agents 

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

structure Commit where
  (author : Agent)
  (changes : Diff)
  (commitMessage : String)

-- ActionF is the fuctorial wrapper for actions 
inductive ActionF (σ : System) (α : Type) where
| commit : Agent → Commit → α → ActionF σ α
| merge  : (source : Timeline σ) → (dest : Timeline σ) → α → ActionF σ α

-- ActionM is the free monad over ActionF 
inductive ActionM {σ : System} : Type → Type _ where
| pure : α → ActionM α
| cons : ActionF σ β → (β → ActionM α) → ActionM α

inductive Action (σ : System) where
| init   : Action σ
| commit (author : Agent) : Commit → Action σ 
| merge  (source : Timeline σ) (dest : Timeline σ) : Action σ

def push {σ : System} (source : Timeline σ) : Action σ :=
  Action.merge source Timeline.origin 

def pull {σ : System} (destination : Timeline σ) : Action σ :=
  Action.merge Timeline.origin destination

class Nothing (ρ : Repository) where
  (proof : (x : File) → (ρ x = none))

class EmptySystem (σ : System) where
  (originality : Nothing σ.origin)
  (emptiness : (α : Agent) → Nothing (σ.agents α))

def isSafe {σ : System} (action : Action σ) : Prop :=
  True

structure SafeAction (σ : System) where
  (action : Action σ)
  (certificate : isSafe action)

inductive safeAction (σ : System) where
| safeInit : EmptySystem σ → safeAction σ
-- | safeCommit :  
-- | safeMerge : 

-- This implementation is subject to change
def executeChanges : Repository → Diff → Repository :=
  fun ρ δ ↦ (fun f ↦ if δ f ≠ none then δ f else ρ f)

def executeAction {σ : System} (_ : safeAction σ) : IO Unit := 
  println! "Hello, world!"

-- Ideas for future:
-- Implement a SystemM Monad which tracks the changing state of Systems

def mysys : System := ⟨fun _ ↦ none, fun _ ↦ (fun _ ↦ none)⟩

#print mysys

def myorigin : Timeline mysys := Timeline.origin
def myagnetics : Agent → Timeline mysys := Timeline.agentic

def firstcommit : Commit := ⟨0, fun _ ↦ none, "none"⟩
def firstaction : Action mysys := Action.init
def secondaction : Action mysys := Action.commit 0 (firstcommit)
def thirdaction : Action mysys := push (myagnetics 0)

end VersionControl
