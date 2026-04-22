namespace VersionControl

-- TODO : Change this to encode a reference to an external filesystem, and also later
-- supplement it with implementation of the filesystem, but for now have it be purely formally in 
-- Lean.
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

def ActionF.map {σ : System} {α β} (f : α → β) : ActionF σ α → ActionF σ β
| ActionF.commit id c next => ActionF.commit id c (f next)
| ActionF.merge t1 t2 next => ActionF.merge t1 t2 (f next)

-- ActionF is a functor encoding a singular step of actions
instance (σ : System) : Functor (ActionF σ) where
  map := ActionF.map

-- ActionM is the free monad over ActionF 
inductive ActionM {σ : System} : Type → Type _ where
| pure : α → ActionM α
| impure : ActionF σ β → (β → ActionM α) → ActionM α

def ActionM.bind {σ : System} (x : @ActionM σ α) (f : α → @ActionM σ β) : @ActionM σ β :=
match x, f with
| ActionM.pure a, f      => f a
| ActionM.impure op k, f =>
    ActionM.impure op (fun x => bind (k x) f)

instance (σ : System) : Monad (@ActionM σ) where
  pure := ActionM.pure
  bind := ActionM.bind

def liftF {σ α} (op : ActionF σ α) : @ActionM σ α :=
  ActionM.impure op ActionM.pure

-- Complete the logic here
def isSafeAction (σ : System) : ActionF σ Unit→ Prop
| ActionF.commit id c _ => True
| ActionF.merge t1 t2 _ => False

structure SafeAction (σ : System) where
  action : ActionF σ Unit
  proof  : isSafeAction σ action

def execSafeAction (σ : System) : SafeAction σ → System 
| ⟨ActionF.commit id c _, proof⟩ => σ
  -- Semantics of commits onto actual Repository
| ⟨ActionF.merge t1 t2 next, proof⟩ => σ 
  -- semantics of merging when proven safe
--
-- TODO : In the future, add a `--force` option to merge, given appropriate credentials which will
-- TODO :
-- merge conflicts.
-- Ideas for future:
-- Implement a SafeM Monad which tracks the changing state of Systems via SafePrograms

inductive SafeProgram : System → System → Type where
| nil  {σ : System} : SafeProgram σ σ
| cons {σ₁ σ₂ : System} : (act : SafeAction σ₂) → (rest : SafeProgram σ₁ σ₂) → SafeProgram σ₁ (execSafeAction σ₂ act) 

-- The logic to verify whether a given Program (ActionM σ Unit) leads to a SafeProgram
--def verify : (σ : System) → @ActionM σ Unit → Option (Σ σ', SafeProgram σ σ') := sorry

def runSafeProgram : SafeProgram σ₁ σ₂ → System
| @SafeProgram.nil σ₁ => σ₁
| @SafeProgram.cons σ₁ σ₂ act rest =>
    execSafeAction σ₂ act

def myorigin : Timeline mysys := Timeline.origin
def myagnetics : Agent → Timeline mysys := Timeline.agentic

def firstcommit : Commit := ⟨0, fun _ ↦ none, "none"⟩

end VersionControl
