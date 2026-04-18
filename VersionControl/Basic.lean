namespace VersionControl

def Agent := Nat
-- The type of agents 

def ValidJSONFormat : String → Type :=
  fun _ ↦ Nat 

def checkValid : String → Bool :=
  fun _ ↦ True

--instance : (σ : String) → (checkValid σ = True) → (ValidJSONFormat σ)  

inductive Timeline where
| origin : Timeline
| remote : (a : Agent) → Timeline

inductive Commit where
| init : Commit 
| update : (author : Agent) → (changes : Diff) → (parent : Commit) → Commit

#print Timeline
#print Commit

#check Commit.update  

-- Or maybe implement as a typeclass
inductive Action where
| commit : Commit → Action
| pull   : (recipient : Agent) → Action
| push   : (author : Agent) → Commit  → Action
| merge  : Commit → Commit → Action

--def HandleAction : Action → IO() :=
--  do


--inductive SafeAction where
--| safePull : 

end VersionControl
