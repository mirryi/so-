import TS.Basic

variable {s a p : Type}

structure ExecutionFrag where
  start : s
  sequence : List (a × s)

variable (ts : @TS s a p)
         (ρ  : @ExecutionFrag s a)

def ExecutionFrag.end :=
  List.getLast (ρ.start :: (List.map Prod.snd ρ.sequence)) (by simp)

def ExecutionFrag.Initial :=
  ρ.start ∈ ts.initial
def ExecutionFrag.Maximal :=
  TS.Terminal ts (ExecutionFrag.end ρ)

def Execution :=
  { ρ : ExecutionFrag // ExecutionFrag.Initial ts ρ ∧ ExecutionFrag.Maximal ts ρ }

def TS.Reachable :=
  { s : s // ∃ ρ : Execution ts, ExecutionFrag.end ρ.1 = s }
def TS.Reach :=
  { s | s : TS.Reachable ts }
