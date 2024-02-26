import Mathlib.Data.Vector.Basic

import TS.Basic

variable {s a p : Type} (ts : @TS s a p) (n : ℕ)

structure TS.ExecutionFragment where
  states  : Vector s n.succ
  actions : Vector a n
  valid   : ∀ i : Fin n, states.get i.succ ∈ ts.trans (states.get i.castSucc, actions.get i)

variable (ρ : ts.ExecutionFragment n)

def TS.ExecutionFragment.start :=
  ρ.states.head
def TS.ExecutionFragment.end :=
  ρ.states.last

def TS.ExecutionFragment.Initial :=
  ρ.start ∈ ts.initial
def TS.ExecutionFragment.Maximal :=
  ts.Terminal ρ.end

def TS.Execution :=
  { ρ : ts.ExecutionFragment n // ρ.Initial ∧ ρ.Maximal }

def TS.ReachableN :=
  { st : s // ∃ ρ : ts.Execution n, ρ.1.end = st }
def TS.Reachable :=
  { st : s // ∀ n, ∃ ρ : ts.Execution n, ρ.1.end = st }
