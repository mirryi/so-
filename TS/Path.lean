import Mathlib.Data.Vector.Basic

import TS.Basic

variable {s a p : Type} (ts : @TS s a p) (n : ℕ)

structure TS.PathFragment where
  states  : Vector s n.succ
  valid   : ∀ i : Fin n, states.get i.succ ∈ ts.post (states.get i)

variable (π : ts.PathFragment n)

def TS.PathFragment.first :=
  π.states.head
def TS.PathFragment.last :=
  π.states.last
def TS.PathFragment.get :=
  π.states.get

def TS.PathFragment.drop :=
  π.states.drop
def TS.PathFragment.take :=
  π.states.take

def TS.PathFragment.Initial :=
  π.first ∈ ts.initial
def TS.PathFragment.Maximal :=
  ts.Terminal π.last

def TS.PathN :=
  { π : ts.PathFragment n // π.Initial ∧ π.Maximal }
def TS.Path :=
  { π : Σ (n : ℕ), ts.PathFragment n // π.2.Initial ∧ π.2.Maximal }
