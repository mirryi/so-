import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Function

variable {s a p : Type}

structure TS where
  initial : Set s
  trans   : s × a -> Set s
  label   : s -> Set p

variable (ts : @TS s a p)

def TS.postOn (s : s) (τ : a) :=
  ts.trans (s, τ)
def TS.post (s : s) :=
  { s' | ∃ τ : a, s' ∈ TS.postOn ts s τ }
def TS.setPost (c : Set s) :=
  { s' | ∃ s ∈ c, s' ∈ TS.post ts s }

def TS.preOn (s : s) (τ : a) :=
  { s' | s ∈ TS.postOn ts s' τ }
def TS.pre (s : s) :=
  { s' | ∃ τ : a, s' ∈ TS.preOn ts s τ }
def TS.setPre (c : Set s) :=
  { s' | ∃ s ∈ c, s' ∈ TS.pre ts s }

def TS.Terminal (s : s) :=
  TS.post ts s = ∅
