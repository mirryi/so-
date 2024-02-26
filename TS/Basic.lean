import Mathlib.Data.Set.Defs
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
  { s' | ∃ τ : a, s' ∈ ts.postOn s τ }
def TS.setPost (c : Set s) :=
  { s' | ∃ s ∈ c, s' ∈ ts.post s }

def TS.preOn (s : s) (τ : a) :=
  { s' | s ∈ ts.postOn s' τ }
def TS.pre (s : s) :=
  { s' | ∃ τ : a, s' ∈ ts.preOn s τ }
def TS.setPre (c : Set s) :=
  { s' | ∃ s ∈ c, s' ∈ ts.pre s }

def TS.Terminal (s : s) :=
  ts.post s = ∅
