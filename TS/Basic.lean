import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Function

variable {s a p : Type}

structure TS where
  initial : Set s
  trans   : s × a -> Set s
  label   : s -> Set p

namespace TS
  variable (ts : @TS s a p)

  def postOn (s : s) (τ : a) :=
    ts.trans (s, τ)
  def post (s : s) :=
    { s' | ∃ τ : a, s' ∈ ts.postOn s τ }
  def setPost (c : Set s) :=
    { s' | ∃ s ∈ c, s' ∈ ts.post s }

  def preOn (s : s) (τ : a) :=
    { s' | s ∈ ts.postOn s' τ }
  def pre (s : s) :=
    { s' | ∃ τ : a, s' ∈ ts.preOn s τ }
  def setPre (c : Set s) :=
    { s' | ∃ s ∈ c, s' ∈ ts.pre s }

  def Terminal (s : s) :=
    ts.post s = ∅
end TS
