import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Defs

class Model (p s : Type) [Fintype s]
            (μ : (p : Type) → (s : Type) → [Fintype s] → Type) where
  initial : (m : μ p s) → Set s
  label   : (m : μ p s) → (st : s) → Set p

  post    : (m : μ p s) → (st : s) → Set s
  pre     : (m : μ p s) → (st : s) → Set s

namespace Model
  variable [Fintype s] [Model p s μ] (m : μ p s)

  @[simp]
  def setPost (c : Set s) :=
      { s' | ∃ s ∈ c, s' ∈ post m s }

  @[simp]
  def setPre (c : Set s) :=
    { s' | ∃ s ∈ c, s' ∈ pre m s }

  @[simp]
  def stateIsTerminal (st : s) :=
    post m st = ∅
end Model

structure TS (a p s : Type) [Fintype s] where
  initial : Set s
  trans   : s × a -> Set s
  label   : s -> Set p

namespace TS
  variable [Fintype s] (ts : TS a p s)

  @[simp]
  def postOn (s : s) (τ : a) :=
    ts.trans (s, τ)
  @[simp]
  def post (s : s) :=
    { s' | ∃ τ : a, s' ∈ ts.postOn s τ }

  @[simp]
  def preOn (s : s) (τ : a) :=
    { s' | s ∈ ts.postOn s' τ }
  @[simp]
  def pre (s : s) :=
    { s' | ∃ τ : a, s' ∈ ts.preOn s τ }

  instance : Model p s (TS a) where
    initial := initial
    label   := label

    post  := post
    pre   := pre
end TS
