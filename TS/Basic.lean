import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Defs

class Model (μ : Type) where
  p  : Type
  s : Type
  sFin : Fintype s

  initial : (m : μ) → Set s
  label   : (m : μ) → (st : s) → Set p

  post    : (m : μ) → (st : s) → Set s
  pre     : (m : μ) → (st : s) → Set s

namespace Model
  variable [Model μ] (m : μ)

  @[simp]
  def setPost (c : Set (s μ)) :=
      { s' | ∃ s ∈ c, s' ∈ post m s }

  @[simp]
  def setPre (c : Set (s μ)) :=
    { s' | ∃ s ∈ c, s' ∈ pre m s }

  @[simp]
  def stateIsTerminal (s : s μ) :=
    post m s = ∅
end Model

structure TS (s a p : Type) [Fintype s] where
  initial : Set s
  trans   : s × a -> Set s
  label   : s -> Set p

namespace TS
  variable [sFin : Fintype s] (ts : TS s a p)

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

  instance : Model (TS s a p) where
    p    := p
    s    := s
    sFin := sFin

    initial := initial
    label   := label

    post  := post
    pre   := pre
end TS
