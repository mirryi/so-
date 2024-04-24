import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Set.Defs

import TS.Finset

class Model (p s : Type) [Fintype s] [DecidableEq s]
            (μ : (p : Type) → (s : Type) → [Fintype s] → Type) where
  initial : (m : μ p s) → Finset s
  label   : (m : μ p s) → (st : s) → Set p

  post    : (m : μ p s) → (st : s) → Finset s
  pre     : (m : μ p s) → (st : s) → Finset s

namespace Model
  variable [Fintype s] [DecidableEq s] [Model p s μ] (m : μ p s)

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

structure TS (a p s : Type) [Fintype a] [Fintype s] where
  initial : Finset s
  trans   : s × a -> Finset s
  label   : s -> Set p

namespace TS
  variable [Fintype a] [Fintype s] [DecidableEq s] (ts : TS a p s)

  @[simp]
  def postOn (st : s) (τ : a) :=
    ts.trans (st, τ)
  @[simp]
  def post (st : s) :=
    let sts := { (st', τ) : s × a | st' ∈ ts.postOn st τ }.toFinset
    Finset.image Prod.fst sts

  @[simp]
  def preOn (s : s) (τ : a) :=
    { s' | s ∈ ts.postOn s' τ }.toFinset
  @[simp]
  def pre (s : s) :=
    { s' | ∃ τ : a, s' ∈ ts.preOn s τ }.toFinset

  instance : Model p s (fun p s => TS a p s) where
    initial := initial
    label   := label

    post  := post
    pre   := pre
end TS
