import Mathlib.Data.Vector.Basic
import Mathlib.Data.Stream.Defs
import Mathlib.Data.ENat.Basic

import TS.Basic
import TS.EFin

class PathFragment [Fintype s] [DecidableEq s] [Model p s μ] (m : μ p s)
                   (β : μ p s → Type) where
  length   : (π : β m) → {n : ℕ∞ // Nat.zero < n}
  get      : (π : β m) → (j : EFin (Order.succ (length π))) → s
  valid    : (π : β m) → (j : EFin (length π)) → get π j.succ ∈ Model.post m (get π j.castSucc)

namespace PathFragment
  variable [Fintype s] [DecidableEq s] [Model p s μ] {m : μ p s}
           {β : μ p s → Type} [PathFragment m β] (π : β m)

  @[simp]
  def first := get π EFin.zero

  @[simp]
  def second := by
    cases h : (length π).val with
    | some n =>
      refine get π ?_
      rewrite [h]
      refine EFin.fin 1 (Nat.succ_lt_succ (WithTop.some_lt_some.1 ?_))
      rewrite [←h]
      exact (length π).2
      done
    | none   =>
      refine get π ?_
      rw [h]
      exact EFin.inf 1

  @[simp]
  def last? : Option s := by
    cases h : (length π).val with
    | some n =>
      refine some (get π ?_)
      rewrite [h]
      exact EFin.mkSucc n
    | none   => exact none

  @[simp]
  def isInitial := first π ∈ Model.initial m

  @[simp]
  def isMaximal := by
    cases last? π with
    | some st => exact Model.stateIsTerminal m st
    | none    => exact True
end PathFragment

namespace Model
  variable [Fintype s] [DecidableEq s] [Model p s μ] (m : μ p s)
           {β : μ p s → Type} [PathFragment m β]

  @[simp]
  def Paths (st : s) :=
    { π : β m // PathFragment.first π = st ∧ PathFragment.isMaximal π }
end Model

structure FinitePathFragment [Fintype s] [DecidableEq s] [Model p s μ] (m : μ p s) where
  length   : {n : ℕ // 0 < n}
  states   : Vector s length.1.succ
  valid    : (j : Fin length) → states.get j.succ ∈ Model.post m (states.get j.castSucc)

namespace FinitePathFragment
  variable [Fintype s] [DecidableEq s] [Model p s μ] {m : μ p s}
           (π : FinitePathFragment m)

  instance : PathFragment m (FinitePathFragment) where
    length π :=
      let n := length π
      ⟨some n.1, WithTop.some_lt_some.2 n.2⟩

    get π j := by
      cases j with
      | fin i lt => exact π.states.get ⟨i, lt⟩

    valid π j := by
      cases j with
      | fin i lt => exact valid π ⟨i, lt⟩
end FinitePathFragment

structure InfinitePathFragment [Fintype s] [DecidableEq s] [Model p s μ] (m : μ p s) where
  states : Stream' s 
  valid  : (j : ℕ) → states.get j.succ ∈ Model.post m (states.get j)

namespace InfinitePathFragment
  variable [Fintype s] [DecidableEq s] [Model p s μ] {m : μ p s}
           (π : InfinitePathFragment m)

  @[simp] def get (j : ℕ) := π.states.get j

  instance : PathFragment m (InfinitePathFragment) where
    length _ := ⟨⊤, WithTop.coe_lt_top 0⟩

    get π j := by
      cases j with
      | inf j => exact get π j

    valid π j := by
      cases j with
      | inf j => exact valid π j
end InfinitePathFragment

inductive FiniteOrInfinitePathFragment [Fintype s] [DecidableEq s] [Model p s μ] (m : μ p s) where
  | fin : FinitePathFragment   m → FiniteOrInfinitePathFragment m
  | inf : InfinitePathFragment m → FiniteOrInfinitePathFragment m

namespace FiniteOrInfinitePathFragment
  variable [Fintype s] [DecidableEq s] [Model p s μ] {m : μ p s}
           (π : FiniteOrInfinitePathFragment m)

  instance : PathFragment m (FiniteOrInfinitePathFragment) where
    length := fun
      | .fin π => PathFragment.length π
      | .inf π => PathFragment.length π

    get := fun
      | .fin π => PathFragment.get π
      | .inf π => PathFragment.get π

    valid := fun
      | .fin π => PathFragment.valid π
      | .inf π => PathFragment.valid π

  @[simp] def length := PathFragment.length π
  @[simp] def get := PathFragment.get π
  @[simp] def valid := PathFragment.valid π
end FiniteOrInfinitePathFragment
