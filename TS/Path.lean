import Mathlib.Data.Vector.Basic
import Mathlib.Data.Stream.Defs
import Mathlib.Data.ENat.Basic

import TS.Basic
import TS.EFin

namespace TS
variable {s a p : Type}

namespace PathFragment
  structure Finite (ts : @TS s a p) (n : ℕ) where
    states   : Vector s n.succ
    valid    : ∀j : Fin n, states.get j.succ ∈ ts.post (states.get j)
    atLeast1 : 0 < n

  structure Infinite (ts : @TS s a p) where
    states : Stream' s
    valid  : ∀j, states.get j.succ ∈ ts.post (states.get j)
end PathFragment

inductive PathFragment (ts : @TS s a p) : ℕ∞ -> Type where
  | finite   : (n : ℕ) -> PathFragment.Finite ts n -> PathFragment ts n
  | infinite :            PathFragment.Infinite ts -> PathFragment ts ⊤

namespace PathFragment
  variable {ts : @TS s a p}

  namespace Finite
    variable (πf : Finite ts n)

    def length :=
      πf.states.length

    def first := πf.states.head
    def last  := πf.states.last
    def get (j : Fin n.succ) :=
      πf.states.get j
    def second := πf.get ⟨1, Nat.succ_lt_succ πf.atLeast1⟩

    def Initial := πf.first ∈ ts.initial
    def Maximal := ts.Terminal πf.last

    def FromN (st : s) := { πf : Finite ts n // πf.first = st ∧ πf.Maximal}
    def From (st : s)  := { πf : Σ (n : ℕ), Finite ts n // πf.2.first = st ∧ πf.2.Maximal}
  end Finite

  namespace Infinite
    variable (πi : Infinite ts)

    def first := πi.states.head
    def get := πi.states.get
    def second := πi.get 1

    def Initial := πi.first ∈ ts.initial

    def From (ts : @TS s a p) (st : s) := { πi : Infinite ts // πi.first = st }
  end Infinite

  variable {n : ℕ∞} (π : ts.PathFragment n)

  def length : ℕ∞ :=
    match π with
      | .finite _ πf => πf.length
      | .infinite πi => ⊤

  def first :=
    match π with
      | .finite _ πf => πf.first
      | .infinite πi => πi.first
  def last :=
    match π with
      | .finite _ πf => some πf.last
      | .infinite _  => none
  def get (i : EFin (Order.succ n)) := by
    cases π with
      | finite n πf =>
        cases i with
        | fin i lt => exact πf.get ⟨i, lt⟩
      | infinite πi =>
        cases i with
        | inf i => exact πi.get i
  def second :=
    match π with
      | .finite _ πf => πf.second
      | .infinite πi => πi.second

  def Initial :=
    match π with
      | .finite _ πf => πf.Initial
      | .infinite πi => πi.Initial
  def Maximal :=
    match π with
      | .finite _ πf => πf.Maximal
      | .infinite πi => True

  def From (ts : @TS s a p) (st : s) := { π : Σ (n : ℕ), PathFragment ts n // π.2.first = st ∧ π.2.Maximal }
end PathFragment
end TS
