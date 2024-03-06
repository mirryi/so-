import Mathlib.Data.Set.Functor

import CTL.Basic
import TS.Basic
import TS.Path

namespace CTL
open TS

variable {s a p : Type}
         (ts : @TS s a p)
         (Φ Φ₁ Φ₂ : @StateFormula p)
         (φ φ₁ φ₂ : @PathFormula p)

mutual
  -- s ⊨ Φ
  def StateSat (ts : @TS s a p) :=
    fun Φ st => match Φ with
      | StateFormula.top => True
      | ⬝a               => a ∈ ts.label st
      | ⬝¬Φ              => ¬(StateSat ts Φ st)
      | Φ₁ ⬝∧ Φ₂         => (StateSat ts Φ₁ st) ∧ (StateSat ts Φ₂ st)
      | ⬝∃ φ             => ∃ π : PathFragment.From st, PathSat ts π.1.2 φ
      | ⬝∀ φ             => ∀ π : PathFragment.From st, PathSat ts π.1.2 φ

  -- π ⊨ φ
  def PathSat (ts : @TS s a p) (π : ts.PathFragment n) :=
    fun
     | ⬝◯ Φ   => StateSat ts Φ (π.get ⟨1, _⟩)
     | Φ ⬝U Ψ => ∃ j : FinWithInf n.succ, (∀ k : FinWithInf ↑j, StateSat ts Φ (π.get k)) ∧ (StateSat ts Ψ (π.get j))
end

-- Sat(Φ)
def TS.SatState := { st : s // ts.StateSat Φ st }
def TS.satStateSet := @Set.range s (ts.SatState Φ) Subtype.val

-- TS ⊨ Φ
def TS.Sat := ∀ st ∈ ts.initial, ts.StateSat Φ st

@[simp]
theorem TS.Sat.subset_iff : (ts.Sat Φ) ↔ (ts.initial ⊆ ts.satStateSet Φ) :=
  by
    apply Iff.intro
    . intro sat st mem
      exact Set.mem_range_self (⟨st, sat st mem⟩ : ts.SatState Φ)
    . intro sub st mem
      specialize sub mem
      unfold TS.satStateSet at sub
      rw [Set.mem_range] at sub
      obtain ⟨stSat, refl⟩ := sub
      rw [← refl]
      exact Subtype.property stSat

@[simp]
theorem TS.StateSat.potentialAll_def : ts.StateSat (⬝∃■Φ) st ↔ ∃π : ts.PathFrom st, ∀j, ts.StateSat Φ (π.1.2.get j) := by
  simp [StateFormula.potentialAll, TS.StateSat, StateFormula.inevitable, TS.PathSat]

@[simp]
theorem TS.StateSat.invariant_def : ts.StateSat (⬝∀■Φ) st ↔ ∀π : ts.PathFrom st, ∀j, ts.StateSat Φ (π.1.2.get j) := by
  simp [StateFormula.invariant, TS.StateSat, StateFormula.potential, TS.PathSat]
end CTL
