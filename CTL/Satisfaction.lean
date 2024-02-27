import Mathlib.Data.Set.Functor

import CTL.Basic
import TS.Basic
import TS.Path

variable {s a p : Type}
         (ts : @TS s a p)
         (Φ Φ₁ Φ₂ : @StateFormula p)
         (φ φ₁ φ₂ : @PathFormula p)

mutual
  -- s ⊨ Φ
  def TS.StateSat (ts : @TS s a p) :=
    fun Φ st => match Φ with
      | StateFormula.top => True
      | ⬝a               => a ∈ ts.label st
      | ⬝¬Φ              => ¬(ts.StateSat Φ st)
      | Φ₁ ⬝∧ Φ₂         => (ts.StateSat Φ₁ st) ∧ (ts.StateSat Φ₂ st)
      | ⬝∃ φ             => ∃ π : ts.PathFrom st, ts.PathSat π.1.2 φ
      | ⬝∀ φ             => ∀ π : ts.PathFrom st, ts.PathSat π.1.2 φ

  -- π ⊨ φ
  def TS.PathSat (ts : @TS s a p) (π : ts.PathFragment n) :=
    fun
     | ⬝◯ Φ   => ts.StateSat Φ (π.1.get 1)
     | Φ ⬝U Ψ => ∃ j, (∀ k < j, ts.StateSat Φ (π.get k)) ∧ (ts.StateSat Ψ (π.get j))
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
