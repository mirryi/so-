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
  def TS.StateSatisfaction (ts : @TS s a p) :=
    fun Φ st => match Φ with
      | StateFormula.top => True
      | ⬝a               => a ∈ ts.label st
      | ⬝¬Φ              => ¬(ts.StateSatisfaction Φ st)
      | Φ₁ ⬝∧ Φ₂         => (ts.StateSatisfaction Φ₁ st) ∧ (ts.StateSatisfaction Φ₂ st)
      | ⬝∃ φ             => ∃ π : ts.PathFrom st, ts.PathSatisfaction π.1.2 φ
      | ⬝∀ φ             => ∀ π : ts.PathFrom st, ts.PathSatisfaction π.1.2 φ

  -- π ⊨ φ
  def TS.PathSatisfaction (ts : @TS s a p) (π : ts.PathFragment n) :=
    fun
     | ⬝◯ Φ   => ts.StateSatisfaction Φ (π.1.get 1)
     | Φ ⬝U Ψ => ∃ j, (∀ k < j, ts.StateSatisfaction Φ (π.get k)) ∧ (ts.StateSatisfaction Ψ (π.get j))
end

-- Sat(Φ)
def TS.Sat := { st : s // ts.StateSatisfaction Φ st }
def TS.satSet := @Set.range s (ts.Sat Φ) Subtype.val

-- TS ⊨ Φ
def TS.Satisfaction := ∀ st ∈ ts.initial, ts.StateSatisfaction Φ st

@[simp]
theorem TS.sat_iff : (ts.Satisfaction Φ) ↔ (ts.initial ⊆ ts.satSet Φ) :=
  by
    apply Iff.intro
    . intro sat st mem
      exact Set.mem_range_self (⟨st, sat st mem⟩ : ts.Sat Φ)
    . intro sub st mem
      specialize sub mem
      unfold TS.satSet at sub
      rw [Set.mem_range] at sub
      obtain ⟨stSat, refl⟩ := sub
      rw [← refl]
      exact Subtype.property stSat

@[simp]
theorem TS.potentialAll_sat : ts.StateSatisfaction (⬝∃■Φ) st ↔ ∃π : ts.PathFrom st, ∀j, ts.StateSatisfaction Φ (π.1.2.get j) := by
  simp [StateFormula.potentialAll, TS.StateSatisfaction, StateFormula.inevitable, TS.PathSatisfaction]

@[simp]
theorem TS.invariant_sat : ts.StateSatisfaction (⬝∀■Φ) st ↔ ∀π : ts.PathFrom st, ∀j, ts.StateSatisfaction Φ (π.1.2.get j) := by
  simp [StateFormula.invariant, TS.StateSatisfaction, StateFormula.potential, TS.PathSatisfaction]
