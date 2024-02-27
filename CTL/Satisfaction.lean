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
  def TS.StateSatisfaction (ts : @TS s a p) (st : s) :=
    fun
      | StateFormula.top => True
      | ⬝a               => a ∈ ts.label st
      | ⬝¬Φ              => ¬(ts.StateSatisfaction st Φ)
      | Φ₁ ⬝∧ Φ₂         => (ts.StateSatisfaction st Φ₁) ∧ (ts.StateSatisfaction st Φ₂)
      | ⬝∃ φ             => ∃ π : ts.Path, ts.PathSatisfaction π φ
      | ⬝∀ φ             => ∀ π : ts.Path, ts.PathSatisfaction π φ

  -- π ⊨ φ
  def TS.PathSatisfaction (ts : @TS s a p) (π : ts.Path) :=
    fun
     | ⬝◯ Φ   => ts.StateSatisfaction (π.1.2.get 1) Φ
     | Φ ⬝U Ψ => ∃ j, (∀ k < j, ts.StateSatisfaction (π.1.2.get k) Φ) ∧ (ts.StateSatisfaction (π.1.2.get j) Ψ)
end

-- Sat(Φ)
def TS.Sat := { st : s // ts.StateSatisfaction st Φ }
def TS.satSet := @Set.range s (ts.Sat Φ) Subtype.val

-- TS ⊨ Φ
def TS.Satisfaction := ∀ st ∈ ts.initial, ts.StateSatisfaction st Φ

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
