import Mathlib.Data.Set.Functor

import CTL.Basic
import TS.Basic
import TS.Path
import TS.EFin

namespace CTL
open TS

variable {s a p : Type}
         (ts : @TS s a p)
         (Φ Φ₁ Φ₂ : @StateFormula p)
         (φ φ₁ φ₂ : @PathFormula p)

mutual
  -- s ⊨ Φ
  def StateSat :=
    fun Φ st => match Φ with
      | StateFormula.top => True
      | ⬝a               => a ∈ ts.label st
      | ⬝¬Φ              => ¬(StateSat Φ st)
      | Φ₁ ⬝∧ Φ₂         => (StateSat Φ₁ st) ∧ (StateSat Φ₂ st)
      | ⬝∃ φ             => ∃ π : PathFragment.From ts st, PathSat π.1.2 φ
      | ⬝∀ φ             => ∀ π : PathFragment.From ts st, PathSat π.1.2 φ

  -- π ⊨ φ
  def PathSat (π : ts.PathFragment n) :=
    fun
      | ⬝◯ Φ   => StateSat Φ (π.second)
      | Φ ⬝U Ψ => ∃ j : EFin (Order.succ n), (StateSat Ψ (π.get j)) ∧ ∀ k : EFin j.val, StateSat Φ (π.get (EFin.castLT j.lt k))
end

-- Sat(Φ)
def SatState := { st : s // StateSat ts Φ st }
def satStateSet := @Set.range s (SatState ts Φ) Subtype.val

-- TS ⊨ Φ
def Sat := ∀ st ∈ ts.initial, StateSat ts Φ st

@[simp]
theorem Sat_iff_subset : (Sat ts Φ) ↔ (ts.initial ⊆ satStateSet ts Φ) :=
  by
    apply Iff.intro
    . intro sat st mem
      exact Set.mem_range_self (⟨st, sat st mem⟩ : SatState ts Φ)
    . intro sub st mem
      specialize sub mem
      unfold satStateSet at sub
      rw [Set.mem_range] at sub
      obtain ⟨stSat, refl⟩ := sub
      rw [← refl]
      exact Subtype.property stSat

namespace StateSat
  @[simp]
  theorem potentialAll_def {st : s} : StateSat ts (⬝∃■Φ) st ↔ ∃π : PathFragment.From ts st, ∀j, StateSat ts Φ (π.1.2.get j) := by
    simp [StateFormula.potentialAll, StateSat, StateFormula.inevitable, PathSat]

  @[simp]
  theorem invariant_def : StateSat ts (⬝∀■Φ) st ↔ ∀π : PathFragment.From ts st, ∀j, StateSat ts Φ (π.1.2.get j) := by
    simp [StateFormula.invariant, StateSat, StateFormula.potential, PathSat]
end StateSat

end CTL
