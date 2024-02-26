import Mathlib.Data.Set.Functor

import CTL.Basic
import TS.Basic
import TS.Path

variable {s a p : Type}
         (ts : @TS s a p)
         (Φ Φ₁ Φ₂ : @StateFormula p)
         (φ φ₁ φ₂ : @PathFormula p)

mutual
  def TS.StateSatisfaction (ts : @TS s a p) (st : s) :=
    fun
      | StateFormula.top => True
      | ⬝a               => a ∈ ts.label st
      | ⬝¬Φ              => ¬(ts.StateSatisfaction st Φ)
      | Φ₁ ⬝∧ Φ₂         => (ts.StateSatisfaction st Φ₁) ∧ (ts.StateSatisfaction st Φ₂)
      | ⬝∃ φ             => ∃ π : ts.Path, ts.PathSatisfaction π φ
      | ⬝∀ φ             => ∀ π : ts.Path, ts.PathSatisfaction π φ

  def TS.PathSatisfaction (ts : @TS s a p) (π : ts.Path) :=
    fun
     | ⬝◯ Φ => ts.StateSatisfaction (π.1.2.get 1) Φ
     | Φ ⬝U Ψ => ∃ j, (∀ k < j, ts.StateSatisfaction (π.1.2.get k) Φ) ∧ (ts.StateSatisfaction (π.1.2.get j) Ψ)
end

def TS.Sat := { st : s // ts.StateSatisfaction st Φ }
def TS.satSet := Subtype.val '' (Set.univ : Set (ts.Sat Φ))

def TS.Satisfaction := ∀ st ∈ ts.initial, ts.StateSatisfaction st Φ

theorem TS.Satisfaction_subset : (ts.Satisfaction Φ) ↔ (ts.initial ⊆ ts.satSet Φ) :=
  by
    apply Iff.intro
    . intro sat st mem
      -- exact sat st mem
      constructor
      . intros
        done
    . intro sub x y
      rw [Set.subset_def] at sub
      specialize sub x
      specialize sub y
      --
    done
