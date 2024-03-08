import TS.Basic
import CTL.Basic
import CTL.Satisfaction

namespace CTL
variable {p : Type}
         (Φ Ψ : @StateFormula p)

-- Sat(Φ) = Sat(Ψ)
@[simp]
def Equiv :=
  ∀{s a : Type} , ∀{ts : @TS s a p}, satStateSet ts Φ = satStateSet ts Ψ

-- TS ⊨ Φ ↔ TS ⊨ Ψ
@[simp]
def Equiv' :=
  ∀{s a : Type} , ∀{ts : @TS s a p}, Sat ts Φ ↔ Sat ts Ψ

@[simp]
theorem equiv'_of_equiv : Equiv Φ Ψ → Equiv' Φ Ψ := by
  simp [Equiv, Equiv']
  intro h s a ts
  rewrite [h]
  trivial

@[simp]
theorem equiv_and_congr (h₁ : Equiv Φ₁ Φ₁') (h₂ : Equiv Φ₂ Φ₂') : Equiv (Φ₁ ⬝∧ Φ₂) (Φ₁' ⬝∧ Φ₂') := by
  simp [Equiv, satStateSet, SatState, StateSat, Set.ext_iff] at *
  intros s a ts st
  constructor
  . rintro ⟨sat₁, sat₂⟩
    constructor
    . exact (h₁ st).1 sat₁
    . exact (h₂ st).1 sat₂
  . rintro ⟨sat₁, sat₂⟩
    constructor
    . exact (h₁ st).2 sat₁
    . exact (h₂ st).2 sat₂

theorem all_next_duality : Equiv (⬝∀⬝◯Φ) (⬝¬(⬝∃⬝◯⬝¬Φ)) := by
  simp [Equiv, satStateSet, SatState, StateSat, PathSat]

theorem inevitable_duality : Equiv (⬝∀♢Φ) (⬝¬(⬝∃■⬝¬Φ)) := by
  simp [Equiv, satStateSet, SatState, StateSat, PathSat, StateFormula.inevitable, PathFormula.untl]

theorem exist_next_duality : Equiv (⬝∃⬝◯Φ) (⬝¬(⬝∀⬝◯⬝¬Φ)) := by
  simp [Equiv, satStateSet, SatState, StateSat, PathSat]

theorem potential_duality : Equiv (⬝∃♢Φ) (⬝¬(⬝∀■⬝¬Φ)) := by
  simp [Equiv, satStateSet, SatState, StateSat, PathSat, StateFormula.potential, PathFormula.untl]

theorem all_untl_duality : Equiv (⬝∀(Φ ⬝U Ψ)) (⬝¬(⬝∃(⬝¬Ψ ⬝U (⬝¬Φ ⬝∧ ⬝¬Ψ))) ⬝∧ ⬝¬(⬝∃■⬝¬Ψ)) := by
  sorry

theorem all_untl_expansion : Equiv (⬝∀(Φ ⬝U Ψ)) (Ψ ⬝∨ (Φ ⬝∧ (⬝∀⬝◯⬝∀(Φ ⬝U Ψ)))) := by
  -- simp [Equiv, satStateSet, SatState, StateSat, PathSat, StateFormula.disj]
  -- intro s a ts
  -- ext x
  -- done
  sorry

end CTL
