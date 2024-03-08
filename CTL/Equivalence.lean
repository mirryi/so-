import TS.Basic
import CTL.Basic
import CTL.Satisfaction

namespace CTL
variable {p : Type}
         (Φ Ψ : @StateFormula p)

-- Sat(Φ) = Sat(Ψ)
def Equiv :=
  ∀{s a : Type} , ∀{ts : @TS s a p}, satStateSet ts Φ = satStateSet ts Ψ
-- TS ⊨ Φ ↔ TS ⊨ Ψ
def Equiv' :=
  ∀{s a : Type} , ∀{ts : @TS s a p}, Sat ts Φ ↔ Sat ts Ψ

@[simp]
theorem Equiv_Equiv' : Equiv Φ Ψ → Equiv' Φ Ψ := by
  simp [Equiv, Equiv']
  intro h s a ts
  rewrite [h]
  trivial

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
