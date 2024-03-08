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
  intro h _ _ _
  rewrite [h]
  trivial

@[simp]
theorem equiv_conj_congr (h₁ : Equiv Φ₁ Φ₁') (h₂ : Equiv Φ₂ Φ₂') : Equiv (Φ₁ ⬝∧ Φ₂) (Φ₁' ⬝∧ Φ₂') := by
  simp [Equiv, satStateSet, SatState, StateSat, Set.ext_iff] at *
  intros _ _ _ _
  constructor
  . rintro ⟨sat₁, sat₂⟩; constructor; exact (h₁ _).1 sat₁; exact (h₂ _).1 sat₂
  . rintro ⟨sat₁, sat₂⟩; constructor; exact (h₁ _).2 sat₁; exact (h₂ _).2 sat₂

@[simp]
theorem equiv_neg_congr (h : Equiv Φ Φ') : Equiv (⬝¬Φ) (⬝¬Φ') := by
  simp [Equiv, satStateSet, SatState, StateSat, Set.ext_iff] at *
  intros _ _ _ _
  constructor
  . rintro negSat sat; exact negSat ((h _).2 sat)
  . rintro negSat sat; exact negSat ((h _).1 sat)

@[simp]
theorem equiv_exist_next_congr (h : Equiv Φ Φ') : Equiv (⬝∃⬝◯Φ) (⬝∃⬝◯Φ') := by
  simp [Equiv, satStateSet, SatState, StateSat, PathSat, Set.ext_iff] at *
  intros _ _ _ _
  constructor
  . rintro ⟨π, sat⟩; exact ⟨π, (h _).1 sat⟩
  . rintro ⟨π, sat⟩; exact ⟨π, (h _).2 sat⟩

@[simp]
theorem equiv_exist_untl_congr (h₁ : Equiv Φ Φ') (h₂ : Equiv Ψ Ψ') : Equiv (⬝∃(Φ ⬝U Ψ)) (⬝∃(Φ' ⬝U Ψ')) := by
  simp [Equiv, satStateSet, SatState, StateSat, PathSat, Set.ext_iff] at *
  intros _ _ _ _
  constructor
  . rintro ⟨π, j, ⟨satJ, satK⟩⟩; exact ⟨π, j, ⟨(h₂ _).1 satJ, fun k => (h₁ _).1 (satK k)⟩⟩
  . rintro ⟨π, j, ⟨satJ, satK⟩⟩; exact ⟨π, j, ⟨(h₂ _).2 satJ, fun k => (h₁ _).2 (satK k)⟩⟩

@[simp]
theorem equiv_all_next_congr (h : Equiv Φ Φ') : Equiv (⬝∀⬝◯Φ) (⬝∀⬝◯Φ') := by
  simp [Equiv, satStateSet, SatState, StateSat, PathSat, Set.ext_iff] at *
  intros _ _ _ _
  constructor
  . rintro sat π; rw [← h]; exact sat π
  . rintro sat π; rw [h]  ; exact sat π
  done

@[simp]
theorem equiv_all_untl_congr (h₁ : Equiv Φ Φ') (h₂ : Equiv Ψ Ψ') : Equiv (⬝∀(Φ ⬝U Ψ)) (⬝∀(Φ' ⬝U Ψ')) := by
  simp [Equiv, satStateSet, SatState, StateSat, PathSat, Set.ext_iff] at *
  intros _ _ _ _
  constructor
  . rintro sat π; obtain ⟨j, ⟨satJ, satK⟩⟩ := sat π; exact ⟨j, ⟨(h₂ _).1 satJ, fun k => (h₁ _).1 (satK k)⟩⟩
  . rintro sat π; obtain ⟨j, ⟨satJ, satK⟩⟩ := sat π; exact ⟨j, ⟨(h₂ _).2 satJ, fun k => (h₁ _).2 (satK k)⟩⟩

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
