import TS.Basic
import CTL.Basic
import CTL.Satisfaction

namespace CTL
variable {p : Type}
         {Φ Φ' Ψ Ψ' : @StateFormula p}

-- Sat(Φ) = Sat(Ψ)
@[simp]
def Equiv (Φ Ψ : @StateFormula p) :=
  ∀{s a : Type} , ∀{ts : @TS s a p}, satStateSet ts Φ = satStateSet ts Ψ

-- TS ⊨ Φ ↔ TS ⊨ Ψ
@[simp]
def Equiv' (Φ Ψ : @StateFormula p) :=
  ∀{s a : Type} , ∀{ts : @TS s a p}, Sat ts Φ ↔ Sat ts Ψ

namespace Equiv
@[simp]
theorem equiv'_of_equiv : Equiv Φ Ψ → Equiv' Φ Ψ := by
  simp [Equiv, Equiv']
  intro h _ _ _
  rewrite [h]
  trivial

instance : IsRefl (@StateFormula p) Equiv where
  refl := by simp

instance : IsSymm (@StateFormula p) Equiv where
  symm := fun Φ Ψ => by simp; intros h _ _ _; exact Eq.symm h

instance : IsTrans (@StateFormula p) Equiv where
  trans := fun _ _ _ h₁ h₂ => Trans.trans h₁ h₂

instance : IsPreorder (@StateFormula p) Equiv where

instance : IsEquiv (@StateFormula p) Equiv where

@[simp]
theorem conj_congr (h₁ : Equiv Φ₁ Φ₁') (h₂ : Equiv Φ₂ Φ₂') : Equiv (Φ₁ ⬝∧ Φ₂) (Φ₁' ⬝∧ Φ₂') := by
  simp [Equiv, satStateSet, SatState, StateSat, Set.ext_iff] at *
  intros _ _ _ _
  constructor
  . rintro ⟨sat₁, sat₂⟩; constructor; exact (h₁ _).1 sat₁; exact (h₂ _).1 sat₂
  . rintro ⟨sat₁, sat₂⟩; constructor; exact (h₁ _).2 sat₁; exact (h₂ _).2 sat₂

@[simp]
theorem neg_congr (h : Equiv Φ Φ') : Equiv (⬝¬Φ) (⬝¬Φ') := by
  simp [Equiv, satStateSet, SatState, StateSat, Set.ext_iff] at *
  intros _ _ _ _
  constructor
  . rintro negSat sat; exact negSat ((h _).2 sat)
  . rintro negSat sat; exact negSat ((h _).1 sat)

@[simp]
theorem exist_next_congr (h : Equiv Φ Φ') : Equiv (⬝∃⬝◯Φ) (⬝∃⬝◯Φ') := by
  simp [Equiv, satStateSet, SatState, StateSat, PathSat, Set.ext_iff] at *
  intros _ _ _ _
  constructor
  . rintro ⟨π, sat⟩; exact ⟨π, (h _).1 sat⟩
  . rintro ⟨π, sat⟩; exact ⟨π, (h _).2 sat⟩

@[simp]
theorem exist_untl_congr (h₁ : Equiv Φ Φ') (h₂ : Equiv Ψ Ψ') : Equiv (⬝∃(Φ ⬝U Ψ)) (⬝∃(Φ' ⬝U Ψ')) := by
  simp [Equiv, satStateSet, SatState, StateSat, PathSat, Set.ext_iff] at *
  intros _ _ _ _
  constructor
  . rintro ⟨π, j, ⟨satJ, satK⟩⟩; exact ⟨π, j, ⟨(h₂ _).1 satJ, fun k => (h₁ _).1 (satK k)⟩⟩
  . rintro ⟨π, j, ⟨satJ, satK⟩⟩; exact ⟨π, j, ⟨(h₂ _).2 satJ, fun k => (h₁ _).2 (satK k)⟩⟩

@[simp]
theorem all_next_congr (h : Equiv Φ Φ') : Equiv (⬝∀⬝◯Φ) (⬝∀⬝◯Φ') := by
  simp [Equiv, satStateSet, SatState, StateSat, PathSat, Set.ext_iff] at *
  intros _ _ _ _
  constructor
  . rintro sat π; rw [← h]; exact sat π
  . rintro sat π; rw [h]  ; exact sat π
  done

@[simp]
theorem all_untl_congr (h₁ : Equiv Φ Φ') (h₂ : Equiv Ψ Ψ') : Equiv (⬝∀(Φ ⬝U Ψ)) (⬝∀(Φ' ⬝U Ψ')) := by
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
  simp [Equiv, satStateSet, SatState, StateSat, PathSat, Set.ext_iff] at *
  intros _ _ _ _
  constructor
  . rintro sat
    constructor
    . rintro π j negSatΦ negSatΨ
      obtain ⟨a, ⟨satΨ, satΦ⟩⟩ := sat π
      sorry
    . rintro π
      obtain ⟨_, ⟨_, _⟩⟩ := sat π
      constructor <;> assumption
  . rintro ⟨negSat, satΨ⟩ π
    obtain ⟨j, satΨ'⟩ := satΨ π
    exact ⟨j, ⟨satΨ', fun k => sorry⟩⟩

theorem all_untl_expansion : Equiv (⬝∀(Φ ⬝U Ψ)) (Ψ ⬝∨ (Φ ⬝∧ (⬝∀⬝◯⬝∀(Φ ⬝U Ψ)))) := by
  -- simp [Equiv, satStateSet, SatState, StateSat, PathSat, StateFormula.disj]
  -- intro s a ts
  -- ext x
  -- done
  sorry
end Equiv

end CTL
