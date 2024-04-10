import TS.Basic
import CTL.Basic
import CTL.Satisfaction

namespace CTL
variable {p α β : Type}
         [αSat : StateSatisfiable p α]
         [βSat : StateSatisfiable p β]
         (Φ : α)
         (Ψ : β)

-- Sat(Φ) = Sat(Ψ)
@[simp]
def Equiv :=
  ∀{s a : Type} , ∀{ts : @TS s a p}, setOfSatStates ts Φ = setOfSatStates ts Ψ

-- TS ⊨ Φ ↔ TS ⊨ Ψ
@[simp]
def Equiv' :=
  ∀{s a : Type} , ∀{ts : @TS s a p}, Sat ts Φ ↔ Sat ts Ψ

namespace Equiv
@[simp]
theorem equiv'_of_equiv : Equiv (p := p) Φ Ψ → Equiv' (p := p) Φ Ψ := by
  simp [Equiv, Equiv']
  intro h _ _ _
  rewrite [h]
  trivial

instance : IsRefl α (Equiv (p := p)) where
  refl := by simp

instance : IsSymm α (Equiv (p := p)) where
  symm := fun Φ Ψ => by simp; intros h _ _ _; exact Eq.symm h

instance : IsTrans α (Equiv (p := p)) where
  trans := fun _ _ _ h₁ h₂ => Trans.trans h₁ h₂

instance : IsPreorder α (Equiv (p := p)) where

instance : IsEquiv α (Equiv (p := p)) where

namespace StateFormula
variable {Φ Φ' Φ₁ Φ₁' Φ₂ Φ₂' Ψ Ψ' : @StateFormula p}

@[simp]
theorem conj_congr (h₁ : Equiv (p := p) Φ₁ Φ₁') (h₂ : Equiv (p := p) Φ₂ Φ₂') : Equiv (p := p) (Φ₁ ⬝∧ Φ₂) (Φ₁' ⬝∧ Φ₂') := by
  simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, Set.ext_iff] at *
  intros _ _ _ _
  constructor
  . rintro ⟨sat₁, sat₂⟩; constructor; exact (h₁ _).1 sat₁; exact (h₂ _).1 sat₂
  . rintro ⟨sat₁, sat₂⟩; constructor; exact (h₁ _).2 sat₁; exact (h₂ _).2 sat₂

@[simp]
theorem neg_congr (h : Equiv (p := p) Φ Φ') : Equiv (p := p) (⬝¬Φ) (⬝¬Φ') := by
  simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, Set.ext_iff] at *
  intros _ _ _ _
  constructor
  . rintro negSat sat; exact negSat ((h _).2 sat)
  . rintro negSat sat; exact negSat ((h _).1 sat)

@[simp]
theorem exist_next_congr (h : Equiv (p := p) Φ Φ') : Equiv (p := p) (⬝∃⬝◯Φ) (⬝∃⬝◯Φ') := by
  simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, Set.ext_iff] at *
  intros _ _ _ _
  constructor
  . rintro ⟨π, sat⟩; exact ⟨π, (h _).1 sat⟩
  . rintro ⟨π, sat⟩; exact ⟨π, (h _).2 sat⟩

@[simp]
theorem exist_untl_congr (h₁ : Equiv (p := p) Φ Φ') (h₂ : Equiv (p := p) Ψ Ψ') : Equiv (p := p) (⬝∃(Φ ⬝U Ψ)) (⬝∃(Φ' ⬝U Ψ')) := by
  simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, Set.ext_iff] at *
  intros _ _ _ _
  constructor
  . rintro ⟨π, j, ⟨satJ, satK⟩⟩; exact ⟨π, j, ⟨(h₂ _).1 satJ, fun k => (h₁ _).1 (satK k)⟩⟩
  . rintro ⟨π, j, ⟨satJ, satK⟩⟩; exact ⟨π, j, ⟨(h₂ _).2 satJ, fun k => (h₁ _).2 (satK k)⟩⟩

@[simp]
theorem all_next_congr (h : Equiv (p := p) Φ Φ') : Equiv (p := p) (⬝∀⬝◯Φ) (⬝∀⬝◯Φ') := by
  simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, Set.ext_iff] at *
  intros _ _ _ _
  constructor
  . rintro sat π; rw [← h]; exact sat π
  . rintro sat π; rw [h]  ; exact sat π
  done

@[simp]
theorem all_untl_congr (h₁ : Equiv (p := p) Φ Φ') (h₂ : Equiv (p := p) Ψ Ψ') : Equiv (p := p) (⬝∀(Φ ⬝U Ψ)) (⬝∀(Φ' ⬝U Ψ')) := by
  simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, Set.ext_iff] at *
  intros _ _ _ _
  constructor
  . rintro sat π; obtain ⟨j, ⟨satJ, satK⟩⟩ := sat π; exact ⟨j, ⟨(h₂ _).1 satJ, fun k => (h₁ _).1 (satK k)⟩⟩
  . rintro sat π; obtain ⟨j, ⟨satJ, satK⟩⟩ := sat π; exact ⟨j, ⟨(h₂ _).2 satJ, fun k => (h₁ _).2 (satK k)⟩⟩

theorem all_next_duality : Equiv (p := p) (⬝∀⬝◯Φ) (⬝¬(⬝∃⬝◯⬝¬Φ)) := by
  simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, Set.ext_iff] at *

theorem inevitable_duality : Equiv (p := p) (⬝∀♢Φ) (⬝¬(⬝∃■⬝¬Φ)) := by
  simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, StateFormula.inevitable, PathFormula.untl]

theorem exist_next_duality : Equiv (p := p) (⬝∃⬝◯Φ) (⬝¬(⬝∀⬝◯⬝¬Φ)) := by
  simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat]

theorem potential_duality : Equiv (p := p) (⬝∃♢Φ) (⬝¬(⬝∀■⬝¬Φ)) := by
  simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, StateFormula.potential, PathFormula.untl]

theorem all_untl_duality : Equiv (p := p) (⬝∀(Φ ⬝U Ψ)) (⬝¬(⬝∃(⬝¬Ψ ⬝U (⬝¬Φ ⬝∧ ⬝¬Ψ))) ⬝∧ ⬝¬(⬝∃■⬝¬Ψ)) := by
  simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, Set.ext_iff] at *
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

theorem all_untl_expansion : Equiv (p := p) (⬝∀(Φ ⬝U Ψ)) (Ψ ⬝∨ (Φ ⬝∧ (⬝∀⬝◯⬝∀(Φ ⬝U Ψ)))) := by
  -- simp [Equiv, satStateSet, SatState, StateSat, PathSat, StateFormula.disj]
  -- intro s a ts
  -- ext x
  -- done
  sorry
end StateFormula
end Equiv

end CTL
