import TS.Basic

namespace CTL
open TS

class StateSatisfiable (p α : Type) where
  StateSat : {s a : Type}
           → {_ : Fintype s}
           → (ts : TS s a p)
           → (st : s)
           → (Φ : α)
           → Prop

variable {p α β : Type}
         [αSat : StateSatisfiable p α]
         [βSat : StateSatisfiable p β]
         {Φ : α}
         {Ψ : β}

-- Sat(Φ)
def SatState {s a : Type} {_ : Fintype s} (ts : TS s a p) (Φ : α) : Type :=
  { st : s // StateSatisfiable.StateSat ts st Φ }
def setOfSatStates {s a : Type} {_ : Fintype s} (ts : TS s a p) (Φ : α) :=
  @Set.range s (SatState ts Φ) Subtype.val

-- TS ⊨ Φ
def Sat {s a : Type} {_ : Fintype s} (ts: TS s a p) (Φ : α) :=
  ∀ st ∈ ts.initial, StateSatisfiable.StateSat ts st Φ

@[simp]
theorem Sat_iff_initial_subset {s a : Type} {_ : Fintype s} (ts : TS s a p) (Φ : α)
  : (Sat ts Φ) ↔ (ts.initial ⊆ setOfSatStates ts Φ) :=
  by
    apply Iff.intro
    . intro sat st mem
      exact Set.mem_range_self (⟨st, sat st mem⟩ : SatState ts Φ)
    . intro sub st mem
      specialize sub mem
      unfold setOfSatStates at sub
      rw [Set.mem_range] at sub
      obtain ⟨stSat, refl⟩ := sub
      rw [← refl]
      exact Subtype.property stSat
end CTL
