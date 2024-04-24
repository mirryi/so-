import Mathlib.Tactic.DeriveFintype

import TS.Basic

namespace CTL
class StateSatisfiable (α : (p : Type) → Type) where
  StateSat : [Fintype s] → [DecidableEq s] → [Model p s μ] → (m : μ p s)
           → (Φ : α p)
           → (st : s)
           → Prop

variable [Fintype s] [DecidableEq s] [Model p s μ] (m : μ p s)
         [StateSatisfiable α] (Φ : α p)

-- Sat(Φ) : Type
@[simp]
def SatState :=
  { st : s // StateSatisfiable.StateSat m Φ st }

variable [DecidablePred (StateSatisfiable.StateSat m Φ)]
instance : Fintype (SatState m Φ) where
  elems    := Finset.subtype _ (Fintype.elems)
  complete := fun ⟨st, _⟩ => by simp; apply Fintype.complete

-- Sat(Φ) : Finset s
def setOfSatStates :=
  @Finset.image (SatState m Φ) s _ Subtype.val Finset.univ

-- TS ⊨ Φ
@[simp]
def Sat :=
  ∀ st ∈ Model.initial m, StateSatisfiable.StateSat m Φ st

@[simp]
theorem Sat_iff_initial_subset
  : (Sat m Φ) ↔ (Model.initial m ⊆ setOfSatStates m Φ) :=
  by
    apply Iff.intro
    . intro sat st mem
      simp only [setOfSatStates]
      -- exact Set.mem_range_self (⟨st, sat st mem⟩ : SatState m Φ)
    . intro sub st mem
      specialize sub mem
      unfold setOfSatStates at sub
      -- rw [Set.mem_range] at sub
      -- obtain ⟨stSat, refl⟩ := sub
      -- rw [← refl]
      -- exact Subtype.property stSat
end CTL
