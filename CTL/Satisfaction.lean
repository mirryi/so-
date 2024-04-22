import TS.Basic

namespace CTL
class StateSatisfiable (α : (p : Type) → Type) where
  StateSat : [Fintype s] → [Model p s μ] → (m : μ p s)
           → (Φ : α p)
           → (st : s)
           → Prop

variable [Fintype s] [Model p s μ] (m : μ p s)
         [StateSatisfiable α] [StateSatisfiable β]
         (Φ : α p) (Ψ : β p)

-- Sat(Φ) : Type
@[simp]
def SatState :=
  { st : s // StateSatisfiable.StateSat m Φ st }
-- Sat(Φ) : Set s
def setOfSatStates :=
  @Set.range s (SatState m Φ) Subtype.val

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
      exact Set.mem_range_self (⟨st, sat st mem⟩ : SatState m Φ)
    . intro sub st mem
      specialize sub mem
      unfold setOfSatStates at sub
      rw [Set.mem_range] at sub
      obtain ⟨stSat, refl⟩ := sub
      rw [← refl]
      exact Subtype.property stSat
end CTL
