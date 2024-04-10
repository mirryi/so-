import CTL.Basic
import TS.Basic
import TS.Path
import TS.EFin

namespace CTL
open TS

class StateSatisfiable (p α : Type) where
  StateSat : {s a : Type}
           → (ts : @TS s a p)
           → (st : s)
           → (Φ : α)
           → Prop

variable {p α β : Type}
         [αSat : StateSatisfiable p α]
         [βSat : StateSatisfiable p β]
         {Φ : α}
         {Ψ : β}

-- Sat(Φ)
def SatState {s a : Type} (ts : @TS s a p) (Φ : α) : Type :=
  { st : s // StateSatisfiable.StateSat ts st Φ }
def setOfSatStates {s a : Type} (ts : @TS s a p) (Φ : α) :=
  @Set.range s (SatState ts Φ) Subtype.val

-- TS ⊨ Φ
def Sat {s a : Type} (ts: @TS s a p) (Φ : α) :=
  ∀ st ∈ ts.initial, StateSatisfiable.StateSat ts st Φ

@[simp]
theorem Sat_iff_initial_subset {s a : Type} (ts : @TS s a p) (Φ : α)
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


namespace StateFormula
variable (Φ Φ₁ Φ₂ : @StateFormula p)
         (φ φ₁ φ₂ : @PathFormula p)

mutual
  -- s ⊨ Φ
  @[simp]
  def StateSat (ts : @TS s a p) (st : s) :=
    fun
      | StateFormula.top => True
      | ⬝a               => a ∈ ts.label st
      | ⬝¬Φ              => ¬(StateSat ts st Φ)
      | Φ₁ ⬝∧ Φ₂         => (StateSat ts st Φ₁) ∧ (StateSat ts st Φ₂)
      | ⬝∃ φ             => ∃ π : PathFragment.From ts st, PathSat ts π.1.2 φ
      | ⬝∀ φ             => ∀ π : PathFragment.From ts st, PathSat ts π.1.2 φ

  -- π ⊨ φ
  @[simp]
  def PathSat (ts : @TS s a p) (π : ts.PathFragment n) :=
    fun
      | ⬝◯ Φ   => StateSat ts (π.second) Φ
      | Φ ⬝U Ψ => ∃ j : EFin (Order.succ n), (StateSat ts (π.get j) Ψ) ∧ ∀ k : EFin j.val, StateSat ts (π.get (EFin.castLT j.lt k)) Φ
end

instance : StateSatisfiable p (@StateFormula p) where
  StateSat := StateSat

@[simp]
theorem StateSat_potentialAll {st : s} : StateSat ts st (⬝∃■Φ) ↔ ∃π : PathFragment.From ts st, ∀j, StateSat ts (π.1.2.get j) Φ := by
  simp

@[simp]
theorem StateStat_invariant : StateSat ts st (⬝∀■Φ) ↔ ∀π : PathFragment.From ts st, ∀j, StateSat ts (π.1.2.get j) Φ := by
  simp

end StateFormula
end CTL
