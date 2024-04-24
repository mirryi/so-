import TS.Basic
import TS.PathFragment
import CTL.Satisfaction
import CTL.Equivalence

namespace CTL
mutual
  inductive StateFormula (p : Type) where
    | top   : StateFormula p
    | prop  : p              → StateFormula p
    | conj  : StateFormula p → StateFormula p → StateFormula p
    | neg   : StateFormula p → StateFormula p
    | exist : PathFormula  p → StateFormula p
    | all   : PathFormula  p → StateFormula p

  inductive PathFormula (p : Type) where
    | next : StateFormula p → PathFormula p
    | untl : StateFormula p → StateFormula p → PathFormula p
end

namespace StateFormula
  open PathFormula

  variable (Φ Φ₁ Φ₂ : StateFormula p)

  @[simp] def bot  : StateFormula p := neg top
  @[simp] def disj := neg (conj (neg Φ₁) (neg Φ₂)) -- ⬝¬(⬝¬Φ₁ ⬝∧ ⬝¬Φ₂)
  @[simp] def impl := disj (neg Φ₁) Φ₂  -- ⬝¬Φ₁ ⬝∨ Φ₂
  @[simp] def iff  := conj (impl Φ₁ Φ₂) (impl Φ₂ Φ₁)  -- (Φ₁ ⬝→ Φ₂) ⬝∧ (Φ₂ ⬝→ Φ₁)
  @[simp] def xor  := disj (conj Φ₁ (neg Φ₂)) (conj Φ₂ (neg Φ₁)) -- (Φ₁ ⬝∧ ⬝¬Φ₂) ⬝∨ (Φ₂ ⬝∧ ⬝¬Φ₁)

  @[simp] def potential       := exist (untl top Φ)
  @[simp] def inevitable      := all (untl top Φ)
  @[simp] def potentialAlways := neg (inevitable (neg Φ))
  @[simp] def invariant       := neg (potential (neg Φ))

namespace Syntax
  notation  "⬝⊤"   => StateFormula.top
  prefix:80 "⬝"    => StateFormula.prop
  prefix:75 "⬝¬"   => StateFormula.neg
  infixl:65 " ⬝∧ " => StateFormula.conj
  infixl:65 " ⬝∨ " => StateFormula.disj
  infixl:65 " ⬝⊕ " => StateFormula.xor
  infixr:60 " ⬝→ " => StateFormula.impl
  infixl:60 " ⬝↔ " => StateFormula.iff
  prefix:50 "⬝∃ "  => StateFormula.exist
  prefix:50 "⬝∀ "  => StateFormula.all
  prefix:50 "⬝∃◇"  => StateFormula.potential -- \exists\Diamond
  prefix:50 "⬝∀◇"  => StateFormula.inevitable -- \forall\Diamond
  prefix:50 "⬝∃□"  => StateFormula.potentialAlways -- \exists\sqw
  prefix:50 "⬝∀□"  => StateFormula.invariant -- \forall\sqw
  prefix:50 "⬝◯"   => PathFormula.next
  infixr:50 " ⬝U " => PathFormula.untl
end Syntax

section Satisfaction
variable [Fintype s] [Model p s μ] (m : μ p s)

mutual
  -- s ⊨ Φ
  @[simp]
  def StateSat (Φ : StateFormula p) (st : s) :=
    match Φ with
      | ⬝⊤       => True
      | ⬝a       => a ∈ Model.label m st
      | ⬝¬Φ      => ¬(StateSat Φ st)
      | Φ₁ ⬝∧ Φ₂ => (StateSat Φ₁ st) ∧ (StateSat Φ₂ st)
      | ⬝∃ φ     => ∃ π : Model.Paths m st, PathSat φ π.1
      | ⬝∀ φ     => ∀ π : Model.Paths m st, PathSat φ π.1

  -- π ⊨ φ
  @[simp]
  def PathSat (φ : PathFormula p) (π : FiniteOrInfinitePathFragment m) :=
    match φ with
      | ⬝◯ Φ   => StateSat Φ (PathFragment.second π)
      | Φ ⬝U Ψ => ∃ j : EFin (Order.succ (PathFragment.length π)), (StateSat Ψ (PathFragment.get π j)) ∧ ∀ k : EFin j.val, StateSat Φ (PathFragment.get π (EFin.castLT j.lt k))
end

-- @[simp]
-- theorem StateSat_potentialAlways : StateSat m (⬝∃□Φ) st ↔ ∃π : Model.Paths (β := FiniteOrInfinitePathFragment) m st, ∀j, StateSat m Φ (PathFragment.get π.1 j) := by
  -- simp

@[simp]
theorem StateStat_invariant   : StateSat m (⬝∀□Φ) st ↔ ∀π : Model.Paths (β := FiniteOrInfinitePathFragment) m st, ∀j, StateSat m Φ (PathFragment.get π.1 j) := by
  simp

instance : StateSatisfiable StateFormula where
  StateSat m Φ st := StateSat m Φ st
end Satisfaction

section Equiv
@[simp]
theorem conj_congr (h₁ : Equiv Φ₁ Φ₁') (h₂ : Equiv Φ₂ Φ₂') : Equiv (Φ₁ ⬝∧ Φ₂) (Φ₁' ⬝∧ Φ₂') := by
  simp only [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, StateSat,
             Set.ext_iff, Subtype.range_coe_subtype, Set.mem_setOf_eq] at *
  intros _ _ _ _ _ _
  constructor
  . rintro ⟨sat₁, sat₂⟩; constructor; exact (h₁ _).1 sat₁; exact (h₂ _).1 sat₂
  . rintro ⟨sat₁, sat₂⟩; constructor; exact (h₁ _).2 sat₁; exact (h₂ _).2 sat₂

@[simp]
theorem neg_congr (h : Equiv Φ Φ') : Equiv (⬝¬Φ) (⬝¬Φ') := by
  simp only [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, StateSat,
             Set.ext_iff, Subtype.range_coe_subtype, Set.mem_setOf_eq] at *
  intros _ _ _ _ _ _
  constructor
  . rintro negSat sat; exact negSat ((h _).2 sat)
  . rintro negSat sat; exact negSat ((h _).1 sat)

@[simp]
theorem exist_next_congr (h : Equiv Φ Φ') : Equiv (⬝∃⬝◯Φ) (⬝∃⬝◯Φ') := by
  simp only [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, StateSat, PathSat,
             Set.ext_iff, Subtype.range_coe_subtype, Set.mem_setOf_eq] at *
  intros _ _ _ _ _ _
  constructor
  . rintro ⟨π, sat⟩; exact ⟨π, (h _).1 sat⟩
  . rintro ⟨π, sat⟩; exact ⟨π, (h _).2 sat⟩

set_option maxHeartbeats 1000000 in
@[simp]
theorem exist_untl_congr (h₁ : Equiv Φ Φ') (h₂ : Equiv Ψ Ψ') : Equiv (⬝∃(Φ ⬝U Ψ)) (⬝∃(Φ' ⬝U Ψ')) := by
  simp only [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, StateSat, PathSat,
             Set.ext_iff, Subtype.range_coe_subtype, Set.mem_setOf_eq] at *
  intros _ _ _ _ _ _
  constructor
  . rintro ⟨π, j, satJ, satK⟩; exact ⟨π, j, (h₂ _).1 satJ, fun k => (h₁ _).1 (satK k)⟩
  . rintro ⟨π, j, satJ, satK⟩; exact ⟨π, j, (h₂ _).2 satJ, fun k => (h₁ _).2 (satK k)⟩

@[simp]
theorem all_next_congr (h : Equiv Φ Φ') : Equiv (⬝∀⬝◯Φ) (⬝∀⬝◯Φ') := by
  simp only [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, StateSat, PathSat,
             Set.ext_iff, Subtype.range_coe_subtype, Set.mem_setOf_eq] at *
  intros _ _ _ _ _ _
  constructor
  . rintro sat π; rw [←h]; exact sat π
  . rintro sat π; rw [h] ; exact sat π
  done

@[simp]
theorem all_untl_congr (h₁ : Equiv Φ Φ') (h₂ : Equiv Ψ Ψ') : Equiv (⬝∀(Φ ⬝U Ψ)) (⬝∀(Φ' ⬝U Ψ')) := by
  simp only [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, StateSat, PathSat,
             Set.ext_iff, Subtype.range_coe_subtype, Set.mem_setOf_eq] at *
  intros _ _ _ _ _ _
  constructor
  . rintro sat π; obtain ⟨j, ⟨satJ, satK⟩⟩ := sat π; exact ⟨j, ⟨(h₂ _).1 satJ, fun k => (h₁ _).1 (satK k)⟩⟩
  . rintro sat π; obtain ⟨j, ⟨satJ, satK⟩⟩ := sat π; exact ⟨j, ⟨(h₂ _).2 satJ, fun k => (h₁ _).2 (satK k)⟩⟩

theorem all_next_duality : Equiv (⬝∀⬝◯Φ) (⬝¬(⬝∃⬝◯⬝¬Φ)) := by
  simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, StateSat, PathSat, Set.ext_iff] at *

-- theorem inevitable_duality : Equiv (⬝∀♢Φ) (⬝¬(⬝∃□⬝¬Φ)) := by
  -- simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, StateSat, PathSat, StateFormula.inevitable, PathFormula.untl, Set.ext_iff] at *

-- theorem exist_next_duality : Equiv (⬝∃⬝◯Φ) (⬝¬(⬝∀⬝◯⬝¬Φ)) := by
  -- simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat]

-- theorem potential_duality : Equiv (⬝∃♢Φ) (⬝¬(⬝∀□⬝¬Φ)) := by
  -- simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, StateSat, PathSat, StateFormula.potential, PathFormula.untl, Set.ext_iff] at *

theorem all_untl_duality : Equiv (⬝∀(Φ ⬝U Ψ)) (⬝¬(⬝∃(⬝¬Ψ ⬝U (⬝¬Φ ⬝∧ ⬝¬Ψ))) ⬝∧ ⬝¬(⬝∃□⬝¬Ψ)) := by
  sorry
  -- simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, Set.ext_iff] at *
  -- intros _ _ _ _ _
  -- constructor
  -- . rintro sat
    -- constructor
    -- . rintro π j negSatΦ negSatΨ
      -- obtain ⟨a, ⟨satΨ, satΦ⟩⟩ := sat π
      -- sorry
    -- . rintro π
      -- obtain ⟨_, ⟨_, _⟩⟩ := sat π
      -- constructor <;> assumption
  -- . rintro ⟨negSat, satΨ⟩ π
    -- obtain ⟨j, satΨ'⟩ := satΨ π
    -- exact ⟨j, ⟨satΨ', fun k => sorry⟩⟩

theorem all_untl_expansion : Equiv (⬝∀(Φ ⬝U Ψ)) (Ψ ⬝∨ (Φ ⬝∧ (⬝∀⬝◯⬝∀(Φ ⬝U Ψ)))) := by
  sorry
  -- -- simp [Equiv, satStateSet, SatState, StateSat, PathSat, StateFormula.disj]
  -- -- intro s a ts
  -- -- ext x
  -- -- done

end Equiv
end StateFormula
end CTL
