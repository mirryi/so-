import TS.Basic
import TS.PathFragment
import CTL.Satisfaction
import CTL.Equivalence

namespace CTL
open TS
variable {p : Type}

mutual
  inductive StateFormula where
    | top   : StateFormula
    | prop  : p            → StateFormula
    | conj  : StateFormula → StateFormula → StateFormula
    | neg   : StateFormula → StateFormula
    | exist : PathFormula  → StateFormula
    | all   : PathFormula  → StateFormula

  inductive PathFormula where
    | next : StateFormula → PathFormula
    | untl : StateFormula → StateFormula → PathFormula
end

namespace StateFormula
  open PathFormula

  variable (Φ Φ₁ Φ₂ : @StateFormula p)

  @[simp]
  def bot  : @StateFormula p := neg top
  @[simp]
  def disj := neg (conj (neg Φ₁) (neg Φ₂)) -- ⬝¬(⬝¬Φ₁ ⬝∧ ⬝¬Φ₂)
  @[simp]
  def impl := disj (neg Φ₁) Φ₂  -- ⬝¬Φ₁ ⬝∨ Φ₂
  @[simp]
  def iff  := conj (impl Φ₁ Φ₂) (impl Φ₂ Φ₁)  -- (Φ₁ ⬝→ Φ₂) ⬝∧ (Φ₂ ⬝→ Φ₁)
  @[simp]
  def xor  := disj (conj Φ₁ (neg Φ₂)) (conj Φ₂ (neg Φ₁)) -- (Φ₁ ⬝∧ ⬝¬Φ₂) ⬝∨ (Φ₂ ⬝∧ ⬝¬Φ₁)

  @[simp]
  def potential    := exist (untl top Φ)
  @[simp]
  def inevitable   := all (untl top Φ)
  @[simp]
  def potentialAll := neg (inevitable (neg Φ))
  @[simp]
  def invariant    := neg (potential (neg Φ))

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
  prefix:50 "⬝∃♢"  => StateFormula.potential -- \exists\diamondsuit
  prefix:50 "⬝∀♢"  => StateFormula.inevitable -- \forall\diamondsuit
  prefix:50 "⬝∃■"  => StateFormula.potentialAll -- \exists\sqb
  prefix:50 "⬝∀■"  => StateFormula.invariant -- \forall\sqb
  prefix:50 "⬝◯"   => PathFormula.next
  infixr:50 " ⬝U " => PathFormula.untl
end Syntax

section Satisfaction
variable {inst : Fintype s}
mutual
  -- s ⊨ Φ
  @[simp]
  def StateSat (ts : TS s a p) (st : s) :=
    fun
      | StateFormula.top => True
      | ⬝a               => a ∈ ts.label st
      | ⬝¬Φ              => ¬(StateSat ts st Φ)
      | Φ₁ ⬝∧ Φ₂         => (StateSat ts st Φ₁) ∧ (StateSat ts st Φ₂)
      | ⬝∃ φ             => ∃ π : TS.PathFragment.From ts st, PathSat ts π.1.2 φ
      | ⬝∀ φ             => ∀ π : TS.PathFragment.From ts st, PathSat ts π.1.2 φ

  -- π ⊨ φ
  @[simp]
  def PathSat (ts : TS s a p) (π : ts.PathFragment n) :=
    fun
      | ⬝◯ Φ   => StateSat ts (π.second) Φ
      | Φ ⬝U Ψ => ∃ j : EFin (Order.succ n), (StateSat ts (π.get j) Ψ) ∧ ∀ k : EFin j.val, StateSat ts (π.get (EFin.castLT j.lt k)) Φ
end

instance : StateSatisfiable p (@StateFormula p) where
  StateSat := StateSat

@[simp]
theorem StateSat_potentialAll {st : s} : StateSat ts st (⬝∃■Φ) ↔ ∃π : TS.PathFragment.From ts st, ∀j, StateSat ts (π.1.2.get j) Φ := by
  simp

@[simp]
theorem StateStat_invariant : StateSat ts st (⬝∀■Φ) ↔ ∀π : TS.PathFragment.From ts st, ∀j, StateSat ts (π.1.2.get j) Φ := by
  simp
end Satisfaction

section Equiv
variable {Φ Φ' Φ₁ Φ₁' Φ₂ Φ₂' Ψ Ψ' : @StateFormula p}

@[simp]
theorem conj_congr (h₁ : Equiv (p := p) Φ₁ Φ₁') (h₂ : Equiv (p := p) Φ₂ Φ₂') : Equiv (p := p) (Φ₁ ⬝∧ Φ₂) (Φ₁' ⬝∧ Φ₂') := by
  simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, Set.ext_iff] at *
  intros _ _ _ _ _
  constructor
  . rintro ⟨sat₁, sat₂⟩; constructor; exact (h₁ _).1 sat₁; exact (h₂ _).1 sat₂
  . rintro ⟨sat₁, sat₂⟩; constructor; exact (h₁ _).2 sat₁; exact (h₂ _).2 sat₂

@[simp]
theorem neg_congr (h : Equiv (p := p) Φ Φ') : Equiv (p := p) (⬝¬Φ) (⬝¬Φ') := by
  simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, Set.ext_iff] at *
  intros _ _ _ _ _
  constructor
  . rintro negSat sat; exact negSat ((h _).2 sat)
  . rintro negSat sat; exact negSat ((h _).1 sat)

@[simp]
theorem exist_next_congr (h : Equiv (p := p) Φ Φ') : Equiv (p := p) (⬝∃⬝◯Φ) (⬝∃⬝◯Φ') := by
  simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, Set.ext_iff] at *
  intros _ _ _ _ _
  constructor
  . rintro ⟨π, sat⟩; exact ⟨π, (h _).1 sat⟩
  . rintro ⟨π, sat⟩; exact ⟨π, (h _).2 sat⟩

@[simp]
theorem exist_untl_congr (h₁ : Equiv (p := p) Φ Φ') (h₂ : Equiv (p := p) Ψ Ψ') : Equiv (p := p) (⬝∃(Φ ⬝U Ψ)) (⬝∃(Φ' ⬝U Ψ')) := by
  simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, Set.ext_iff] at *
  intros _ _ _ _ _
  constructor
  . rintro ⟨π, j, ⟨satJ, satK⟩⟩; exact ⟨π, j, ⟨(h₂ _).1 satJ, fun k => (h₁ _).1 (satK k)⟩⟩
  . rintro ⟨π, j, ⟨satJ, satK⟩⟩; exact ⟨π, j, ⟨(h₂ _).2 satJ, fun k => (h₁ _).2 (satK k)⟩⟩

@[simp]
theorem all_next_congr (h : Equiv (p := p) Φ Φ') : Equiv (p := p) (⬝∀⬝◯Φ) (⬝∀⬝◯Φ') := by
  simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, Set.ext_iff] at *
  intros _ _ _ _ _
  constructor
  . rintro sat π; rw [← h]; exact sat π
  . rintro sat π; rw [h]  ; exact sat π
  done

@[simp]
theorem all_untl_congr (h₁ : Equiv (p := p) Φ Φ') (h₂ : Equiv (p := p) Ψ Ψ') : Equiv (p := p) (⬝∀(Φ ⬝U Ψ)) (⬝∀(Φ' ⬝U Ψ')) := by
  simp [Equiv, setOfSatStates, SatState, StateSatisfiable.StateSat, Set.ext_iff] at *
  intros _ _ _ _ _
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
  intros _ _ _ _ _
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

end Equiv
end StateFormula
end CTL
