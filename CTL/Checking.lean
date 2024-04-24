import TS.Basic
import TS.PathFragment
import CTL.Basic
import CTL.Normal

namespace CTL
open StateFormula

-- theorem top_satStateSet_def : setOfSatStates ts ⬝⊤ = Set.univ := by
  -- simp [Set.ext_iff, setOfSatStates, SatState, StateSat]

-- theorem prop_satStateSet_def : (setOfSatStates ts (⬝a) : Set s) = { st : s | a ∈ ts.label st } := by
  -- simp [Set.ext_iff, setOfSatStates, SatState, StateSat]

-- theorem conj_satStateSet_def : setOfSatStates ts (Φ₁.1 ⬝∧ Φ₂.1setOfSatStateseSet ts ΦsetOfSatStatesateSet ts Φ₂.1 := by
  -- simp [Set.ext_iff, setOfSatStates, SatState, StateSat]

-- theorem neg_satStateSet_def : setOfSatStates ts (⬝¬Φ.1) = Set.univ setOfSatStateset ts Φ.1 := by
  -- simp [Set.ext_iff, setOfSatStates, SatState, StateSat]

-- theorem exist_next_satStatsetOfSatStates(satStateSet ts (⬝∃⬝◯Φ.setOfSatStates = { st : s | ts.post st ∩ (satStateSet ts Φ.1) ≠ ∅ } := by
  -- simp [Set.ext_iff, satStateSet, SatState, StateSat]
  -- intros st
  -- constructor
  -- . rintro ⟨⟨⟨_, π⟩, ⟨stIsHead, _⟩⟩, sat⟩
    -- simp [PathSat] at satsetOfSatStates
    -- rw [← stIsHead]
    -- exact ⟨π.second, ⟨π.second_mem_post_first, sat⟩⟩
  -- . rintro ⟨st', ⟨memPost, sat⟩⟩
    -- simp [PathSat]
    -- exact ⟨_ , _⟩

variable [Fintype s] [DecidableEq s] [Model p s μ] (m : μ p s)

example (t : Type) [Fintype t] (s : Set t) [DecidablePred (· ∈ s)]
: ∃ f : Finset t, ↑f = s := by
  exact ⟨s.toFinset, s.coe_toFinset⟩

def sat (Φ : StateFormula p) : Set s :=
  satENF (ENF.ofFormula Φ)
where
  satENF := fun
    | ENF.top => Set.univ
    | ENF.prop a => { st : s | a ∈ Model.label m st }
    | ENF.conj Φ₁ Φ₂ => (satENF Φ₁) ∩ (satENF Φ₂)
    | ENF.neg Φ => Set.univ \ (satENF Φ)
    | ENF.existNext Φ => { st : s | Model.post m st ∩ (satENF Φ) ≠ ∅ }
    | ENF.existUntil Φ Ψ => sorry
    | ENF.existAlways Φ => sorry

  satENFExistAlways (T : Finset s) :=
    let T' := { st ∈ T | Model.post m st ∩ T = ∅ }
    let _ : DecidablePred (· ∈ T') := fun st => by
      simp [T']
      exact And.decidable (dp := Finset.decidableMem _ _) (dq := decEq _ _)
    let T' := setFintype T'
    T'
    -- if T'.Nonempty then T
    -- else T

-- theorem computerSat_def : computeSat ts Φ = satStateSet ts Φ :=
  -- sorry

-- instance : (ts : @TS s a p) → (Φ : @StateFormula p) → Decidable (Sat ts Φ) :=
  -- fun ts Φ => _

end CTL
