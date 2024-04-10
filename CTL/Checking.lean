import CTL.Basic
import CTL.Normal
import TS.Basic
import TS.Path

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

def computeSatENF (ts : @TS s a p) (Φ : @StateFormula.ENF p) : Set s :=
  match Φ with
  | ENF.top => Set.univ
  | ENF.prop a => { st : s | a ∈ ts.label st }
  | ENF.conj Φ₁ Φ₂ => (computeSatENF ts Φ₁) ∩ (computeSatENF ts Φ₂)
  | ENF.neg Φ => Set.univ \ (computeSatENF ts Φ)
  | ENF.existNext Φ => { st : s | ts.post st ∩ (computeSatENF ts Φ) ≠ ∅ }
  | ENF.existUntil Φ Ψ => _
  | ENF.potentialAll Φ => _

-- theorem computerSat_def : computeSat ts Φ = satStateSet ts Φ :=
  -- sorry

-- instance : (ts : @TS s a p) → (Φ : @StateFormula p) → Decidable (Sat ts Φ) :=
  -- fun ts Φ => _

end CTL
