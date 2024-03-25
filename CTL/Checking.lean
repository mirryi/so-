import CTL.Basic
import CTL.Normal
import TS.Basic
import TS.Path

namespace CTL
variable {Φ Φ₁ Φ₂ : @StateFormula.ENF p}

theorem top_satStateSet_def : satStateSet ts ⬝⊤ = Set.univ := by
  simp [Set.ext_iff, satStateSet, SatState, StateSat]

theorem prop_satStateSet_def : (satStateSet ts (⬝a) : Set s) = { st : s | a ∈ ts.label st } := by
  simp [Set.ext_iff, satStateSet, SatState, StateSat]

theorem conj_satStateSet_def : satStateSet ts (Φ₁.1 ⬝∧ Φ₂.1) = satStateSet ts Φ₁.1 ∩ satStateSet ts Φ₂.1 := by
  simp [Set.ext_iff, satStateSet, SatState, StateSat]

theorem neg_satStateSet_def : satStateSet ts (⬝¬Φ.1) = Set.univ \ satStateSet ts Φ.1 := by
  simp [Set.ext_iff, satStateSet, SatState, StateSat]

theorem exist_next_satStateSet_def : (satStateSet ts (⬝∃⬝◯Φ.1) : Set s) = { st : s | ts.post st ∩ (satStateSet ts Φ.1) ≠ ∅ } := by
  simp [Set.ext_iff, satStateSet, SatState, StateSat]
  intros st
  constructor
  . rintro ⟨⟨⟨_, π⟩, ⟨stIsHead, _⟩⟩, sat⟩
    simp [PathSat] at sat
    rw [← stIsHead]
    exact ⟨π.second, ⟨π.second_mem_post_first, sat⟩⟩
  . rintro ⟨st', ⟨memPost, sat⟩⟩
    simp [PathSat]

def computeSat (ts : @TS s a p) (Φ : @StateFormula p) : Set s :=
  sorry

theorem computerSat_def : computeSat ts Φ = satStateSet ts Φ :=
  sorry

instance : (ts : @TS s a p) → (Φ : @StateFormula p) → Decidable (Sat ts Φ) :=
  fun ts Φ => _

end CTL
