import TS.Basic
import CTL.Basic
import CTL.Satisfaction
import CTL.Equivalence

namespace CTL
variable {p : Type}

namespace StateFormula
@[simp]
def isENF : @StateFormula p → Prop
  | ⬝⊤ | ⬝_ => True
  | Φ₁ ⬝∧ Φ₂ => Φ₁.isENF ∧ Φ₂.isENF
  | ⬝¬(⬝∀(top ⬝U ⬝¬Φ)) => Φ.isENF
  | ⬝¬Φ => Φ.isENF
  | ⬝∃⬝◯Φ => Φ.isENF
  | ⬝∃(Φ ⬝U Ψ) => Φ.isENF ∧ Ψ.isENF
  | ⬝∀_ => False

def ENF := { Φ : @StateFormula p // Φ.isENF }

@[simp]
def enf : (Φ : @StateFormula p) → @StateFormula p
  | ⬝⊤ => ⬝⊤
  | ⬝a => ⬝a
  | Φ₁ ⬝∧ Φ₂ => (enf Φ₁) ⬝∧ (enf Φ₂)
  | ⬝¬Φ => ⬝¬(enf Φ)
  | ⬝∃⬝◯Φ => ⬝∃⬝◯(enf Φ)
  | ⬝∃(Φ ⬝U Ψ) => ⬝∃((enf Φ) ⬝U (enf Ψ))
  | ⬝∀⬝◯Φ => ⬝¬(⬝∃⬝◯⬝¬(enf Φ))
  | ⬝∀(Φ ⬝U Ψ) =>
    let Φ := enf Φ
    let Ψ := enf Ψ
    ⬝¬(⬝∃(⬝¬Ψ ⬝U (⬝¬Φ ⬝∧ ⬝¬Ψ))) ⬝∧ ⬝¬(⬝∃■⬝¬Ψ)

theorem enf_def : (Φ : @StateFormula p) → (enf Φ).isENF
  | ⬝⊤ => by simp
  | ⬝a => by simp
  | Φ₁ ⬝∧ Φ₂ => by simp; constructor <;> apply enf_def
  | ⬝¬Φ => by simp; exact neg_isENF _ (enf_def Φ)
  | ⬝∃⬝◯Φ => by simp; apply enf_def
  | ⬝∃(Φ ⬝U Ψ) => by simp; constructor <;> apply enf_def
  | ⬝∀⬝◯Φ => by simp; exact neg_isENF _ (enf_def Φ)
  | ⬝∀(Φ ⬝U Ψ) => by
      simp
      constructor
      . constructor
        . exact neg_isENF _ (enf_def Ψ)
        . constructor
          . exact neg_isENF _ (enf_def Φ)
          . exact neg_isENF _ (enf_def Ψ)
      . simp [isENF, StateFormula.potentialAll, StateFormula.inevitable]; exact neg_isENF _ (enf_def Ψ)
where
  neg_isENF (Φ : @StateFormula p) (h : Φ.isENF) : (⬝¬Φ).isENF := by
    unfold isENF
    cases Φ with
    | top => simp
    | prop => simp
    | conj => simp; unfold isENF at h; exact h
    | neg => simp; exact h
    | exist => simp; exact h
    | all => unfold isENF at h; apply False.elim; exact h

theorem enf_equiv : (Φ : @StateFormula p) → Equiv Φ (enf Φ)
  | ⬝⊤ => by simp
  | ⬝a => by simp
  | Φ₁ ⬝∧ Φ₂ => by simp; apply Equiv.conj_congr <;> apply enf_equiv
  | ⬝¬Φ => by simp; apply Equiv.neg_congr; apply enf_equiv
  | ⬝∃⬝◯Φ => by simp; apply Equiv.exist_next_congr; apply enf_equiv
  | ⬝∃(Φ ⬝U Ψ) => by simp; apply Equiv.exist_untl_congr <;> apply enf_equiv
  | ⬝∀⬝◯Φ => by simp; exact Trans.trans (Equiv.all_next_congr (enf_equiv Φ)) Equiv.all_next_duality
  | ⬝∀(Φ ⬝U Ψ) => by simp; exact Trans.trans (Equiv.all_untl_congr (enf_equiv Φ) (enf_equiv Ψ)) Equiv.all_untl_duality

end StateFormula
end CTL
