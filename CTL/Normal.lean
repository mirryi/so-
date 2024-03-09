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

theorem enf_exists : (Φ : @StateFormula p) → { Φ' : @ENF p // Equiv Φ Φ'.1 }
  | ⬝⊤ => ⟨⟨⬝⊤, by simp⟩, by simp⟩
  | ⬝a => ⟨⟨⬝a, by simp⟩, by simp⟩
  | Φ₁ ⬝∧ Φ₂ => 
    let ⟨⟨Φ₁, h₁⟩, eq₁⟩ := enf_exists Φ₁
    let ⟨⟨Φ₂, h2⟩, eq₂⟩ := enf_exists Φ₂
    ⟨⟨_, by simp; constructor <;> assumption⟩, Equiv.conj_congr eq₁ eq₂⟩
  | ⬝¬Φ => 
    let ⟨⟨Φ, h⟩, eq⟩ := enf_exists Φ
    ⟨⟨_, by simp; exact neg_isENF _ h⟩, Equiv.neg_congr eq⟩
  | ⬝∃⬝◯Φ =>
    let ⟨⟨Φ, h⟩, eq⟩ := enf_exists Φ
    ⟨⟨_, by simp; assumption⟩, Equiv.exist_next_congr eq⟩
  | ⬝∃(Φ ⬝U Ψ) => 
    let ⟨⟨Φ, h₁⟩, eq₁⟩ := enf_exists Φ
    let ⟨⟨Ψ, h₂⟩, eq₂⟩ := enf_exists Ψ
    ⟨⟨_, by simp; constructor <;> assumption⟩, Equiv.exist_untl_congr eq₁ eq₂⟩
  | ⬝∀⬝◯Φ =>
    let ⟨⟨Φ, h⟩, eq⟩ := enf_exists Φ
    ⟨⟨_, by simp; exact neg_isENF _ h⟩, Trans.trans (Equiv.all_next_congr eq) Equiv.all_next_duality⟩
  | ⬝∀(Φ ⬝U Ψ) =>
    let ⟨⟨Φ, h₁⟩, eq₁⟩ := enf_exists Φ
    let ⟨⟨Ψ, h₂⟩, eq₂⟩ := enf_exists Ψ
    ⟨⟨_, by simp; exact ⟨⟨neg_isENF _ h₂, neg_isENF _ h₁, neg_isENF _ h₂⟩,
                         by simp [isENF, StateFormula.potentialAll, StateFormula.inevitable]; exact neg_isENF _ h₂⟩
    ⟩, Trans.trans (Equiv.all_untl_congr eq₁ eq₂) Equiv.all_untl_duality⟩
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

end StateFormula
end CTL
