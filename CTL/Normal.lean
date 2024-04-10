import TS.Basic
import CTL.Basic
import CTL.Satisfaction
import CTL.Equivalence

namespace CTL
variable {p : Type}

namespace StateFormula
inductive ENF where
  | top          : ENF
  | prop         : p → ENF
  | conj         : ENF → ENF → ENF
  | neg          : ENF → ENF
  | existNext    : ENF → ENF
  | existUntil   : ENF → ENF → ENF
  | potentialAll : ENF -> ENF

namespace ENF
@[simp]
def ofFormula : (Φ : @StateFormula p) → @ENF p
  | ⬝⊤ => ENF.top
  | ⬝a => ENF.prop a
  | Φ ⬝∧ Ψ => ENF.conj (ofFormula Φ) (ofFormula Ψ)
  | ⬝¬Φ => ENF.neg (ofFormula Φ)
  | ⬝∃⬝◯Φ => ENF.existNext (ofFormula Φ)
  | ⬝∃(Φ ⬝U Ψ) => ENF.existUntil (ofFormula Φ) (ofFormula Ψ)
  | ⬝∀⬝◯Φ => ENF.neg (ENF.existNext (ENF.neg (ofFormula Φ)))
  | ⬝∀(Φ ⬝U Ψ) =>
    let Φ := ofFormula Φ
    let Ψ := ofFormula Ψ
    ENF.conj (ENF.neg (ENF.existUntil (ENF.neg Ψ) (ENF.conj (ENF.neg Φ) (ENF.neg Ψ)))) (ENF.neg (ENF.potentialAll (ENF.neg Ψ)))

@[simp]
def toFormula : (Φ : @ENF p) → @StateFormula p
  | top => ⬝⊤
  | prop a => ⬝a
  | conj Φ₁ Φ₂ => (Φ₁.toFormula) ⬝∧ (Φ₂.toFormula)
  | neg Φ => ⬝¬(Φ.toFormula)
  | existNext Φ => ⬝∃⬝◯(Φ.toFormula)
  | existUntil Φ Ψ => ⬝∃(Φ.toFormula ⬝U Ψ.toFormula)
  | potentialAll Φ => ⬝∃■(Φ.toFormula)

@[simp]
def StateSat (ts : @TS s a p) (st : s) (Φ : ENF) := StateFormula.StateSat ts st Φ.toFormula

instance : StateSatisfiable p (@ENF p) where
  StateSat := StateSat

theorem ofFormula_equiv {Φ : @StateFormula p} : Equiv (p := p) Φ (ofFormula Φ) :=
  match Φ with
  | ⬝⊤ => by simp [setOfSatStates, StateSatisfiable.StateSat]
  | ⬝a => by simp [setOfSatStates, StateSatisfiable.StateSat]
  | Φ₁ ⬝∧ Φ₂ => by simp; apply Equiv.StateFormula.conj_congr <;> apply ofFormula_equiv
  | ⬝¬Φ => by simp; apply Equiv.StateFormula.neg_congr; apply ofFormula_equiv
  | ⬝∃⬝◯Φ => by simp; apply Equiv.StateFormula.exist_next_congr; apply ofFormula_equiv
  | ⬝∃(Φ ⬝U Ψ) => by simp; apply Equiv.StateFormula.exist_untl_congr <;> apply ofFormula_equiv
  | ⬝∀⬝◯Φ => by simp; exact Trans.trans (Equiv.StateFormula.all_next_congr ofFormula_equiv) Equiv.StateFormula.all_next_duality
  | ⬝∀(Φ ⬝U Ψ) => by simp; exact Trans.trans (Equiv.StateFormula.all_untl_congr ofFormula_equiv ofFormula_equiv) Equiv.StateFormula.all_untl_duality

end ENF
end StateFormula
end CTL
