import TS.Basic
import CTL.Basic
import CTL.Satisfaction
import CTL.Equivalence

namespace CTL
namespace StateFormula
inductive ENF (p : Type) where
  | top         : ENF p
  | prop        : p → ENF p
  | conj        : ENF p → ENF p → ENF p
  | neg         : ENF p → ENF p
  | existNext   : ENF p → ENF p
  | existUntil  : ENF p → ENF p → ENF p
  | existAlways : ENF p → ENF p

namespace ENF
@[simp]
def ofFormula : (Φ : StateFormula p) → ENF p
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
    ENF.conj (ENF.neg (ENF.existUntil (ENF.neg Ψ) (ENF.conj (ENF.neg Φ) (ENF.neg Ψ)))) (ENF.neg (existAlways (ENF.neg Ψ)))

@[simp]
def toFormula : (Φ : ENF p) → StateFormula p
  | top => ⬝⊤
  | prop a => ⬝a
  | conj Φ₁ Φ₂ => (Φ₁.toFormula) ⬝∧ (Φ₂.toFormula)
  | neg Φ => ⬝¬(Φ.toFormula)
  | existNext Φ => ⬝∃⬝◯(Φ.toFormula)
  | existUntil Φ Ψ => ⬝∃(Φ.toFormula ⬝U Ψ.toFormula)
  | existAlways Φ => ⬝∃□(Φ.toFormula)

section Satisfaction
variable [Fintype s] [Model p s μ] (m : μ p s)

@[simp]
def StateSat (Φ : ENF p) (st : s) := StateFormula.StateSat m Φ.toFormula st

instance : StateSatisfiable ENF where
  StateSat m Φ st := StateSat m Φ st
end Satisfaction

section Equivalence
theorem ofFormula_equiv {Φ : StateFormula p} : Equiv (p := p) Φ (ofFormula Φ) :=
  match Φ with
  | ⬝⊤ => by simp [setOfSatStates, StateSatisfiable.StateSat]
  | ⬝a => by simp [setOfSatStates, StateSatisfiable.StateSat]
  | Φ₁ ⬝∧ Φ₂ => by simp; apply StateFormula.conj_congr <;> apply ofFormula_equiv
  | ⬝¬Φ => by simp; apply StateFormula.neg_congr; apply ofFormula_equiv
  | ⬝∃⬝◯Φ => by simp; apply StateFormula.exist_next_congr; apply ofFormula_equiv
  | ⬝∃(Φ ⬝U Ψ) => by simp; apply StateFormula.exist_untl_congr <;> apply ofFormula_equiv
  | ⬝∀⬝◯Φ => by simp; exact Trans.trans (StateFormula.all_next_congr _ ofFormula_equiv) (StateFormula.all_next_duality _)
  | ⬝∀(Φ ⬝U Ψ) => by simp; exact Trans.trans (StateFormula.all_untl_congr _ ofFormula_equiv ofFormula_equiv) (StateFormula.all_untl_duality _)
end Equivalence

end ENF
end StateFormula
end CTL
