import TS.Basic
import CTL.Satisfaction

namespace CTL
variable {p α β : Type}
         [αSat : StateSatisfiable p α]
         [βSat : StateSatisfiable p β]
         (Φ : α)
         (Ψ : β)

-- Sat(Φ) = Sat(Ψ)
@[simp]
def Equiv :=
  ∀{s a : Type} {_ : Fintype s}, ∀{ts : TS s a p}, setOfSatStates ts Φ = setOfSatStates ts Ψ

-- TS ⊨ Φ ↔ TS ⊨ Ψ
@[simp]
def Equiv' :=
  ∀{s a : Type} {_ : Fintype s}, ∀{ts : TS s a p}, Sat ts Φ ↔ Sat ts Ψ

namespace Equiv
@[simp]
theorem equiv'_of_equiv : Equiv (p := p) Φ Ψ → Equiv' (p := p) Φ Ψ := by
  simp [Equiv, Equiv']
  intro h _ _ _ _
  rewrite [h]
  trivial

instance : IsRefl α (Equiv (p := p)) where
  refl := by simp

instance : IsSymm α (Equiv (p := p)) where
  symm := fun Φ Ψ => by simp; intros h _ _ _; exact Eq.symm h

instance : IsTrans α (Equiv (p := p)) where
  trans := fun _ _ _ h₁ h₂ => Trans.trans h₁ h₂

instance : IsPreorder α (Equiv (p := p)) where

instance : IsEquiv α (Equiv (p := p)) where

end Equiv
end CTL
