import TS.Basic
import CTL.Satisfaction

namespace CTL
variable [StateSatisfiable α] [StateSatisfiable β]
         (Φ : α p) (Ψ : β p)

-- Sat(Φ) = Sat(Ψ)
@[simp]
def Equiv :=
  ∀ {s} [Fintype s] {μ} [Model p s μ] {m : μ p s}, setOfSatStates m Φ = setOfSatStates m Ψ

-- TS ⊨ Φ ↔ TS ⊨ Ψ
@[simp]
def Equiv' :=
  ∀ {s} [Fintype s] {μ} [Model p s μ] {m : μ p s}, Sat m Φ ↔ Sat m Ψ

namespace Equiv
@[simp]
def toEquiv' : Equiv Φ Ψ → Equiv' Φ Ψ := by
  simp [setOfSatStates, Set.ext_iff]
  intro h _ _ _ _ _
  constructor
  . rintro sat st mem
    exact (h st).1 (sat st mem)
  . rintro sat st mem
    exact (h st).2 (sat st mem)

instance : IsRefl (α p) (Equiv) where
  refl := by simp

instance : IsSymm (α p) (Equiv) where
  symm := fun Φ Ψ => by simp; intros h _ _ _; exact Eq.symm h

instance : IsTrans (α p) (Equiv) where
  trans := fun _ _ _ h₁ h₂ => Trans.trans h₁ h₂

instance : IsPreorder (α p) (Equiv) where

instance : IsEquiv (α p) (Equiv) where

end Equiv
end CTL
