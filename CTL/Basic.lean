variable {p : Type}

namespace CTL
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

  def bot  : @StateFormula p := neg top
  def disj := neg (conj (neg Φ₁) (neg Φ₂)) -- ⬝¬(⬝¬Φ₁ ⬝∧ ⬝¬Φ₂)
  def impl := disj (neg Φ₁) Φ₂  -- ⬝¬Φ₁ ⬝∨ Φ₂
  def iff  := conj (impl Φ₁ Φ₂) (impl Φ₂ Φ₁)  -- (Φ₁ ⬝→ Φ₂) ⬝∧ (Φ₂ ⬝→ Φ₁)
  def xor  := disj (conj Φ₁ (neg Φ₂)) (conj Φ₂ (neg Φ₁)) -- (Φ₁ ⬝∧ ⬝¬Φ₂) ⬝∨ (Φ₂ ⬝∧ ⬝¬Φ₁)

  def potential    := exist (untl top Φ)
  def inevitable   := all (untl top Φ)
  def potentialAll := neg (inevitable (neg Φ))
  def invariant    := neg (potential (neg Φ))
end StateFormula

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
end CTL
