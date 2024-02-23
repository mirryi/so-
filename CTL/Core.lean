universe u

mutual
  inductive StateFormula (P : Type u) where
    | top   : StateFormula P
    | prop  : P              -> StateFormula P
    | conj  : StateFormula P -> StateFormula P -> StateFormula P
    | neg   : StateFormula P -> StateFormula P
    | exist : PathFormula P  -> StateFormula P
    | all   : PathFormula P  -> StateFormula P

  inductive PathFormula (P : Type u) where
    | next : StateFormula P -> PathFormula P
    | untl : StateFormulaP  -> StateFormula P -> PathFormula P
end

open StateFormula
open PathFormula

def StateFormula.bot                           : StateFormula P := neg top
def StateFormula.disj (Φ₁ Φ₂ : StateFormula P) : StateFormula P := neg (conj (neg Φ₁) (neg Φ₂)) -- ⬝¬(⬝¬Φ₁ ⬝∧ ⬝¬Φ₂)
def StateFormula.impl (Φ₁ Φ₂ : StateFormula P) : StateFormula P := disj (neg Φ₁) Φ₂  -- ⬝¬Φ₁ ⬝∨ Φ₂
def StateFormula.iff  (Φ₁ Φ₂ : StateFormula P) : StateFormula P := conj (impl Φ₁ Φ₂) (impl Φ₂ Φ₁)  -- (Φ₁ ⬝→ Φ₂) ⬝∧ (Φ₂ ⬝→ Φ₁)
def StateFormula.xor  (Φ₁ Φ₂ : StateFormula P) : StateFormula P := disj (conj Φ₁ (neg Φ₂)) (conj Φ₂ (neg Φ₁)) -- (Φ₁ ⬝∧ ⬝¬Φ₂) ⬝∨ (Φ₂ ⬝∧ ⬝¬Φ₁)

def StateFormula.potential    (Φ : StateFormula P) : StateFormula P := exist (untl true Φ)
def StateFormula.inevitable   (Φ : StateFormula P) : StateFormula P := all (untl true Φ)
def StateFormula.potentialAll (Φ : StateFormula P) : StateFormula P := neg (inevitable (neg Φ))
def StateFormula.invariantly  (Φ : StateFormula P) : StateFormula P := neg (potential (neg Φ))

namespace Syntax
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
  prefix:50 "⬝∃■"  => StateFormula.potential -- \exists\sqb
  prefix:50 "⬝∀■"  => StateFormula.inevitable -- \forall\sqb
  prefix:50 "⬝◯"   => PathFormula.next
  infixr:50 " ⬝U " => PathFormula.untl
end Syntax

namespace Examples
  open StateFormula

  -- Example 6.2. Legal CTL Formulae
  section
    variable (x : Nat)

    #check ⬝∃⬝◯⬝(x = 5)
    #check ⬝∀⬝◯⬝(x = 5)
    #check ⬝(x < 2) ⬝∨ ⬝(x = 1)
    #check ⬝∃⬝◯(⬝(x = 1) ⬝∧ (⬝∀⬝◯⬝(x ≥ 3)))
    #check ⬝∃⬝◯⬝∀(top ⬝U ⬝(x = 1))
  end

  -- Example 6.3. CTL Formulae
  section
    variable (α β γ : Type)
    variable (crit₁ crit₂ : α)
    variable (red yellow green : β)

    #check ⬝∀■(⬝¬⬝crit₁ ⬝∨ ⬝¬⬝crit₂)
    #check (⬝∀■⬝∀♢⬝crit₁) ⬝∧ (⬝∀■⬝∀♢⬝crit₂)
    #check ⬝∀■(⬝yellow ⬝∨ (⬝∀⬝◯⬝¬⬝red))
    #check ⬝∀■⬝∀♢⬝green
  end
end Examples
