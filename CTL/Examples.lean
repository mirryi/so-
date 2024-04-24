import TS.Examples
import CTL.Basic
import CTL.Satisfaction

namespace CTL.Examples
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

  #check ⬝∀□(⬝¬⬝crit₁ ⬝∨ ⬝¬⬝crit₂)
  #check (⬝∀□⬝∀◇⬝crit₁) ⬝∧ (⬝∀□⬝∀◇⬝crit₂)
  #check ⬝∀□(⬝yellow ⬝∨ (⬝∀⬝◯⬝¬⬝red))
  #check ⬝∀□⬝∀◇⬝green
end

section
  open TS.Examples.CokeMachine

  -- #eval CTL.Sat coke_machine ⬝⊤
end

end CTL.Examples
