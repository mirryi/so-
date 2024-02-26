import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Function

structure TS (s a p : Type) where
  states  : Set s
  initial : ∃ i : Set s, i ⊆ states 
  actions : Set a
  props   : Set p
  trans   : states × actions -> Option states
  label   : states -> Set props

namespace Examples
  -- Example 2.2 Beverage Vending Machine
  section
    inductive State where
      | Pay | Select | Soda | Beer
    inductive Action where
      | InsertCoin | GetSoda | GetBeer | Internal
    inductive P where
      | Paid | Drink
    open State
    open Action
    open P

    def coke_machine : TS State Action P :=
      {
        states := {Pay, Select, Soda, Beer},
        initial := ⟨
          {Pay},
          by
            intros s mem
            simp at mem
            exact Or.inl mem
        ⟩,
        actions := {InsertCoin, GetSoda, GetBeer, Internal},
        props := {Paid, Drink},
        trans :=
          fun (s, τ) => s
        -- label :=
          -- Set.restrict
            -- {Pay, Select, Soda, Beer}
            -- (fun | Pay => ∅ | Select => {Paid} | Soda => {Paid, Drink} | Beer => {Paid, Drink} )
        label :=
          Set.restrict
            {Pay, Select, Soda, Beer}
            (fun
             | Pay => ∅
             | Select => {Paid}
             | Soda | Beer => ({Paid, Drink} : Set P))
      }
  end
end Examples
