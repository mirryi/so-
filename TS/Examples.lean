import Mathlib.Tactic.DeriveFintype

import TS.Basic

namespace TS.Examples
-- Example 2.2 Beverage Vending Machine
namespace CokeMachine
  inductive State where
    | Pay | Select | Soda | Beer deriving Fintype
  inductive Action where
    | InsertCoin | GetSoda | GetBeer | Internal
  inductive Props where
    | Paid | Drink

  open State
  open Action
  open Props

  def coke_machine :=
    {
      initial := {Pay},
      trans :=
        fun
          | (Pay, InsertCoin) => {Select}
          | (Select, Internal) => {Soda, Beer}
          | (Soda, GetSoda) => {Pay}
          | (Beer, GetBeer) => {Pay}
          | _ => ∅
      label :=
        fun
          | Pay => ∅
          | Select => {Paid}
          | Soda | Beer => {Paid, Drink}
      : TS Action Props State
    }
end CokeMachine
end TS.Examples
