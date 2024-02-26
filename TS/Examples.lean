import TS.Basic

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
      : TS
    }
end
