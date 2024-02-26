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

  def state := {s : String // s ∈ ({"Pay", "Select", "Soda", "Beer"} : Set String)}
  def action := {s : String // s ∈ ({"InsertCoin", "GetSoda", "GetBeer", "Internal"} : Set String)}
  def p := {s : String // s ∈ ({"Paid", "Drink"} : Set String)}
  def coke_machine_string : @TS state action p :=
    {
      initial := {⟨"Pay", by simp⟩}
      trans :=
        fun
          | (⟨"Pay", _ ⟩, ⟨"InsertCoin", _⟩) => {⟨"Select", by simp⟩}
          | (⟨"Select", _ ⟩, ⟨"Internal", _⟩) => {⟨"Soda", by simp⟩, ⟨"Beer", by simp⟩}
          | (⟨"Soda", _⟩, ⟨"GetSoda", _⟩) => {⟨"Pay", by simp⟩}
          | (⟨"Beer", _ ⟩, ⟨"GetBeer", _⟩) => {⟨"Pay", by simp⟩}
          | _ => ∅
      label :=
        fun
          | ⟨"Pay", _⟩ => ∅
          | ⟨"Select", _⟩ => {⟨"Paid", by simp⟩}
          | ⟨"Soda", _⟩ | ⟨"Beer", _⟩ => {⟨"Paid", by simp⟩, ⟨"Drink", by simp⟩}
          | ⟨_, _⟩ => ∅
    }
end
