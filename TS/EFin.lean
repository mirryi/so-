import Mathlib.Data.ENat.Basic

inductive EFin : ℕ∞ → Type where
  | fin {n m : ℕ} : (lt : n < m) → EFin m
  | inf (n   : ℕ) : EFin ⊤

namespace EFin
end EFin
