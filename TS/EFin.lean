import Mathlib.Data.ENat.Basic

inductive EFin : ℕ∞ → Type where
  | fin (i : ℕ) (lt : i < n) : EFin n
  | inf (i : ℕ) : EFin ⊤

namespace EFin
@[inline]
def val : EFin n → ℕ
  | .fin i _ => i
  | .inf i   => i

attribute [coe] EFin.val

@[inline]
def lt (i : EFin n) : i.val < n :=
  match i with
  | .fin _ lt => WithTop.coe_lt_coe.2 lt
  | .inf i    => WithTop.coe_lt_top i

@[inline]
def succ : EFin n → EFin (Order.succ n)
  | .fin i lt => fin i.succ (Nat.succ_lt_succ lt)
  | .inf i    => inf i.succ

@[inline]
def castInfty {n : ℕ} (i : EFin n) : EFin ⊤ :=
  match i with | .fin i _ => .inf i

@[inline]
def castLT {m : ℕ} {n : ℕ∞} (h : m < n) (i : EFin m) : EFin n :=
  match n with
  | ⊤      => i.castInfty
  | some _ => match i with | .fin i lt => fin i (Nat.lt_trans lt (WithTop.some_lt_some.1 h))

@[inline]
def castLT' {m n : ℕ} (i : EFin m) (h : i.val < n) : EFin n :=
  match i with | .fin i _ => (fin i h : EFin n)

@[inline]
def castSucc (i : EFin n) : EFin (Order.succ n) :=
  match i with
  | .fin i lt => fin i (Nat.lt_succ_of_lt lt)
  | .inf i    => inf i

instance : LT (EFin n) where
  lt i j := LT.lt i.val j.val

instance : LE (EFin n) where
  le i j := LE.le i.val j.val

end EFin
