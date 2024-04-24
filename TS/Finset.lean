import Mathlib.Data.Finset.Basic

open Std.ExtendedBinder Finset

syntax "[" extBinder " | " term "]" : term

open Lean Elab Term in
elab_rules : term
  | `([ $x:ident | $p ])      => do elabTerm (← `(filter (fun $x:ident ↦ $p) univ)) none
  | `([ $x:ident : $t | $p ]) => do elabTerm (← `(filter (fun $x:ident :$t ↦ $p) univ)) none
  | `([ $x:ident ∈ $s | $p ]) => do elabTerm (← `(filter (fun $x:ident ↦ $p) $s)) none
