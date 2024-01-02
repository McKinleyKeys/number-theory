
import Mathlib
import Playground.SetTheory
import Playground.NumberTheory.Basic

open Nat Finset BigOperators


/-
 - Lagrange's Theorem
 -/
 
structure Nat.Poly where
  data : Array ℕ

def Nat.Poly.degree (p : Nat.Poly) :=
  p.data.size - 1

def Nat.Poly.coeff (p : Nat.Poly) (k : ℕ) :=
  p.data.getD k 0

def Nat.Poly.eval (p : Nat.Poly) (x : ℕ) : ℕ :=
  ∑ k in range p.data.size, (p.coeff k) * x^k

theorem lagrange's_theorem {n p : ℕ} {f : Nat.Poly} (hn : n > 0) (hf : f.degree = n) (hp : p.Prime) (h : p ∤ f.coeff n) :
  card (filter (fun x => f.eval x ≡ 1 [MOD p]) (range p)) ≤ n
  := by
    sorry

theorem pow_cong_one_solutions {n p : ℕ} (hp : p.Prime) (hn : n ∣ p-1) :
  card (filter (fun x => x^n ≡ 1 [MOD p]) (range p)) = n
  := by
    sorry
