
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Irrational
import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.Basic
open Algebra

variable {α : Type*} [LinearOrder α]

def ConvergesTo (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| ≤ ε

/-
  { a } converges to a
-/
theorem const_converges (a : ℝ) :
  ConvergesTo (fun (_ : ℕ) ↦ a) a := by
    intro ε ε_pos
    use 0
    intro n _
    rw [sub_self, abs_zero]
    apply le_of_lt
    exact ε_pos

/-
  { 1/n } converges to 0
-/
theorem reciprocal_converges :
  ConvergesTo (fun (n : ℝ) ↦ 1 / n) 0 := by
    intro ε ε_pos
    use (1/ε)
    intro n n_ge
    rw [sub_zero]
    dsimp
    have n_pos : 0 < n := by
      apply one_div_pos.mpr at ε_pos
      apply lt_of_lt_of_le ε_pos n_ge
    have one_div_n_le_ε : 1/n ≤ ε := by
      apply (one_div_le n_pos ε_pos).mpr n_ge
    have abs_le_abs : |1/n| ≤ |ε| := by
      have one_div_n_pos : 1/n ≥ 0 := by
        apply one_div_nonneg.mpr
        apply le_of_lt n_pos
      apply abs_le_abs_of_nonneg one_div_n_pos one_div_n_le_ε
    have abs_ε_eq_ε : |ε| = ε := by
      exact abs_of_pos ε_pos
    rw [abs_ε_eq_ε] at abs_le_abs
    exact abs_le_abs

open Nat

lemma succ_neg_one (n : ℕ) :
  succ n - 1 = n := by
    rw [succ_eq_add_one, Nat.add_sub_assoc]
    rw [Nat.sub_self, add_zero]
    exact le_rfl

theorem sum_self (n : ℕ) :
  (Finset.sum (Finset.range n) fun (k : ℕ) => k) = n*(n-1) / 2 := by
    induction' n with m hm
    · dsimp
      rw [zero_mul, Nat.zero_div]
    rw [
      succ_neg_one,
      succ_mul,
      Finset.sum_range_succ,
      hm,
      Nat.mul_sub_left_distrib,
      mul_one,
    ]
    have zero_lt_two : 0 < 2 := by
      sorry
    nth_rewrite 4 [← Nat.mul_div_cancel m zero_lt_two]
    sorry

def MRational (x : ℝ) :=
  ∃ a b : ℕ, b ≠ 0 ∧ Coprime a b ∧ x = a/b
def MIrrational (x : ℝ) :=
  ¬MRational x

lemma two_dvd_of_sq_eq_two_mul
  {a b : ℕ} (h : a^2 = 2*b^2) :
  2 ∣ a := by
    have two_dvd_right : (2 ∣ 2*b^2) := by
      apply dvd_mul_right
    have two_dvd_left : (2 ∣ a^2) := by
      rw [<- h] at two_dvd_right
      exact two_dvd_right
    apply Nat.Prime.dvd_of_dvd_pow prime_two two_dvd_left

theorem even_of_even_sq (n : ℕ) (h : 2 ∣ n^2) : 2 ∣ n := by
  rw [pow_two, prime_two.dvd_mul] at h
  sorry

theorem add_one_eq_add_one_of_eq (a b : ℕ) (h : a = b) : a + 1 = b + 1 := by
  apply Eq.subst h
  rfl

example (a b : ℕ) (p : ℕ -> Prop) (h₁ : a = b) (h₂ : p a) : p b :=
  h₁ ▸ h₂

theorem sqrt_two_irrational :
  MIrrational (Real.sqrt 2) := by
    intro sqrt_two_rat
    rcases sqrt_two_rat with ⟨a, b, b_ne_zero, a_co_b, h⟩
    have h_sq : (Real.sqrt 2)^2 = (a/b)^2 := by
      rw [h]
    have zero_lt_two : (0 < (2 : ℕ)) := by
      sorry
    have zero_le_two : (0 <= (2 : ℝ)) := by
      sorry
    have b_sq_ne_zero : ((b : ℝ)^2 ≠ 0) := by
      apply pow_ne_zero
      sorry
    rw [Real.sq_sqrt zero_le_two, div_pow] at h_sq
    have two_b_sq_eq_a_sq : (2*b^2 = a^2) := by
      
      rw [h_sq, div_mul, div_self b_sq_ne_zero, div_one]
    have two_dvd_a : (2 ∣ a) := by
      apply two_dvd_of_sq_eq_two_mul (symm two_b_sq_eq_a_sq)
    have exists_c : (∃ c, a = 2*c) := by
      apply exists_eq_mul_right_of_dvd at two_dvd_a
      exact two_dvd_a
    rcases exists_c with ⟨c, a_eq_two_c⟩
    rw [a_eq_two_c, mul_pow, sq 2, mul_assoc] at two_b_sq_eq_a_sq
    apply Nat.mul_left_cancel zero_lt_two at two_b_sq_eq_a_sq
    have two_dvd_b : (2 ∣ b) := by
      apply two_dvd_of_sq_eq_two_mul two_b_sq_eq_a_sq
    have two_dvd_gcd : (2 ∣ Nat.gcd a b) := by
      apply Nat.dvd_gcd two_dvd_a two_dvd_b
    have gcd_pos : (0 < Nat.gcd a b) := by
      sorry
    apply Nat.le_of_dvd gcd_pos at two_dvd_gcd
    apply coprime_iff_gcd_eq_one.mp at a_co_b
    rw [a_co_b] at two_dvd_gcd
    apply (two_le_iff 1).mp at two_dvd_gcd
    rcases two_dvd_gcd with ⟨one_ne_zero, one_ne_one⟩
    have one_eq_one : (1 = 1) := by
      rfl
    apply one_ne_one one_eq_one
