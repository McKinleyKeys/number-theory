
import Mathlib
import Playground.Logic

open Nat


/-
 - Definitions
 -/

def QuadraticResidue (a p : ℕ) :=
  ∃ b, b^2 ≡ a [MOD p]
def QuadraticNonresidue (a p : ℕ) :=
  ¬QuadraticResidue a p

instance : Decidable (QuadraticResidue a b) := by
  sorry


/-
 - Legendre Symbol
 -/

def legendre (a p : ℕ) : ℕ :=
  if QuadraticResidue a p then 1 else p - 1

lemma legendre_qnr_eq_p_sub_one {a p : ℕ} (h : QuadraticNonresidue a p) :
  legendre a p = p - 1
  := by
    rw [legendre, if_false' h]

theorem legendre_cong_pow_p_sub_one_div_two {a p : ℕ} (hp : p.Prime) :
  legendre a p ≡ a^((p-1)/2) [MOD p]
  := by
    sorry


lemma two_has_only_qrs (a : ℕ) :
  QuadraticResidue a 2
  := by
    have : a ≡ 0 [MOD 2] ∨ a ≡ 1 [MOD 2] := by
      rcases (even_or_odd a) with a_even | a_odd
      · left
        apply Even.two_dvd at a_even
        rw [ModEq, zero_mod]
        apply mod_eq_zero_of_dvd a_even
      · right
        rw [ModEq, one_mod]
        contrapose a_odd with a_even
        apply even_iff_not_odd.mp
        apply mod_two_ne_one.mp at a_even
        apply even_iff.mpr at a_even
        exact a_even
    cases this
    · use 0
      rw [zero_pow (by norm_num)]
      symm
      assumption
    . use 1
      rw [one_pow]
      symm
      assumption
