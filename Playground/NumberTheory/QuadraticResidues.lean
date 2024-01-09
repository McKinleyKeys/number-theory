
import Mathlib
import Playground.Logic
import Playground.NumberTheory.Basic
import Playground.NumberTheory.Order
import Playground.NumberTheory.PrimitiveRoots

open Nat


lemma two_sqrts {a p : ℕ} (hp : p.Prime) :
  ∀ x y : ℕ, x^2 ≡ a [MOD p] → y^2 ≡ a [MOD p] → x ≡ y [MOD p] ∨ x + y ≡ 0 [MOD p]
  := by
    rintro x y hx hy
    wlog h : x ≥ y generalizing x y
    · apply le_of_not_ge at h
      specialize this y x hy hx h
      rw [add_comm, ModEq.comm] at this
      exact this
    · have h_sq : x^2 ≥ y^2 := by
        rw [sq, sq]
        apply Nat.mul_le_mul h h
      have : (x - y) * (x + y) ≡ 0 [MOD p] := calc
        _ = (x + y) * (x - y)     := mul_comm _ _
        _ = x^2 - y^2             := (Nat.sq_sub_sq x y).symm
        _ ≡ 0 [MOD p]             := by
                                    rw [ModEq] at hx hy
                                    rw [
                                      ModEq.sub_cong_iff_add_cong h_sq,
                                      zero_add,
                                      ModEq,
                                      hx,
                                      hy,
                                    ]
      have : x - y ≡ 0 [MOD p] ∨ x + y ≡ 0 [MOD p] := cong_zero_of_mul_cong_zero hp this
      rw [ModEq.sub_cong_iff_add_cong h, zero_add] at this
      exact this

lemma sqrt_one {x p : ℕ} (hp : p.Prime) :
  x^2 ≡ 1 [MOD p] → x ≡ 1 [MOD p] ∨ x ≡ p - 1 [MOD p]
  := by
    intro h
    have one_sq : 1^2 ≡ 1 [MOD p] := by
      rw [one_pow]
    by_cases hx : x ≡ 1 [MOD p]
    · left
      exact hx
    · right
      by_cases hp' : p = 0
      · exfalso
        rw [hp'] at h hx
        apply ModEq.mod_zero_iff.mp at h
        apply ModEq.not_mod_zero_iff.mp at hx
        have : sqrt (x^2) = sqrt 1 := by rw [h]
        rw [sqrt_eq', Nat.sqrt_one] at this
        contradiction
      · apply one_le_iff_ne_zero.mpr at hp'
        have : _ := two_sqrts hp x 1 h one_sq
        apply (or_iff_right hx).mp at this
        apply ModEq.add_right_cancel' 1
        rw [← Nat.sub_add_comm hp', Nat.add_one_sub_one]
        calc
          x + 1 ≡ 0 [MOD p]     := this
          _ ≡ p [MOD p]         := ModEq.card.symm

lemma neg_one_sq_cong_one {m : ℕ} (hm : m > 0) :
  (m-1)^2 ≡ 1 [MOD m]
  := calc
    (m-1)^2
    _ = m^2 + 1 - 2*m       := sub_one_sq hm
    _ ≡ m^2 + 1 [MOD m]     := by
                              apply (ModEq.sub_mul_erase _).mpr rfl
                              apply two_mul_le_sq_add_one
    _ ≡ 1 [MOD m]           := (ModEq.add_left_pow_erase two_pos).mpr rfl

lemma neg_one_pow_even {n m : ℕ} (hm : m > 0) (hn : Even n) :
  (m-1)^n ≡ 1 [MOD m]
  := by
    rcases (even_iff_eq_two_mul).mp hn with ⟨k, hk⟩
    rw [hk, pow_mul]
    nth_rw 2 [← one_pow k]
    apply ModEq.pow _ (neg_one_sq_cong_one hm)

lemma neg_one_pow_odd {n m : ℕ} (hn : Odd n) :
  (m-1)^n ≡ m-1 [MOD m]
  := by
    by_cases hm : m = 0
    · rw [hm, Nat.zero_sub, zero_pow (pos_of_odd hn)]
    · apply zero_lt_of_ne_zero at hm
      rcases odd_iff_eq_even_add_one.mp hn with ⟨k, ⟨hk₁, hk₂⟩⟩
      rw [hk₂, pow_add, pow_one]
      nth_rw 3 [← one_mul (m-1)]
      apply ModEq.mul_right (m-1)
      apply neg_one_pow_even hm hk₁


/-
 - Definitions
 -/

def QuadraticResidue (a m : ℕ) :=
  ∃ b, b^2 ≡ a [MOD m]
@[simp, reducible]
def QuadraticNonresidue (a m : ℕ) :=
  ¬QuadraticResidue a m


/-
 - Decidability of QuadraticResidue
 -/

instance : Decidable (QuadraticResidue a m) := by
  rw [QuadraticResidue]
  by_cases hm : m = 0
  · by_cases ha : PerfectSquare a
    · apply Decidable.isTrue
      rcases ha with ⟨b, _, h⟩
      use b
      rw [h]
    · apply Decidable.isFalse
      rw [not_exists] at ha ⊢
      intro x
      rw [hm]
      apply ModEq.mod_zero_iff.not.mpr
      specialize ha x
      rw [not_and] at ha
      by_cases hx : x ≤ a
      · specialize ha hx
        exact ha
      · rw [not_le] at hx
        have : a < x^2 := calc
          _ < x         := hx
          _ ≤ x*x       := le_mul_self x
          _ = x^2       := (sq x).symm
        rw [← Ne]
        symm
        apply Nat.ne_of_lt this
  · by_cases h : ∃ b < m, b^2 ≡ a [MOD m]
    · apply Decidable.isTrue
      rcases h with ⟨b, _, hb⟩
      use b
    · apply Decidable.isFalse
      rw [not_exists] at h ⊢
      intro x
      specialize h (x % m)
      rw [not_and] at h
      have : x % m < m := mod_lt _ (pos_iff_ne_zero.mpr hm)
      specialize h this
      rw [ModEq, ← pow_mod] at h
      exact h


lemma qr_of_cong_zero {a m : ℕ} (ha : a ≡ 0 [MOD m]) :
  QuadraticResidue a m
  := by
    use 0
    rw [zero_pow two_pos]
    symm
    exact ha
lemma qr_of_not_coprime {a p : ℕ} (hp : p.Prime) (ha : ¬Coprime a p) :
  QuadraticResidue a p
  := by
    apply (not_coprime_iff_cong_zero hp).mp at ha
    apply qr_of_cong_zero ha
lemma ncong_zero_of_qnr {a m : ℕ} (ha : QuadraticNonresidue a m) :
  a ≢ 0 [MOD m]
  := by
    contrapose ha
    simp
    simp at ha
    apply qr_of_cong_zero ha
lemma coprime_of_qnr {a p : ℕ} (hp : p.Prime) (ha : QuadraticNonresidue a p) :
  Coprime a p
  := by
    apply (coprime_iff_ncong_zero hp).mpr
    apply ncong_zero_of_qnr ha


/-
 - Legendre Symbol
 -/

def legendre (a p : ℕ) : ℕ :=
  if Coprime a p then
    if QuadraticResidue a p then
      1
    else
      p - 1
  else
    0

lemma legendre_eq_one_of_coprime_of_qr {a p : ℕ} (ha₁ : Coprime a p) (ha₂ : QuadraticResidue a p) :
  legendre a p = 1
  := by
    rw [legendre, if_true' ha₁, if_true' ha₂]
lemma legendre_eq_neg_one_of_qnr {a p : ℕ} (hp : p.Prime) (ha : QuadraticNonresidue a p) :
  legendre a p = p - 1
  := by
    have : Coprime a p := coprime_of_qnr hp ha
    rw [legendre, if_true' this, if_false' ha]

theorem legendre_cong {a p : ℕ} (hp : p.Prime) (hp' : p > 2) :
  legendre a p ≡ a^((p-1)/2) [MOD p]
  := by
    have p_sub_one_div_two_pos : 0 < ((p-1)/2) := by
      have : 2 ≤ p - 1 := le_sub_one_of_lt hp'
      apply Nat.div_pos this zero_lt_two
    by_cases ha : QuadraticResidue a p
    · by_cases ha' : Coprime a p
      · rw [legendre, if_true' ha', if_true' ha]
        rcases ha with ⟨b, h⟩
        have hb : Coprime b p := by
          apply coprime_mod_eq h.symm at ha'
          apply (coprime_pow_iff two_pos).mp ha'
        calc
        1 ≡ b^(p-1) [MOD p]       := by symm; apply fermat's_little_theorem hp hb
        _ = (b^2)^((p-1)/2)       := by
                                    ring_nf
                                    congr
                                    rw [Nat.div_mul_cancel (Prime.two_dvd hp hp')]
        _ ≡ a^((p-1)/2) [MOD p]   := by rw [ModEq, pow_mod, pow_mod a, h]
      · rw [legendre, if_false' ha']
        apply (not_coprime_iff_cong_zero hp).mp at ha'
        apply ModEq.pow ((p-1)/2) at ha'
        rw [zero_pow p_sub_one_div_two_pos] at ha'
        symm
        exact ha'
    · rw [legendre, if_false' ha]
      /-
        a ≡ r^k [MOD p]
        if k is even, then a is a QR
        if k is odd:
          a^((p-1)/2)
          _ = (r^k)^((p-1)/2)
          _ = r^((p-1)/2)^k
          _ ≡ (-1)^k
          _ = -1
       -/
      have ha' : Coprime a p := coprime_of_qnr hp ha
      rw [if_true' ha']
      rcases (cong_primitive_root_pow hp ha') with ⟨r, _, ⟨hr, ⟨k, _, hrk⟩⟩⟩
      by_cases hk' : Even k
      · exfalso
        rcases (even_iff_eq_two_mul.mp hk') with ⟨j, hj⟩
        rw [hj, pow_mul'] at hrk
        have : QuadraticResidue a p := by
          use r^j
        contradiction
      · apply odd_iff_not_even.mpr at hk'
        symm
        have : (r^((p-1)/2))^2 ≡ 1 [MOD p] := by
          ring_nf
          rw [Nat.div_mul_cancel (Prime.two_dvd hp hp')]
          apply fermat's_little_theorem hp (Prime.coprime_of_primitive_root hp hr)
        have r_pow : r^((p-1)/2) ≡ p-1 [MOD p] := by
          apply _root_.sqrt_one hp at this
          rcases this with one | neg_one
          · exfalso
            have ne_one : r^((p-1)/2) ≢ 1 [MOD p] := by
              apply primitive_root_min hr
              · linarith
              · apply Nat.div_lt_self _ one_lt_two
                simp
                linarith [hp']
            contradiction
          · exact neg_one
        calc
          a^((p-1)/2)
          _ ≡ (r^k)^((p-1)/2) [MOD p]     := by symm; apply ModEq.pow _ hrk
          _ = (r^((p-1)/2))^k             := by ring
          _ ≡ (p - 1)^k [MOD p]           := ModEq.pow _ r_pow
          _ ≡ p - 1 [MOD p]               := neg_one_pow_odd hk'


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
