
import Mathlib
import Playground.Logic
import Playground.NumberTheory.Basic
import Playground.NumberTheory.Order
import Playground.NumberTheory.PrimitiveRoots
import Playground.BigOperators

open Nat Finset BigOperators


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
    · rw [hm, Nat.zero_sub, zero_pow (ne_zero_of_odd hn)]
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
    rw [zero_pow two_ne_zero]
    symm
    exact ha
lemma qr_of_not_coprime {a p : ℕ} (hp : p.Prime) (ha : ¬Coprime a p) :
  QuadraticResidue a p
  := by
    apply hp.not_coprime_iff_cong_zero.mp at ha
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
    apply hp.coprime_iff_ncong_zero.mpr
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

theorem euler's_criterion {a p : ℕ} (hp : p.Prime) (hp' : p > 2) :
  legendre a p ≡ a^((p-1)/2) [MOD p]
  := by
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
        apply hp.not_coprime_iff_cong_zero.mp at ha'
        apply ModEq.pow ((p-1)/2) at ha'
        rw [zero_pow (pos_iff_ne_zero.mp (sub_one_div_two_pos hp'))] at ha'
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
              · apply sub_one_div_two_pos hp'
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

namespace Nat.Prime.Half

def H (p : ℕ) := Icc 1 ((p-1)/2)

def abs' (x p : ℕ) :=
  if x ≤ (p-1)/2 then
    x
  else
    p - x

lemma half_lt {p : ℕ} (hp : p.Prime) :
  (p-1)/2 < p
  := calc
    _ ≤ p - 1           := Nat.div_le_self _ _
    _ < p               := sub_one_lt_self hp.pos

lemma one_le_half {p : ℕ} (hp' : p > 2) :
  1 ≤ (p-1)/2
  := by
    rw [one_le_div_iff zero_lt_two]
    apply le_sub_one_of_lt hp'

lemma sub_half {p : ℕ} (hp : p.Prime) (hp' : p > 2) :
  p - (p-1)/2 = (p-1)/2 + 1
  := by
    apply Nat.sub_eq_of_eq_add
    rw [
      add_right_comm,
      ← mul_two,
      div_two_mul_two_of_even,
      Nat.sub_add_cancel hp.one_le,
    ]
    apply hp.even_sub_one (Nat.ne_of_gt hp')

lemma mul_mod_inj {a p : ℕ} (hp : p.Prime) (hp' : p > 2) (ha : Coprime a p) :
  Set.InjOn (fun x => a*x % p) (H p)
  := by
      apply Set.InjOn.mono (s₂ := Ico 1 p) _ (hp.mul_mod_injOn_Ico ha)
      apply (Icc_subset_Ico_iff (one_le_half hp')).mpr
      exact And.intro le_rfl (half_lt hp)

lemma cong_ite_self_neg_abs'_self {x p : ℕ} (hx : x ≤ p) :
      x ≡ if x ≤ (p-1)/2 then x else (p-1) * (abs' x p) [MOD p]
      := by
        by_cases h : x ≤ (p-1)/2
        · rw [if_pos h]
        · dsimp only
          rw [if_neg h, abs', if_neg h]
          symm
          apply ModEq.neg_one_mul_neg hx

lemma abs'_eq_abs' {x y p : ℕ} (hp : p.Prime) (hxp : x ≤ p) (hyp : y ≤ p) (h : abs' x p = abs' y p) :
      x ≡ y [MOD p] ∨ x ≡ p - y [MOD p]
      := by
        rw [abs', abs'] at h
        by_cases hx : x ≤ (p-1)/2
        all_goals by_cases hy : y ≤ (p-1)/2
        · rw [if_pos hx, if_pos hy] at h
          left
          rw [h]
        · rw [if_pos hx, if_neg hy] at h
          right
          rw [h]
        · rw [if_neg hx, if_pos hy] at h
          right
          rw [← h, Nat.sub_sub_self hxp]
        · rw [if_neg hx, if_neg hy] at h
          left
          apply ModEq.cancel_left_of_coprime (c := p - 1) hp.coprime_sub_one_right
          calc
            _ ≡ p - x [MOD p]       := ModEq.neg_one_mul hxp
            _ = p - y               := h
            _ ≡ (p-1) * y [MOD p]   := (ModEq.neg_one_mul hyp).symm

end Nat.Prime.Half

open Nat.Prime.Half

-- Proof taken from Wikipedia: https://en.wikipedia.org/wiki/Gauss%27s_lemma_(number_theory)#Proof
theorem gauss's_lemma {a p : ℕ} (hp : p.Prime) (hp' : p > 2) (ha : Coprime a p) :
  let g := count (fun x => (a * x) % p > p/2) (Icc 1 ((p-1)/2))
  legendre a p ≡ (p-1)^g [MOD p]
  := by
    intro g
    -- aH = {1a, 2a, ..., (p-1)/2 * a}
    let H := H p
    let aH := image (fun x => (a * x) % p) H
    let z := ∏ x in aH, x
    have h_card_H : card H = (p-1)/2 := card_Icc_one _
    have h_card_aH : card aH = (p-1)/2 := by
      rw [← h_card_H]
      apply card_image_iff.mpr (mul_mod_inj hp hp' ha)
    have coprime_of_mem_H {x : ℕ} (h : x ∈ H) : Coprime x p := by
      change x ∈ Icc 1 ((p-1)/2) at h
      rw [mem_Icc] at h
      apply hp.coprime_of_mem_Ico
      rw [mem_Ico]
      apply And.intro h.1 (lt_of_le_of_lt h.2 (half_lt hp))
    have lt_of_mem_aH {x : ℕ} (h : x ∈ aH) : x < p := by
      rw [mem_image] at h
      rcases h with ⟨k, ⟨_, hkx⟩⟩
      rw [← hkx]
      apply mod_lt _ hp.pos
    have hz₁ : z ≡ a^((p-1)/2) * ∏ x in H, x [MOD p] := by
      rw [
        ← h_card_H,
        ← prod_const (s := H) a,
        ← prod_mul_distrib,
      ]
      unfold_let z
      unfold_let aH
      rw [prod_image (mul_mod_inj hp hp' ha), ModEq]
      nth_rw 2 [prod_nat_mod]
    have : z ≡ (p-1)^g * ∏ x in aH, abs' x p [MOD p] := by
      symm
      calc
        _ = (∏ x in aH, if x ≤ (p-1)/2 then 1 else p-1) * ∏ x in aH, abs' x p
                  := by
                    rw [
                      prod_ite,
                      prod_const_one,
                      one_mul,
                      prod_const,
                    ]
                    congr
                    unfold_let g
                    simp
                    rw [filter_image, card_image_iff.mpr]
                    · congr
                      funext x
                      rw [sub_one_div_two_eq_div_two (Prime.odd_of_two_lt hp hp')]
                    · apply Set.InjOn.mono _ (hp.mul_mod_injOn_Ico ha)
                      rw [coe_subset]
                      apply subset_trans (b := Icc 1 ((p-1)/2))
                      · apply filter_subset
                      · rw [Icc_subset_Ico_iff]
                        · constructor
                          · rfl
                          · rw [Nat.div_lt_iff_lt_mul two_pos]
                            apply lt_trans (b := p)
                            · apply sub_one_lt_of_le hp.pos le_rfl
                            · apply lt_mul_right hp.pos one_lt_two
                        · rw [← pos_iff_one_le]
                          apply sub_one_div_two_pos hp'
        _ = ∏ x in aH, if x ≤ (p-1)/2 then x else (p-1)*(p-x)
                  := by
                    rw [← prod_mul_distrib]
                    congr
                    funext x
                    rw [abs', apply_ite₂ HMul.hMul, one_mul]
        _ ≡ ∏ x in aH, x [MOD p]
                  := by
                    rw [ModEq, prod_nat_mod]
                    apply congrArg₂ _ _ rfl
                    apply prod_congr rfl
                    intro x hx
                    rw [mem_image] at hx
                    rcases hx with ⟨k, ⟨_, hkx⟩⟩
                    rw [
                      apply_ite (fun x => x % p),
                      ModEq.neg_one_mul_neg (by
                        rw [← hkx]
                        apply le_of_lt
                        apply mod_lt _ hp.pos
                      ),
                      ite_id,
                      ← hkx,
                      mod_mod,
                    ]
        _ = z     := rfl
    have h_subset : image (abs' · p) aH ⊆ H := by
      intro x hx
      rw [mem_image] at hx
      rcases hx with ⟨k, ⟨hk, hkx⟩⟩
      rw [mem_image] at hk
      rcases hk with ⟨j, ⟨hj, hjk⟩⟩
      change x ∈ Icc 1 ((p-1)/2)
      rw [abs'] at hkx
      by_cases hk' : k ≤ (p-1)/2
      · rw [if_pos hk'] at hkx
        rw [← hkx, mem_Icc]
        constructor
        · rw [← hjk, one_le_iff_ne_zero, Ne, ← (dvd_iff_mod_eq_zero _ _).not]
          apply hp.not_dvd_mul
          all_goals apply not_dvd_of_coprime hp.ne_one
          · exact ha
          · exact coprime_of_mem_H hj
        · exact hk'
      · rw [if_neg hk'] at hkx
        rw [← hkx, mem_Icc]
        constructor
        · apply le_sub_of_add_le
          rw [add_comm]
          change k < p
          rw [← hjk]
          apply mod_lt _ hp.pos
        · rw [not_le] at hk'
          apply Nat.lt_add_one_iff.mp
          calc
            _ < p - (p-1)/2       := Nat.sub_lt_sub_left (half_lt hp) hk'
            _ = (p-1)/2 + 1       := sub_half hp hp'
    have h_inj : Set.InjOn (abs' · p) aH := by
      intro x hx y hy hxy
      rw [mem_coe] at hx hy
      have hxp := lt_of_mem_aH hx
      have hyp := lt_of_mem_aH hy
      apply abs'_eq_abs' hp (le_of_lt hxp) (le_of_lt hyp) at hxy
      rcases hxy with eq | eq_neg
      · apply ModEq.eq_of_lt_of_lt eq hxp hyp
      · exfalso
        apply (ModEq.trans · (ModEq.neg_one_mul (le_of_lt hyp)).symm) at eq_neg
        rw [mem_image] at hx hy
        rcases hx with ⟨x', ⟨hx', hx'x⟩⟩
        rcases hy with ⟨y', ⟨hy', hy'y⟩⟩
        change x' ∈ Icc 1 ((p-1)/2) at hx'
        change y' ∈ Icc 1 ((p-1)/2) at hy'
        rw [mem_Icc] at hx' hy'
        rw [
          ← hx'x,
          ← hy'y,
          ← mod_eq_of_lt (a := p - 1) (b := p) (sub_one_lt_self hp.one_le),
          ModEq,
          ← mul_mod,
          mod_mod,
          ← ModEq,
          mul_left_comm,
        ] at eq_neg
        apply ModEq.cancel_left_of_coprime ha.symm at eq_neg
        have hx'p : x' < p := calc
          _ ≤ (p-1)/2     := hx'.2
          _ < p           := half_lt hp
        have hy'p : y' < p := calc
          _ ≤ (p-1)/2     := hy'.2
          _ < p           := half_lt hp
        have y'_pos : 0 < y' := pos_iff_one_le.mpr hy'.1
        apply (ModEq.trans · (ModEq.neg_one_mul (le_of_lt hy'p))) at eq_neg
        apply (ModEq.eq_of_lt_of_lt · hx'p (Nat.sub_lt_self y'_pos (le_of_lt hy'p))) at eq_neg
        have : x' < p - y' := by
          apply lt_of_le_of_lt hx'.2
          calc
            _ < (p-1)/2 + 1       := (lt_add_iff_pos_right _).mpr zero_lt_one
            _ = p - (p-1)/2       := (sub_half hp hp').symm
            _ ≤ p - y'            := Nat.sub_le_sub_left hy'.2 _
        apply Nat.ne_of_lt at this
        exact this eq_neg
    have h_abs' : image (abs' · p) aH = H := by
      apply eq_image_of_inj_of_subset_of_card_eq h_inj h_subset
      rw [h_card_aH, h_card_H]
    have hz₂ : z ≡ (p-1)^g * ∏ x in H, x [MOD p] := by
      conv at this =>
        rhs
        arg 2
        arg 2
        intro x
        change id (abs' x p)
      rw [
        ← prod_image (g := (abs' · p)) h_inj,
        h_abs',
      ] at this
      exact this
    have hz := ModEq.trans hz₁.symm hz₂
    apply ModEq.cancel_right_of_coprime at hz
    · calc
        _ ≡ a^((p-1)/2) [MOD p]     := euler's_criterion hp hp'
        _ ≡ (p-1)^g [MOD p]         := hz
    · rw [Nat.gcd_comm]
      apply coprime_prod_left_iff.mpr
      intro i
      exact coprime_of_mem_H

theorem gauss's_lemma' {a p : ℕ} (hp : p.Prime) (hp' : p > 2) (ha : Coprime a p) (ha' : Odd a) :
  let S := ∑ k in Icc 1 ((p-1)/2), a * k / p
  legendre a p ≡ (p-1)^S [MOD p]
  := by
    intro S
    -- The lower half of the range [1, p]. That is, {1, 2, ..., (p-1)/2}
    let H := Icc 1 ((p-1)/2)
    -- aH = {1a, 2a, ..., (p-1)/2 * a}
    let aH := image (a * ·) H
    let aH_div := image (a * · / p) H
    let aH_mod := image (a * · % p) H
    let G := filter (· > p/2) aH_mod
    let g := card G
    let L := filter (· ≤ p/2) aH_mod
    let paHp := image (fun x => p * (a*x / p)) H
    have one_le_half : 1 ≤ (p-1)/2 := by
      rw [one_le_div_iff zero_lt_two]
      apply le_sub_one_of_lt hp'
    have half_lt : (p-1)/2 < p := calc
      _ ≤ p - 1           := Nat.div_le_self _ _
      _ < p               := sub_one_lt_self hp.pos
    have mul_mod_inj : Set.InjOn (fun x => a*x % p) H := by
      apply Set.InjOn.mono (s₂ := Ico 1 p) _ (hp.mul_mod_injOn_Ico ha)
      apply (Icc_subset_Ico_iff one_le_half).mpr
      exact And.intro le_rfl half_lt
    have hGL : Disjoint G L := by
      rw [disjoint_filter]
      intro x hx hx'
      rw [not_le]
      exact hx'
    have hR : aH_mod = Finset.disjUnion G L hGL := by
      ext x
      rw [mem_disjUnion]
      constructor
      · intro hx
        rw [mem_filter, mem_filter, ← and_or_left]
        exact And.intro hx (lt_or_ge _ _)
      · intro hx
        rcases hx with hx | hx <;> exact (mem_filter.mp hx).1
    have a_ne_zero : a ≠ 0 := hp.ne_zero_of_coprime ha
    have : ∑ aH = ∑ x in H, (p * (a*x / p)) + ∑ G + ∑ L := by
      rw [sum_image (by
        intro x _ y _
        apply (Nat.mul_right_inj a_ne_zero).mp
      )]
      conv =>
        lhs
        arg 2
        intro x
        rw [← div_add_mod (a*x) p]
      rw [sum_add_distrib, add_assoc]
      congr
      rw [← sum_image_id (f := (a * · % p)) mul_mod_inj]
      change ∑ aH_mod = ∑ G + ∑ L
      rw [hR, sum_disjUnion]
    have : ∑ H = ∑ x in G, (p - x) + ∑ L := by
      
      sorry
    -- have : (a - 1) * ∑ H = ∑ paH' - p*g + 2 * ∑ G := by
    --   sorry
    have : S ≡ g [MOD 2] := by
      sorry
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
