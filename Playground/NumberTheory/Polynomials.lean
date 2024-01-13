
import Mathlib
import Playground.SetTheory
import Playground.NumberTheory.Basic

open Nat Finset BigOperators Int.ModEq


/-
 - Definitions
 -/

structure Poly' (α : Type) [CommSemiring α] where
  degree : ℕ
  coeff : ℕ → α

def Poly'.eval [CommSemiring α] (p : Poly' α) (x : α) : α :=
  ∑ k in Icc 0 p.degree, (p.coeff k) * x^k


/-
 - Lemmas
 -/

lemma Poly'.eval_of_deg_zero [CommSemiring α] {p : Poly' α} {x : α} (hp : p.degree = 0) :
  p.eval x = p.coeff 0
  := by
    rw [eval, hp]
    simp

lemma sum_sub_sum {S : Finset α} {f g : α → ℤ} :
  ∑ i in S, f i - ∑ i in S, g i = ∑ i in S, (f i - g i)
  := by
    sorry

lemma sum_eq_sum {S : Finset ℕ} {f g : ℕ → ℤ} (h : ∀ i ∈ S, f i = g i) :
  ∑ i in S, f i = ∑ i in S, g i
  := by
    sorry

theorem mul_eq_telescoping_sum {n : ℕ} {a b : ℤ} :
  (a - b) * ∑ i in range n, a^i * b^(n - i - 1) = a^n - b^n
  := by
    let f (i : ℕ) := a^i * b^(n - i)
    calc
      _ = ∑ i in range n, (a^(i + 1) * b^(n - i - 1) - a^i * b^(n - i))
                := by
                  rw [mul_sum]
                  apply sum_eq_sum
                  intro i hi
                  rw [
                    mul_sub_right_distrib,
                    ← mul_assoc,
                    ← mul_assoc,
                    pow_add,
                    pow_one,
                    mul_comm (a^i) a,
                  ]
                  simp
                  rw [mul_comm b, mul_assoc]
                  nth_rw 1 [← pow_one b]
                  have : 1 ≤ n - i := by
                    rw [mem_range] at hi
                    rw [← pos_iff_one_le]
                    simp [hi]
                  rw [
                    ← pow_add,
                    ← Nat.add_sub_assoc this,
                    Nat.add_sub_cancel_left,
                  ]
      _ = ∑ i in range n, (f (i + 1) - f i)   := by congr
      _ = f n - f 0                           := by apply Finset.sum_range_sub
      _ = a^n - b^n                           := by simp

lemma sum_Icc_succ {a b : ℕ} {f : ℕ → α} [AddCommMonoid α] :
  ∑ i in Icc a (succ b), f i = (∑ i in Icc a b, f i) + f (succ b)
  := by
    sorry

lemma sum_Icc_one {n : ℕ} {f : ℕ → α} [AddCommMonoid α] [HSub α α α] :
  ∑ i in Icc 1 n, f i = (∑ i in range (n + 1), f i) - f 0
  := by
    sorry

theorem sum_mul_sum_mul {n : ℕ} {a t : ℕ → R} {b : ℕ → ℕ → R} [CommSemiring R] :
  ∑ i in range (n+1), (a i) * ∑ j in range i, (t j) * (b i j) = ∑ j in range n, (t j) * ∑ i in Icc (j+1) n, (a i) * (b i j)
  := by
    induction' n with m hm
    · simp
    · rw [succ_add, sum_range_succ, hm]
      simp only [sum_Icc_succ, mul_add, sum_add_distrib]
      rw [sum_range_succ, sum_range_succ, add_assoc]
      congr
      simp
      rw [mul_add, sum_range_succ, mul_sum, mul_left_comm]
      simp [mul_left_comm]


/-
 - Lagrange's Theorem
 -/

theorem lagrange's_theorem {n p : ℕ} {f : Poly' ℤ} (hf : f.degree = n) (hp : p.Prime) (h : ↑p ∤ f.coeff n) :
  card (filter (fun (x : ℕ) => f.eval ↑x ≡ 0 [ZMOD ↑p]) (range p)) ≤ n
  := by
    revert f
    induction' n with m hm
    all_goals intro f hf h
    · rw [Nat.le_zero, Finset.card_eq_zero, filter_eq_empty_iff]
      intro x _
      rw [f.eval_of_deg_zero hf, Int.ModEq]
      simp
      apply h
    · by_contra h'
      rw [not_le] at h'
      -- X = roots of f
      let X := filter (fun (x : ℕ) => f.eval ↑x ≡ 0 [ZMOD ↑p]) (range p)
      change succ m < card X at h'
      have h'' := h'
      apply lt_trans (succ_pos _) at h''
      rw [Finset.card_pos, Finset.Nonempty] at h''
      rcases h'' with ⟨x₀, hx₀⟩
      rw [mem_filter] at hx₀
      rcases hx₀ with ⟨hx₀, hx₀'⟩
      let c (i : ℕ) := f.coeff i
      let f' := Poly'.mk
        m
        (fun i => ∑ j in Icc (i + 1) (m + 1), (c j) * x₀^(j - i - 1))
      have (x : ℤ) : f.eval x - f.eval x₀ = (x - x₀) * (f'.eval x) := calc
        _ = ∑ i in Icc 1 m.succ, (c i) * (x^i - x₀^i)
                := by
                  rw [
                    Poly'.eval,
                    Poly'.eval,
                    hf,
                    sum_sub_sum,
                    ← insert_Icc_add_one (by simp),
                    sum_insert (by simp),
                    _root_.pow_zero,
                    mul_one,
                    _root_.pow_zero,
                    mul_one,
                    sub_self,
                    zero_add,
                  ]
                  apply sum_eq_sum
                  intro i _
                  rw [mul_sub_left_distrib]
        _ = ∑ j in Icc 1 m.succ, (c j) * (x - x₀) * ∑ i in range j, x^i * x₀^(j - i - 1)
                := by
                  apply sum_eq_sum
                  intro i _
                  rw [mul_assoc, mul_eq_telescoping_sum]
        _ = (x - x₀) * (f'.eval x)
                := by
                  unfold_let f'
                  rw [Poly'.eval]
                  simp (config := {zeta:=false}) only [mul_comm, mul_assoc]
                  rw [← mul_sum]
                  apply congrArg
                  rw [sum_Icc_one, sum_mul_sum_mul, ← Finset.range_add_one_eq_Icc, sum_range_zero, mul_zero, sub_zero]
                  apply sum_eq_sum
                  intro i _
                  congr
                  funext j
                  rw [mul_comm]
      specialize hm (f := f') (by simp) (by simp [h])
      -- X' = roots of f except x₀
      let X' := erase X x₀
      have card_X' : card X' ≥ succ m := by
        apply le_pred_of_lt at h'
        apply le_trans h' pred_card_le_card_erase
      have hX' : ∀ xₖ ∈ X', f'.eval xₖ ≡ 0 [ZMOD ↑p] := by
        intro xₖ hxₖ
        have : (xₖ - x₀) * (f'.eval xₖ) ≡ 0 [ZMOD ↑p] := calc
          _ = (f.eval xₖ) - (f.eval x₀)     := by rw [← this xₖ]
          _ ≡ (f.eval xₖ) [ZMOD ↑p]         := by
                                              nth_rw 2 [← sub_zero (f.eval xₖ)]
                                              apply Int.ModEq.sub_left _ hx₀'
          _ ≡ 0 [ZMOD ↑p]                   := by
                                              rcases mem_erase.mp hxₖ with ⟨_, hxₖ'⟩
                                              exact (mem_filter.mp hxₖ').right
        rw [Int.ModEq, Int.zero_emod, ← Int.dvd_iff_emod_eq_zero] at this
        apply Int.Prime.dvd_mul' hp at this
        rcases this with left | right
        · have : (p : ℤ) ∤ xₖ - x₀ := by
            apply Int.not_dvd_of_ne_zero_of_lt_of_gt_neg
            · apply sub_eq_zero.not.mpr
              rw [mem_erase] at hxₖ
              simp [hxₖ.left]
            · apply Int.sub_lt
              · rw [mem_erase, mem_filter, mem_range] at hxₖ
                rcases hxₖ with ⟨_, xₖ_lt_p, _⟩
                simp [xₖ_lt_p]
              · simp
            · rw [gt_iff_lt, neg_lt, neg_sub]
              apply Int.sub_lt
              · rw [mem_range] at hx₀
                simp [hx₀]
              · simp
          contradiction
        · apply Int.ModEq.cong_zero_iff_dvd.mpr right
      have : succ m ≤ card (filter (fun (x : ℕ) => f'.eval x ≡ 0 [ZMOD p]) (range p)) := calc
        _ ≤ card X - 1      := le_sub_one_of_lt h'
        _ ≤ card X'         := pred_card_le_card_erase
        _ ≤ card (filter (fun (x : ℕ) => f'.eval x ≡ 0 [ZMOD p]) (range p))
                  := by
                    apply Finset.card_le_of_subset
                    intro xₖ hxₖ
                    rw [mem_filter]
                    constructor
                    · apply mem_of_mem_erase at hxₖ
                      rw [mem_filter] at hxₖ
                      exact hxₖ.left
                    · apply hX' xₖ hxₖ
      rw [add_one_le_iff, lt_iff_not_ge] at this
      contradiction

-- theorem pow_cong_one_solutions {n p : ℕ} (hp : p.Prime) (hn : n ∣ p-1) :
--   card (filter (fun x => x^n ≡ 1 [MOD p]) (range p)) = n
--   := by
--     sorry
