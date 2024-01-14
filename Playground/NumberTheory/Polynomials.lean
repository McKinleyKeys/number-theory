
import Mathlib
import Playground.SetTheory
import Playground.NumberTheory.Basic

open Nat Finset BigOperators


/-
 - Definitions
 -/

structure Poly' (α : Type) [CommSemiring α] where
  degree : ℕ
  coeff : ℕ → α

def Poly'.eval [CommSemiring α] (p : Poly' α) (x : α) : α :=
  ∑ k in Icc 0 p.degree, (p.coeff k) * x^k


/-
 - Miscellaneous
 -/

lemma Poly'.eval_of_deg_zero [CommSemiring α] {p : Poly' α} {x : α} (hp : p.degree = 0) :
  p.eval x = p.coeff 0
  := by
    rw [eval, hp]
    simp

theorem Finset.sum_mul_sum_mul {n : ℕ} {a t : ℕ → R} {b : ℕ → ℕ → R} [CommSemiring R] :
  ∑ i in range (n+1), (a i) * ∑ j in range i, (t j) * (b i j) = ∑ j in range n, (t j) * ∑ i in Icc (j+1) n, (a i) * (b i j)
  := by
    induction' n with m hm
    · simp
    · conv =>
        rhs
        rw [sum_congr']
        · skip
        · tactic =>
            intro j hj
            have : j + 1 ≤ succ m := by
              simp [mem_range.mp hj, succ_le_iff]
            rw [
              sum_Icc_succ this,
              mul_add,
            ]
      rw [
        succ_add,
        sum_range_succ,
        hm,
        sum_range_succ,
        sum_range_succ,
      ]
      simp
      rw [
        mul_add,
        sum_add_distrib,
        mul_sum,
        ← add_assoc,
        mul_left_comm,
      ]
      congr
      funext i
      ring


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
                    Int.sum_sub_sum,
                    ← insert_Icc_succ_left (by simp),
                    sum_insert (by simp),
                    _root_.pow_zero,
                    mul_one,
                    _root_.pow_zero,
                    mul_one,
                    sub_self,
                    zero_add,
                  ]
                  apply sum_congr'
                  intro i _
                  rw [mul_sub_left_distrib]
        _ = ∑ j in Icc 1 m.succ, (c j) * (x - x₀) * ∑ i in range j, x^i * x₀^(j - i - 1)
                := by
                  apply sum_congr'
                  intro i _
                  rw [mul_assoc, Int.mul_eq_telescoping_sum]
        _ = (x - x₀) * (f'.eval x)
                := by
                  unfold_let f'
                  rw [Poly'.eval]
                  simp (config := {zeta:=false}) only [mul_comm, mul_assoc]
                  rw [← mul_sum]
                  apply congrArg
                  rw [
                    Int.sum_Icc_one,
                    sum_mul_sum_mul,
                    ← Finset.range_add_one_eq_Icc,
                    sum_range_zero,
                    mul_zero,
                    sub_zero,
                  ]
                  apply sum_congr'
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

lemma Poly'.int_root_eq_nat_root {cn : ℕ → ℕ} {cz : ℕ → ℤ} {d x : ℕ} (h : ∀ (i : ℕ), ↑(cn i) = cz i) :
  (Poly'.mk d cz).eval ↑x = ↑((Poly'.mk d cn).eval x)
  := by
    rw [eval, eval]
    dsimp only
    simp
    apply sum_congr'
    intro i _
    rw [h i]

lemma Int.sub_right_iff {a b c m : ℤ} :
  a - c ≡ b - c [ZMOD m] ↔ a ≡ b [ZMOD m]
  := by
    sorry

theorem pow_cong_one_solutions {n p : ℕ} (hp : p.Prime) (hn : n ∣ p-1) :
  card (filter (fun x => x^n ≡ 1 [MOD p]) (range p)) = n
  := by
    have n_pos : 0 < n := by
      apply pos_of_dvd_of_pos hn
      simp
      apply Prime.one_lt hp
    -- f(x) = x^n - 1       (in ℤ)
    let f := Poly'.mk
      n
      fun i =>
        if i = n then
          1
        else if i = 0 then
          -1
        else
          0
    have f_eval {x : ℤ} : f.eval x = x^n - 1 := by
      rw [Poly'.eval]
      dsimp only
      simp only [ite_mul]
      rw [sum_ite, sum_ite]
      simp only [zero_mul]
      rw [sum_const_zero, filter_eq', filter_eq', filter_ne']
      congr
      · rw [if_pos (by simp), sum_singleton, one_mul]
      · rw [
          if_pos (by simp [n_pos]),
          sum_singleton,
          _root_.pow_zero,
          mul_one,
          add_zero,
        ]
    let roots := filter (fun x => x^n ≡ 1 [MOD p]) (range p)
    let f_roots := filter (fun (x : ℕ) => f.eval ↑x ≡ 0 [ZMOD ↑p]) (range p)
    change card roots = n
    have h_roots : roots = f_roots := by
      apply filter_congr
      intro x hx
      rw [f_eval, ← sub_self 1, Int.sub_right_iff, ← Int.coe_nat_modEq_iff]
      simp
    have le : card roots ≤ n := by
      rw [h_roots]
      apply lagrange's_theorem (by dsimp) hp
      dsimp only
      rw [if_pos rfl]
      apply Prime.not_dvd_one
      apply prime_iff_prime_int.mp hp
    have ge : card roots ≥ n := by
      sorry
    apply le_antisymm le ge
