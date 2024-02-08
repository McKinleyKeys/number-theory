
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
                    apply Finset.card_le_card
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

lemma Finset.filter_dvd_eq_image {n k : ℕ} (hn : n > 0) :
  filter (fun x => n ∣ x) (range (n * k)) = image (fun x => n * x) (range k)
  := by
    ext x
    constructor
    · intro h
      rw [mem_filter] at h
      rcases h with ⟨h₁, h₂⟩
      rw [dvd_iff_exists_eq_mul_right] at h₂
      rcases h₂ with ⟨c, hc⟩
      rw [mem_image]
      use c
      constructor
      · rw [mem_range]
        rw [mem_range, hc] at h₁
        apply lt_of_mul_lt_mul_left' h₁
      · exact hc.symm
    · intro h
      rw [mem_image] at h
      rcases h with ⟨a, ⟨ha, h⟩⟩
      rw [mem_range] at ha
      rw [mem_filter]
      constructor
      · rw [mem_range, ← h]
        exact Nat.mul_lt_mul_of_pos_left ha hn
      · exact Dvd.intro a h

lemma Finset.Icc_union_Ioo_eq_Ico {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b < c) :
  Icc a b ∪ Ioo b c = Ico a c
  := by
    ext x
    rw [mem_union, mem_Icc, mem_Ioo, mem_Ico]
    constructor
    · intro h
      rcases h with left | right
      · rcases left with ⟨left₁, left₂⟩
        apply And.intro left₁ (lt_of_le_of_lt left₂ h₂)
      · rcases right with ⟨right₁, right₂⟩
        apply And.intro (le_of_lt (lt_of_le_of_lt h₁ right₁)) right₂
    · intro h
      by_cases hx : x ≤ b
      · left
        apply And.intro h.1 hx
      · right
        rw [not_le] at hx
        apply And.intro hx h.2

lemma Finset.filter_dvd_Icc_eq_filter_dvd_range {n k : ℕ} (hn : n > 0) (hk : k > 0) :
  filter (fun x => n ∣ x) (Icc 0 (n * (k - 1))) = filter (fun x => n ∣ x) (range (n * k))
  := by
    let f (S : Finset ℕ) := filter (fun x => n ∣ x) S
    change f (Icc 0 (n * (k - 1))) = f (range (n * k))
    have : f (Ioo (n * (k - 1)) (n * k)) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x hx
      rw [mem_Ioo] at hx
      rcases hx with ⟨h₁, h₂⟩
      apply not_dvd_of_between_consec_multiples h₁
      rw [Nat.sub_add_cancel (pos_iff_one_le.mp hk)]
      exact h₂
    rw [
      ← union_empty (f (Icc 0 (n * (k - 1)))),
      ← this,
      ← filter_union,
    ]
    rw [Icc_union_Ioo_eq_Ico (Nat.zero_le _), Ico_zero_eq_range]
    rw [Nat.mul_sub_left_distrib]
    apply Nat.sub_lt_self
    · rw [mul_one]
      exact hn
    · apply Nat.mul_le_mul_left _ (pos_iff_one_le.mp hk)

lemma Int.sub_right_iff {a b c m : ℤ} :
  a - c ≡ b - c [ZMOD m] ↔ a ≡ b [ZMOD m]
  := by
    constructor
    · intro h
      apply ModEq.add_right c at h
      rw [sub_add_cancel, sub_add_cancel] at h
      exact h
    · intro h
      apply ModEq.add_right (-c) at h
      rw [← sub_eq_add_neg, ← sub_eq_add_neg] at h
      exact h

theorem pow_cong_one_solutions {n p : ℕ} (hp : p.Prime) (hn : n ∣ p-1) :
  card (filter (fun x => x^n ≡ 1 [MOD p]) (range p)) = n
  := by
    have n_pos : 0 < n := by
      apply pos_of_dvd_of_pos hn
      simp
      apply Prime.one_lt hp
    have n_le : n ≤ p - 1 := le_of_dvd (Prime.sub_one_pos hp) hn
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
      intro x _
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
      let k := (p - 1) / n
      -- g(x) = x^(n(k-1)) + x^(n(k-2)) + ... + x^n + 1
      let g : Poly' ℤ := Poly'.mk
        (n * (k - 1))
        fun i =>
          if n ∣ i then
            1
          else
            0
      have g_eval {x : ℤ} : g.eval x = ∑ i in range k, (x^n)^i := by
        rw [Poly'.eval]
        dsimp only
        simp [ite_mul]
        rw [sum_ite, sum_const_zero, add_zero]
        have : (p - 1) / n > 0 := Nat.div_pos n_le n_pos
        conv =>
          lhs
          arg 1
          rw [
            filter_dvd_Icc_eq_filter_dvd_range n_pos this,
            filter_dvd_eq_image n_pos,
          ]
        conv =>
          rhs
          arg 2
          intro i
          rw [← pow_mul]
        rw [sum_image]
        intro a _ b _ habn
        apply (Nat.mul_right_inj (pos_iff_ne_zero.mp n_pos)).mp habn
      have hfg {x : ℤ} : (f.eval x) * (g.eval x) = x^(p-1) - 1 := by
        rw [f_eval, g_eval]
        conv =>
          lhs
          arg 2
          arg 2
          intro i
          rw [← mul_one ((x^n)^i), ← one_pow (k - i - 1)]
        rw [Int.mul_eq_telescoping_sum, one_pow, ← pow_mul]
        unfold_let k
        rw [Nat.mul_div_cancel' hn]
      rw [h_roots]
      have fg_roots : card (filter (fun (x : ℕ) => x^(p-1) - 1 ≡ 0 [ZMOD p]) (range p)) = p - 1 := by
        rw [
          range_eq_insert_zero_Ico_one (Prime.pos hp),
          filter_insert,
          if_neg (by
            rw [
              (Int.coe_nat_eq_zero (n := 0)).mpr (by rfl),
              zero_pow (pos_iff_ne_zero.mp (Prime.sub_one_pos hp)),
              zero_sub,
              Int.ModEq,
              Int.zero_emod,
              ← Int.dvd_iff_emod_eq_zero,
              Int.dvd_neg,
            ]
            apply Prime.not_dvd_one (prime_iff_prime_int.mp hp)
          ),
          filter_eq_self.mpr (by
            intro x hx
            rw [← sub_self 1]
            apply Int.ModEq.sub_right
            nth_rw 2 [← cast_one]
            rw [← Int.coe_nat_pow]
            rw [Int.coe_nat_modEq_iff]
            apply fermat's_little_theorem hp (coprime_of_mem_Ico hp hx)
          ),
          card_Ico,
        ]
      have : ∀ x ∈ range p, x^(p-1) - 1 ≡ 0 [ZMOD p] ↔ f.eval x ≡ 0 [ZMOD p] ∨ g.eval x ≡ 0 [ZMOD p] := by
        intro h _
        rw [
          ← Int.dvd_iff_cong_zero,
          ← Int.dvd_iff_cong_zero,
          ← Int.dvd_iff_cong_zero,
          ← hfg,
        ]
        apply Int.Prime.dvd_mul_iff hp
      let g_roots := filter (fun (x : ℕ) => g.eval x ≡ 0 [ZMOD p]) (range p)
      have card_g_roots : card g_roots ≤ p - 1 - n := by
        apply lagrange's_theorem _ hp _
        · dsimp only
          rw [Nat.mul_sub_left_distrib, mul_one, Nat.mul_div_cancel' hn]
        · dsimp only
          rw [if_pos _]
          · apply Prime.not_dvd_one (prime_iff_prime_int.mp hp)
          · apply Nat.dvd_sub n_le hn dvd_rfl
      rw [filter_congr this, filter_or] at fg_roots
      change card (f_roots ∪ g_roots) = p - 1 at fg_roots
      have : card f_roots + card g_roots ≥ p - 1 := calc
        _ ≥ card (f_roots ∪ g_roots)    := card_union_le _ _
        _ = p - 1                       := fg_roots
      apply sub_le_of_le_add at this
      calc
        _ ≥ p - 1 - g_roots.card    := this
        _ ≥ p - 1 - (p - 1 - n)     := Nat.sub_le_sub_left card_g_roots _
        _ = n                       := sub_self_sub n_le
    apply le_antisymm le ge
