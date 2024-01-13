
import Mathlib
import Playground.SetTheory
import Playground.NumberTheory.Basic

open Nat Finset BigOperators Int.ModEq


/-
 - Definitions
 -/

structure Nat.Poly where
  data : Array ℕ
  hd : 0 < data.size

def Nat.Poly.degree (p : Nat.Poly) :=
  p.data.size - 1

def Nat.Poly.coeff (p : Nat.Poly) (k : ℕ) :=
  p.data.getD k 0

def Nat.Poly.eval (p : Nat.Poly) (x : ℕ) : ℕ :=
  ∑ k in range p.data.size, (p.coeff k) * x^k

def Nat.Poly.ofFn (n : ℕ) (c : ℕ → ℕ) : Nat.Poly where
  data := (Array.range (n + 1)).map c
  hd := by simp


structure Int.Poly where
  data : Array ℤ
  hd : 0 < data.size

def Int.Poly.degree (p : Int.Poly) :=
  p.data.size - 1

def Int.Poly.coeff (p : Int.Poly) (k : ℕ) :=
  p.data.getD k 0

def Int.Poly.eval (p : Int.Poly) (x : ℤ) : ℤ :=
  ∑ k in Finset.range p.data.size, (p.coeff k) * x^k

def Int.Poly.ofFn (n : ℕ) (c : ℕ → ℤ) : Int.Poly where
  data := (Array.range (n + 1)).map c
  hd := by simp


/-
 - Lemmas
 -/

lemma Nat.Poly.one_le_size {p : Nat.Poly} :
  1 ≤ p.data.size
  :=
    pos_iff_one_le.mp p.hd

lemma Int.Poly.one_le_size {p : Int.Poly} :
  1 ≤ p.data.size
  :=
    _root_.pos_iff_one_le.mp p.hd

lemma Nat.Poly.size_eq_degree_add_one {p : Nat.Poly} :
  p.data.size = p.degree + 1
  := by
    rw [degree, Nat.sub_add_cancel one_le_size]

lemma Int.Poly.size_eq_degree_add_one {p : Int.Poly} :
  p.data.size = p.degree + 1
  := by
    rw [degree, Nat.sub_add_cancel one_le_size]

lemma Nat.Poly.eval' {p : Nat.Poly} {x : ℕ} :
  p.eval x = ∑ k in Icc 0 p.degree, (p.coeff k) * x^k
  := by
    rw [eval, size_eq_degree_add_one, range_add_one_eq_Icc]

lemma Int.Poly.eval' {p : Int.Poly} {x : ℤ} :
  p.eval x = ∑ k in Icc 0 p.degree, (p.coeff k) * x^k
  := by
    rw [eval, size_eq_degree_add_one, range_add_one_eq_Icc]

lemma Nat.Poly.eval_of_deg_zero {p : Nat.Poly} {x : ℕ} (hp : p.degree = 0) :
  p.eval x = p.coeff 0
  := by
    rw [eval', hp]
    simp

lemma Int.Poly.eval_of_deg_zero {p : Int.Poly} {x : ℤ} (hp : p.degree = 0) :
  p.eval x = p.coeff 0
  := by
    rw [eval', hp]
    simp


lemma Int.Poly.degree_ofFn {c : ℕ → ℤ} {n : ℕ} :
  (Int.Poly.ofFn n c).degree = n
  := by
    rw [ofFn, degree]
    simp

lemma Int.Poly.coeff_ofFn {c : ℕ → ℤ} {n i : ℕ} (h : i ≤ n) :
  (Int.Poly.ofFn n c).coeff i = c i
  := by
    rw [ofFn, coeff]
    simp only [Array.getD_eq_get?]
    have : (Array.map c (Array.range (n + 1))).size = n + 1 := by
      simp
    rw [Array.get?, dif_pos]
    · simp
      rw [Array.getElem_map]
      congr
      rw [Array.range (n+1)]
      sorry
    · 
      sorry


lemma Icc_eq_insert_Icc {a b : ℕ} :
  Icc a b = insert a (Icc (a + 1) b)
  := by
    sorry

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

lemma Icc_zero_eq_range_succ {n : ℕ} :
  Icc 0 n = range (succ n)
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

theorem lagrange's_theorem {n p : ℕ} {f : Int.Poly} (hf : f.degree = n) (hp : p.Prime) (h : ↑p ∤ f.coeff n) :
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
      let f' := Int.Poly.ofFn
        m
        (fun i => ∑ j in Icc (i + 1) (m + 1), (c j) * x₀^(j - i - 1))
      have (x : ℤ) : f.eval x - f.eval x₀ = (x - x₀) * (f'.eval x) := calc
        _ = ∑ i in Icc 1 m.succ, (c i) * (x^i - x₀^i)
                := by
                  rw [
                    Int.Poly.eval',
                    Int.Poly.eval',
                    hf,
                    sum_sub_sum,
                    Icc_eq_insert_Icc,
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
                  rw [Int.Poly.eval', Int.Poly.degree_ofFn]
                  simp (config := {zeta:=false}) only [mul_comm, mul_assoc]
                  rw [← mul_sum]
                  apply congrArg
                  rw [sum_Icc_one, sum_mul_sum_mul, Icc_zero_eq_range_succ, sum_range_zero, mul_zero, sub_zero]
                  apply sum_eq_sum
                  intro i hi
                  congr
                  unfold_let f'
                  rw [Int.Poly.coeff_ofFn]
                  rw [mem_range, lt_succ] at hi
                  exact hi
      have hf' : ↑p ∤ f'.coeff m := by
        rw [Int.Poly.coeff_ofFn]
        simp
        apply h
        rfl
      specialize hm (f := f') (Int.Poly.degree_ofFn) hf'
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
