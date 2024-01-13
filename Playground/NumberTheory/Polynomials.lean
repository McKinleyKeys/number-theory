
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

lemma Nat.Poly.size_eq_degree_add_one {p : Nat.Poly} :
  p.data.size = p.degree + 1
  := by
    rw [degree, Nat.sub_add_cancel one_le_size]

lemma Nat.Poly.eval' {p : Nat.Poly} {x : ℕ} :
  p.eval x = ∑ k in Icc 0 p.degree, (p.coeff k) * x^k
  := by
    rw [eval, size_eq_degree_add_one, ]
    sorry

lemma Int.Poly.eval' {p : Int.Poly} {x : ℤ} :
  p.eval x = ∑ k in Icc 0 p.degree, (p.coeff k) * x^k
  := by
    rw [eval]
    sorry

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


lemma Int.Poly.coeff_ofFn {c : ℕ → ℤ} {n i : ℕ} (h : i ≤ n) :
  (Int.Poly.ofFn n c).coeff i = c i
  := by
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

theorem telescoping_sum {n : ℕ} {f : ℕ → ℕ} (h : Monotone f) :
  ∑ i in range n, f (i + 1) - f i = f n - f 0
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
    induction' n with m hm
    · rw [Nat.le_zero, Finset.card_eq_zero, filter_eq_empty_iff]
      intro x hx
      rw [f.eval_of_deg_zero hf, Int.ModEq]
      simp
      apply h
    · by_contra h'
      rw [not_le] at h'
      have hf : f.degree = m.succ := by sorry
      have x₀ : ℤ := by sorry
      -- have hx₀ : f.eval x₀ ≡ 0 [MOD p] := by sorry
      let c (i : ℕ) := f.coeff i
      have (x : ℤ) (j : ℕ) : (x - x₀) * ∑ i in range j, x^i * x₀^(j - i - 1) = x^j - x₀^j :=
        mul_eq_telescoping_sum
      let f' := Int.Poly.ofFn
        m
        (fun i => ∑ j in Icc (i + 1) (m + 1), (c j) * x₀^(j - i - 1))
      have hf' : f'.degree = m := by sorry
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
                  intro i hi
                  rw [mul_sub_left_distrib]
        _ = ∑ j in Icc 1 m.succ, (c j) * (x - x₀) * ∑ i in range j, x^i * x₀^(j - i - 1)
                := by
                  apply sum_eq_sum
                  intro i hi
                  rw [mul_assoc, mul_eq_telescoping_sum]
        _ = (x - x₀) * (f'.eval x)
                := by
                  rw [Int.Poly.eval', hf']
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
      
      sorry

-- theorem pow_cong_one_solutions {n p : ℕ} (hp : p.Prime) (hn : n ∣ p-1) :
--   card (filter (fun x => x^n ≡ 1 [MOD p]) (range p)) = n
--   := by
--     sorry
