
import Mathlib
import Playground.SetTheory

open Nat Finset BigOperators


/-
 - Custom Operators
 -/

def NotModEq (n a b : ℕ) :=
  ¬(a ≡ b [MOD n])
notation:50 a:50 " ≢ " b:50 " [MOD " n:50 "]" => NotModEq n a b

def NotDvd (a b : ℕ) :=
  ¬(a ∣ b)
notation:50 a:50 " ∤ " b:50 => NotDvd a b


/-
 - Modular Equality
 -/

/- TODO: Consider removing -/
lemma ModEq.eq_of_le_of_le {a b m : ℕ} (h : a ≡ b [MOD m]) (ha : 1 ≤ a ∧ a ≤ m) (hb : 1 ≤ b ∧ b ≤ m) :
  a = b
  := by
    rcases ha with ⟨ha₁, ha₂⟩
    rcases hb with ⟨hb₁, hb₂⟩
    let inj := mod_injOn_Ico 1 m
    have a_mem : a ∈ Ico 1 (1 + m) := by
      apply mem_Ico.mpr
      constructor
      · exact ha₁
      · rw [add_comm]
        apply lt_add_one_iff.mpr ha₂
    have b_mem : b ∈ Ico 1 (1 + m) := by
      apply mem_Ico.mpr
      constructor
      · exact hb₁
      · rw [add_comm]
        apply lt_add_one_iff.mpr hb₂
    dsimp [Set.InjOn] at inj
    apply inj a_mem b_mem h


/-
 - Coprimality
 -/

lemma coprime_mul {a b n : ℕ} (ha : Coprime a n) (hb : Coprime b n) :
  Coprime (a * b) n
  := by
    apply coprime_mul_iff_left.mpr
    constructor
    · exact ha
    · exact hb
lemma coprime_mod {a n : ℕ} (ha : Coprime a n) :
  Coprime (a % n) n
  := by
    rw [Coprime]
    cases n
    · rw [mod_zero, Nat.gcd_zero_right]
      apply (coprime_zero_right a).mp ha
    · rw [← gcd_succ, ← Coprime, coprime_comm] 
      exact ha

def Nat.coprimes (n : ℕ) : Finset ℕ
  := filter (fun x => Coprime x n) (range n)

lemma mem_coprimes₁ {a n : ℕ} (ha : a ∈ n.coprimes) :
  Coprime a n
  := by
    apply (mem_filter (s := (range n))).mp at ha
    rcases ha with ⟨_, right⟩
    exact right
lemma mem_coprimes₂ {a n : ℕ} (ha : a ∈ n.coprimes) :
  a < n
  := by
    apply (mem_filter (s := (range n))).mp at ha
    rcases ha with ⟨left, _⟩
    apply Finset.mem_range.mp left

lemma totient_eq_card_coprimes (n : ℕ) :
  φ n = card n.coprimes
  := by
    rw [totient, coprimes]
    congr
    change (fun x => Coprime n x) = (fun x => Coprime x n)
    simp [coprime_comm]


/-
 - Euler's Totient Theorem
 -/

theorem euler's_totient_theorem {a m : ℕ} (hm : m > 0) (ha : Coprime a m) :
  a^(φ m) ≡ 1 [MOD m]
  := by
    let f (x : ℕ) := a*x % m
    let S := image f m.coprimes
    have inj : Set.InjOn f m.coprimes := by
      intro x hx y hy h
      change (a*x ≡ a*y [MOD m]) at h
      apply ModEq.cancel_left_of_coprime at h
      · let hx' := mem_coprimes₂ hx
        let hy' := mem_coprimes₂ hy
        apply ModEq.eq_of_lt_of_lt h hx' hy'
      · rw [Coprime, Nat.gcd_comm] at ha
        exact ha
    have subset : S ⊆ m.coprimes := by
      intro c hc
      apply mem_image.mp at hc
      rcases hc with ⟨b, ⟨hb, h⟩⟩
      apply mem_coprimes₁ at hb
      have hc : Coprime (a * b) m := coprime_mul ha hb
      apply coprime_mod at hc
      dsimp at h
      rw [h] at hc
      have : c ∈ range m := by
        apply mem_range.mpr
        rw [← h]
        apply mod_lt _ hm
      apply mem_filter.mpr
      constructor
      · exact this
      · exact hc
    have : S = m.coprimes := eq_image_of_inj inj subset
    have : (a^(φ m) * ∏ c in m.coprimes, c) ≡ (∏ c in m.coprimes, c) [MOD m] := calc
      a^(φ m) * ∏ c in m.coprimes, c
      _ ≡ ∏ c in m.coprimes, a * c [MOD m]      := by
                                                  rw [
                                                    prod_mul_distrib,
                                                    prod_const,
                                                    totient_eq_card_coprimes
                                                  ]
      _ ≡ ∏ c in S, c [MOD m]                   := by
                                                  dsimp [S, ModEq]
                                                  rw [prod_image, prod_nat_mod]
                                                  congr
      _ ≡ ∏ c in m.coprimes, c [MOD m]          := by rw [this]
    have h_prod : Coprime (∏ c in coprimes m, c) m := by
      apply Coprime.prod_left
      rintro c hc
      apply mem_coprimes₁ hc
    apply ModEq.cancel_right_of_coprime (c := ∏ x in coprimes m, x)
    · rw [← Coprime]
      apply coprime_comm.mpr h_prod
    · rw [one_mul]
      exact this

theorem fermat's_little_theorem {a p : ℕ} (hp : p.Prime) (ha : Coprime a p) :
  a^(p-1) ≡ 1 [MOD p]
  := by
    rw [← totient_prime hp]
    apply euler's_totient_theorem (Prime.pos hp) ha
