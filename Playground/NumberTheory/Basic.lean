
import Mathlib
import Playground.SetTheory

open Nat Finset BigOperators


/-
 - Miscellaneous
 -/

lemma pos_iff_one_le {n : ℕ} :
  0 < n ↔ 1 ≤ n
  := calc
    0 < n ↔ n ≠ 0       := pos_iff_ne_zero
    _     ↔ 1 ≤ n       := by symm; apply one_le_iff_ne_zero

lemma sub_sub' {a b c : ℕ} (h : c ≤ b) :
  a - (b - c) = a + c - b
  := by
    induction' b with d hd
    · rw [Nat.sub_zero, Nat.zero_sub, Nat.sub_zero]
      apply le_zero.mp at h
      rw [h, add_zero]
    · by_cases hc : c = succ d
      · simp [hc]
      · apply lt_of_le_of_ne h at hc
        apply le_of_lt_succ at hc
        rw [sub_succ, succ_sub hc, sub_succ]
        apply hd at hc
        rw [hc]

lemma sub_one_sq {n : ℕ} (h : n > 0) :
  (n-1)^2 = n^2 + 1 - 2*n
  := by
    apply one_le_of_lt at h
    rw [
      pow_two,
      Nat.mul_sub_left_distrib,
      Nat.mul_sub_right_distrib,
      mul_one,
      one_mul,
      ← pow_two,
      Nat.sub_right_comm,
      sub_sub' h,
      Nat.sub_sub,
    ]
    ring_nf


/-
 - Parity
 -/

lemma even_iff_eq_two_mul {n : ℕ} :
  Even n ↔ ∃ k, n = 2 * k
  := calc
    Even n ↔ n % 2 = 0      := Nat.even_iff
    _ ↔ 2 ∣ n               := by symm; apply dvd_iff_mod_eq_zero
    _ ↔ ∃ k, n = 2 * k      := dvd_iff_exists_eq_mul_right

lemma even_add_even {a b : ℕ} (ha : Even a) (hb : Even b) :
  Even (a + b)
  := by
    apply even_add.mpr
    apply iff_of_true ha hb
lemma even_add_odd {a b : ℕ} (ha : Even a) (hb : Odd b) :
  Odd (a + b)
  := by
    rw [add_comm]
    apply odd_add.mpr
    apply iff_of_true hb ha
lemma odd_add_even {a b : ℕ} (ha : Odd a) (hb : Even b) :
  Odd (a + b)
  := by
    apply odd_add.mpr
    apply iff_of_true ha hb
lemma odd_add_odd {a b : ℕ} (ha : Odd a) (hb : Odd b) :
  Even (a + b)
  := by
    apply even_add.mpr
    apply iff_of_false
    · apply odd_iff_not_even.mp ha
    · apply odd_iff_not_even.mp hb

lemma one_le_of_odd {n : ℕ} (h : Odd n) :
  1 ≤ n
  := by
    apply one_le_iff_ne_zero.mpr
    contrapose h
    apply even_iff_not_odd.mp
    apply not_ne_iff.mp at h
    rw [h]
    apply even_zero
lemma pos_of_odd {n : ℕ} (h : Odd n) :
  0 < n
  :=
    pos_iff_one_le.mpr (one_le_of_odd h)
lemma ne_zero_of_odd {n : ℕ} (h : Odd n) :
  n ≠ 0
  :=
    one_le_iff_ne_zero.mp (one_le_of_odd h)

lemma odd_iff_eq_even_add_one {n : ℕ} :
  Odd n ↔ ∃ k, Even k ∧ n = k + 1
  := by
    constructor
    · intro hn
      use n - 1
      constructor
      · apply Nat.Odd.sub_odd hn odd_one
      · rw [← Nat.sub_add_comm (one_le_of_odd hn)]
        simp
    · rintro ⟨k, ⟨hk, hn⟩⟩
      rw [hn]
      apply even_add_odd hk odd_one


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

lemma ModEq.add_left_erase {a b m : ℕ} (h : m + a ≡ b [MOD m]) :
  a ≡ b [MOD m]
  := by
    sorry
lemma ModEq.add_left_mul_erase {a b m k : ℕ} (h : k*m + a ≡ b [MOD m]) :
  a ≡ b [MOD m]
  := by
    sorry
lemma ModEq.add_left_pow_erase {a b m k : ℕ} (hk : k > 0) (h : m^k + a ≡ b [MOD m]) :
  a ≡ b [MOD m]
  := by
    sorry
lemma ModEq.sub_erase {a b m : ℕ} (h : a - m ≡ b [MOD m]) :
  a ≡ b [MOD m]
  := by
    sorry
lemma ModEq.sub_mul_erase {a b m k : ℕ} (h : a - k*m ≡ b [MOD m]) :
  a ≡ b [MOD m]
  := by
    sorry
lemma ModEq.sub_pow_erase {a b m k : ℕ} (h : a - m^k ≡ b [MOD m]) (hk : k > 0) :
  a ≡ b [MOD m]
  := by
    sorry

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
 - Primes
 -/

lemma Nat.Prime.two_dvd {p : ℕ} (hp : p.Prime) (hp' : p > 2) :
  2 ∣ p-1
  := by
    sorry

lemma Nat.Prime.dvd_iff_dvd_pow {a b p : ℕ} (hp : p.Prime) (hb : b > 0) :
  p ∣ a ↔ p ∣ a^b
  := by
    constructor
    · intro h
      apply dvd_pow h (Nat.pos_iff_ne_zero.mp hb)
    · apply Prime.dvd_of_dvd_pow hp


/-
 - Coprimes
 -/

lemma exists_dvd_of_not_coprime {a b : ℕ} (h : ¬Coprime a b) :
  ∃ d > 1, d ∣ a ∧ d ∣ b
  := by
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · use 2
        rw [ha, hb]
        simp
      · use b
        constructor
        · apply one_lt_iff_ne_zero_and_ne_one.mpr
          constructor
          · apply hb
          · contrapose h
            apply not_ne_iff.mp at h
            rw [not_not, ha]
            apply (coprime_zero_left b).mpr h
        · rw [ha]
          simp
    · use Nat.gcd a b
      constructor
      · rw [Coprime] at h
        apply one_lt_iff_ne_zero_and_ne_one.mpr
        constructor
        · contrapose ha
          apply not_ne_iff.mp at ha
          apply Nat.gcd_eq_zero_iff.mp at ha
          rcases ha with ⟨left, _⟩
          rw [not_not]
          exact left
        · apply h
      · apply Nat.gcd_dvd

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
lemma coprime_pow_iff {a b n : ℕ} (hb : b > 0) :
  Coprime (a^b) n ↔ Coprime a n
  := by
    constructor
    · contrapose
      intro h
      apply exists_dvd_of_not_coprime at h
      rcases h with ⟨d, hd, ⟨ha, hn⟩⟩
      apply pos_iff_ne_zero.mp at hb
      apply dvd_pow (n := b) at ha
      apply ha at hb
      apply not_coprime_of_dvd_of_dvd hd hb hn
    · intro h
      rw [pow_eq_prod_const]
      apply Coprime.prod_left
      rintro _ _
      apply h
lemma coprime_pow {a b n : ℕ} (ha : Coprime a n) :
  Coprime (a^b) n
  := by
    by_cases hb : b = 0
    · rw [hb, Nat.pow_zero]
      apply coprime_one_left
    · apply pos_iff_ne_zero.mpr at hb
      apply (coprime_pow_iff hb).mpr ha

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
