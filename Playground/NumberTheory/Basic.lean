
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

lemma lt_of_dvd_sub {a n : ℕ} (hn : 1 < n) (ha : a ∣ n-1) :
  a < n
  := by
    apply le_of_dvd at ha
    · apply lt_of_le_pred _ ha
      simp
      apply lt_trans zero_lt_one hn
    · simp
      apply hn
lemma mem_range_of_dvd_sub {a n : ℕ} (hn : 1 < n) (ha : a ∣ n-1) :
  a ∈ range n
  :=
    Finset.mem_range.mpr (lt_of_dvd_sub hn ha)

lemma Nat.exists_pos_eq_add_of_lt {a b : ℕ} (h : a < b) :
  ∃ k > 0, b = a + k
  := by
    apply exists_eq_add_of_lt at h
    rcases h with ⟨k, hk⟩
    use k + 1
    constructor
    · simp
    · rw [hk]
      ring

lemma Finset.range_eq_insert_zero_Ico_one {n : ℕ} (h : n > 0) :
  range n = insert 0 (Ico 1 n)
  := by
    rw [range_eq_Ico, one_eq_succ_zero, Ico_insert_succ_left h]


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

lemma even_sub_one_of_odd {n : ℕ} (hn : Odd n) :
  Even (n - 1)
  := by
    apply odd_iff_eq_even_add_one.mp at hn
    rcases hn with ⟨k, hk, h⟩
    rw [h]
    simp
    exact hk


/-
 - Custom Operators
 -/

@[simp]
def NotModEq (n a b : ℕ) :=
  ¬(a ≡ b [MOD n])
notation:50 a:50 " ≢ " b:50 " [MOD " n:50 "]" => NotModEq n a b

@[simp]
def NotDvd (a b : ℕ) :=
  ¬(a ∣ b)
notation:50 a:50 " ∤ " b:50 => NotDvd a b


/-
 - Modular Equality
 -/

lemma ModEq.card {m : ℕ} :
  m ≡ 0 [MOD m]
  := by
    apply Dvd.dvd.modEq_zero_nat (dvd_refl m)
lemma ModEq.mul_card {k m : ℕ} :
  k * m ≡ 0 [MOD m]
  := by
    apply Dvd.dvd.modEq_zero_nat (dvd_mul_left m k)
lemma ModEq.card_pow {m k : ℕ} (hk : k > 0) :
  m^k ≡ 0 [MOD m]
  := by
    apply pos_iff_ne_zero.mp at hk
    apply Dvd.dvd.modEq_zero_nat
    apply dvd_pow (dvd_refl m) hk

lemma ModEq.add_left_erase {a b m : ℕ} :
  m + a ≡ b [MOD m] ↔ a ≡ b [MOD m]
  := by
    sorry
lemma ModEq.add_left_mul_erase {a b m k : ℕ} :
  k*m + a ≡ b [MOD m] ↔ a ≡ b [MOD m]
  := by
    sorry
lemma ModEq.add_left_pow_erase {a b m k : ℕ} (hk : k > 0) :
  m^k + a ≡ b [MOD m] ↔ a ≡ b [MOD m]
  := by
    sorry
lemma ModEq.sub_erase {a b m : ℕ} :
  a - m ≡ b [MOD m] ↔ a ≡ b [MOD m]
  := by
    sorry
lemma ModEq.sub_mul_erase {a b m k : ℕ} :
  a - k*m ≡ b [MOD m] ↔ a ≡ b [MOD m]
  := by
    sorry
lemma ModEq.sub_pow_erase {a b m k : ℕ} (hk : k > 0) :
  a - m^k ≡ b [MOD m] ↔ a ≡ b [MOD m]
  := by
    sorry

lemma ModEq.mod_zero_iff {a b : ℕ} :
  a ≡ b [MOD 0] ↔ a = b
  := by
    rw [ModEq, mod_zero, mod_zero]
lemma ModEq.not_mod_zero_iff {a b : ℕ} :
  a ≢ b [MOD 0] ↔ a ≠ b
  := by
    rw [NotModEq, ModEq, mod_zero, mod_zero]

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

lemma Nat.Prime.one_le {p : ℕ} (hp : p.Prime) :
  1 ≤ p
  :=
    le_of_lt (Prime.one_lt hp)

lemma Nat.Prime.two_dvd {p : ℕ} (hp : p.Prime) (hp' : p > 2) :
  2 ∣ p-1
  := by
    apply ne_of_lt at hp'
    symm at hp'
    apply Prime.odd_of_ne_two hp at hp'
    apply even_sub_one_of_odd at hp'
    apply even_iff_two_dvd.mp hp'

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
lemma coprime_mod_iff {a n : ℕ} :
  Coprime a n ↔ Coprime (a % n) n
  := by
    constructor
    · exact coprime_mod
    · intro h
      rw [Coprime, ← gcd_rec, Nat.gcd_comm] at h
      rw [Coprime, h]
lemma coprime_mod_eq {a b m : ℕ} (h : a ≡ b [MOD m]) (ha : Coprime a m) :
  Coprime b m
  := by
    rw [ModEq] at h
    apply coprime_mod_iff.mp at ha
    rw [h] at ha
    apply coprime_mod_iff.mpr at ha
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

lemma not_coprime_iff_cong_zero {a p : ℕ} (hp : p.Prime) :
  ¬Coprime a p ↔ a ≡ 0 [MOD p]
  := calc
    ¬Coprime a p
    _ ↔ p ∣ a           := by
                          symm
                          rw [coprime_comm]
                          apply Prime.dvd_iff_not_coprime hp
    _ ↔ a ≡ 0 [MOD p]   := by
                          dsimp only [ModEq]
                          rw [zero_mod]
                          apply dvd_iff_mod_eq_zero
lemma coprime_iff_ncong_zero {a p : ℕ} (hp : p.Prime) :
  Coprime a p ↔ a ≢ 0 [MOD p]
  := by
    apply not_iff_not.mp
    rw [NotModEq, Classical.not_not]
    apply not_coprime_iff_cong_zero hp

lemma coprime_of_mod_eq_one {a m : ℕ} (hm : m ≠ 1) (ha : a % m = 1) :
  Coprime a m
  := by
    apply coprime_of_mul_modEq_one 1
    rw [mul_one, ModEq, one_mod_of_ne_one hm]
    exact ha

lemma coprime_of_cong_one {a m : ℕ} (ha : a ≡ 1 [MOD m]) :
  Coprime a m
  := by
    by_cases hm : m = 1
    · rw [hm]
      apply coprime_one_right
    · rw [ModEq, one_mod_of_ne_one hm] at ha
      apply coprime_of_mod_eq_one hm ha

lemma coprime_of_mem_Ico {a p : ℕ} (hp : p.Prime) (ha : a ∈ Ico 1 p) :
  Coprime a p
  := by
    rw [mem_Ico] at ha
    apply Coprime.symm
    apply coprime_of_lt_prime (pos_iff_one_le.mpr ha.left) ha.right hp

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
lemma mem_coprimes₃ {a n : ℕ} (hn : n ≠ 1) (ha : a ∈ n.coprimes) :
  0 < a
  := by
    apply (mem_filter (s := (range n))).mp at ha
    rcases ha with ⟨_, right⟩
    contrapose hn with ha
    simp at ha
    rw [ha, coprime_zero_left] at right
    simp [right]

lemma totient_eq_card_coprimes (n : ℕ) :
  φ n = card n.coprimes
  := by
    rw [totient, coprimes]
    congr
    change (fun x => Coprime n x) = (fun x => Coprime x n)
    simp [coprime_comm]

lemma not_dvd_of_coprime {a m : ℕ} (hm : m ≠ 1) (ha : Coprime a m) :
  m ∤ a
  := by
    contrapose ha
    rw [NotDvd, Classical.not_not, Nat.gcd_eq_right_iff_dvd] at ha
    rw [Coprime, ha]
    exact hm

lemma mod_pos_iff_not_dvd {a m : ℕ} :
  0 < a % m ↔ m ∤ a
  := by
    rw [
      pos_iff_ne_zero,
      ← not_iff_not,
      NotDvd,
      Classical.not_not,
      Classical.not_not,
    ]
    symm
    apply Nat.dvd_iff_mod_eq_zero
lemma mod_pos_of_coprime {a m : ℕ} (hm : m ≠ 1) (ha : Coprime a m) :
  0 < a % m
  := by
    apply not_dvd_of_coprime hm at ha
    contrapose ha
    apply Nat.eq_zero_of_not_pos at ha
    rw [NotDvd, Classical.not_not]
    apply (Nat.dvd_iff_mod_eq_zero _ _).mpr ha


/-
 - Big Operators
 -/

-- theorem Finset.exists_lt_of_sum_lt_sum {S : Finset α} {f g : α → ℕ} (h : (∑ x in S, f x) < (∑ x in S, g x)) :
--   ∃ x ∈ S, f x < g x
--   := by
--     sorry

theorem Finset.sum_le_of_all_le {S : Finset α} [DecidableEq α] {f g : α → ℕ} (h : ∀ x ∈ S, f x ≤ g x) :
  (∑ x in S, f x) ≤ (∑ x in S, g x)
  := by
    let p (T : Finset α) := ∑ x in T, f x ≤ ∑ x in T, g x
    change p S
    apply Finset.induction_on'
    · simp
    · intros n T hn _ hnT hT
      simp [hnT]
      apply Nat.add_le_add (h n hn)
      exact hT

theorem Finset.sum_lt_of_all_le_of_lt {S : Finset α} [DecidableEq α] {f g : α → ℕ} (h₁ : ∀ x ∈ S, f x ≤ g x) (h₂ : ∃ s ∈ S, f s < g s) :
  (∑ x in S, f x) < (∑ x in S, g x)
  := by
    rcases h₂ with ⟨s, hs, hs'⟩
    let T := erase S s
    have : ∑ x in T, f x ≤ ∑ x in T, g x := by
      apply sum_le_of_all_le
      intro x hx
      apply Finset.mem_erase.mp at hx
      rcases hx with ⟨_, right⟩
      apply h₁ x right
    have : (∑ x in T, f x) + f s < (∑ x in T, g x) + g s :=
      add_lt_add_of_le_of_lt this hs'
    rw [sum_erase_add _ _ hs, sum_erase_add _ _ hs] at this
    exact this

theorem Finset.all_eq_of_sum_eq_of_all_le {S : Finset α} [DecidableEq α] {f g : α → ℕ} (h₁ : ∑ x in S, f x = ∑ x in S, g x) (h₂ : ∀ x ∈ S, f x ≤ g x) :
  ∀ x ∈ S, f x = g x
  := by
    contrapose h₁
    apply not_forall.mp at h₁
    simp at h₁
    rcases h₁ with ⟨s, ⟨hs, hs'⟩⟩
    have le : f s ≤ g s := h₂ s hs
    have lt : f s < g s := lt_of_le_of_ne le hs'
    apply Nat.ne_of_lt
    apply Finset.sum_lt_of_all_le_of_lt h₂
    use s

-- Whoops, accidentally proved Finset.card_eq_sum_card_fiberwise
theorem Finset.sum_card_eq_card_union [DecidableEq α] {I : Finset ℕ} {f : ℕ → Finset α} (h : Set.PairwiseDisjoint I f) :
  ∑ i in I, card (f i) = card (I.biUnion f)
  := by
    let p (J : Finset ℕ) := ∑ i in J, card (f i) = card (J.biUnion f)
    change p I
    apply Finset.induction_on'
    · simp
    · intro n J hnI hJI hnJ hJ
      simp [hnJ]
      simp at hJI
      have h_disjoint : Disjoint (f n) (J.biUnion f) := by
        let q (K : Finset ℕ) := Disjoint (f n) (K.biUnion f)
        change q J
        apply Finset.induction_on'
        · simp
        · intro m K hmJ hKJ hmK hK
          simp
          constructor
          · rw [Set.PairwiseDisjoint, Set.Pairwise] at h
            have hnm : n ≠ m := by
              symm
              apply ne_of_mem_of_not_mem hmJ hnJ
            have hmI : m ∈ I := hJI hmJ
            apply h hnI hmI hnm
          · apply hK
      rw [card_disjoint_union h_disjoint, hJ]


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
