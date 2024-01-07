
import Mathlib
import Playground.Logic
import Playground.NumberTheory.Basic

open Nat Finset BigOperators

lemma exists_ord {a m : ℕ} (ha : Coprime a m) :
  ∃ d > 0, a^d ≡ 1 [MOD m]
  := by
    by_cases hm : m = 0
    · use 1
      constructor
      · norm_num
      · have : a = 1 := by
          apply eq_one_of_dvd_coprimes (a := a) (b := m) ha
          · apply dvd_rfl
          · rw [hm]
            apply dvd_zero
        rw [this, pow_one]
    · use φ m
      apply Nat.pos_of_ne_zero at hm
      constructor
      · apply totient_pos hm
      · apply euler's_totient_theorem hm ha

def ord (a m : ℕ) : ℕ :=
  if hm : Coprime a m then
    Nat.find (exists_ord hm)
  else
    0

lemma ord_pos {a m : ℕ} (hm : Coprime a m) :
  ord a m > 0
  := by
    have : (ord a m) > 0 ∧ a^(ord a m) ≡ 1 [MOD m] := by
      rw [ord, dite_true' hm]
      apply Nat.find_spec (exists_ord hm)
    rcases this with ⟨left, _⟩
    exact left

lemma pow_ord {a m : ℕ} :
  a^(ord a m) ≡ 1 [MOD m]
  := by
    by_cases hm : (Coprime a m)
    · have : (ord a m) > 0 ∧ a^(ord a m) ≡ 1 [MOD m] := by
        rw [ord, dite_true' hm]
        apply Nat.find_spec (exists_ord hm)
      rcases this with ⟨_, right⟩
      exact right
    · rw [ord, dite_false' hm, Nat.pow_zero]

lemma ord_min {a n m : ℕ} (hn₁ : 0 < n) (hn₂ : n < ord a m) :
  a^n ≢ 1 [MOD m]
  := by
    rw [ord] at hn₂
    by_cases ha : Coprime a m
    · rw [dite_true' ha] at hn₂
      apply Nat.find_min at hn₂
      apply not_and_or.mp at hn₂
      rcases hn₂ with left | right
      · contradiction
      · exact right
    · exfalso
      rw [dite_false' ha] at hn₂
      contradiction


/-
 - Primitive Roots
 -/

@[reducible]
def PrimitiveRoot (a m : ℕ) :=
  ord a m = m - 1

def Nat.primitive_roots (m : ℕ) : Finset ℕ
  := filter (fun x => PrimitiveRoot x m) (range m)

lemma primitive_root_min {r n m : ℕ} (hr : PrimitiveRoot r m) (hn₁ : 0 < n) (hn₂ : n < m-1) :
  r^n ≢ 1 [MOD m]
  := by
    rw [PrimitiveRoot] at hr
    rw [← hr] at hn₂
    apply ord_min hn₁ hn₂

theorem coprime_of_primitive_root {r m : ℕ} (hm : 1 < m) (hr : PrimitiveRoot r m) :
  Coprime r m
  := by
    contrapose hr
    rw [PrimitiveRoot, ord, dite_false' hr]
    have : 0 < m - 1 := by
      simp [hm]
    apply Nat.ne_of_lt this
theorem Nat.Prime.coprime_of_primitive_root {r p : ℕ} (hp : p.Prime) (hr : PrimitiveRoot r p) :
  Coprime r p
  := by
    apply _root_.coprime_of_primitive_root (Prime.one_lt hp) hr

theorem ord_dvd_of_pow_cong_one {a b m : ℕ} (h : a^b ≡ 1 [MOD m]) :
  ord a m ∣ b
  := by
    sorry

theorem ord_dvd_p_sub_one {a p : ℕ} (hp : p.Prime) (ha : Coprime a p) :
  (ord a p) ∣ p-1
  := by
    let k := (p-1) % ord a p
    let j := (p-1) / ord a p
    have k_lt : k < ord a p := by
      dsimp only [k]
      apply mod_lt
      apply ord_pos ha
    have : p - 1 = k + j * ord a p := by
      dsimp
      rw [mul_comm, Nat.mod_add_div (p-1) (ord a p)]
    have hk : a^k ≡ 1 [MOD p] := calc
      a^k ≡ a^k * (a^(ord a p))^j [MOD p]   := by
                                              nth_rw 1 [← mul_one (a^k)]
                                              apply ModEq.mul_left (a^k)
                                              rw [
                                                ModEq,
                                                pow_mod,
                                                pow_ord,
                                                ← pow_mod,
                                                one_pow
                                              ]
      _   = a^(k + j * (ord a p))           := by
                                              rw [← pow_mul, ← pow_add, mul_comm]
      _   = a^(p-1)                         := by
                                              congr
                                              linarith
      _   ≡ 1 [MOD p]                       := fermat's_little_theorem hp ha
    rw [ord, dite_true' ha] at k_lt
    have : ¬(k > 0 ∧ a^k ≡ 1 [MOD p]) := Nat.find_min (exists_ord a p ha) k_lt
    apply not_and_or.mp at this
    rcases this with left | right
    · simp at left
      apply (dvd_iff_mod_eq_zero (ord a p) (p - 1)).mpr left
    · exfalso
      contradiction

theorem pow_mod_ord {a k m : ℕ} :
  a^(k % (ord a m)) ≡ a^k [MOD m]
  := by
    let o := ord a m
    symm
    calc
      a^k
      _ = a^(o * (k/o) + k%o)           := by rw [div_add_mod k o]
      _ = (a^o)^(k/o) * a^(k%o)         := by rw [pow_add, pow_mul]
      _ ≡ 1^(k/o) * a^(k%o) [MOD m]     := by
                                          apply ModEq.mul_right
                                          apply ModEq.pow
                                          exact pow_ord
      _ = a^(k % o)                     := by rw [one_pow, one_mul]

theorem eq_of_pow_cong_pow_of_lt_of_lt {a k j m : ℕ} (ha : Coprime a m) (h : a^k ≡ a^j [MOD m]) (hk : k < ord a m) (hj : j < ord a m) :
  k = j
  := by
    apply Classical.by_contradiction
    intro hkj
    change k ≠ j at hkj
    wlog lt : k < j
    · specialize this (a := a) (k := j) (j := k) (m := m) ha h.symm hj hk hkj.symm
      rw [not_lt] at lt
      have lt' : j < k := lt_of_le_of_ne lt hkj.symm
      apply this lt'
    · apply exists_pos_eq_add_of_lt at lt
      rcases lt with ⟨d, ⟨hd, hjkd⟩⟩
      rw [hjkd, pow_add] at h
      nth_rw 1 [← mul_one (a^k)] at h
      have hak : Coprime (a^k) m := coprime_pow ha
      apply ModEq.cancel_left_of_coprime hak.symm at h
      have hdj : d ≤ j := by
        simp [hjkd]
      have hd' : d < ord a m := lt_of_le_of_lt hdj hj
      have : a^d ≢ 1 [MOD m] := ord_min hd hd'
      symm at h
      contradiction

theorem pow_cong_pow_iff_cong {a k j m : ℕ} (ha : Coprime a m) :
  a^k ≡ a^j [MOD m] ↔ k ≡ j [MOD ord a m]
  := by
    let o := ord a m
    constructor
    · intro h
      rw [ModEq]
      have hk : k % o < o := mod_lt _ (ord_pos ha)
      have hj : j % o < o := mod_lt _ (ord_pos ha)
      have : a^(k%o) ≡ a^(j%o) [MOD m] := calc
        a^(k%o)
        _ ≡ a^k [MOD m]       := pow_mod_ord
        _ ≡ a^j [MOD m]       := h
        _ ≡ a^(j%o) [MOD m]   := pow_mod_ord.symm
      apply eq_of_pow_cong_pow_of_lt_of_lt ha this hk hj
    · intro h
      rw [ModEq] at h
      calc
        a^k
        _ ≡ a^(k % o) [MOD m]       := by
                                      symm
                                      apply pow_mod_ord
        _ = a^(j % o)               := by rw [h]
        _ ≡ a^j       [MOD m]       := pow_mod_ord

/-
 - Page 92 of https://resources.saylor.org/wwwresources/archived/site/wp-content/uploads/2013/05/An-Introductory-in-Elementary-Number-Theory.pdf
 -/
theorem ord_pow {a b m : ℕ} (hb : 0 < b):
  ord (a^b) m = (ord a m) / (Nat.gcd b (ord a m))
  := by
    let t := ord a m
    let g := Nat.gcd b t
    let t' := t / g
    let b' := b / g
    let x := ord (a^b) m
    show x = t'
    have g_pos : 0 < g := Nat.gcd_pos_of_pos_left _ hb
    have g_dvd_b : g ∣ b := by apply Nat.gcd_dvd_left
    have g_dvd_t : g ∣ t := by apply Nat.gcd_dvd_right
    have t'_b' : Coprime t' b' := by
      unfold_let t' b' g
      apply coprime_comm.mp
      apply coprime_div_gcd_div_gcd
      apply g_pos
    have h₁ : (a^b)^t' ≡ 1 [MOD m] := calc
      (a^b)^t'
      _ = (a^(b' * g))^(t / g)      := by
                                      unfold_let b' t'
                                      rw [Nat.div_mul_cancel g_dvd_b]
      _ = (a^t)^b'                  := by
                                      rw [
                                        ← pow_mul,
                                        mul_assoc,
                                        ← Nat.mul_div_assoc _ g_dvd_t,
                                        Nat.mul_div_cancel_left _ g_pos,
                                        pow_mul'
                                      ]
      _ ≡ 1^b' [MOD m]              := by
                                      apply ModEq.pow
                                      apply pow_ord
      _ = 1                         := one_pow _
    have h₂ : t' ∣ x := by
      have : a^(b*x) ≡ 1 [MOD m] := calc
        a^(b*x)
        _ = (a^b)^x                 := by apply pow_mul
        _ ≡ 1 [MOD m]               := pow_ord
      apply ord_dvd_of_pow_cong_one at this
      have : t'*g ∣ b'*g*x := by
        unfold_let t' b'
        rw [Nat.div_mul_cancel g_dvd_t, Nat.div_mul_cancel g_dvd_b]
        exact this
      rw [mul_comm, mul_comm b', mul_assoc] at this
      apply Nat.dvd_of_mul_dvd_mul_left g_pos at this
      apply (Coprime.dvd_mul_left t'_b').mp this
    apply ord_dvd_of_pow_cong_one at h₁
    apply dvd_antisymm h₁ h₂

-- theorem ord_pow_eq_iff_coprime {a b m : ℕ} (ha : Coprime a m) :
--   ord (a^b) m = ord a m ↔ Coprime b m
--   := calc
--     ord (a^b) m = ord a m
--     _ ↔ (ord a m) / (Nat.gcd b m) = ord a m     := by rw [ord_pow]
--     _ ↔ ord a m = 0 ∨ Nat.gcd b m = 1           := Nat.div_eq_self
--     _ ↔ Nat.gcd b m = 1                         := by
--                                                   have : ord a m ≠ 0 := pos_iff_ne_zero.mp (ord_pos ha)
--                                                   rw [eq_false this]
--                                                   apply false_or_iff
--     _ ↔ Coprime b m                             := by apply Nat.coprime_iff_gcd_eq_one

-- theorem ord_pow_of_coprime {a b m : ℕ} (hb : Coprime b m) :
--   ord (a^b) m = ord a m
--   := by
--     by_cases ha : Coprime a m
--     · apply (ord_pow_eq_iff_coprime ha).mpr hb
--     · by_cases hb' : b = 0
--       · exfalso
--         rw [hb'] at hb
--         apply (coprime_zero_left m).mp at hb
--         rw [hb] at ha
--         have : Coprime a 1 := coprime_one_right a
--         contradiction
--       · apply pos_iff_ne_zero.mpr at hb'
--         rw [ord, ord]
--         have hab : ¬Coprime (a^b) m := by
--           contrapose ha
--           rw [not_not]
--           rw [not_not] at ha
--           apply (coprime_pow_iff hb').mp ha
--         rw [dite_false' ha, dite_false' hab]

-- The number of elements of order t is φ(t)
theorem ord_count {p t : ℕ} (hp : p.Prime) (ht : t ∣ p-1) :
  card (filter (fun x => ord x p = t) (Ico 1 p)) = φ t
  := by
    let divs := (p - 1).divisors
    -- bucket(d) = the set of incongruent residues that have order d
    let bucket (d : ℕ) := filter (fun x => ord x p = d) (Ico 1 p)
    -- buckets = the set of all buckets
    let buckets := image bucket divs
    -- c(d) = size of bucket(d) = the number of incongruent residues that have order d
    let c (d : ℕ) := card (bucket d)
    have zero_or_eq (d : ℕ) (hd : d ∣ p-1) : c d = 0 ∨ c d = φ d := by
      by_cases hc : c d = 0
      · left
        exact hc
      · right
        apply pos_iff_ne_zero.mpr at hc
        apply card_pos.mp at hc
        rw [Finset.Nonempty] at hc
        rcases hc with ⟨a, ha⟩
        rw [mem_filter] at ha
        rcases ha with ⟨ha, ha'⟩
        /-
         ord (a^b) p = (ord a o) / (Nat.gcd b (ord a p))
         
         ord a p = d
         for each k coprime with d:
         ord (a^k) p = d
         
         Goal: a^k are all incongruent
         For every k, j coprime with d:
         a^k ≢ a^j [MOD p]
         
         If ord b p = d:
           b^d ≡ 1
           
         
         -/
        let pows := image (fun k => a^k % p) d.coprimes
        have subset : pows ⊆ bucket d := by
          sorry
        have card_pows : card pows = φ d := by
          sorry
        sorry
    have le (d : ℕ) (hd : d ∣ p-1) : c d ≤ φ d := by
      rcases zero_or_eq d hd with zero | eq
      · rw [zero]
        apply Nat.zero_le
      · rw [eq]
    have sum_c : ∑ d in divs, c d = p - 1 := by
      rw [← card_Ico 1 p]
      symm
      apply Finset.card_eq_sum_card_fiberwise
      intro x hx
      apply Nat.mem_divisors.mpr
      constructor
      · apply ord_dvd_p_sub_one hp
        rw [coprime_comm]
        apply mem_Ico.mp at hx
        rcases hx with ⟨left, right⟩
        apply coprime_of_lt_prime (pos_iff_one_le.mpr left) right hp
      · simp
        apply Prime.one_lt hp
    have sum_φ : ∑ d in divs, φ d = p - 1 := by
      rw [sum_totient]
    have sum_c_eq_sum_φ : ∑ d in divs, c d = ∑ d in divs, φ d := by
      rw [sum_c, sum_φ]
    apply all_eq_of_sum_eq_of_all_le sum_c_eq_sum_φ
    · intro x hx
      apply Finset.mem_filter.mp at hx
      rcases hx with ⟨_, right⟩
      apply le x right
    · apply Finset.mem_filter.mpr
      constructor
      · rw [mem_Ico]
        constructor
        · apply pos_iff_one_le.mp
          apply pos_of_dvd_of_pos ht
          simp
          apply Prime.one_lt hp
        · rw [← Nat.sub_add_comm (Prime.one_le hp)]
          apply lt_of_dvd_sub (Prime.one_lt hp) ht
      · exact ht

theorem primitive_root_count {p : ℕ} (hp : p.Prime) :
  card p.primitive_roots = φ (p - 1)
  := by
    sorry

theorem exists_primitive_root {p : ℕ} (hp : p.Prime) :
  ∃ a < p, PrimitiveRoot a p
  := by
    sorry

theorem cong_primitive_root_pow {a p : ℕ} (hp : p.Prime) (ha : Coprime a p) :
  ∃ r < p, PrimitiveRoot r p ∧ ∃ k > 0, r^k ≡ a [MOD p]
  := by
    sorry
