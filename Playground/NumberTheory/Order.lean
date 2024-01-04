
import Mathlib
import Playground.Logic
import Playground.NumberTheory.Basic

open Nat Finset BigOperators

lemma exists_ord (a m : ℕ) (ha : Coprime a m) :
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
    Nat.find (exists_ord a m hm)
  else
    0

lemma ord_pos {a m : ℕ} (hm : Coprime a m) :
  ord a m > 0
  := by
    have : (ord a m) > 0 ∧ a^(ord a m) ≡ 1 [MOD m] := by
      rw [ord, dite_true' hm]
      apply Nat.find_spec (exists_ord a m hm)
    rcases this with ⟨left, _⟩
    exact left

lemma pow_ord {a m : ℕ} :
  a^(ord a m) ≡ 1 [MOD m]
  := by
    by_cases hm : (Coprime a m)
    · have : (ord a m) > 0 ∧ a^(ord a m) ≡ 1 [MOD m] := by
        rw [ord, dite_true' hm]
        apply Nat.find_spec (exists_ord a m hm)
      rcases this with ⟨_, right⟩
      exact right
    · rw [ord, dite_false' hm, Nat.pow_zero]

lemma ord_min {a n m : ℕ} (hn : 0 < n ∧ n < ord a m) :
  a^n ≢ 1 [MOD m]
  := by
    sorry


/-
 - Primitive Roots
 -/

@[reducible]
def PrimitiveRoot (a p : ℕ) :=
  ord a p = p - 1

def Nat.primitive_roots (p : ℕ) : Finset ℕ
  := filter (fun x => PrimitiveRoot x p) (range p)

lemma primitive_root_min {r n p : ℕ} (hp : p.Prime) (hr : PrimitiveRoot r p) (hn : 0 < n ∧ n < p-1) :
  r^n ≢ 1 [MOD p]
  := by
    
    sorry

lemma coprime_of_primitive_root {r p : ℕ} (hp : p.Prime) (hr : PrimitiveRoot r p) :
  Coprime r p
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

theorem ord_pow {a b m : ℕ} :
  ord (a^b) m = (ord a m) / (Nat.gcd b m)
  := by
    sorry

theorem ord_pow_eq_iff_coprime {a b m : ℕ} (ha : Coprime a m) :
  ord (a^b) m = ord a m ↔ Coprime b m
  := calc
    ord (a^b) m = ord a m
    _ ↔ (ord a m) / (Nat.gcd b m) = ord a m     := by rw [ord_pow]
    _ ↔ ord a m = 0 ∨ Nat.gcd b m = 1           := Nat.div_eq_self
    _ ↔ Nat.gcd b m = 1                         := by
                                                  have : ord a m ≠ 0 := pos_iff_ne_zero.mp (ord_pos ha)
                                                  rw [eq_false this]
                                                  apply false_or_iff
    _ ↔ Coprime b m                             := by apply Nat.coprime_iff_gcd_eq_one

theorem ord_pow_of_coprime {a b m : ℕ} (hb : Coprime b m) :
  ord (a^b) m = ord a m
  := by
    by_cases ha : Coprime a m
    · apply (ord_pow_eq_iff_coprime ha).mpr hb
    · by_cases hb' : b = 0
      · exfalso
        rw [hb'] at hb
        apply (coprime_zero_left m).mp at hb
        rw [hb] at ha
        have : Coprime a 1 := coprime_one_right a
        contradiction
      · apply pos_iff_ne_zero.mpr at hb'
        rw [ord, ord]
        have hab : ¬Coprime (a^b) m := by
          contrapose ha
          rw [not_not]
          rw [not_not] at ha
          apply (coprime_pow_iff hb').mp ha
        rw [dite_false' ha, dite_false' hab]

-- The number of elements of order t is totient(t)
theorem ord_count {p t : ℕ} (hp : p.Prime) (ht : t ∣ p-1) :
  card (filter (fun x => ord x p = t) (range p)) = φ t
  := by
    let c (m : ℕ) := card (filter (fun x => ord x p = m) (range p))
    have zero_or_eq (m : ℕ) (hm : m < p) : c m = 0 ∨ c m = φ m := by
      by_cases hc : c m = 0
      · left
        exact hc
      · right
        have a : ℕ := by sorry
        have ha : ord a p = m := by sorry
        
        sorry
    have le (m : ℕ) : c m ≤ φ m := by sorry
    sorry

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
