
import Mathlib
import Playground.Logic
import Playground.SetTheory
import Playground.NumberTheory.Basic
import Playground.NumberTheory.QuadraticResidues

open Nat

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

def PrimitiveRoot (a p : ℕ) :=
  ord a p = p - 1

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

theorem mckinley's (a p : ℕ) (hp : p.Prime) (h : ∃ k, p = 2^k + 1) :
  QuadraticNonresidue a p -> PrimitiveRoot a p
  := by
    intro a_qnr
    have ha : Coprime a p := by
      rcases coprime_or_dvd_of_prime hp a with left | right
      · rw [coprime_comm] at left
        exact left
      · have : a ≡ 0 [MOD p] := by
          rw [ModEq, zero_mod]
          apply mod_eq_zero_of_dvd right
        have : QuadraticResidue a p := by
          use 0
          rw [zero_pow (by norm_num)]
          symm
          exact this
        contradiction
    rcases h with ⟨k, h⟩
    have : p = 2 ∨ p ≠ 2 := by
      apply eq_or_ne
    rcases this with eq_two | ne_two
    -- p = 2 case
    · exfalso
      rw [eq_two] at a_qnr
      have a_qr : QuadraticResidue a 2 := two_has_only_qrs a
      contradiction
    -- p ≠ 2 case
    have ge_two : 2 < p := by
      apply lt_of_le_of_ne
      . apply Nat.Prime.two_le hp
      · apply ne_two.symm
    have k_ge_one : k ≥ 1 := by
      rw [h] at ge_two
      contrapose ge_two with lt_one
      apply lt_of_not_ge at lt_one
      apply lt_one_iff.mp at lt_one
      rw [lt_one]
      norm_num
    have : (ord a p) ∣ 2^k := calc
      (ord a p) ∣ (p - 1)           := by apply ord_dvd_p_sub_one hp ha
      _         = 2^k               := by rw [h]; simp
    apply (Nat.dvd_prime_pow prime_two).mp at this
    rcases this with ⟨r, ⟨r_le_k, hr⟩⟩
    have : r < k ∨ r = k := by
      apply lt_or_eq_of_le r_le_k
    rcases this with r_lt_k | r_eq_k
    -- r < k case. Use contradiction.
    · exfalso
      have : p - 1 ≡ 1 [MOD p] := calc
        p - 1 = legendre a p              := by rw [← legendre_qnr_eq_p_sub_one a_qnr]
        _     ≡ a^((p-1)/2) [MOD p]       := legendre_cong_pow_p_sub_one_div_two hp
        _     = (a^2^r)^2^(k-r-1)         := by
                                            rw [h]
                                            ring_nf
                                            congr
                                            rw [Nat.one_add_sub_one, ← pow_add]
                                            nth_rw 2 [← pow_one 2]
                                            rw [pow_div k_ge_one (by norm_num)]
                                            congr
                                            have : 0 < k - r := Nat.zero_lt_sub_of_lt r_lt_k
                                            apply one_le_of_lt at this
                                            rw [
                                              ← Nat.add_sub_assoc this r,
                                              Nat.add_sub_of_le r_le_k,
                                            ]
        _     = (a^(ord a p))^2^(k-r-1)   := by rw [hr]
        _     ≡ 1^2^(k-r-1) [MOD p]       := by apply ModEq.pow; apply pow_ord
        _     = 1                         := by rw [one_pow]
      -- We have 1 ≡ -1 [MOD p], which is impossible because p > 2
      have : p ≡ 2 [MOD p] := by
        apply ModEq.add_right 1 at this
        rw [Nat.sub_add_cancel (by linarith), one_add_one_eq_two] at this
        exact this
      have : 0 ≡ 2 [MOD p] := calc
        0 ≡ p [MOD p]       := Dvd.dvd.zero_modEq_nat dvd_rfl
        _ ≡ 2 [MOD p]       := this
      have : p ∣ 2 := by
        apply (Nat.modEq_iff_dvd' (by norm_num)).mp at this
        rw [Nat.sub_zero] at this
        exact this
      apply (Nat.dvd_prime prime_two).mp at this
      rcases this with one | two
      · linarith
      · linarith
    -- r = k case
    have : ord a p = p - 1 := by
      nth_rw 2 [h]
      rw [hr, r_eq_k]
      congr
    exact this



-- Turn hp into a Fact so that ord will be defined
    -- apply fact_iff.mpr at hp


/-
p = 7

d   = 0 1 2 3 4 5 6 7 8 9
1^d = 1 1 1 1 1 1 1 1 1 1         period = 1
2^d = 1 2 4 1 2 4 1 2 4 1         period = 3
3^d = 1 3 2 6 4 5 1 3 2 6 4 5     period = 6
4^d = 1 4 2 1 4 2 1 4 2 1 4 2     period = 3
5^d = 1 5 4 6 2 3 1 5 4 6 2 3     period = 6
6^d = 1 6 1 6 1 6 1 6 1 6 1 6     period = 2

When p is prime, the period always divides p - 1
A primitive root is a value whose period is p - 1

a     a^2
0     0
1     1
2     4
3     2
4     2
5     4
6     1
7     0
8     1
9     4

Present: 0, 1, 2, 4     (quadratic residues)
Not present: 3, 5, 6    (quadratic nonresidues)


p = 5 = 2^2 + 1

d   = 0 1 2 3 4
1^d = 1 1 1 1 1 1 1 1     period: 1
2^d = 1 2 4 3 1 2 4 3     period: 4
3^d = 1 3 4 2 1 3 4 2     period: 4
4^d = 1 4 1 4 1 4 1 4     period: 2

Primitive roots: 2, 3

a     a^2
0     0
1     1
2     4
3     4
4     1
5     0

Present: 0, 1, 4     (quadratic residues)
Not present: 2, 3    (quadratic nonresidues)


p = 2

a   a^2
0   0
1   1
2   0
3   1

0 1 are quadratic residues



-/
