
import Mathlib
import Playground.Logic
import Playground.SetTheory
import Playground.NumberTheory.Basic
import Playground.NumberTheory.QuadraticResidues
import Playground.NumberTheory.Order

open Nat

theorem mckinley's (a p : ℕ) (hp : p.Prime) (h : ∃ k, p = 2^k + 1) :
  QuadraticNonresidue a p -> PrimitiveRoot a p
  := by
    intro a_qnr
    have ha : Coprime a p := by
      rcases coprime_or_dvd_of_prime hp a with left | right
      · rw [coprime_comm] at left
        exact left
      · exfalso
        have : a ≡ 0 [MOD p] := by
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
