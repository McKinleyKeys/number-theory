
import Mathlib
import Playground.Logic
import Playground.NumberTheory.Basic
import Playground.NumberTheory.Polynomials

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

lemma ord_pos_iff_coprime {a m : ℕ} :
  ord a m > 0 ↔ Coprime a m
  := by
    constructor
    · intro h
      contrapose h
      rw [ord, dite_false' h]
      simp
    · exact ord_pos

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

lemma ord_eq_zero_iff {a m : ℕ} :
  ord a m = 0 ↔ ¬Coprime a m
  := by
    apply Iff.not_right
    constructor
    · intro h
      rw [ord] at h
      apply dite_ne_right_iff.mp at h
      exact h.1
    · intro h
      rw [← Ne, ← pos_iff_ne_zero]
      apply ord_pos h



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

theorem ord_dvd_iff_pow_cong_one {a b m : ℕ} :
  ord a m ∣ b ↔ a^b ≡ 1 [MOD m]
  := by
    let o := ord a m
    constructor
    · intro h
      apply exists_eq_mul_right_of_dvd at h
      rcases h with ⟨c, hc⟩
      rw [hc, pow_mul, ← one_pow c]
      apply ModEq.pow c pow_ord
    · intro h
      by_cases ho : o = 0
      · unfold_let o at ho
        rw [ho]
        simp
        apply ord_eq_zero_iff.mp at ho
        apply eq_zero_of_pow_cong_one_of_not_coprime ho h
      · apply Classical.by_contradiction
        intro hb
        have hbo : b % o > 0 := mod_pos_iff_not_dvd.mpr hb
        have : a^(b % o) ≡ 1 [MOD m] := calc
          _ ≡ a^b [MOD m]       := pow_mod_ord
          _ ≡ 1 [MOD m]         := h
        have : a^(b % o) ≢ 1 [MOD m] := by
          apply ord_min hbo
          apply mod_lt _ (pos_iff_ne_zero.mpr ho)
        contradiction

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
    have : ¬(k > 0 ∧ a^k ≡ 1 [MOD p]) := Nat.find_min (exists_ord ha) k_lt
    apply not_and_or.mp at this
    rcases this with left | right
    · simp at left
      apply (dvd_iff_mod_eq_zero (ord a p) (p - 1)).mpr left
    · exfalso
      contradiction

theorem eq_ord_of_pow_cong_one_of_dvd_ord {a m o : ℕ} (h₁ : a^o ≡ 1 [MOD m]) (h₂ : o ∣ ord a m) :
  o = ord a m
  := by
    apply ord_dvd_iff_pow_cong_one.mpr at h₁
    apply dvd_antisymm h₂ h₁

theorem ord_mod {a m : ℕ} :
  ord (a % m) m = ord a m
  := by
    let o := ord a m
    let o' := ord (a % m) m
    change o' = o
    have h₁ : (a % m)^o ≡ 1 [MOD m] := by
      rw [ModEq, ← pow_mod, pow_ord]
    have h₂ : a^o' ≡ 1 [MOD m] := by
      rw [ModEq, pow_mod, pow_ord]
    apply ord_dvd_iff_pow_cong_one.mpr at h₂
    exact (eq_ord_of_pow_cong_one_of_dvd_ord h₁ h₂).symm

lemma ord_zero {m : ℕ} (hm : m ≠ 1) :
  ord 0 m = 0
  := by
    rw [ord]
    by_cases h : Coprime 0 m
    · have : m = 1 := (coprime_zero_left _).mp h
      contradiction
    · rw [dite_false' h]

lemma ord_eq_one_iff {a m : ℕ} :
  ord a m = 1 ↔ a ≡ 1 [MOD m]
  := by
    constructor
    · intro h
      rw [← pow_one a]
      nth_rw 1 [← h]
      apply pow_ord
    · intro h
      have ha : Coprime a m := coprime_of_cong_one h
      have le : ord a m ≤ 1 := by
        rw [ord, dite_true' ha]
        apply Nat.find_min' (exists_ord ha)
        constructor
        · norm_num
        · rw [pow_one]
          exact h
      have pos : 0 < ord a m := ord_pos ha
      apply eq_of_le_of_not_lt le
      simp [pos_iff_ne_zero.mp pos]
lemma ord_one {m : ℕ} :
  ord 1 m = 1
  := by
    apply ord_eq_one_iff.mpr
    apply ModEq.refl

theorem eq_of_pow_cong_pow {a k j m : ℕ} (ha : Coprime a m) (hk : k < ord a m) (hj : j < ord a m) (h : a^k ≡ a^j [MOD m]) :
  k = j
  := by
    apply Classical.by_contradiction
    intro hkj
    change k ≠ j at hkj
    wlog lt : k < j
    · specialize this (a := a) (k := j) (j := k) (m := m) ha hj hk h.symm hkj.symm
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

theorem eq_of_pow_cong_pow' {a k j m : ℕ} {S : Finset ℕ} (ha : Coprime a m) (hS : IncongruentSet S (ord a m)) (hk : k ∈ S) (hj : j ∈ S) (h : a^k ≡ a^j [MOD m]) :
  k = j
  := by
    apply hS k hk j hj
    let o := ord a m
    have : a^(k%o) ≡ a^(j%o) [MOD m] := calc
      _ ≡ a^k [MOD m]         := pow_mod_ord
      _ ≡ a^j [MOD m]         := h
      _ ≡ a^(j%o) [MOD m]     := pow_mod_ord.symm
    have hko : k % o < o := mod_lt _ (ord_pos ha)
    have hjo : j % o < o := mod_lt _ (ord_pos ha)
    apply eq_of_pow_cong_pow ha hko hjo this

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
      apply eq_of_pow_cong_pow ha hk hj this
    · intro h
      rw [ModEq] at h
      calc
        a^k
        _ ≡ a^(k % o) [MOD m]       := by
                                      symm
                                      apply pow_mod_ord
        _ = a^(j % o)               := by rw [h]
        _ ≡ a^j       [MOD m]       := pow_mod_ord

-- a^k ≢ a^j [MOD m] for any two k, j ∈ S, where S is a set of incongruent residues mod (ord a m)
lemma pow_injOn_incong {a m : ℕ} {S : Finset ℕ} (ha : Coprime a m) (hS : IncongruentSet S (ord a m)) :
  Set.InjOn (fun k => a^k % m) S
  := by
    intro x hx y hy h
    change a^x ≡ a^y [MOD m] at h
    apply eq_of_pow_cong_pow' ha hS hx hy h
-- a^k ≢ a^j [MOD m] for any two k, j < ord a m
lemma pow_injOn_range_ord {a m : ℕ} (ha : Coprime a m) :
  Set.InjOn (fun k => a^k % m) (range (ord a m))
  :=
    pow_injOn_incong ha range_incong_set
lemma card_image_pow_eq_card {a m : ℕ} {S : Finset ℕ} (ha : Coprime a m) (hS : IncongruentSet S (ord a m)) :
  card (image (fun k => a^k % m) S) = card S
  :=
    card_image_iff.mpr (pow_injOn_incong ha hS)
lemma card_image_pow_eq_ord {a m : ℕ} (ha : Coprime a m) :
  card (image (fun k => a^k % m) (range (ord a m))) = ord a m
  := by
    nth_rw 2 [← card_range (ord a m)]
    apply card_image_pow_eq_card ha
    apply range_incong_set

/-
 - Page 92 of https://resources.saylor.org/wwwresources/archived/site/wp-content/uploads/2013/05/An-Introductory-in-Elementary-Number-Theory.pdf
 -/
theorem ord_pow {a b m : ℕ} (hb : 0 < b):
  ord (a^b) m = (ord a m) / (Nat.gcd b (ord a m))
  := by
    let o := ord a m
    let g := Nat.gcd b o
    let o' := o / g
    let b' := b / g
    let x := ord (a^b) m
    show x = o'
    have g_pos : 0 < g := Nat.gcd_pos_of_pos_left _ hb
    have g_dvd_b : g ∣ b := by apply Nat.gcd_dvd_left
    have g_dvd_t : g ∣ o := by apply Nat.gcd_dvd_right
    have t'_b' : Coprime o' b' := by
      unfold_let o' b' g
      apply coprime_comm.mp
      apply coprime_div_gcd_div_gcd
      apply g_pos
    have h₁ : (a^b)^o' ≡ 1 [MOD m] := calc
      (a^b)^o'
      _ = (a^(b' * g))^(o / g)      := by
                                      unfold_let b' o'
                                      rw [Nat.div_mul_cancel g_dvd_b]
      _ = (a^o)^b'                  := by
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
    have h₂ : o' ∣ x := by
      have : a^(b*x) ≡ 1 [MOD m] := calc
        a^(b*x)
        _ = (a^b)^x                 := by apply pow_mul
        _ ≡ 1 [MOD m]               := pow_ord
      apply ord_dvd_iff_pow_cong_one.mpr at this
      have : o'*g ∣ b'*g*x := by
        unfold_let o' b'
        rw [Nat.div_mul_cancel g_dvd_t, Nat.div_mul_cancel g_dvd_b]
        exact this
      rw [mul_comm, mul_comm b', mul_assoc] at this
      apply Nat.dvd_of_mul_dvd_mul_left g_pos at this
      apply (Coprime.dvd_mul_left t'_b').mp this
    exact (eq_ord_of_pow_cong_one_of_dvd_ord h₁ h₂).symm

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

theorem coprime_ord_of_pow_cong_of_ord_eq_ord {a b k n : ℕ} (h_ord : ord a n = ord b n) (h_ord' : ord a n > 0) (h : a^k ≡ b [MOD n]) :
  Coprime k (ord a n)
  := by
    by_cases hk : k = 0
    · rw [hk, Nat.pow_zero, ModEq.comm] at h
      rw [← ord_eq_one_iff] at h
      rw [h] at h_ord
      rw [hk]
      apply (coprime_zero_left _).mpr h_ord
    · apply pos_iff_ne_zero.mpr at hk
      rw [← ord_mod (a := b)] at h_ord
      rw [ModEq] at h
      rw [← h, ord_mod, ord_pow hk] at h_ord
      symm at h_ord
      apply Nat.div_eq_self.mp at h_ord
      apply pos_iff_ne_zero.mp at h_ord'
      rw [Coprime]
      apply (or_iff_right h_ord').mp h_ord

-- The number of elements of order t is φ(t)
theorem ord_count {p t : ℕ} (hp : p.Prime) (ht : t ∣ p-1) :
  card (filter (fun x => ord x p = t) (Ico 1 p)) = φ t
  := by
    let divs := (p - 1).divisors
    -- bucket(d) = the set of incongruent residues that have order d
    let bucket (d : ℕ) := filter (fun x => ord x p = d) (Ico 1 p)
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
        apply hp.coprime_of_mem_Ico at ha
        have d_pos : d > 0 := by
          rw [← ha']
          apply ord_pos ha
        let pows := image (fun k => a^k % p) (range d)
        let pows' := image (fun k => a^k % p) d.coprimes
        have card_pows : card pows = d := by
          unfold_let pows
          rw [← ha']
          apply card_image_pow_eq_ord ha
        have card_pows' : card pows' = φ d := by
          rw [totient_eq_card_coprimes]
          apply card_image_pow_eq_card ha
          rw [ha']
          apply coprimes_incong_set
        have : filter (fun x => x^d ≡ 1 [MOD p]) (range p) = pows := by
          symm
          apply eq_of_subset_of_card_le
          · intro x hx
            apply mem_image.mp at hx
            rcases hx with ⟨k, _, hk⟩
            apply mem_filter.mpr
            rw [← hk]
            constructor
            · simp [mod_lt _ (Prime.pos hp)]
            · rw [
                ModEq,
                ← pow_mod,
                ← pow_mul',
                pow_mul,
                pow_mod,
                ← ha',
                pow_ord,
                one_mod_of_ne_one (Nat.Prime.ne_one hp),
                one_pow,
                one_mod_of_ne_one (Nat.Prime.ne_one hp),
              ]
          · rw [card_pows, pow_cong_one_solutions hp hd]
        have subset : pows' ⊆ bucket d := by
          intro t ht
          apply mem_image.mp at ht
          rcases ht with ⟨k, hk, hk'⟩
          rw [← hk']
          apply mem_filter.mpr
          constructor
          · apply mem_Ico.mpr
            constructor
            · apply pos_iff_one_le.mp
              apply mod_pos_of_coprime (Nat.Prime.ne_one hp)
              apply coprime_pow
              apply ha
            · apply mod_lt _ (Prime.pos hp)
          · by_cases k_zero : k = 0
            · have d_one : d = 1 := by
                apply mem_coprimes₁ at hk
                rw [k_zero, coprime_zero_left] at hk
                exact hk
              rw [
                k_zero,
                Nat.pow_zero,
                one_mod_of_ne_one (Nat.Prime.ne_one hp),
                ord_one,
                d_one,
              ]
            · apply pos_iff_ne_zero.mpr at k_zero
              apply mem_coprimes₁ at hk
              rw [Coprime] at hk
              rw [ord_mod, ord_pow k_zero, ha', hk, Nat.div_one]
        have supset : pows' ⊇ bucket d := by
          intro b hb
          apply mem_filter.mp at hb
          rcases hb with ⟨hb, hb'⟩
          have : b ∈ pows := by
            rw [← this, mem_filter]
            constructor
            · rw [mem_range]
              rw [mem_Ico] at hb
              exact hb.right
            · rw [← hb']
              exact pow_ord
          apply mem_image.mp at this
          rcases this with ⟨k, ⟨hk₁, hk₂⟩⟩
          have hk' : Coprime k d := by
            rw [← ha']
            apply coprime_ord_of_pow_cong_of_ord_eq_ord (b := b)
            · rw [ha', hb']
            · rw [ha']
              apply d_pos
            · rw [ModEq, hk₂]
              symm
              apply Nat.mod_eq_of_lt (mem_Ico.mp hb).right
          have : k ∈ d.coprimes := by
            apply mem_filter.mpr
            constructor <;> assumption
          apply mem_image.mpr
          use k
        have eq : pows' = bucket d := subset_antisymm subset supset
        change card (bucket d) = φ d
        rw [← eq, card_pows']
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

-- The number of elements of order t is φ(t)
theorem ord_count' {p t : ℕ} (hp : p.Prime) (ht : t ∣ p-1) :
  card (filter (fun x => ord x p = t) (range p)) = φ t
  := by
    have t_pos : t > 0 := by
      apply pos_of_dvd_of_pos ht
      simp
      apply Prime.one_lt hp
    rw [
      range_eq_insert_zero_Ico_one (Prime.pos hp),
      filter_insert,
      ord_zero (Nat.Prime.ne_one hp),
      ← ord_count hp ht,
      if_false' (pos_iff_ne_zero.mp t_pos).symm,
    ]
