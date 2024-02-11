
import Mathlib
import Playground.SetTheory

open Nat Finset BigOperators


/-
 - Count
 -/

@[simp]
def Finset.count (p : α → Prop) [DecidablePred p] (s : Finset α) :=
  card (filter p s)


/-
 - NotModEq
 -/

@[simp]
def Nat.NotModEq (n a b : ℕ) :=
  ¬(a ≡ b [MOD n])
notation:50 a:50 " ≢ " b:50 " [MOD " n:50 "]" => Nat.NotModEq n a b

@[simp]
def Int.NotModEq (n a b : ℤ) :=
  ¬(a ≡ b [ZMOD n])
notation:50 a:50 " ≢ " b:50 " [ZMOD " n:50 "]" => Int.NotModEq n a b


/-
 - NotDvd
 -/

class NotDvd (α : Type _) where
  not_dvd : α → α → Prop

instance : NotDvd Nat := ⟨fun a b => ¬a ∣ b⟩
instance : NotDvd Int := ⟨fun a b => ¬a ∣ b⟩

infix:50 " ∤ " => NotDvd.not_dvd

lemma Nat.not_dvd {a b : ℕ} :
  a ∤ b ↔ ¬a ∣ b
  := Iff.rfl
lemma Int.not_dvd {a b : ℤ} :
  a ∤ b ↔ ¬a ∣ b
  := Iff.rfl


/-
 - PerfectSquare
 -/

@[reducible]
def Nat.PerfectSquare (a : ℕ) :=
  ∃ b ≤ a, b^2 = a


/-
 - Miscellaneous
 -/

lemma Nat.pos_iff_one_le {n : ℕ} :
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

lemma sub_self_sub {a b : ℕ} (h : b ≤ a) :
  a - (a - b) = b
  := by
    rw [sub_sub' h]
    apply add_sub_self_left

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

lemma two_mul_le_sq_of_ne_one {n : ℕ} (hn : n ≠ 1) :
  2*n ≤ n^2
  := by
    by_cases hn' : n = 0
    · norm_num [hn']
    · have : n ≥ 2 := (two_le_iff n).mpr (And.intro hn' hn)
      rw [sq]
      apply Nat.mul_le_mul_right _ this

lemma two_mul_le_sq_add_one {n : ℕ} :
  2*n ≤ n^2 + 1
  := by
    by_cases hn : n = 1
    · norm_num [hn]
    · calc
        _ ≤ n^2       := two_mul_le_sq_of_ne_one hn
        _ ≤ n^2 + 1   := by
                        simp

lemma sub_one_lt_self {n : ℕ} (h : 0 < n) :
  n - 1 < n
  :=
    Nat.sub_lt_self zero_lt_one (pos_iff_one_le.mp h)

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

lemma Nat.sub_mul_sub {a b c d : ℕ} (h : b ≤ a) :
  (a - b) * (c - d) = a*c - b*c + b*d - a*d
  := by
    rw [
      Nat.mul_sub_left_distrib,
      Nat.mul_sub_right_distrib,
      Nat.mul_sub_right_distrib,
      sub_sub' (mul_le_mul_right d h),
    ]

lemma Nat.sub_one_div_two_eq_div_two {n : ℕ} (h : Odd n) :
  (n - 1) / 2 = n / 2
  := by
    rw [Odd] at h
    rcases h with ⟨k, hk⟩
    rw [
      hk,
      Nat.add_one_sub_one,
      mul_div_right k zero_lt_two,
      Nat.add_div_of_dvd_right (dvd_mul_right 2 k),
      Nat.mul_div_cancel_left k zero_lt_two,
      (Nat.div_eq_zero_iff zero_lt_two).mpr one_lt_two,
      add_zero,
    ]

lemma sub_one_div_two_pos {n : ℕ} (hn : n > 2) :
  0 < (n - 1) / 2
  := by
      have : 2 ≤ n - 1 := le_sub_one_of_lt hn
      apply Nat.div_pos this zero_lt_two

lemma Finset.range_eq_insert_zero_Ico_one {n : ℕ} (h : n > 0) :
  range n = insert 0 (Ico 1 n)
  := by
    rw [range_eq_Ico, one_eq_succ_zero, Ico_insert_succ_left h]
lemma Finset.card_Ico_one (n : ℕ) :
  card (Ico 1 n) = n - 1
  := by
    simp

lemma Finset.range_add_one_eq_Icc {n : ℕ} :
  range (n + 1) = Icc 0 n
  := by
    ext x
    rw [mem_range, mem_Icc]
    constructor
    · intro hx
      constructor
      · simp
      · apply lt_add_one_iff.mp hx
    · intro hx
      apply lt_add_one_iff.mpr hx.right

lemma Finset.insert_Icc_succ_left {a b : ℕ} (h : a ≤ b) :
  insert a (Icc a.succ b) = Icc a b
  := by
    ext x
    rw [mem_insert, mem_Icc, mem_Icc]
    constructor
    · intro hx
      rcases hx with left | right
      · constructor
        · simp [left]
        · rw [left]
          exact h
      · constructor
        · apply le_trans (le_succ a) right.left
        · exact right.right
    · intro hx
      by_cases hxa : x = a
      · left
        exact hxa
      · right
        rw [← Ne] at hxa
        constructor
        · apply add_one_le_iff.mpr
          apply lt_of_le_of_ne hx.left hxa.symm
        · exact hx.right

lemma Finset.Icc_succ_right {a b : ℕ} (h : a ≤ succ b) :
  Icc a b.succ = insert b.succ (Icc a b)
  := by
    ext x
    rw [mem_Icc, mem_insert, mem_Icc]
    constructor
    · intro hx
      rcases hx with ⟨hax, hxb⟩
      rw [or_iff_not_imp_left]
      intro h
      apply lt_of_le_of_ne hxb at h
      rw [lt_succ] at h
      constructor <;> assumption
    · intro hx
      rcases hx with left | right
      · constructor
        · simp [h, left]
        · simp [left]
      · rcases right with ⟨hax, hbx⟩
        simp [hax]
        apply le_trans hbx (le_succ b)

lemma Finset.mem_Ico' {a n x : ℕ} (h : x ∈ Ico a (a+n)) :
  ∃ c < n, x = a + c
  := by
    rw [mem_Ico] at h
    rcases h with ⟨h₁, h₂⟩
    use x - a
    constructor
    · apply Nat.sub_lt_right_of_lt_add h₁
      rw [add_comm]
      exact h₂
    · simp [h₁]

lemma Finset.Icc_union_Ioo_eq_Ico {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b < c) :
  Icc a b ∪ Ioo b c = Ico a c
  := by
    ext x
    rw [mem_union, mem_Icc, mem_Ioo, mem_Ico]
    constructor
    · intro h
      rcases h with left | right
      · rcases left with ⟨left₁, left₂⟩
        apply And.intro left₁ (lt_of_le_of_lt left₂ h₂)
      · rcases right with ⟨right₁, right₂⟩
        apply And.intro (le_of_lt (lt_of_le_of_lt h₁ right₁)) right₂
    · intro h
      by_cases hx : x ≤ b
      · left
        apply And.intro h.1 hx
      · right
        rw [not_le] at hx
        apply And.intro hx h.2

lemma Nat.sq_le_sq_iff {a b : ℕ} :
  a^2 ≤ b^2 ↔ a ≤ b
  := by
    constructor
    · intro h
      apply sqrt_le_sqrt at h
      rw [sqrt_eq', sqrt_eq'] at h
      exact h
    · intro h
      rw [sq, sq]
      apply Nat.mul_le_mul h h
lemma Nat.sq_lt_sq_of_lt {a b : ℕ} (h : a < b) :
  a^2 < b^2
  := by
    by_cases hb : b = 0
    · exfalso
      rw [hb] at h
      apply (not_lt_zero a) h
    · apply pos_iff_ne_zero.mpr at hb
      rw [sq, sq]
      apply Nat.mul_lt_mul_of_le_of_lt (le_of_lt h) h hb

lemma Int.neg_of_ne_zero_of_not_pos {n : ℤ} (h₁ : n ≠ 0) (h₂ : ¬n > 0) :
  n < 0
  := by
    simp at h₂
    exact lt_of_le_of_ne h₂ h₁

lemma Int.not_dvd_of_ne_zero_of_lt_of_gt_neg {a n : ℤ} (h₁ : a ≠ 0) (h₂ : a < n) (h₃ : a > -n) :
  n ∤ a
  := by
    intro h
    rcases h with ⟨c, hc⟩
    rw [hc] at h₁ h₂ h₃
    rw [gt_iff_lt] at h₃
    simp at h₁
    rw [not_or] at h₁
    by_cases hn : n = 0
    · rw [hn] at h₂
      simp at h₂
    · by_cases hn' : n > 0
      · simp [hn'] at h₂
        rw [neg_lt, ← mul_neg, mul_lt_iff_lt_one_right hn', neg_lt] at h₃
        have : c = 0 := by
          linarith [h₂, h₃]
        apply h₁.right this
      · have : -n < n := lt_trans h₃ h₂
        rw [neg_lt_self_iff] at this
        contradiction

lemma Int.sub_lt {a b n : ℤ} (ha : a < n) (hb : 0 ≤ b) :
  a - b < n
  := by
    apply lt_of_le_of_lt (b := a)
    · simp [hb]
    · exact ha


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

lemma ModEq.add_left_mul_erase {a b m k : ℕ} :
  k*m + a ≡ b [MOD m] ↔ a ≡ b [MOD m]
  := by
    have : m ∣ k*m := by simp
    rw [
      ModEq,
      add_mod,
      (dvd_iff_mod_eq_zero _ _).mp this,
      zero_add,
      mod_mod,
      ← ModEq,
    ]
lemma ModEq.add_left_erase {a b m : ℕ} :
  m + a ≡ b [MOD m] ↔ a ≡ b [MOD m]
  := by
    nth_rw 2 [← one_mul m]
    exact add_left_mul_erase
lemma ModEq.add_left_pow_erase {a b m k : ℕ} (hk : k > 0) :
  m^k + a ≡ b [MOD m] ↔ a ≡ b [MOD m]
  := by
    apply pos_iff_ne_zero.mp at hk
    apply exists_eq_succ_of_ne_zero at hk
    rcases hk with ⟨j, hj⟩
    rw [hj, Nat.pow_succ, add_left_mul_erase]
lemma ModEq.sub_mul_erase {a b m k : ℕ} (h : a ≥ k*m) :
  a - k*m ≡ b [MOD m] ↔ a ≡ b [MOD m]
  := by
    rw [← add_left_mul_erase (k := k), Nat.add_sub_cancel' h]
lemma ModEq.sub_erase {a b m : ℕ} (h : a ≥ m) :
  a - m ≡ b [MOD m] ↔ a ≡ b [MOD m]
  := by
    nth_rw 2 [← one_mul m]
    rw [← one_mul m] at h
    exact sub_mul_erase h
lemma ModEq.sub_pow_erase {a b m k : ℕ} (hk : k > 0) (h : a ≥ m^k) :
  a - m^k ≡ b [MOD m] ↔ a ≡ b [MOD m]
  := by
    apply pos_iff_ne_zero.mp at hk
    apply exists_eq_succ_of_ne_zero at hk
    rcases hk with ⟨j, hj⟩
    rw [hj, Nat.pow_succ] at h
    rw [hj, Nat.pow_succ, sub_mul_erase h]

lemma ModEq.add_left_cancel'_iff {a b m : ℕ} (c : ℕ) :
  c + a ≡ c + b [MOD m] ↔ a ≡ b [MOD m]
  := by
    constructor
    · apply ModEq.add_left_cancel'
    · apply ModEq.add_left

lemma ModEq.add_right_cancel'_iff {a b m : ℕ} (c : ℕ) :
  a + c ≡ b + c [MOD m] ↔ a ≡ b [MOD m]
  := by
    constructor
    · apply ModEq.add_right_cancel'
    · apply ModEq.add_right

lemma ModEq.sub_cong_iff_add_cong {a b c m : ℕ} (h : a ≥ b) :
  a - b ≡ c [MOD m] ↔ a ≡ c + b [MOD m]
  := by
    rw [← ModEq.add_right_cancel'_iff b, Nat.sub_add_cancel h]

lemma ModEq.mod_zero_iff {a b : ℕ} :
  a ≡ b [MOD 0] ↔ a = b
  := by
    rw [ModEq, mod_zero, mod_zero]
lemma ModEq.not_mod_zero_iff {a b : ℕ} :
  a ≢ b [MOD 0] ↔ a ≠ b
  := by
    rw [NotModEq, ModEq, mod_zero, mod_zero]

lemma ModEq.cong_zero_iff_dvd {a m : ℕ} :
  a ≡ 0 [MOD m] ↔ m ∣ a
  := by
    rw [ModEq, zero_mod]
    exact (Nat.dvd_iff_mod_eq_zero _ _).symm
lemma Int.ModEq.cong_zero_iff_dvd {a m : ℤ} :
  a ≡ 0 [ZMOD m] ↔ m ∣ a
  := by
    rw [ModEq, zero_emod]
    exact (Int.dvd_iff_emod_eq_zero _ _).symm

lemma Int.sub_right_iff {a b c m : ℤ} :
  a - c ≡ b - c [ZMOD m] ↔ a ≡ b [ZMOD m]
  := by
    constructor
    · intro h
      apply ModEq.add_right c at h
      rw [sub_add_cancel, sub_add_cancel] at h
      exact h
    · intro h
      apply ModEq.add_right (-c) at h
      rw [← sub_eq_add_neg, ← sub_eq_add_neg] at h
      exact h

lemma ModEq.neg_one_mul {a m : ℕ} (ha : a ≤ m) :
  (m - 1) * a ≡ m - a [MOD m]
  := by
    by_cases ha' : a = 0
    · rw [ha', mul_zero, Nat.sub_zero]
      apply ModEq.card.symm
    · apply pos_iff_ne_zero.mpr at ha'
      rw [Nat.mul_sub_right_distrib, one_mul]
      nth_rw 1 [← Nat.one_add_sub_one a]
      rw [
        Nat.add_sub_assoc ha',
        mul_add,
        mul_one,
        add_comm,
        Nat.add_sub_assoc ha,
        mul_comm,
        add_left_mul_erase,
      ]

lemma ModEq.neg_one_mul_neg {a m : ℕ} (ha : a ≤ m) :
  (m - 1) * (m - a) ≡ a [MOD m]
  := calc
    _ ≡ m - (m - a) [MOD m]     := neg_one_mul (sub_le _ _)
    _ = a                       := Nat.sub_sub_self ha

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

lemma Int.dvd_iff_cong_zero {a m : ℤ} :
  m ∣ a ↔ a ≡ 0 [ZMOD m]
  := by
    rw [Int.ModEq, Int.zero_emod]
    apply Int.dvd_iff_emod_eq_zero


/-
 - Incongruent Sets
 -/

def IncongruentSet (S : Finset ℕ) (m : ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≡ y [MOD m] → x = y

lemma incong_set_of_subset {m : ℕ} {S T : Finset ℕ} (hT : IncongruentSet T m) (hS : S ⊆ T) :
  IncongruentSet S m
  := by
    intro x hx y hy hxy
    apply hS at hx
    apply hS at hy
    apply hT x hx y hy hxy

lemma Ico_incong_set {a m : ℕ} :
  IncongruentSet (Ico a (a+m)) m
  := by
    intro x hx y hy hxy
    apply mem_Ico' at hx
    apply mem_Ico' at hy
    rcases hx with ⟨c, hc, hxc⟩
    rcases hy with ⟨d, hd, hyd⟩
    rw [hxc, hyd] at hxy
    apply ModEq.add_left_cancel' at hxy
    rw [ModEq, mod_eq_of_lt hc, mod_eq_of_lt hd] at hxy
    rw [hxc, hyd, hxy]

lemma range_incong_set {m : ℕ} :
  IncongruentSet (range m) m
  := by
    rw [range_eq_Ico]
    nth_rw 1 [← zero_add m]
    apply Ico_incong_set

lemma incong_set_of_subset_range {m : ℕ} {S : Finset ℕ} (hS : S ⊆ range m) :
  IncongruentSet S m
  :=
    incong_set_of_subset range_incong_set hS

lemma incong_set_of_subset_Ico {a m : ℕ} {S : Finset ℕ} (hS : S ⊆ Ico a (a+m)) :
  IncongruentSet S m
  :=
    incong_set_of_subset Ico_incong_set hS


/-
 - Primes
 -/

lemma Nat.Prime.sub_one_pos {p : ℕ} (hp : p.Prime) :
  p - 1 > 0
  :=
    Nat.sub_pos_iff_lt.mpr (Prime.one_lt hp)

lemma Nat.Prime.coprime_sub_one_left {p : ℕ} (hp : p.Prime) :
  Coprime (p - 1) p
  := by
    sorry
lemma Nat.Prime.coprime_sub_one_right {p : ℕ} (hp : p.Prime) :
  Coprime p (p - 1)
  := by
    sorry

lemma Nat.Prime.two_dvd {p : ℕ} (hp : p.Prime) (hp' : p > 2) :
  2 ∣ p-1
  := by
    apply ne_of_lt at hp'
    symm at hp'
    apply Prime.odd_of_ne_two hp at hp'
    apply even_sub_one_of_odd at hp'
    apply even_iff_two_dvd.mp hp'

lemma Nat.Prime.odd_of_two_lt {p : ℕ} (hp : p.Prime) (hp' : p > 2) :
  Odd p
  := odd_of_ne_two hp (ne_of_gt hp')

lemma Nat.Prime.dvd_iff_dvd_pow {a b p : ℕ} (hp : p.Prime) (hb : b > 0) :
  p ∣ a ↔ p ∣ a^b
  := by
    constructor
    · intro h
      apply dvd_pow h (Nat.pos_iff_ne_zero.mp hb)
    · apply Prime.dvd_of_dvd_pow hp

lemma cong_zero_of_mul_cong_zero {a b p : ℕ} (hp : p.Prime) (h : a * b ≡ 0 [MOD p]) :
  a ≡ 0 [MOD p] ∨ b ≡ 0 [MOD p]
  := by
    rw [
      ModEq,
      ModEq,
      zero_mod,
      ← Nat.dvd_iff_mod_eq_zero,
      ← Nat.dvd_iff_mod_eq_zero,
    ] at *
    exact (Nat.Prime.dvd_mul hp).mp h

lemma Int.Prime.dvd_mul_iff {a b : ℤ} {p : ℕ} (hp : p.Prime) :
  ↑p ∣ a * b ↔ (↑p ∣ a) ∨ (↑p ∣ b)
  := by
    constructor
    · apply Prime.dvd_mul' hp
    · intro h
      rcases h with ha | hb
      · apply dvd_trans ha
        apply dvd_mul_right
      · apply dvd_trans hb
        apply dvd_mul_left


/-
 - Coprimes
 -/

lemma not_coprime_zero_left {n : ℕ} (h : n ≠ 1) :
  ¬Coprime 0 n
  := (coprime_zero_left n).not.mpr h
lemma not_coprime_zero_right {n : ℕ} (h : n ≠ 1) :
  ¬Coprime n 0
  := (coprime_zero_right n).not.mpr h

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
lemma coprime_mod_eq_iff {a b m : ℕ} (h : a ≡ b [MOD m]) :
  Coprime a m ↔ Coprime b m
  := by
    constructor
    · apply coprime_mod_eq h
    · apply coprime_mod_eq h.symm
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
    apply Iff.not_right
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

lemma coprimes_subset_range {n : ℕ} :
  n.coprimes ⊆ range n
  := by
    intro a ha
    rw [mem_range]
    apply mem_coprimes₂ ha

lemma coprimes_eq_Ico_one_of_prime {p : ℕ} (hp : p.Prime) :
  p.coprimes = Ico 1 p
  := by
    rw [
      coprimes,
      range_eq_insert_zero_Ico_one hp.pos,
      filter_insert,
      if_neg (not_coprime_zero_left hp.ne_one),
      filter_eq_self,
    ]
    intro a ha
    apply coprime_of_mem_Ico hp ha

lemma coprimes_incong_set {n : ℕ} :
  IncongruentSet n.coprimes n
  :=
    incong_set_of_subset range_incong_set coprimes_subset_range

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
    rw [not_dvd, Classical.not_not, Nat.gcd_eq_right_iff_dvd] at ha
    rw [Coprime, ha]
    exact hm

lemma mod_pos_iff_not_dvd {a m : ℕ} :
  0 < a % m ↔ m ∤ a
  := by
    apply Iff.not_right
    rw [pos_iff_ne_zero, Classical.not_not]
    symm
    apply Nat.dvd_iff_mod_eq_zero
lemma mod_pos_of_coprime {a m : ℕ} (hm : m ≠ 1) (ha : Coprime a m) :
  0 < a % m
  := by
    apply not_dvd_of_coprime hm at ha
    contrapose ha
    apply Nat.eq_zero_of_not_pos at ha
    rw [not_dvd, Classical.not_not]
    apply (Nat.dvd_iff_mod_eq_zero _ _).mpr ha


/-
 - Big Operators
 -/

lemma Finset.sum_congr' {S : Finset α} {f g : α → β} [AddCommMonoid β] (h : ∀ i ∈ S, f i = g i) :
  ∑ i in S, f i = ∑ i in S, g i
  :=
    sum_congr rfl h

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

lemma Int.sum_sub_sum {S : Finset α} {f g : α → ℤ} :
  ∑ i in S, f i - ∑ i in S, g i = ∑ i in S, (f i - g i)
  := by
    rw [
      sub_eq_add_neg,
      ← neg_one_mul,
      mul_sum,
      ← sum_add_distrib,
    ]
    apply sum_congr'
    intro i _
    rw [neg_one_mul, ← sub_eq_add_neg]

theorem Int.mul_eq_telescoping_sum {n : ℕ} {a b : ℤ} :
  (a - b) * ∑ i in Finset.range n, a^i * b^(n - i - 1) = a^n - b^n
  := by
    let f (i : ℕ) := a^i * b^(n - i)
    calc
      _ = ∑ i in Finset.range n, (a^(i + 1) * b^(n - i - 1) - a^i * b^(n - i))
                := by
                  rw [mul_sum]
                  apply sum_congr'
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
                    rw [← Nat.pos_iff_one_le]
                    simp [hi]
                  rw [
                    ← pow_add,
                    ← Nat.add_sub_assoc this,
                    Nat.add_sub_cancel_left,
                  ]
      _ = ∑ i in Finset.range n, (f (i + 1) - f i)   := by congr
      _ = f n - f 0                                  := by apply sum_range_sub
      _ = a^n - b^n                                  := by simp

lemma Finset.sum_Icc_succ {a b : ℕ} {f : ℕ → α} [AddCommMonoid α] (h : a ≤ succ b) :
  ∑ i in Icc a (succ b), f i = (∑ i in Icc a b, f i) + f (succ b)
  := by
    rw [Icc_succ_right h, sum_insert, add_comm]
    simp

lemma Int.sum_Icc_one {n : ℕ} {f : ℕ → ℤ} :
  ∑ i in Icc 1 n, f i = (∑ i in Finset.range (n + 1), f i) - f 0
  := by
    rw [
      range_eq_insert_zero_Ico_one (by simp),
      sum_insert (by simp),
      Ico_succ_right,
      add_sub_cancel',
    ]


/-
 - Euler's Totient Theorem
 -/

theorem mul_mod_injOn_coprimes {a m : ℕ} (ha : Coprime a m) :
  Set.InjOn (fun x => a*x % m) m.coprimes
  := by
    intro x hx y hy h
    change (a*x ≡ a*y [MOD m]) at h
    apply ModEq.cancel_left_of_coprime at h
    · let hx' := mem_coprimes₂ hx
      let hy' := mem_coprimes₂ hy
      apply ModEq.eq_of_lt_of_lt h hx' hy'
    · rw [Coprime, Nat.gcd_comm] at ha
      exact ha

theorem mul_mod_injOn_Ico_of_prime {a p : ℕ} (hp : p.Prime) (ha : Coprime a p) :
  Set.InjOn (fun x => a*x % p) (Ico 1 p)
  := by
    rw [← coprimes_eq_Ico_one_of_prime hp]
    apply mul_mod_injOn_coprimes ha
theorem mul_mod_injOn_of_prime {a p : ℕ} (hp : p.Prime) (ha : Coprime a p) :
  Set.InjOn (fun x => a*x % p) (range p)
  := by
    rw [range_eq_insert_zero_Ico_one hp.pos]
    change Set.InjOn (fun x => a * x % p) ↑({0} ∪ (Ico 1 p))
    rw [coe_union, Set.injOn_union]
    · constructor
      · rw [coe_singleton]
        apply Set.injOn_singleton
      · constructor
        · apply mul_mod_injOn_Ico_of_prime hp ha
        · intro x hx y hy
          rw [coe_singleton, Set.mem_singleton_iff] at hx
          rw [hx, mul_zero, zero_mod, ne_comm, Ne, ← dvd_iff_mod_eq_zero]
          apply hp.not_dvd_mul
          · apply not_dvd_of_coprime hp.ne_one ha
          · rw [coe_Ico, Set.mem_Ico] at hy
            apply not_dvd_of_pos_of_lt (pos_iff_one_le.mp hy.1) hy.2
    · simp only [coe_singleton, coe_Ico, Set.disjoint_singleton_left, Set.mem_Ico,
      nonpos_iff_eq_zero, one_ne_zero, false_and, not_false_eq_true]

theorem euler's_totient_theorem {a m : ℕ} (hm : m > 0) (ha : Coprime a m) :
  a^(φ m) ≡ 1 [MOD m]
  := by
    let f (x : ℕ) := a*x % m
    let S := image f m.coprimes
    have inj : Set.InjOn f m.coprimes := mul_mod_injOn_coprimes ha
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
    have : S = m.coprimes := eq_image_of_inj_of_subset inj subset
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

theorem eq_zero_of_pow_cong_one_of_not_coprime {a b m : ℕ} (ha : ¬Coprime a m) (h : a^b ≡ 1 [MOD m]) :
  b = 0
  := by
    apply Classical.by_contradiction
    intro hb
    apply pos_iff_ne_zero.mpr at hb
    apply (coprime_pow_iff hb).not.mpr at ha
    have : ¬Coprime 1 m := (coprime_mod_eq_iff h).not.mp ha
    have : Coprime 1 m := coprime_one_left m
    contradiction
