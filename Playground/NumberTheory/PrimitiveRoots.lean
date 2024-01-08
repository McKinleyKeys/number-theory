
import Mathlib
import Playground.Logic
import Playground.NumberTheory.Basic
import Playground.NumberTheory.Order

open Nat Finset BigOperators


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


/-
 - Existence of Primitive Roots
 -/

theorem primitive_root_count {p : ℕ} (hp : p.Prime) :
  card p.primitive_roots = φ (p - 1)
  :=
    ord_count' hp (dvd_refl (p-1))

theorem exists_primitive_root {p : ℕ} (hp : p.Prime) :
  ∃ r < p, PrimitiveRoot r p
  := by
    have : card p.primitive_roots > 0 := by
      rw [primitive_root_count hp]
      apply totient_pos
      simp [Prime.one_lt hp]
    apply card_pos.mp at this
    change ∃ r, r ∈ p.primitive_roots at this
    rcases this with ⟨r, hr⟩
    rw [primitive_roots, mem_filter, mem_range] at hr
    use r

theorem primitive_root_generates {r t m : ℕ} (hm : m > 1) (ht : Coprime t m) (hr : PrimitiveRoot r m) :
  ∃ k ∈ Ico 1 m, r^k ≡ t [MOD m]
  := by
    let span := image (fun k => r^k % m) (Ico 1 m)
    have hr' : Coprime r m := coprime_of_primitive_root hm hr
    have card_span : card span = m - 1 := by
      rw [← card_Ico_one m]
      apply card_image_pow_eq_card hr'
      rw [hr]
      have : IncongruentSet (Ico 1 (1 + (m-1))) (m-1) := Ico_incong_set
      rw [← Nat.add_sub_assoc (le_of_lt hm), Nat.add_sub_cancel_left] at this
      exact this
    have subset : span ⊆ Ico 1 m := by
      apply image_subset_iff.mpr
      intro k hk
      rw [mem_Ico] at hk ⊢
      constructor
      · apply one_le_iff_ne_zero.mpr
        apply (Nat.dvd_iff_mod_eq_zero m (r^k)).not.mp
        apply not_dvd_of_coprime (Nat.ne_of_lt hm).symm
        apply coprime_pow hr'
      · apply mod_lt
        linarith [hm]
    rw [← card_Ico_one] at card_span
    have eq : span = Ico 1 m := by
      apply eq_of_subset_of_card_le subset
      apply le_of_eq card_span.symm
    have : t % m ∈ Ico 1 m := by
      rw [mem_Ico]
      constructor
      · apply pos_iff_one_le.mp
        apply mod_pos_of_coprime (Nat.ne_of_lt hm).symm ht
      · apply mod_lt
        linarith [hm]
    rw [← eq, mem_image] at this
    exact this
theorem Nat.Prime.primitive_root_generates {r t p : ℕ} (hp : p.Prime) (ht : Coprime t p) (hr : PrimitiveRoot r p) :
  ∃ k ∈ Ico 1 p, r^k ≡ t [MOD p]
  :=
    _root_.primitive_root_generates (Prime.one_lt hp) ht hr

-- Every residue is congruent to r^k where r is a primitive root
theorem cong_primitive_root_pow {a p : ℕ} (hp : p.Prime) (ha : Coprime a p) :
  ∃ r < p, PrimitiveRoot r p ∧ ∃ k > 0, r^k ≡ a [MOD p]
  := by
    rcases (exists_primitive_root hp) with ⟨r, hr₁, hr₂⟩
    use r
    constructor
    · assumption
    constructor
    · assumption
    rcases (Prime.primitive_root_generates hp ha hr₂) with ⟨k, hk₁, hk₂⟩
    use k
    constructor
    · rw [mem_Ico] at hk₁
      apply pos_iff_one_le.mpr hk₁.left
    · exact hk₂
