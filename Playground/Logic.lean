
import Mathlib

lemma if_true' {c : Prop} [Decidable c] {t : ℕ} {e : ℕ} (h : c) :
  (if c then t else e) = t
  := by
    apply (ite_eq_left_iff (P := c)).mpr
    intro hc
    contradiction
lemma if_false' {c : Prop} [Decidable c] {t : ℕ} {e : ℕ} (h : ¬c) :
  (if c then t else e) = e
  := by
    rw [← ite_not c, if_true' h]

lemma dite_true' {c : Prop} [Decidable c] {t : c → ℕ} {e : ¬c → ℕ} (h : c) :
  (if hc : c then t hc else e hc) = t h
  := by
    change (if hc : c then t h else e hc) = t h
    apply (dite_eq_left_iff (P := c)).mpr
    intro hc
    contradiction
lemma dite_false' {c : Prop} [Decidable c] {t : c → ℕ} {e : ¬c → ℕ} (h : ¬c) :
  (if hc : c then t hc else e hc) = e h
  := by
    change (if hc : c then t hc else e h) = e h
    apply (dite_eq_right_iff (P := c)).mpr
    intro hc
    contradiction
