
import Mathlib

open Finset

theorem eq_image_of_inj_of_subset_of_card_eq {S : Finset α} {T : Finset β} [DecidableEq β] {f : α → β} (h_inj : Set.InjOn f S) (h_subset : image f S ⊆ T) (h_card : card S = card T) :
  image f S = T
  := by
    apply card_image_iff.mpr at h_inj
    contrapose h_inj
    have : image f S ⊂ T := by
      apply ssubset_of_subset_of_ne h_subset
      dsimp
      exact h_inj
    apply card_lt_card at this
    rw [h_card]
    apply ne_of_lt this

theorem eq_image_of_inj_of_subset {S : Finset α} [DecidableEq α] {f : α → α} (h_inj : Set.InjOn f S) (h_subset : image f S ⊆ S) :
  image f S = S
  :=
    eq_image_of_inj_of_subset_of_card_eq h_inj h_subset rfl
