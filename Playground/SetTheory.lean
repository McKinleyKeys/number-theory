
import Mathlib

open Finset

theorem eq_image_of_inj {S : Finset α} [DecidableEq α] {f : α → α} (hf : Set.InjOn f S) (h : image f S ⊆ S) :
  image f S = S
  := by
    apply card_image_iff.mpr at hf
    contrapose hf
    have : image f S ⊂ S := by
      apply ssubset_of_subset_of_ne h
      dsimp
      exact hf
    apply card_lt_card at this
    apply ne_of_lt this
