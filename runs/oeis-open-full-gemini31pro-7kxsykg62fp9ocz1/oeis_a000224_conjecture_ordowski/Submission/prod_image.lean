import Mathlib
open Finset

lemma card_image_prod {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  (f : α → α) (g : β → β) :
  (univ.image (fun x : α × β => (f x.1, g x.2))).card =
  (univ.image f).card * (univ.image g).card := by
  have H : univ.image (fun x : α × β => (f x.1, g x.2)) =
    (univ.image f) ×ˢ (univ.image g) := by
    ext ⟨a, b⟩
    simp
    constructor
    · rintro ⟨⟨x, y⟩, ⟨rfl, rfl⟩⟩
      exact ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
    · rintro ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
      exact ⟨⟨x, y⟩, ⟨rfl, rfl⟩⟩
  rw [H, card_product]
