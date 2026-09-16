import Mathlib
import Submission.Spec
open Finset

lemma A000224_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h_coprime : m.Coprime n) :
  A000224 (m * n) = A000224 m * A000224 n := by
  haveI : NeZero m := ⟨hm⟩
  haveI : NeZero n := ⟨hn⟩
  haveI : NeZero (m * n) := ⟨mul_ne_zero hm hn⟩
  unfold A000224
  simp only [hm, hn, mul_ne_zero hm hn, ite_false, card_image_ZMod]
  let e := ZMod.chineseRemainder h_coprime
  have h_bij : (univ.image (fun x : ZMod (m * n) => x ^ 2)).card =
    (univ.image (fun x : (ZMod m) × (ZMod n) => (x.1 ^ 2, x.2 ^ 2))).card := by
    have H1 : (univ.image (fun x : ZMod (m * n) => e (x ^ 2))) =
      (univ.image (fun x : ZMod (m * n) => x ^ 2)).image e := by
      ext y
      simp
    have H2 : (univ.image (fun x : ZMod (m * n) => x ^ 2)).card =
      (univ.image (fun x : ZMod (m * n) => e (x ^ 2))).card := by
      rw [H1]
      symm
      apply card_image_of_injOn
      intro x hx y hy heq
      exact e.injective heq
    have H3 : ∀ x : ZMod (m * n), e (x ^ 2) = ((e x).1 ^ 2, (e x).2 ^ 2) := by
      intro x
      simp only [map_pow]
      rfl
    have H4 : univ.image (fun x : ZMod (m * n) => e (x ^ 2)) =
      univ.image (fun x : (ZMod m) × (ZMod n) => (x.1 ^ 2, x.2 ^ 2)) := by
      ext y
      simp only [mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨x, rfl⟩
        rw [H3]
        exact ⟨e x, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨e.symm x, by rw [H3]; simp⟩
    rw [H2, H4]
  have h_prod : (univ.image (fun x : (ZMod m) × (ZMod n) => (x.1 ^ 2, x.2 ^ 2))).card =
    (univ.image (fun x : ZMod m => x ^ 2)).card * (univ.image (fun x : ZMod n => x ^ 2)).card := by
    have H : univ.image (fun x : (ZMod m) × (ZMod n) => (x.1 ^ 2, x.2 ^ 2)) =
      (univ.image (fun x : ZMod m => x ^ 2)) ×ˢ (univ.image (fun x : ZMod n => x ^ 2)) := by
      ext ⟨a, b⟩
      simp
    rw [H, card_product]
  rw [h_bij, h_prod]
