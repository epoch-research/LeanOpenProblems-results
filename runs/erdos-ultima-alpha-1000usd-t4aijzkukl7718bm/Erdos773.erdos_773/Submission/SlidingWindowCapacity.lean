import FormalConjecturesUtil

/-!
The information cost of fixing all overlapping digit-window statistics.
This is a capacity bound for one digit-selection method, not for square-Sidon sets.
-/
namespace Erdos773.SlidingWindowCapacity

open Finset

set_option maxHeartbeats 1000000

/-- Zero padding is used only to simplify the indexing of consecutive windows. -/
def padded {α : Type*} {d : ℕ} (φ : α → ℤ) (w : Fin d → α) (i : ℕ) : ℤ :=
  if hi : i < d then φ (w ⟨i, hi⟩) else 0

def window {α : Type*} {d : ℕ} (φ : α → ℤ) (w : Fin d → α) (L i : ℕ) : ℤ :=
  ∑ j ∈ range L, padded φ w (i + j)

lemma window_step {α : Type*} {d : ℕ} (φ : α → ℤ) (w : Fin d → α) (L i : ℕ) :
    window φ w L (i + 1) + padded φ w i =
      window φ w L i + padded φ w (i + L) := by
  have h := Finset.sum_range_succ (fun j => padded φ w (i + j)) L
  have h' := Finset.sum_range_succ' (fun j => padded φ w (i + j)) L
  have he := h.symm.trans h'
  simpa only [window, add_zero, add_assoc, add_left_comm, add_comm] using he.symm

/-- Matching windows propagate equality by one window length. -/
lemma propagate {α : Type*} {d : ℕ} {φ : α → ℤ} {w z : Fin d → α} {L i : ℕ}
    (h0 : window φ w L i = window φ z L i)
    (h1 : window φ w L (i + 1) = window φ z L (i + 1))
    (hi : padded φ w i = padded φ z i) :
    padded φ w (i + L) = padded φ z (i + L) := by
  have hw := window_step φ w L i
  have hz := window_step φ z L i
  rw [h0, h1, hi] at hw
  linarith

/-- Within a fixed window profile, the first L letters determine the entire word. -/
theorem determined_by_prefix {α : Type*} {d L : ℕ} {φ : α → ℤ}
    (hφ : Function.Injective φ) (hL : 0 < L) (hLd : L ≤ d)
    {w z : Fin d → α}
    (hprefix : ∀ i : Fin L, w (Fin.castLE hLd i) = z (Fin.castLE hLd i))
    (hwindow : ∀ i, i + L ≤ d → window φ w L i = window φ z L i) :
    w = z := by
  have hpad : ∀ n, n < d → padded φ w n = padded φ z n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hnd
      by_cases hnL : n < L
      · have hp := congrArg φ (hprefix ⟨n, hnL⟩)
        simpa only [padded, dif_pos hnd, Fin.castLE_mk] using hp
      · have hLn : L ≤ n := by omega
        have hold := ih (n - L) (by omega) (by omega)
        have hs := propagate
          (hwindow (n - L) (by omega))
          (hwindow (n - L + 1) (by omega)) hold
        simpa only [Nat.sub_add_cancel hLn] using hs
  funext i
  apply hφ
  simpa only [padded, dif_pos i.isLt] using hpad i.val i.isLt


/-- The first window also determines the last letter of the prefix.
Consequently only L initial letters are free for windows of length L+1. -/
theorem determined_by_short_prefix {α : Type*} {d L : ℕ} {φ : α → ℤ}
    (hφ : Function.Injective φ) (hLd : L + 1 ≤ d)
    {w z : Fin d → α}
    (hprefix : ∀ i : Fin L,
      w (Fin.castLE (by omega : L ≤ d) i) = z (Fin.castLE (by omega : L ≤ d) i))
    (hwindow : ∀ i, i + (L + 1) ≤ d → window φ w (L + 1) i = window φ z (L + 1) i) :
    w = z := by
  have hpre : ∀ n, n < L → padded φ w n = padded φ z n := by
    intro n hn
    have hnd : n < d := by omega
    have h := congrArg φ (hprefix ⟨n, hn⟩)
    simpa only [padded, dif_pos hnd, Fin.castLE_mk] using h
  have hlast : padded φ w L = padded φ z L := by
    have h := hwindow 0 (by omega)
    simp only [window, zero_add, Finset.sum_range_succ] at h
    have hs : (∑ i ∈ range L, padded φ w i) = ∑ i ∈ range L, padded φ z i := by
      exact Finset.sum_congr rfl (fun i hi => hpre i (Finset.mem_range.mp hi))
    rw [hs] at h
    exact add_left_cancel h
  apply determined_by_prefix hφ (by omega : 0 < L + 1) hLd _ hwindow
  intro i
  apply hφ
  have hi := i.isLt
  have hnd : i.val < d := by omega
  have he : padded φ w i.val = padded φ z i.val := by
    by_cases hiL : i.val < L
    · exact hpre i.val hiL
    · have hie : i.val = L := by omega
      simpa only [hie] using hlast
  simpa only [padded, dif_pos hnd, Fin.castLE_mk] using he

noncomputable def fiber {α : Type*} [Fintype α] {d : ℕ}
    (φ : α → ℤ) (L : ℕ) (profile : ℕ → ℤ) : Finset (Fin d → α) := by
  classical
  exact univ.filter (fun w => ∀ i, i + L ≤ d → window φ w L i = profile i)

/-- The count is at most |alphabet|^L, regardless of the prescribed profile. -/
theorem fiber_card_le {α : Type*} [Fintype α] {d L : ℕ}
    (φ : α → ℤ) (hφ : Function.Injective φ) (hL : 0 < L) (hLd : L ≤ d)
    (profile : ℕ → ℤ) :
    (fiber (d := d) φ L profile).card ≤ Fintype.card α ^ L := by
  classical
  let restriction : (Fin d → α) → (Fin L → α) := fun w i => w (Fin.castLE hLd i)
  have hc := Finset.card_le_card_of_injOn
    (s := fiber (d := d) φ L profile) (t := (univ : Finset (Fin L → α))) restriction
    (fun _ _ => mem_univ _) (by
      intro w hw z hz hp
      apply determined_by_prefix hφ hL hLd
      · intro i
        exact congrFun hp i
      · intro i hi
        have hw' := (Finset.mem_filter.mp hw).2 i hi
        have hz' := (Finset.mem_filter.mp hz).2 i hi
        exact hw'.trans hz'.symm)
  simpa using hc


/-- The sharper bound accounts for the prescribed sum in the first window too. -/
theorem fiber_succ_card_le {α : Type*} [Fintype α] {d L : ℕ}
    (φ : α → ℤ) (hφ : Function.Injective φ) (hLd : L + 1 ≤ d)
    (profile : ℕ → ℤ) :
    (fiber (d := d) φ (L + 1) profile).card ≤ Fintype.card α ^ L := by
  classical
  let restriction : (Fin d → α) → (Fin L → α) :=
    fun w i => w (Fin.castLE (by omega : L ≤ d) i)
  have hc := Finset.card_le_card_of_injOn
    (s := fiber (d := d) φ (L + 1) profile) (t := (univ : Finset (Fin L → α))) restriction
    (fun _ _ => mem_univ _) (by
      intro w hw z hz hp
      apply determined_by_short_prefix hφ hLd
      · intro i
        exact congrFun hp i
      · intro i hi
        have hw' := (Finset.mem_filter.mp hw).2 i hi
        have hz' := (Finset.mem_filter.mp hz).2 i hi
        exact hw'.trans hz'.symm)
  simpa using hc

theorem fiber_card_le_pred {α : Type*} [Fintype α] {d L : ℕ}
    (φ : α → ℤ) (hφ : Function.Injective φ) (hL : 0 < L) (hLd : L ≤ d)
    (profile : ℕ → ℤ) :
    (fiber (d := d) φ L profile).card ≤ Fintype.card α ^ (L - 1) := by
  have he : L - 1 + 1 = L := Nat.sub_add_cancel hL
  simpa only [he] using fiber_succ_card_le φ hφ (by omega : L - 1 + 1 ≤ d) profile

/-- Ordinary sums of every sliding digit window have this capacity bound. -/
theorem digit_sum_fiber_card_le {B d L : ℕ} (hL : 0 < L) (hLd : L ≤ d)
    (profile : ℕ → ℤ) :
    (fiber (d := d) (fun a : Fin B => (a.val : ℤ)) L profile).card ≤ B ^ L := by
  have hf : Function.Injective (fun a : Fin B => (a.val : ℤ)) := by
    intro a b hab
    apply Fin.ext
    dsimp only at hab ⊢
    exact_mod_cast hab
  simpa only [Fintype.card_fin] using fiber_card_le _ hf hL hLd profile

/-- Squared-digit window sums have the same bound, because the digits are nonnegative. -/
theorem digit_square_fiber_card_le {B d L : ℕ} (hL : 0 < L) (hLd : L ≤ d)
    (profile : ℕ → ℤ) :
    (fiber (d := d) (fun a : Fin B => ((a.val ^ 2 : ℕ) : ℤ)) L profile).card ≤ B ^ L := by
  have hf : Function.Injective (fun a : Fin B => ((a.val ^ 2 : ℕ) : ℤ)) := by
    intro a b hab
    apply Fin.ext
    apply Nat.pow_left_injective (by decide : 2 ≠ 0)
    dsimp only at hab ⊢
    exact_mod_cast hab
  simpa only [Fintype.card_fin] using fiber_card_le _ hf hL hLd profile


theorem digit_sum_fiber_card_le_pred {B d L : ℕ} (hL : 0 < L) (hLd : L ≤ d)
    (profile : ℕ → ℤ) :
    (fiber (d := d) (fun a : Fin B => (a.val : ℤ)) L profile).card ≤ B ^ (L - 1) := by
  have hf : Function.Injective (fun a : Fin B => (a.val : ℤ)) := by
    intro a b hab
    apply Fin.ext
    dsimp only at hab
    exact_mod_cast hab
  simpa only [Fintype.card_fin] using fiber_card_le_pred _ hf hL hLd profile

theorem digit_square_fiber_card_le_pred {B d L : ℕ} (hL : 0 < L) (hLd : L ≤ d)
    (profile : ℕ → ℤ) :
    (fiber (d := d) (fun a : Fin B => ((a.val ^ 2 : ℕ) : ℤ)) L profile).card ≤ B ^ (L - 1) := by
  have hf : Function.Injective (fun a : Fin B => ((a.val ^ 2 : ℕ) : ℤ)) := by
    intro a b hab
    apply Fin.ext
    apply Nat.pow_left_injective (by decide : 2 ≠ 0)
    dsimp only at hab ⊢
    exact_mod_cast hab
  simpa only [Fintype.card_fin] using fiber_card_le_pred _ hf hL hLd profile

#print axioms determined_by_short_prefix
#print axioms fiber_succ_card_le
#print axioms fiber_card_le_pred
#print axioms digit_sum_fiber_card_le_pred
#print axioms digit_square_fiber_card_le_pred

#print axioms determined_by_prefix
#print axioms fiber_card_le
#print axioms digit_sum_fiber_card_le
#print axioms digit_square_fiber_card_le

end Erdos773.SlidingWindowCapacity
