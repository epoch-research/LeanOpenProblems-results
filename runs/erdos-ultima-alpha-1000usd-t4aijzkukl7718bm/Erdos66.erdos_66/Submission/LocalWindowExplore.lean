import Submission.FiniteRepairExplore

/-! A logarithmic representation upper bound controls the number of old
points in every short interval, wherever the interval is located. -/
namespace Erdos66LocalWindow
open Erdos66OriginRepair Erdos66FiniteRepair
open scoped Classical
set_option maxHeartbeats 1000000

lemma pairCount_eq_product_filter_card (A B : Finset ℤ) (z : ℤ) :
    pairCount A B z = ((A.product B).filter (fun p ↦ p.1 + p.2 = z)).card := by
  rw [pairCount]
  apply Finset.card_bij (fun a _ ↦ (a, z - a))
  · intro a ha
    obtain ⟨ha, hb⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, by omega⟩
  · intro a ha b hb he
    exact congrArg Prod.fst he
  · intro p hp
    obtain ⟨hp, hs⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    refine ⟨p.1, Finset.mem_filter.mpr ⟨ha, ?_⟩, ?_⟩
    · convert hb using 1; omega
    · exact Prod.ext rfl (by omega)

lemma pairCount_mono {A B C D : Finset ℤ} (hA : A ⊆ C) (hB : B ⊆ D) (z : ℤ) :
    pairCount A B z ≤ pairCount C D z := by
  apply Finset.card_le_card
  intro a ha
  obtain ⟨ha, hb⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨hA ha, hB hb⟩

lemma window_card_sq_bound (A : Finset ℤ) (V : ℝ)
    (hA : ∀ z : ℤ, (pairCount A A z : ℝ) ≤ V) (a : ℤ) (L : ℕ) :
    (((A.filter (fun x ↦ a ≤ x ∧ x < a + L)).card : ℝ) ^ 2) ≤ 2 * (L : ℝ) * V := by
  let Q := A.filter (fun x ↦ a ≤ x ∧ x < a + L)
  let I := Finset.Ico (2 * a) (2 * a + 2 * (L : ℤ))
  have hmap : Set.MapsTo (fun p : ℤ × ℤ ↦ p.1 + p.2)
      ((Q.product Q : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) (I : Set ℤ) := by
    intro p hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
    obtain ⟨_, ha₁, hb₁⟩ := Finset.mem_filter.mp hp₁
    obtain ⟨_, ha₂, hb₂⟩ := Finset.mem_filter.mp hp₂
    change p.1 + p.2 ∈ Finset.Ico (2 * a) (2 * a + 2 * (L : ℤ))
    apply Finset.mem_Ico.mpr
    constructor <;> omega
  have hmass : (Q.card : ℝ) ^ 2 = ∑ z ∈ I, (pairCount Q Q z : ℝ) := by
    have hh := Finset.card_eq_sum_card_fiberwise hmap
    simp_rw [← pairCount_eq_product_filter_card] at hh
    exact_mod_cast (show Q.card ^ 2 = ∑ z ∈ I, pairCount Q Q z by simpa only [pow_two, Finset.product_eq_sprod, Finset.card_product] using hh)
  have hcard : (I.card : ℝ) = 2 * (L : ℝ) := by
    have he : (2 * (L : ℤ)).toNat = 2 * L := by omega
    simp [I, he]
  change (Q.card : ℝ) ^ 2 ≤ _
  rw [hmass]
  calc
    _ ≤ ∑ _z ∈ I, V := by
      apply Finset.sum_le_sum
      intro z hz
      have hh : (pairCount Q Q z : ℝ) ≤ pairCount A A z := by
        exact_mod_cast pairCount_mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) z
      exact hh.trans (hA z)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hcard]

lemma window_card_bound (A : Finset ℤ) (V : ℝ)
    (hA : ∀ z : ℤ, (pairCount A A z : ℝ) ≤ V) (a : ℤ) (L : ℕ) :
    ((A.filter (fun x ↦ a ≤ x ∧ x < a + L)).card : ℝ) ≤ Real.sqrt (2 * (L : ℝ) * V) := by
  have hh := window_card_sq_bound A V hA a L
  have hsq := Real.sqrt_le_sqrt hh
  simpa only [Real.sqrt_sq (Nat.cast_nonneg _)] using hsq

lemma affine_filter_bound {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset ℤ) (V : ℝ) (hA : ∀ z : ℤ, (pairCount A A z : ℝ) ≤ V)
    (f : α → ℤ) (hf : Function.Injective f) (a : ℤ) (L : ℕ)
    (hwindow : ∀ i : α, a ≤ f i ∧ f i < a + L) :
    ((Finset.univ.filter (fun i ↦ f i ∈ A)).card : ℝ) ≤ Real.sqrt (2 * (L : ℝ) * V) := by
  let Q := Finset.univ.filter (fun i : α ↦ f i ∈ A)
  have hsub : Q.image f ⊆ A.filter (fun x ↦ a ≤ x ∧ x < a + L) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2, hwindow i⟩
  have hcard : Q.card ≤ (A.filter (fun x ↦ a ≤ x ∧ x < a + L)).card := by
    rw [← Finset.card_image_of_injective Q hf]
    exact Finset.card_le_card hsub
  have hc : (Q.card : ℝ) ≤ (A.filter (fun x ↦ a ≤ x ∧ x < a + L)).card := by exact_mod_cast hcard
  exact hc.trans (window_card_bound A V hA a L)

lemma plus_filter_bound (A : Finset ℤ) (V : ℝ)
    (hA : ∀ z : ℤ, (pairCount A A z : ℝ) ≤ V) (a : ℤ) (L : ℕ) :
    ((Finset.univ.filter (fun i : Fin L ↦ a + (i.val : ℤ) ∈ A)).card : ℝ) ≤
      Real.sqrt (2 * (L : ℝ) * V) := by
  refine affine_filter_bound A V hA _ ?_ a L ?_
  · intro i j he
    apply Fin.ext
    exact_mod_cast add_left_cancel he
  · intro i
    have hi : (i.val : ℤ) < L := by exact_mod_cast i.isLt
    have hi0 : (0 : ℤ) ≤ i.val := by positivity
    constructor <;> omega

lemma minus_filter_bound (A : Finset ℤ) (V : ℝ)
    (hA : ∀ z : ℤ, (pairCount A A z : ℝ) ≤ V) (a : ℤ) (L : ℕ) :
    ((Finset.univ.filter (fun i : Fin L ↦ a - (i.val : ℤ) ∈ A)).card : ℝ) ≤
      Real.sqrt (2 * (L : ℝ) * V) := by
  refine affine_filter_bound A V hA _ ?_ (a - L + 1) L ?_
  · intro i j he
    apply Fin.ext
    have hh : (i.val : ℤ) = j.val := sub_right_injective he
    exact_mod_cast hh
  · intro i
    have hi : (i.val : ℤ) < L := by exact_mod_cast i.isLt
    have hi0 : (0 : ℤ) ≤ i.val := by positivity
    constructor <;> omega

lemma filter_or_card_le {α : Type*} [Fintype α] (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    (Finset.univ.filter (fun i ↦ P i ∨ Q i)).card ≤
      (Finset.univ.filter P).card + (Finset.univ.filter Q).card := by
  rw [Finset.filter_or]
  exact Finset.card_union_le _ _

/-- Both the forbidden choices and every mixed-count test have density at
most O(sqrt(V/L)) in a candidate interval of length L. -/
theorem interval_choice_bounds (A : Finset ℤ) (V : ℝ)
    (hA : ∀ z : ℤ, (pairCount A A z : ℝ) ≤ V) (n a : ℤ) (L : ℕ) :
    ((forbidden A n (fun i : Fin L ↦ a + (i.val : ℤ))).card : ℝ) ≤
        2 * Real.sqrt (2 * (L : ℝ) * V) ∧
      ∀ z : ℤ, ((hitChoices A n (fun i : Fin L ↦ a + (i.val : ℤ)) z).card : ℝ) ≤
        2 * Real.sqrt (2 * (L : ℝ) * V) := by
  constructor
  · have h₁ := plus_filter_bound A V hA a L
    have h₂ := minus_filter_bound A V hA (n - a) L
    have hh := filter_or_card_le (fun i : Fin L ↦ a + (i.val : ℤ) ∈ A)
      (fun i : Fin L ↦ n - (a + (i.val : ℤ)) ∈ A)
    have he : (Finset.univ.filter (fun i : Fin L ↦ n - (a + (i.val : ℤ)) ∈ A)) =
        Finset.univ.filter (fun i : Fin L ↦ n - a - (i.val : ℤ) ∈ A) := by
      apply Finset.filter_congr
      intro i hi
      rw [show n - (a + (i.val : ℤ)) = n - a - (i.val : ℤ) by ring]
    rw [he] at hh
    have hh' : ((forbidden A n (fun i : Fin L ↦ a + (i.val : ℤ))).card : ℝ) ≤
        (Finset.univ.filter (fun i : Fin L ↦ a + (i.val : ℤ) ∈ A)).card +
          (Finset.univ.filter (fun i : Fin L ↦ n - a - (i.val : ℤ) ∈ A)).card := by exact_mod_cast hh
    linarith
  · intro z
    have h₁ := minus_filter_bound A V hA (z - a) L
    have h₂ := plus_filter_bound A V hA (z - n + a) L
    have hh := filter_or_card_le (fun i : Fin L ↦ z - (a + (i.val : ℤ)) ∈ A)
      (fun i : Fin L ↦ z - (n - (a + (i.val : ℤ))) ∈ A)
    have he₁ : (Finset.univ.filter (fun i : Fin L ↦ z - (a + (i.val : ℤ)) ∈ A)) =
        Finset.univ.filter (fun i : Fin L ↦ z - a - (i.val : ℤ) ∈ A) := by
      apply Finset.filter_congr
      intro i hi
      rw [show z - (a + (i.val : ℤ)) = z - a - (i.val : ℤ) by ring]
    have he₂ : (Finset.univ.filter (fun i : Fin L ↦ z - (n - (a + (i.val : ℤ))) ∈ A)) =
        Finset.univ.filter (fun i : Fin L ↦ z - n + a + (i.val : ℤ) ∈ A) := by
      apply Finset.filter_congr
      intro i hi
      rw [show z - (n - (a + (i.val : ℤ))) = z - n + a + (i.val : ℤ) by ring]
    rw [he₁, he₂] at hh
    have hh' : ((hitChoices A n (fun i : Fin L ↦ a + (i.val : ℤ)) z).card : ℝ) ≤
        (Finset.univ.filter (fun i : Fin L ↦ z - a - (i.val : ℤ) ∈ A)).card +
          (Finset.univ.filter (fun i : Fin L ↦ z - n + a + (i.val : ℤ) ∈ A)).card := by exact_mod_cast hh
    linarith

end Erdos66LocalWindow
