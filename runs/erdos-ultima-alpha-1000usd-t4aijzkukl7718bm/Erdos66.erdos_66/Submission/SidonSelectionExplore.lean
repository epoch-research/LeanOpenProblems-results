import Submission.UniformSelectionExplore

/-! Selecting a Sidon family while simultaneously controlling its intersections
with a prescribed finite family of sets. -/
namespace Erdos66SidonSelection
open Erdos66UniformSelection
open scoped Classical
set_option maxHeartbeats 1000000
variable {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]
  [DecidableEq ι] [DecidableEq α]

lemma nontrivial_sum_collision_fiber (x : α → ℤ) (hx : Function.Injective x)
    (i j k l : ι) (hne : ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k))) :
    ∃ v : ι, ∀ f : ι → α, ∀ a b : α,
      x (Function.update f v a i) + x (Function.update f v a j) =
        x (Function.update f v a k) + x (Function.update f v a l) →
      x (Function.update f v b i) + x (Function.update f v b j) =
        x (Function.update f v b k) + x (Function.update f v b l) → a = b := by
  by_cases hik : i = k
  · subst k
    have hjl : j ≠ l := by tauto
    refine ⟨j, fun f a b ha hb ↦ hx ?_⟩
    have ha' := add_left_cancel ha
    have hb' := add_left_cancel hb
    simp only [Function.update_self, Function.update_of_ne hjl.symm] at ha' hb'
    exact ha'.trans hb'.symm
  by_cases hil : i = l
  · subst l
    have hjk : j ≠ k := by tauto
    refine ⟨j, fun f a b ha hb ↦ hx ?_⟩
    have ha' : x (Function.update f j a j) = x (Function.update f j a k) := by linarith
    have hb' : x (Function.update f j b j) = x (Function.update f j b k) := by linarith
    simp only [Function.update_self, Function.update_of_ne hjk.symm] at ha' hb'
    exact ha'.trans hb'.symm
  refine ⟨i, fun f a b ha hb ↦ hx ?_⟩
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self, Function.update_of_ne (Ne.symm hik),
      Function.update_of_ne (Ne.symm hil)] at ha hb
    omega
  · simp only [Function.update_self, Function.update_of_ne (Ne.symm hik),
      Function.update_of_ne (Ne.symm hil), Function.update_of_ne hji] at ha hb
    omega

/-- This includes injectivity: a repeated selected point is a nontrivial
collision between a diagonal sum and a mixed sum. -/
theorem exists_sidon_avoid_and_hits {ζ : Type*}
    (x : α → ℤ) (hx : Function.Injective x) (B : Finset α)
    (T : Finset ζ) (S : ζ → Finset α) (K R t : ℝ)
    (hS : ∀ z ∈ T, (S z).card ≤ K) (ht : 0 < t)
    (hsmall : ((Fintype.card ι : ℝ) ^ 4 + Fintype.card ι * B.card) / Fintype.card α +
      T.card * Real.exp ((Fintype.card ι : ℝ) * Real.exp t * K / Fintype.card α - t * R) < 1) :
    ∃ ω : ι → α, Function.Injective ω ∧ (∀ i, ω i ∉ B) ∧
      (∀ i j k l, x (ω i) + x (ω j) = x (ω k) + x (ω l) →
        (i = k ∧ j = l) ∨ (i = l ∧ j = k)) ∧
      ∀ z ∈ T, hits (S z) ω < R := by
  let Q : Finset (ι × ι × ι × ι) := Finset.univ.filter
    (fun q ↦ ¬ ((q.1 = q.2.2.1 ∧ q.2.1 = q.2.2.2) ∨
      (q.1 = q.2.2.2 ∧ q.2.1 = q.2.2.1)))
  let D : Finset (ι × α) := Finset.univ.product B
  let E := Q.disjSum D
  let P : ((ι × ι × ι × ι) ⊕ (ι × α)) → (ι → α) → Prop
    | .inl q, ω => x (ω q.1) + x (ω q.2.1) = x (ω q.2.2.1) + x (ω q.2.2.2)
    | .inr q, ω => ω q.1 = q.2
  have hP : ∀ e ∈ E, ∃ v : ι, ∀ f : ι → α, ∀ a b : α,
      P e (Function.update f v a) → P e (Function.update f v b) → a = b := by
    intro e he
    cases e with
    | inl q =>
      have hq : q ∈ Q := Finset.inl_mem_disjSum.mp he
      exact nontrivial_sum_collision_fiber x hx q.1 q.2.1 q.2.2.1 q.2.2.2
        (Finset.mem_filter.mp hq).2
    | inr q =>
      refine ⟨q.1, fun f a b ha hb ↦ ?_⟩
      dsimp only [P] at ha hb
      simp only [Function.update_self] at ha hb
      exact ha.trans hb.symm
  have hcard : (E.card : ℝ) ≤ (Fintype.card ι : ℝ) ^ 4 + Fintype.card ι * B.card := by
    have hq : Q.card ≤ Fintype.card (ι × ι × ι × ι) := Finset.card_le_univ _
    have hq' : (Q.card : ℝ) ≤ (Fintype.card ι : ℝ) ^ 4 := by
      simp only [Fintype.card_prod] at hq
      exact_mod_cast (show Q.card ≤ Fintype.card ι ^ 4 by nlinarith [hq])
    simp only [E, D, Finset.card_disjSum, Finset.product_eq_sprod,
      Finset.card_product, Finset.card_univ, Nat.cast_add, Nat.cast_mul]
    linarith
  have hsmall' : (E.card : ℝ) / Fintype.card α +
      T.card * Real.exp ((Fintype.card ι : ℝ) * Real.exp t * K / Fintype.card α - t * R) < 1 := by
    have hh := div_le_div_of_nonneg_right hcard (Nat.cast_nonneg (α := ℝ) (Fintype.card α))
    linarith
  obtain ⟨ω, havoid, hhits⟩ := exists_avoid_and_small_hits E P hP T S K R t hS ht hsmall'
  have hsidon (i j k l : ι) (he : x (ω i) + x (ω j) = x (ω k) + x (ω l)) :
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
    by_contra hn
    have hq : (i, j, k, l) ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
    exact havoid (.inl (i, j, k, l)) (Finset.inl_mem_disjSum.mpr hq) he
  refine ⟨ω, ?_, ?_, hsidon, hhits⟩
  · intro i j hij
    have hh := hsidon i i i j (by rw [hij])
    tauto
  · intro i hi
    have hd : (i, ω i) ∈ D := Finset.mem_product.mpr ⟨Finset.mem_univ _, hi⟩
    exact havoid (.inr (i, ω i)) (Finset.inr_mem_disjSum.mpr hd) rfl

end Erdos66SidonSelection
