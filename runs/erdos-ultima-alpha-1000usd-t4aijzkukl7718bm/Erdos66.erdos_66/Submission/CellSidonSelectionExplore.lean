import Submission.BoundedFiberSelectionExplore
import Submission.SidonSelectionExplore

/-! Sidon sampling with additional bounded-fiber avoidance. In particular,
all endpoints can be required to occupy distinct cells of a prescribed map. -/
namespace Erdos66CellSidonSelection
open Erdos66UniformSelection Erdos66BoundedFiberSelection Erdos66SidonSelection
open scoped Classical
set_option maxHeartbeats 2200000
variable {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]
  [DecidableEq ι] [DecidableEq α]

theorem exists_sidon_extra_avoid_and_hits {κ ζ : Type*}
    (x : α → ℤ) (hx : Function.Injective x)
    (E : Finset κ) (P : κ → (ι → α) → Prop) (H : κ → ℕ)
    (hP : ∀ e ∈ E, ∃ i : ι, ∀ f : ι → α,
      (Finset.univ.filter (fun a ↦ P e (Function.update f i a))).card ≤ H e)
    (T : Finset ζ) (S : ζ → Finset α) (K R t : ℝ)
    (hS : ∀ z ∈ T, (S z).card ≤ K) (ht : 0 < t)
    (hsmall : ((Fintype.card ι : ℝ)^4 + ∑ e ∈ E, (H e : ℝ)) / Fintype.card α +
      T.card * Real.exp ((Fintype.card ι : ℝ) * Real.exp t * K / Fintype.card α - t*R) < 1) :
    ∃ ω : ι → α, Function.Injective ω ∧ (∀ e ∈ E, ¬ P e ω) ∧
      (∀ i j k l, x (ω i) + x (ω j) = x (ω k) + x (ω l) →
        (i = k ∧ j = l) ∨ (i = l ∧ j = k)) ∧
      ∀ z ∈ T, hits (S z) ω < R := by
  let Q : Finset (ι × ι × ι × ι) := Finset.univ.filter
    (fun q ↦ ¬ ((q.1 = q.2.2.1 ∧ q.2.1 = q.2.2.2) ∨
      (q.1 = q.2.2.2 ∧ q.2.1 = q.2.2.1)))
  let E' := Q.disjSum E
  let P' : ((ι × ι × ι × ι) ⊕ κ) → (ι → α) → Prop
    | .inl q, ω => x (ω q.1) + x (ω q.2.1) = x (ω q.2.2.1) + x (ω q.2.2.2)
    | .inr e, ω => P e ω
  let H' : ((ι × ι × ι × ι) ⊕ κ) → ℕ
    | .inl _ => 1
    | .inr e => H e
  have hP' : ∀ e ∈ E', ∃ i : ι, ∀ f : ι → α,
      (Finset.univ.filter (fun a ↦ P' e (Function.update f i a))).card ≤ H' e := by
    intro e he
    cases e with
    | inl q =>
      have hq : q ∈ Q := Finset.inl_mem_disjSum.mp he
      obtain ⟨i, hi⟩ := nontrivial_sum_collision_fiber x hx q.1 q.2.1 q.2.2.1 q.2.2.2
        (Finset.mem_filter.mp hq).2
      exact ⟨i, one_fiber_card_le_one (P' (.inl q)) i hi⟩
    | inr e => exact hP e (Finset.inr_mem_disjSum.mp he)
  have hcard : (Q.card : ℝ) ≤ (Fintype.card ι : ℝ)^4 := by
    have hq : Q.card ≤ Fintype.card (ι × ι × ι × ι) := Finset.card_le_univ _
    simp only [Fintype.card_prod] at hq
    exact_mod_cast (show Q.card ≤ Fintype.card ι^4 by nlinarith [hq])
  have hcost : (∑ e ∈ E', (H' e : ℝ)) ≤ (Fintype.card ι : ℝ)^4 + ∑ e ∈ E, (H e : ℝ) := by
    simp only [E', Finset.sum_disjSum, H', Nat.cast_one, Finset.sum_const,
      nsmul_eq_mul, mul_one]
    linarith only [hcard]
  have hsmall' : (∑ e ∈ E', (H' e : ℝ)) / Fintype.card α +
      T.card * Real.exp ((Fintype.card ι : ℝ) * Real.exp t * K / Fintype.card α - t*R) < 1 := by
    have hh := div_le_div_of_nonneg_right hcost (Nat.cast_nonneg (α := ℝ) (Fintype.card α))
    linarith
  obtain ⟨ω, havoid, hhits⟩ := exists_avoid_bounded_fibers_and_small_hits E' P' H' hP'
    T S K R t hS ht hsmall'
  have hsidon (i j k l : ι) (he : x (ω i) + x (ω j) = x (ω k) + x (ω l)) :
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
    by_contra hn
    have hq : (i, j, k, l) ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
    exact havoid (.inl (i, j, k, l)) (Finset.inl_mem_disjSum.mpr hq) he
  refine ⟨ω, ?_, ?_, hsidon, hhits⟩
  · intro i j he
    have hh := hsidon i i i j (by rw [he])
    tauto
  · intro e he
    exact havoid (.inr e) (Finset.inr_mem_disjSum.mpr he)

/-- Each choice supplies finitely many endpoint cells. A bounded fiber for
each endpoint map suffices to prevent collisions between all selected cells. -/
theorem exists_cell_sidon_avoid_and_hits {β γ ζ : Type*} [Fintype β]
    (x : α → ℤ) (hx : Function.Injective x) (cell : β → α → γ) (H : ℕ)
    (hfiber : ∀ b r, (Finset.univ.filter (fun a ↦ cell b a = r)).card ≤ H)
    (hsep : ∀ a, Function.Injective (fun b ↦ cell b a))
    (B : Finset α) (T : Finset ζ) (S : ζ → Finset α) (K R t : ℝ)
    (hS : ∀ z ∈ T, (S z).card ≤ K) (ht : 0 < t)
    (hsmall : ((Fintype.card ι : ℝ)^4 +
        (Fintype.card ι : ℝ)^2 * (Fintype.card β : ℝ)^2 * H + Fintype.card ι * B.card) /
        Fintype.card α + T.card *
        Real.exp ((Fintype.card ι : ℝ) * Real.exp t * K / Fintype.card α - t*R) < 1) :
    ∃ ω : ι → α, Function.Injective ω ∧ (∀ i, ω i ∉ B) ∧
      Function.Injective (fun p : ι × β ↦ cell p.2 (ω p.1)) ∧
      (∀ i j k l, x (ω i) + x (ω j) = x (ω k) + x (ω l) →
        (i = k ∧ j = l) ∨ (i = l ∧ j = k)) ∧
      ∀ z ∈ T, hits (S z) ω < R := by
  let C : Finset (ι × ι × β × β) := Finset.univ.filter (fun p ↦ p.1 ≠ p.2.1)
  let E := C.disjSum (Finset.univ : Finset ι)
  let P : ((ι × ι × β × β) ⊕ ι) → (ι → α) → Prop
    | .inl p, ω => cell p.2.2.1 (ω p.1) = cell p.2.2.2 (ω p.2.1)
    | .inr i, ω => ω i ∈ B
  let h : ((ι × ι × β × β) ⊕ ι) → ℕ
    | .inl _ => H
    | .inr _ => B.card
  have hP : ∀ e ∈ E, ∃ i : ι, ∀ f : ι → α,
      (Finset.univ.filter (fun a ↦ P e (Function.update f i a))).card ≤ h e := by
    intro e he
    cases e with
    | inl p =>
      have hp : p.1 ≠ p.2.1 := (Finset.mem_filter.mp (Finset.inl_mem_disjSum.mp he)).2
      refine ⟨p.1, fun f ↦ ?_⟩
      simpa only [P, h, Function.update_self, Function.update_of_ne hp.symm] using
        hfiber p.2.2.1 (cell p.2.2.2 (f p.2.1))
    | inr i =>
      refine ⟨i, fun f ↦ ?_⟩
      simp only [P, h, Function.update_self, Finset.filter_mem_eq_inter, Finset.univ_inter, le_refl]
  have hcard : (C.card : ℝ) ≤ (Fintype.card ι : ℝ)^2 * (Fintype.card β : ℝ)^2 := by
    have hc : C.card ≤ Fintype.card (ι × ι × β × β) := Finset.card_le_univ _
    simp only [Fintype.card_prod] at hc
    have hc' : C.card ≤ (Fintype.card ι)^2 * (Fintype.card β)^2 := by nlinarith [hc]
    exact_mod_cast hc'
  have hcost : (∑ e ∈ E, (h e : ℝ)) ≤
      (Fintype.card ι : ℝ)^2 * (Fintype.card β : ℝ)^2 * H + Fintype.card ι * B.card := by
    simp only [E, Finset.sum_disjSum, h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hh := mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg H)
    linarith only [hh]
  have hsmall' : ((Fintype.card ι : ℝ)^4 + ∑ e ∈ E, (h e : ℝ)) / Fintype.card α +
      T.card * Real.exp ((Fintype.card ι : ℝ) * Real.exp t * K / Fintype.card α - t*R) < 1 := by
    have hh := div_le_div_of_nonneg_right (add_le_add_left hcost ((Fintype.card ι : ℝ)^4))
      (Nat.cast_nonneg (α := ℝ) (Fintype.card α))
    simp only [add_div] at hh hsmall ⊢
    linarith
  obtain ⟨ω, hω, havoid, hsidon, hhits⟩ := exists_sidon_extra_avoid_and_hits x hx E P h hP
    T S K R t hS ht hsmall'
  refine ⟨ω, hω, ?_, ?_, hsidon, hhits⟩
  · intro i
    exact havoid (.inr i) (Finset.inr_mem_disjSum.mpr (Finset.mem_univ i))
  · rintro ⟨i, b⟩ ⟨j, c⟩ he
    have hij : i = j := by
      by_contra hn
      have hh : (i, j, b, c) ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
      exact havoid (.inl (i, j, b, c)) (Finset.inl_mem_disjSum.mpr hh) he
    subst j
    exact Prod.ext rfl (hsep (ω i) he)

end Erdos66CellSidonSelection
