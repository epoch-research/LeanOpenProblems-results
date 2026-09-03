import Submission.PriorityHypergraphSelection

/-!
The integral version of the finite priority bound. The discretization error
is bounded directly by a monotone sum/integral comparison.
-/
namespace Erdos773.PriorityIntegralSelection
open Finset PriorityHypergraphSelection
set_option maxHeartbeats 1000000

lemma right_sum_lower (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Icc 0 1))
    (h0 : f 0 ≤ 1) (h1 : 0 ≤ f 1) (K : ℕ) (hK : 0 < K) :
    (∫ x in (0:ℝ)..1, f x) ≤
      (1/(K:ℝ))*(∑ t : Fin K, f (((t.val+1:ℕ):ℝ)/K)) + 1/K := by
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  have hg : AntitoneOn (fun x : ℝ => f (x/K)) (Set.Icc 0 (0+(K:ℝ))) := by
    intro x hx y hy hxy
    apply hf
    · exact ⟨div_nonneg hx.1 hK0.le,(div_le_one hK0).mpr (by simpa using hx.2)⟩
    · exact ⟨div_nonneg hy.1 hK0.le,(div_le_one hK0).mpr (by simpa using hy.2)⟩
    · exact div_le_div_of_nonneg_right hxy hK0.le
  have hi := hg.integral_le_sum
  simp only [zero_add] at hi
  rw [intervalIntegral.integral_comp_div f hK0.ne', zero_div, div_self hK0.ne',
    smul_eq_mul] at hi
  have ht := sum_range_sub' (fun i : ℕ => f ((i:ℝ)/K)) K
  rw [sum_sub_distrib] at ht
  simp only [Nat.cast_zero, zero_div, div_self hK0.ne'] at ht
  have he : (∑ t : Fin K, f (((t.val+1:ℕ):ℝ)/K)) =
      ∑ i ∈ range K, f (((i+1:ℕ):ℝ)/K) := Fin.sum_univ_eq_sum_range (fun i => f (((i+1:ℕ):ℝ)/K)) K
  rw [he]
  have hh : (K:ℝ)*(∫ x in (0:ℝ)..1, f x) ≤
      (∑ i ∈ range K, f (((i+1:ℕ):ℝ)/K)) + 1 := by linarith
  apply (mul_le_mul_iff_right₀ hK0).mp
  convert hh using 1; field_simp

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def linkFunction (H : Finset (Finset α)) (v : α) (x : ℝ) : ℝ :=
  ∏ e ∈ H.filter (fun e => v ∈ e), (1-x^(e.card-1))

omit [Fintype α] in
lemma linkFunction_nonneg (H : Finset (Finset α)) (v : α)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : 0 ≤ linkFunction H v x := by
  apply prod_nonneg
  intro e _
  exact sub_nonneg.mpr (pow_le_one₀ hx.1 hx.2)

omit [Fintype α] in
lemma linkFunction_antitone (H : Finset (Finset α)) (v : α) :
    AntitoneOn (linkFunction H v) (Set.Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  apply prod_le_prod
  · intro e _
    exact sub_nonneg.mpr (pow_le_one₀ hy.1 hy.2)
  · intro e _
    exact sub_le_sub_left (pow_le_pow_left₀ hx.1 hxy (e.card-1)) 1

omit [Fintype α] in
lemma linkFunction_le_one (H : Finset (Finset α)) (v : α)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : linkFunction H v x ≤ 1 := by
  apply prod_le_one
  · intro e _
    exact sub_nonneg.mpr (pow_le_one₀ hx.1 hx.2)
  · intro e _
    exact sub_le_self _ (pow_nonneg hx.1 _)

/-- The integral bound obtained by letting the number of priority levels grow.
The maximizing independent set is chosen once, before taking this limit. -/
theorem integral_selection (H : Finset (Finset α)) (hH : ∀ e ∈ H, e.Nonempty) :
    ∃ B : Finset α, (∀ e ∈ H, ¬ e ⊆ B) ∧
      (∑ v : α, ∫ x in (0:ℝ)..1, linkFunction H v x) ≤ B.card := by
  classical
  let I : Finset (Finset α) := univ.filter (fun B => ∀ e ∈ H, ¬ e ⊆ B)
  have hI : I.Nonempty := by
    refine ⟨∅,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    intro e he hh
    exact (hH e he).ne_empty (subset_empty.mp hh)
  obtain ⟨A,hAI,hmax⟩ := exists_max_image I (fun B => B.card) hI
  refine ⟨A,(mem_filter.mp hAI).2,?_⟩
  have hbound (K : ℕ) (hK : 0 < K) :
      (∑ v : α, ∫ x in (0:ℝ)..1, linkFunction H v x) ≤
        (A.card:ℝ)+(Fintype.card α:ℝ)/K := by
    obtain ⟨B,hB,hcost⟩ := finite_selection K hK H hH
    have hBc : (B.card:ℝ) ≤ A.card := by
      exact_mod_cast hmax B (mem_filter.mpr ⟨mem_univ _,hB⟩)
    have hi (v : α) := right_sum_lower (linkFunction H v) (linkFunction_antitone H v)
      (linkFunction_le_one H v (by norm_num : (0:ℝ) ∈ Set.Icc 0 1))
      (linkFunction_nonneg H v (by norm_num : (1:ℝ) ∈ Set.Icc 0 1)) K hK
    have hh := sum_le_sum (s := (univ : Finset α)) (fun v _ => hi v)
    rw [sum_add_distrib, sum_const, nsmul_eq_mul] at hh
    dsimp [linkFunction] at hh ⊢
    have hc : (Fintype.card α:ℝ)*(1/(K:ℝ)) = (Fintype.card α:ℝ)/K := by ring
    simp only [hc] at hh
    linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨K,hK⟩ := exists_nat_gt (max (1:ℝ) ((Fintype.card α:ℝ)/ε))
  have hK1 : (1:ℝ) < K := lt_of_le_of_lt (le_max_left _ _) hK
  have hKpos : 0 < K := by exact_mod_cast (show (0:ℝ)<K by linarith)
  have hK0 : (0:ℝ) < K := by exact_mod_cast hKpos
  have hn : (Fintype.card α:ℝ) < (K:ℝ)*ε :=
    (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_right _ _) hK)
  have hsmall : (Fintype.card α:ℝ)/K < ε := (div_lt_iff₀ hK0).mpr (by linarith)
  exact (hbound K hKpos).trans (by linarith)

/-- The Caro--Tuza integral bound for an `(r+1)`-uniform hypergraph. -/
theorem uniform_integral_selection (H : Finset (Finset α)) (r : ℕ)
    (hH : ∀ e ∈ H, e.card=r+1) :
    ∃ B : Finset α, (∀ e ∈ H, ¬ e ⊆ B) ∧
      (∑ v : α, ∫ x in (0:ℝ)..1,
        (1-x^r)^(H.filter (fun e => v ∈ e)).card) ≤ B.card := by
  have hne : ∀ e ∈ H, e.Nonempty := fun e he => card_pos.mp (by rw [hH e he]; omega)
  obtain ⟨B,hB,hcard⟩ := integral_selection H hne
  refine ⟨B,hB,?_⟩
  have he (v : α) (x : ℝ) : linkFunction H v x =
      (1-x^r)^(H.filter (fun e => v ∈ e)).card := by
    unfold linkFunction
    have hh : (∏ e ∈ H.filter (fun e => v ∈ e), (1-x^(e.card-1))) =
        ∏ _e ∈ H.filter (fun e => v ∈ e), (1-x^r) := by
      apply prod_congr rfl
      intro e he
      rw [hH e (mem_filter.mp he).1, Nat.add_sub_cancel]
    rw [hh, prod_const]
  simpa only [he] using hcard

#print axioms right_sum_lower
#print axioms integral_selection
#print axioms uniform_integral_selection
end Erdos773.PriorityIntegralSelection
