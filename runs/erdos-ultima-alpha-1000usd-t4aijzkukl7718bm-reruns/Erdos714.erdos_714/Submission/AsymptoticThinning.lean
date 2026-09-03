import Submission.ClassThinning

/-! A uniform vanishing edge-density consequence of the verified averaging bound. -/

open Filter SimpleGraph Classical
open scoped Topology

namespace Erdos714ClassGraph

/-- An explicit coefficient tending to zero as the available biclique grows. -/
noncomputable def decayCoefficient (r t : ℕ) : ℝ :=
  (((r : ℝ)-1)^(1/(r : ℝ))/2 * (2:ℝ)^((2:ℝ)-1/(r:ℝ))) *
    (t:ℝ)^(-(1/(r:ℝ))) + ((r:ℝ)-1)*(t:ℝ)^(-1:ℝ)

lemma decay_nonneg {r : ℕ} (hr : 1 ≤ r) (t : ℕ) : 0 ≤ decayCoefficient r t := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hsub : 0 ≤ (r:ℝ)-1 := sub_nonneg.mpr hr'
  unfold decayCoefficient
  positivity

lemma decay_tendsto {r : ℕ} (hr : 1 ≤ r) :
    Tendsto (decayCoefficient r) atTop (𝓝 0) := by
  have hr' : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have h₁ := (tendsto_rpow_neg_atTop (one_div_pos.mpr hr')).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h₂ := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := (h₁.const_mul (((r : ℝ)-1)^(1/(r : ℝ))/2 *
    (2:ℝ)^((2:ℝ)-1/(r:ℝ)))).add (h₂.const_mul ((r:ℝ)-1))
  simpa only [decayCoefficient, mul_zero, add_zero, Function.comp_apply] using h

variable {Γ : Type*} [Group Γ] [Fintype Γ]

/-- Dividing the averaged KST bound gives an explicit density loss. -/
theorem thinning_density_bound (a : Γ) (H : SimpleGraph (Γ ⊕ Γ)) (r t : ℕ)
    (hr : 1 ≤ r) (ht : 0 < t) (hHG : H ≤ graph a)
    (hH : (completeBipartiteGraph (Fin r) (Fin r)).Free H)
    (hcopy : ¬ (completeBipartiteGraph (Fin t) (Fin t)).Free (graph a)) :
    (H.edgeFinset.card : ℝ) ≤ decayCoefficient r t * (graph a).edgeFinset.card := by
  have ht' : (0:ℝ)<t := by exact_mod_cast ht
  have hpow : (t:ℝ)^2 * (t:ℝ)^(-(1/(r:ℝ))) = (t:ℝ)^((2:ℝ)-1/(r:ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_add ht']
    rfl
  have hlin : (t:ℝ)^2 * (t:ℝ)^(-1:ℝ) = t := by
    rw [Real.rpow_neg_one]
    field_simp
  have hprod : (t:ℝ)^2 * decayCoefficient r t =
      ((r:ℝ)-1)^(1/(r:ℝ))/2 * ((2*t:ℕ):ℝ)^((2:ℝ)-1/(r:ℝ)) +
      ((r:ℝ)-1)/2 * ((2*t:ℕ):ℝ) := by
    push_cast
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) ht'.le]
    unfold decayCoefficient
    calc
      _ = (((r:ℝ)-1)^(1/(r:ℝ))/2 * (2:ℝ)^((2:ℝ)-1/(r:ℝ))) *
          ((t:ℝ)^2 * (t:ℝ)^(-(1/(r:ℝ)))) +
          ((r:ℝ)-1) * ((t:ℝ)^2 * (t:ℝ)^(-1:ℝ)) := by ring
      _ = _ := by rw [hpow, hlin]; ring
  have h := thinning_real_bound a H r t hr hHG hH hcopy
  rw [← hprod] at h
  exact (mul_le_mul_iff_right₀ (pow_pos ht' 2)).mp (by nlinarith [h])

/-- The threshold is independent of the group and the particular class host. -/
theorem eventual_density_bound (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, ∀ (a : Γ) (H : SimpleGraph (Γ ⊕ Γ)),
      H ≤ graph a → (completeBipartiteGraph (Fin r) (Fin r)).Free H →
      ¬ (completeBipartiteGraph (Fin t) (Fin t)).Free (graph a) →
      (H.edgeFinset.card : ℝ) ≤ ε * (graph a).edgeFinset.card := by
  filter_upwards [(decay_tendsto hr).eventually (eventually_lt_nhds hε),
    eventually_gt_atTop 0] with t hct ht
  intro a H hHG hH hcopy
  exact (thinning_density_bound a H r t hr ht hHG hH hcopy).trans
    (mul_le_mul_of_nonneg_right hct.le (by positivity))

/-- In a family of class hosts, growing bicliques force every free thinning's
edge fraction to tend to zero. Both the groups and the graphs may vary. -/
theorem density_tendsto_zero (K : ℕ → Type*) [∀ t, Group (K t)] [∀ t, Fintype (K t)]
    (a : ∀ t, K t) (H : ∀ t, SimpleGraph (K t ⊕ K t)) (r : ℕ) (hr : 1 ≤ r)
    (hHG : ∀ t, H t ≤ graph (a t))
    (hH : ∀ t, (completeBipartiteGraph (Fin r) (Fin r)).Free (H t))
    (hcopy : ∀ t, ¬ (completeBipartiteGraph (Fin t) (Fin t)).Free (graph (a t))) :
    Tendsto (fun t => (H t).edgeFinset.card / ((graph (a t)).edgeFinset.card : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => by positivity)) _ (decay_tendsto hr)
  filter_upwards [eventually_gt_atTop 0] with t ht
  exact div_le_of_le_mul₀ (by positivity) (decay_nonneg hr t)
    (thinning_density_bound (a t) (H t) r t hr ht (hHG t) (hH t) (hcopy t))

end Erdos714ClassGraph

#print axioms Erdos714ClassGraph.decay_tendsto
#print axioms Erdos714ClassGraph.thinning_density_bound
#print axioms Erdos714ClassGraph.eventual_density_bound

#print axioms Erdos714ClassGraph.density_tendsto_zero
