import Submission.ApproximateComplementarityExplore

/-! In a growing unit-mean family with sublinear self caps, a common upper
bound on distinct-pair mean-square errors cannot converge below one. -/
namespace Erdos66ComplementarityErrorFloor
open Filter Erdos66ApproximateComplementarity Erdos66CenteredMixedEnergy Erdos66CyclicVariance
open scoped Topology Classical
set_option maxHeartbeats 1800000

lemma normalized_numeric_bound {q k C E : ℝ} (hq : 0<q) (hk : 0<k+1)
    (h : q*(k-1) ≤ (k+1)*(C-1+(q-1)*E)) :
    1-2/(k+1) ≤ C/q-1/q+(1-1/q)*E := by
  calc
    _ = (k-1)/(k+1) := by field_simp; ring
    _ ≤ (C-1+(q-1)*E)/q := (div_le_div_iff₀ hk hq).mpr (by nlinarith [h])
    _ = _ := by field_simp

/-- Pure scalar limiting consequence of the finite family budget. -/
theorem numeric_limit_floor (q k C E : ℕ → ℝ) (e : ℝ)
    (hq : Tendsto q atTop atTop) (hk : Tendsto k atTop atTop)
    (hC : Tendsto (fun n ↦ C n/q n) atTop (𝓝 0))
    (hE : Tendsto E atTop (𝓝 e))
    (hbound : ∀ᶠ n in atTop, q n*(k n-1) ≤ (k n+1)*(C n-1+(q n-1)*E n)) :
    1≤e := by
  have hiq := hq.const_div_atTop (1 : ℝ)
  have hk1 : Tendsto (fun n ↦ k n+1) atTop atTop := hk.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hik := hk1.const_div_atTop (2 : ℝ)
  have hleft : Tendsto (fun n ↦ 1-2/(k n+1)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using hik.const_sub (1 : ℝ)
  have hright : Tendsto (fun n ↦ C n/q n-1/q n+(1-1/q n)*E n) atTop (𝓝 e) := by
    simpa only [sub_zero,one_mul,zero_add] using (hC.sub hiq).add ((hiq.const_sub 1).mul hE)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [hbound,hq.eventually_gt_atTop 0,hk.eventually_gt_atTop 0] with n hn hqn hkn
  exact normalized_numeric_bound hqn (by linarith) hn

/-- Concrete finite-group formulation. The ambient group size is k(n)^2,
each color has k(n) points, and both k(n) and the number of colors grow.
If the self-count cap is little-o of the number of colors, then any limiting
uniform mean-square error bound for distinct pairs is at least one. -/
theorem mixed_error_limit_ge_one
    (G I : ℕ → Type*) [∀ n, AddCommGroup (G n)] [∀ n, Fintype (G n)]
    [∀ n, Fintype (I n)] [∀ n, Nonempty (I n)]
    (B : (n : ℕ) → I n → Finset (G n)) (k : ℕ → ℕ) (C E : ℕ → ℝ) (e : ℝ)
    (hq : Tendsto (fun n ↦ Fintype.card (I n)) atTop atTop)
    (hk : Tendsto k atTop atTop)
    (hG : ∀ n, Fintype.card (G n)=(k n)^2)
    (hB : ∀ n i, (B n i).card=k n)
    (hself : ∀ n (i : I n) (z : G n), (((B n i).filter (fun x ↦ z-x∈B n i)).card : ℝ) ≤ C n)
    (hmixed : ∀ n (i j : I n), i≠j →
      centeredEnergy (indicator (B n i)) (indicator (B n j)) ≤ (k n : ℝ)^2*E n)
    (hC : Tendsto (fun n ↦ C n/(Fintype.card (I n) : ℝ)) atTop (𝓝 0))
    (hE : Tendsto E atTop (𝓝 e)) : 1≤e := by
  apply numeric_limit_floor (fun n ↦ (Fintype.card (I n) : ℝ)) (fun n ↦ (k n : ℝ)) C E e
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hq)
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hk) hC hE
  filter_upwards [hk.eventually_ge_atTop 2] with n hn
  exact approximate_complementary_family_bound (B n) (k n) hn (hG n) (hB n) (C n) (E n)
    (hmixed n) (hself n)

end Erdos66ComplementarityErrorFloor
