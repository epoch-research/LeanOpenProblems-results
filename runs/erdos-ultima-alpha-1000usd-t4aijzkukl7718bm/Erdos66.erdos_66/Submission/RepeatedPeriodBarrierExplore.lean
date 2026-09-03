import Submission.Explore

/-! A quantitative restriction on repeated-pattern gluing. A nonempty pattern
repeated throughout a macroscopic interval forces its period to be at least
of order N/log N in any putative witness. Consequently two such periods have
product much larger than N, precluding averaging over a full product period.
This is a restriction on one construction method, not a disproof. -/
namespace Erdos66RepeatedPeriodBarrier
open Filter AdditiveCombinatorics Erdos66Explore
open scoped Topology Classical

lemma finite_progression_sumRep_lower {A : Set ℕ} (a d K : ℕ) (hd : 0 < d)
    (hA : ∀ j ≤ K, a+d*j ∈ A) : K+1 ≤ sumRep A (2*a+d*K) := by
  let f : ℕ → ℕ × ℕ := fun j ↦ (a+d*j,a+d*(K-j))
  have hf : Function.Injective f := by
    intro i j hij
    have he : a+d*i=a+d*j := congrArg Prod.fst hij
    exact Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel he)
  have hs : (Finset.range (K+1)).image f ⊆
      (Finset.antidiagonal (2*a+d*K)).filter (fun p : ℕ × ℕ ↦ p.1∈A ∧ p.2∈A) := by
    intro p hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
    have hjK : j ≤ K := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr ?_,hA j hjK,hA (K-j) (by omega)⟩
    change a+d*j+(a+d*(K-j))=2*a+d*K
    have he := Nat.sub_add_cancel hjK
    nlinarith
  calc
    K+1 = (Finset.range (K+1)).card := (Finset.card_range _).symm
    _ = ((Finset.range (K+1)).image f).card := (Finset.card_image_of_injective _ hf).symm
    _ ≤ _ := Finset.card_le_card hs
    _ = _ := (sumRep_def _ _).symm

/-- An arithmetic progression contained in [N,4N], spanning at least N
when its final gap is included, has at most (c+1)log(6N) points. -/
lemma progression_length_bound {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a d K : ℕ,
      0 < d → N ≤ a → a ≤ 2*N → d*(K+1) ≤ 2*N →
      (∀ j ≤ K, a+d*j ∈ A) →
      ((K : ℝ)+1) ≤ (c+1)*Real.log (6*(N : ℝ)) := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp (h.eventually_lt_const (lt_add_one c))
  refine ⟨max M 2,fun N hN a d K hd ha ha' hspan hA ↦ ?_⟩
  let n := 2*a+d*K
  have hnM : M ≤ n := by dsimp [n]; omega
  have hn2 : 2 ≤ n := by dsimp [n]; omega
  have hn6 : n ≤ 6*N := by dsimp [n]; nlinarith
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hb : (sumRep A n : ℝ) ≤ (c+1)*Real.log n := by
    exact ((div_lt_iff₀ hlog).mp (hM n hnM)).le
  have hlow : (K : ℝ)+1 ≤ sumRep A n := by
    exact_mod_cast finite_progression_sumRep_lower a d K hd hA
  have hc0 : 0 ≤ c+1 := by linarith [limit_nonneg h]
  have hmono : Real.log (n : ℝ) ≤ Real.log (6*(N : ℝ)) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hn6)
  exact hlow.trans (hb.trans (mul_le_mul_of_nonneg_left hmono hc0))

/-- The period of a macroscopic fully repeated pattern is at least
N/((c+1)log(6N)). The hypothesis only needs one residue of that pattern. -/
theorem progression_period_bound {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a d K : ℕ,
      0 < d → N ≤ a → a ≤ 2*N → N ≤ d*(K+1) → d*(K+1) ≤ 2*N →
      (∀ j ≤ K, a+d*j ∈ A) →
      (N : ℝ) ≤ ((c+1)*Real.log (6*(N : ℝ)))*d := by
  obtain ⟨N₀,hN₀⟩ := progression_length_bound h
  refine ⟨N₀,fun N hN a d K hd ha ha' hspan hspan' hA ↦ ?_⟩
  have hh := mul_le_mul_of_nonneg_right (hN₀ N hN a d K hd ha ha' hspan' hA)
    (Nat.cast_nonneg (α := ℝ) d)
  have hs : (N : ℝ) ≤ d*((K : ℝ)+1) := by exact_mod_cast hspan
  nlinarith

lemma log_six_square_div_limit :
    Tendsto (fun N : ℕ ↦ (Real.log (6*(N : ℝ)))^2/(N : ℝ)) atTop (𝓝 0) := by
  have hx : Tendsto (fun N : ℕ ↦ 6*(N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ)<6)
  have hh := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero).comp hx
  have hh' := hh.const_mul 6
  simp only [mul_zero,Function.comp_def,Real.rpow_two,Real.rpow_one] at hh'
  apply hh'.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hne : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp

/-- If two proposed stages each retain a macroscopic complete repetition of
a nonempty pattern, the transition scale divided by the product of their
periods tends to zero, not infinity. Thus a full-product-period averaging
argument cannot be applied at that transition scale. -/
theorem scale_div_period_product_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (N a d K b e L : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hdata : ∀ᶠ k : ℕ in atTop,
      0 < d k ∧ N k ≤ a k ∧ a k ≤ 2*N k ∧
      N k ≤ d k*(K k+1) ∧ d k*(K k+1) ≤ 2*N k ∧
      (∀ j ≤ K k, a k+d k*j ∈ A) ∧
      0 < e k ∧ N k ≤ b k ∧ b k ≤ 2*N k ∧
      N k ≤ e k*(L k+1) ∧ e k*(L k+1) ≤ 2*N k ∧
      (∀ j ≤ L k, b k+e k*j ∈ A)) :
    Tendsto (fun k ↦ (N k : ℝ)/((d k : ℝ)*(e k : ℝ))) atTop (𝓝 0) := by
  obtain ⟨N₀,hbound⟩ := progression_period_bound h
  have hupper : Tendsto (fun k ↦ (c+1)^2*(Real.log (6*(N k : ℝ)))^2/(N k : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,mul_div_assoc] using
      (log_six_square_div_limit.comp hN).const_mul ((c+1)^2)
  refine squeeze_zero' (Eventually.of_forall (fun k ↦ by positivity)) ?_ hupper
  filter_upwards [hdata,hN.eventually (eventually_ge_atTop (max N₀ 1))] with k hk hNk
  obtain ⟨hd,ha,ha',hs,hs',hA,he,hb,hb',ht,ht',hB⟩ := hk
  have h₁ := hbound (N k) (by omega) (a k) (d k) (K k) hd ha ha' hs hs' hA
  have h₂ := hbound (N k) (by omega) (b k) (e k) (L k) he hb hb' ht ht' hB
  let x := (c+1)*Real.log (6*(N k : ℝ))
  have hx : 0 ≤ x := by
    apply mul_nonneg (by linarith [limit_nonneg h])
    apply Real.log_nonneg
    have hN1 : (1 : ℝ) ≤ N k := by exact_mod_cast (show 1≤N k by omega)
    linarith
  have hdp : (0 : ℝ) < d k := by exact_mod_cast hd
  have hep : (0 : ℝ) < e k := by exact_mod_cast he
  have hnp : (0 : ℝ) < N k := by exact_mod_cast (show 0<N k by omega)
  have hp : (N k : ℝ)^2 ≤ x^2*(d k : ℝ)*(e k : ℝ) := by
    have hh := mul_le_mul h₁ h₂ (Nat.cast_nonneg (α := ℝ) (N k))
      (mul_nonneg hx hdp.le)
    change (N k : ℝ)*(N k : ℝ) ≤ x*(d k : ℝ)*(x*(e k : ℝ)) at hh
    nlinarith
  have hquot : (N k : ℝ)/((d k : ℝ)*(e k : ℝ)) ≤ x^2/(N k : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos hdp hep) hnp).mpr
    nlinarith
  simpa only [x,mul_pow,mul_div_assoc] using hquot

end Erdos66RepeatedPeriodBarrier
