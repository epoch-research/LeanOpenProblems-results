import FormalConjecturesUtil
import Submission.UniformIncidence

/-! Uniform low-degree control on near-extremal hosts. These necessary
conditions do not establish rationality of the extremal exponent. -/
open Filter SimpleGraph Finset Asymptotics
open scoped Topology Classical
namespace Erdos713UniformLowDegree
set_option maxHeartbeats 2000000

lemma small_deletion_gain {α c a ε : ℝ} (hα : 1 < α) (hc : 0 < c)
    (ha : a < c*α) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ t < ε ∧ a*t < c*(1-(1-t)^α) := by
  have hcont : ContinuousAt (fun x : ℝ => c*α*(1-x)^(α-1)) 0 := by
    fun_prop (disch := left; norm_num)
  have hh : ∀ᶠ x : ℝ in 𝓝 0, a < c*α*(1-x)^(α-1) := by
    exact hcont.tendsto.eventually_const_lt (by simpa using ha)
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hh
  let t := min (min (δ/2) (ε/2)) (1/2 : ℝ)
  have ht : 0 < t := lt_min (lt_min (by positivity) (by positivity)) (by norm_num)
  have htδ : t ≤ δ/2 := (min_le_left _ _).trans (min_le_left _ _)
  have htε : t ≤ ε/2 := (min_le_left _ _).trans (min_le_right _ _)
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hh' : a < c*α*(1-t)^(α-1) := hball (by
    simpa only [Real.dist_eq,sub_zero,abs_of_pos ht] using (show t < δ by linarith))
  have hs := (convexOn_rpow hα.le).le_slope_of_hasDerivAt
    (show 1-t ∈ Set.Ici (0 : ℝ) by simpa using (sub_pos.mpr ht1).le)
    (show (1 : ℝ) ∈ Set.Ici 0 by simp)
    (show 1-t < 1 by linarith)
    (Real.hasDerivAt_rpow_const (Or.inr hα.le))
  simp only [slope_def_field,Real.one_rpow,sub_sub_cancel] at hs
  have hs' := (le_div_iff₀ ht).mp hs
  have hm := mul_le_mul_of_nonneg_left hs' hc.le
  refine ⟨t,ht,ht1,by linarith,?_⟩
  have hl := mul_lt_mul_of_pos_right hh' ht
  nlinarith only [hm,hl]

lemma floor_fraction_le {t : ℝ} (ht : t ≤ 1) (n : ℕ) : ⌊t*(n : ℝ)⌋₊ ≤ n := by
  apply Nat.floor_le_of_le
  nlinarith only [ht,Nat.cast_nonneg (α := ℝ) n]

lemma remaining_ratio {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    Tendsto (fun n : ℕ => ((n-⌊t*(n : ℝ)⌋₊ : ℕ) : ℝ)/(n : ℝ))
      atTop (𝓝 (1-t)) := by
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub
    ((tendsto_nat_floor_mul_div_atTop ht.le).comp tendsto_natCast_atTop_atTop)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [Nat.cast_sub (floor_fraction_le ht1.le n),sub_div]
  rw [div_self (by exact_mod_cast (Nat.ne_of_gt hn))]
  rfl

lemma remaining_atTop {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    Tendsto (fun n : ℕ => n-⌊t*(n : ℝ)⌋₊) atTop atTop := by
  have hm : Tendsto (fun n : ℕ => ⌊(1-t)*(n : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (sub_pos.mpr ht1))
  apply tendsto_atTop_mono (fun n => ?_) hm
  have h1 := Nat.floor_le (show 0 ≤ t*(n : ℝ) by positivity)
  have h2 := Nat.floor_le (mul_nonneg (sub_pos.mpr ht1).le (Nat.cast_nonneg n))
  have hsum : ⌊(1-t)*(n : ℝ)⌋₊ + ⌊t*(n : ℝ)⌋₊ ≤ n := by
    have : (⌊(1-t)*(n : ℝ)⌋₊ : ℝ) + (⌊t*(n : ℝ)⌋₊ : ℝ) ≤ n := by linarith
    exact_mod_cast this
  omega

lemma remaining_power_ratio {f : ℕ → ℝ} {α c t : ℝ}
    (ht : 0 < t) (ht1 : t < 1)
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) :
    Tendsto (fun n : ℕ => f (n-⌊t*(n : ℝ)⌋₊)/(n : ℝ)^α)
      atTop (𝓝 (c*(1-t)^α)) := by
  have hm := remaining_atTop ht ht1
  have hp := (remaining_ratio ht ht1).rpow_const (p := α)
    (Or.inl (sub_pos.mpr ht1).ne')
  have hh := ((Erdos713FutureRecords.ratio_limit hf).comp hm).mul hp
  apply hh.congr'
  filter_upwards [hm.eventually_gt_atTop 0,eventually_gt_atTop (0 : ℕ)] with n hm' hn
  have hmR : (0 : ℝ) < (n-⌊t*(n : ℝ)⌋₊ : ℕ) := by exact_mod_cast hm'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp_apply,Real.div_rpow hmR.le hnR.le]
  field_simp [(Real.rpow_pos_of_pos hmR α).ne']

lemma deletion_gap_limit {f : ℕ → ℝ} {α c t a : ℝ}
    (ht : 0 < t) (ht1 : t < 1)
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) :
    Tendsto (fun n : ℕ =>
      (f n-f (n-⌊t*(n : ℝ)⌋₊)-(⌊t*(n : ℝ)⌋₊ : ℝ)*a*(n : ℝ)^(α-1))/(n : ℝ)^α)
      atTop (𝓝 (c*(1-(1-t)^α)-a*t)) := by
  have hs := ((tendsto_nat_floor_mul_div_atTop ht.le).comp
    tendsto_natCast_atTop_atTop).const_mul a
  have hh := ((Erdos713FutureRecords.ratio_limit hf).sub
    (remaining_power_ratio ht ht1 hf)).sub hs
  have he : c-c*(1-t)^α-a*t = c*(1-(1-t)^α)-a*t := by ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp_apply]
  rw [Real.rpow_sub_one hnR.ne']
  field_simp [hnR.ne',(Real.rpow_pos_of_pos hnR α).ne']

/-- A finite deletion test, applicable to every near-extremal host. -/
lemma low_card_lt_of_gap {W : Type*} (H : SimpleGraph W) {n s : ℕ}
    (G : SimpleGraph (Fin n)) (hf : H.Free G) {D L : ℝ}
    (he : (extremalNumber n H : ℝ)-L ≤ (Nat.card G.edgeSet : ℝ))
    (hgap : L + (s : ℝ)*D < (extremalNumber n H : ℝ)-(extremalNumber (n-s) H : ℝ)) :
    (univ.filter (fun v => (Nat.card (G.neighborSet v) : ℝ) ≤ D)).card < s := by
  by_contra hh
  obtain ⟨S,hS,hcard⟩ := exists_subset_card_eq (Nat.le_of_not_gt hh)
  have hfree : H.Free (G.induce (S : Set (Fin n))ᶜ) := by
    intro hc
    exact hf (hc.trans ⟨Copy.induce G _⟩)
  have hremain : Nat.card (G.induce (S : Set (Fin n))ᶜ).edgeSet ≤ extremalNumber (n-s) H := by
    have hb := card_edgeFinset_le_extremalNumber hfree
    have hcS : Fintype.card (S : Set (Fin n)) = s := by simpa using hcard
    rw [Fintype.card_compl_set,hcS,Fintype.card_fin] at hb
    simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using hb
  have hsum : (∑ v ∈ S, (Nat.card (G.neighborSet v) : ℝ)) ≤ (s : ℝ)*D := by
    have hb := sum_le_sum (s := S) (fun v hv => (mem_filter.mp (hS hv)).2)
    simpa only [sum_const,nsmul_eq_mul,hcard] using hb
  have hdel : (Nat.card G.edgeSet : ℝ) ≤
      (Nat.card (G.induce (S : Set (Fin n))ᶜ).edgeSet : ℝ)+
        ∑ v ∈ S, (Nat.card (G.neighborSet v) : ℝ) := by
    exact_mod_cast Erdos713UniformIncidence.edges_le_induce_compl_add_degree G S
  have hremR : (Nat.card (G.induce (S : Set (Fin n))ᶜ).edgeSet : ℝ) ≤
      (extremalNumber (n-s) H : ℝ) := by exact_mod_cast hremain
  linarith

/-- For each fixed accuracy there is a uniform relative edge tolerance:
all hosts within that tolerance have few vertices below any subcritical
minimum-degree coefficient. No consecutive-difference limit is assumed. -/
theorem near_extremal_few_low {W : Type*} (H : SimpleGraph W) {α c a ε : ℝ}
    (hα : 1 < α) (hc : 0 < c) (ha : a < c*α) (hε : 0 < ε)
    (hf : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), H.Free G →
        (extremalNumber n H : ℝ)-δ*(n : ℝ)^α ≤ (Nat.card G.edgeSet : ℝ) →
        ((univ.filter (fun v => (Nat.card (G.neighborSet v) : ℝ) ≤
          a*(n : ℝ)^(α-1))).card : ℝ) < ε*n := by
  obtain ⟨t,ht,ht1,htε,hgain⟩ := small_deletion_gain hα hc ha hε
  let δ := (c*(1-(1-t)^α)-a*t)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδg : δ < c*(1-(1-t)^α)-a*t := by dsimp [δ]; linarith
  have hg := (deletion_gap_limit (a := a) ht ht1 hf).eventually_const_lt hδg
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hg,eventually_gt_atTop (0 : ℕ)] with n hn hnp
  intro G hfree he
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnp
  have hgap := (lt_div_iff₀ (Real.rpow_pos_of_pos hnR α)).mp hn
  have hcount := low_card_lt_of_gap H G hfree he
    (s := ⌊t*(n : ℝ)⌋₊) (D := a*(n : ℝ)^(α-1)) (by linarith only [hgap])
  have hcR : ((univ.filter (fun v => (Nat.card (G.neighborSet v) : ℝ) ≤
      a*(n : ℝ)^(α-1))).card : ℝ) < (⌊t*(n : ℝ)⌋₊ : ℝ) := by exact_mod_cast hcount
  exact hcR.trans_le ((Nat.floor_le (by positivity)).trans
    (mul_le_mul_of_nonneg_right htε.le hnR.le))

/-- In particular this bound holds uniformly over all exactly extremal hosts
at every sufficiently large order, not merely at selected support orders. -/
theorem exact_few_low {W : Type*} (H : SimpleGraph W) {α c a ε : ℝ}
    (hα : 1 < α) (hc : 0 < c) (ha : a < c*α) (hε : 0 < ε)
    (hf : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), G.IsExtremal H.Free →
      ((univ.filter (fun v => (Nat.card (G.neighborSet v) : ℝ) ≤
        a*(n : ℝ)^(α-1))).card : ℝ) < ε*n := by
  obtain ⟨δ,hδ,hbound⟩ := near_extremal_few_low H hα hc ha hε hf
  filter_upwards [hbound] with n hn
  intro G hG
  have he : Nat.card G.edgeSet = extremalNumber n H := by
    simpa only [edgeFinset_card,Fintype.card_eq_nat_card,Nat.card_fin] using
      card_edgeFinset_of_isExtremal_free hG
  apply hn G hG.prop
  rw [he]
  exact sub_le_self _ (by positivity)

/-- A sequence of H-free hosts with the full asymptotic coefficient has a
vanishing proportion of vertices below any coefficient a<c*alpha. -/
theorem low_fraction_tendsto_zero {W : Type*} (H : SimpleGraph W)
    (G : (n : ℕ) → SimpleGraph (Fin n)) {α c a : ℝ}
    (hα : 1 < α) (hc : 0 < c) (ha : a < c*α)
    (hf : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α))
    (hfree : ∀ n, H.Free (G n))
    (hG : (fun n : ℕ => (Nat.card (G n).edgeSet : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    Tendsto (fun n : ℕ =>
      ((univ.filter (fun v => (Nat.card ((G n).neighborSet v) : ℝ) ≤
        a*(n : ℝ)^(α-1))).card : ℝ)/(n : ℝ)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall (fun n => hb.trans_le (by positivity))
  · intro ε hε
    obtain ⟨δ,hδ,hbound⟩ := near_extremal_few_low H hα hc ha hε hf
    have hh := (Erdos713FutureRecords.ratio_limit hf).sub
      (Erdos713FutureRecords.ratio_limit hG)
    rw [sub_self] at hh
    filter_upwards [hbound,hh.eventually_lt_const hδ,
      eventually_gt_atTop (0 : ℕ)] with n hn hsmall hnp
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnp
    have hnear : (extremalNumber n H : ℝ)-δ*(n : ℝ)^α ≤
        (Nat.card (G n).edgeSet : ℝ) := by
      rw [← sub_div] at hsmall
      have hmul := (div_lt_iff₀ (Real.rpow_pos_of_pos hnR α)).mp hsmall
      linarith
    exact (div_lt_iff₀ hnR).mpr (hn (G n) (hfree n) hnear)

#print axioms exact_few_low
#print axioms low_fraction_tendsto_zero

#print axioms near_extremal_few_low
end Erdos713UniformLowDegree
