import FormalConjecturesUtil

/-! Future power-ratio records yield small forward increments along an
unbounded sequence. This is a numerical consequence, not rationality. -/
open Filter Asymptotics Finset
open scoped Topology
namespace Erdos713FutureRecords

lemma ratio_limit {f : ℕ → ℝ} {α c : ℝ}
    (h : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) :
    Tendsto (fun n : ℕ => f n/(n : ℝ)^α) atTop (𝓝 c) := by
  have hd : (fun n : ℕ => f n/(n : ℝ)^α) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α/(n : ℝ)^α) := h.div .refl
  apply IsEquivalent.tendsto_const
  apply hd.congr_right
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos (by exact_mod_cast hn) α).ne'

lemma higher_ratio_zero {f : ℕ → ℝ} {α c r : ℝ} (har : α < r)
    (h : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) :
    Tendsto (fun n : ℕ => f n/(n : ℝ)^r) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => (n : ℝ)^(α-r)) atTop (𝓝 0) := by
    simpa only [neg_sub] using (tendsto_rpow_neg_atTop (sub_pos.mpr har)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := (ratio_limit h).mul hp
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_sub hpos]
  field_simp [(Real.rpow_pos_of_pos hpos α).ne']

lemma eventually_pos {f : ℕ → ℝ} {α c : ℝ} (hc : 0 < c)
    (h : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) : ∀ᶠ n in atTop, 0 < f n := by
  filter_upwards [(ratio_limit h).eventually_const_lt hc,eventually_gt_atTop (0 : ℕ)] with n hn hnp
  have hp := Real.rpow_pos_of_pos (show (0 : ℝ) < n by exact_mod_cast hnp) α
  exact (div_pos_iff_of_pos_right hp).mp hn

lemma exists_tail_max {f : ℕ → ℝ} (h : Tendsto f atTop (𝓝 0)) (N : ℕ) (hN : 0 < f N) :
    ∃ n, N ≤ n ∧ 0 < f n ∧ ∀ j, N ≤ j → f j ≤ f n := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp (h.eventually_lt_const hN)
  obtain ⟨n,hn,hmax⟩ := (Icc N (max N M)).exists_max_image f ⟨N,by simp⟩
  have hNn := hmax N (by simp)
  refine ⟨n,(mem_Icc.mp hn).1,hN.trans_le hNn,?_⟩
  intro j hNj
  by_cases hj : j ≤ max N M
  · exact hmax j (mem_Icc.mpr ⟨hNj,hj⟩)
  · exact (hM j (by omega)).le.trans hNn

lemma increment_upper {x r : ℝ} (hx : 0 ≤ x) (hr : 1 ≤ r) :
    (x+1)^r-x^r ≤ r*(x+1)^(r-1) := by
  have hh := (convexOn_rpow hr).slope_le_of_hasDerivAt
    (show x ∈ Set.Ici (0 : ℝ) from hx)
    (show x+1 ∈ Set.Ici (0 : ℝ) from by change 0 ≤ x+1; linarith)
    (show x < x+1 by linarith) (Real.hasDerivAt_rpow_const (Or.inr hr))
  simpa only [slope_def_field,add_sub_cancel_left,div_one] using hh

lemma eventual_increment_upper {r s : ℝ} (hr : 1 ≤ r) (hrs : r < s) :
    ∀ᶠ n : ℕ in atTop, ((n : ℝ)+1)^r-(n : ℝ)^r ≤ s*(n : ℝ)^(r-1) := by
  have hRatio : Tendsto (fun n : ℕ => (1+1/(n : ℝ))^(r-1)) atTop (𝓝 1) := by
    have hb : Tendsto (fun n : ℕ => 1+1/(n : ℝ)) atTop (𝓝 (1+0 : ℝ)) :=
      tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using hb.rpow_const (p := r-1) (Or.inr (sub_nonneg.mpr hr))
  have hT : Tendsto (fun n : ℕ => r*(1+1/(n : ℝ))^(r-1)) atTop (𝓝 r) := by
    simpa using hRatio.const_mul r
  filter_upwards [hT.eventually_lt_const hrs,eventually_gt_atTop (0 : ℕ)] with n hn hnp
  have hp : (0 : ℝ) < n := by exact_mod_cast hnp
  have he : ((n : ℝ)+1)^(r-1) = (1+1/(n : ℝ))^(r-1)*(n : ℝ)^(r-1) := by
    rw [← Real.mul_rpow (by positivity) hp.le]
    congr 1
    field_simp
  have hi := increment_upper hp.le hr
  rw [he] at hi
  have hm := mul_le_mul_of_nonneg_right hn.le (Real.rpow_nonneg hp.le (r-1))
  nlinarith

lemma change_ratio (f : ℕ → ℝ) (r s : ℝ) {n : ℕ} (hn : 0 < n) :
    f n/(n : ℝ)^r = (f n/(n : ℝ)^s)*(n : ℝ)^(s-r) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_sub hp]
  field_simp [(Real.rpow_pos_of_pos hp s).ne']

lemma lower_ratio_top {f : ℕ → ℝ} {α c r : ℝ} (hra : r < α) (hc : 0 < c)
    (h : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) :
    Tendsto (fun n : ℕ => f n/(n : ℝ)^r) atTop atTop := by
  have hp : Tendsto (fun n : ℕ => (n : ℝ)^(α-r)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hra)).comp tendsto_natCast_atTop_atTop
  apply ((ratio_limit h).pos_mul_atTop hc hp).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (change_ratio f r α hn).symm

lemma exists_past_record {f : ℕ → ℝ} {α c r : ℝ} (hra : r < α) (hc : 0 < c)
    (h : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) (N : ℕ) :
    ∃ n, N ≤ n ∧ 0 < n ∧ 0 < f n ∧
      ∀ j, j ≤ n → f j/(j : ℝ)^r ≤ f n/(n : ℝ)^r := by
  let g : ℕ → ℝ := fun n => f n/(n : ℝ)^r
  obtain ⟨j,hj,hsmall⟩ := (range (N+1)).exists_max_image g ⟨0,by simp⟩
  obtain ⟨p,hp⟩ := ((lower_ratio_top hra hc h).eventually_gt_atTop (max (g j) 0)).exists
  obtain ⟨n,hn,hmax⟩ := (range (p+1)).exists_max_image g ⟨p,by simp⟩
  have hnlarge : max (g j) 0 < g n := hp.trans_le (hmax p (by simp))
  have hN : N < n := by
    by_contra hNn
    have hh := hsmall n (mem_range.mpr (by omega))
    exact (not_lt_of_ge hh) ((le_max_left _ _).trans_lt hnlarge)
  have hnp : 0 < n := by omega
  have hpos : 0 < f n :=
    (div_pos_iff_of_pos_right (Real.rpow_pos_of_pos (by exact_mod_cast hnp) r)).mp
      ((le_max_right _ _).trans_lt hnlarge)
  refine ⟨n,hN.le,hnp,hpos,?_⟩
  intro k hk
  exact hmax k (mem_range.mpr (by have := mem_range.mp hn; omega))

/-- Taking a maximum of the higher-exponent ratio over a tail preserves the
past lower-exponent record. Both controls concern the same index. -/
lemma exists_two_sided_record {f : ℕ → ℝ} {α c r s : ℝ} (hra : r < α) (has : α < s)
    (hc : 0 < c) (h : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) (N : ℕ) :
    ∃ n, N ≤ n ∧ 0 < n ∧ 0 < f n ∧
      (∀ j, 0 < j → j ≤ n → f j/(j : ℝ)^r ≤ f n/(n : ℝ)^r) ∧
      (∀ j, n ≤ j → f j/(j : ℝ)^s ≤ f n/(n : ℝ)^s) := by
  obtain ⟨m,hm,hmp,hmf,hpast⟩ := exists_past_record hra hc h N
  obtain ⟨n,hmn,hnpos,htail⟩ := exists_tail_max (higher_ratio_zero has h) m
    (div_pos hmf (Real.rpow_pos_of_pos (by exact_mod_cast hmp) s))
  have hnp : 0 < n := hmp.trans_le hmn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnp
  have hnf : 0 < f n := (div_pos_iff_of_pos_right (Real.rpow_pos_of_pos hnreal s)).mp hnpos
  have htransfer {j : ℕ} (hjp : 0 < j) (hjn : j ≤ n)
      (hj : f j/(j : ℝ)^s ≤ f n/(n : ℝ)^s) :
      f j/(j : ℝ)^r ≤ f n/(n : ℝ)^r := by
    rw [change_ratio f r s hjp,change_ratio f r s hnp]
    exact mul_le_mul hj
      (Real.rpow_le_rpow (Nat.cast_nonneg j) (by exact_mod_cast hjn) (by linarith))
      (Real.rpow_nonneg (Nat.cast_nonneg j) (s-r)) hnpos.le
  refine ⟨n,hm.trans hmn,hnp,hnf,?_,fun j hj => htail j (hmn.trans hj)⟩
  intro j hjp hjn
  by_cases hjm : j ≤ m
  · exact (hpast j hjm).trans (htransfer hmp hmn (htail m le_rfl))
  · exact htransfer hjp hjn (htail j (by omega))

/-- A pure power exponent below s gives arbitrarily late positive terms whose
forward increment is at most s*f(n)/n. No global monotonicity is required. -/
lemma exists_small_increment {f : ℕ → ℝ} {α c s : ℝ} (hα : 1 ≤ α) (hc : 0 < c)
    (hαs : α < s) (h : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) (N : ℕ) :
    ∃ n, N ≤ n ∧ 0 < n ∧ 0 < f n ∧ (n : ℝ)*(f (n+1)-f n) ≤ s*f n := by
  obtain ⟨r,har,hrs⟩ := exists_between hαs
  obtain ⟨M,hM⟩ := eventually_atTop.mp (eventual_increment_upper (hα.trans har.le) hrs)
  obtain ⟨L,hL⟩ := eventually_atTop.mp (eventually_pos hc h)
  let K := max (max N M) (max L 1)
  have hKpos : 0 < K := by dsimp [K]; omega
  have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hKf : 0 < f K := hL K (by dsimp [K]; omega)
  obtain ⟨n,hn,hnpos,hmax⟩ := exists_tail_max (higher_ratio_zero har h) K
    (div_pos hKf (Real.rpow_pos_of_pos hKr r))
  have hnp : 0 < n := hKpos.trans_le hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnp
  have hnf : 0 < f n := (div_pos_iff_of_pos_right (Real.rpow_pos_of_pos hnr r)).mp hnpos
  refine ⟨n,by dsimp [K] at hn; omega,hnp,hnf,?_⟩
  let C : ℝ := f n/(n : ℝ)^r
  have hC : 0 < C := hnpos
  have he : C*(n : ℝ)^r = f n := div_mul_cancel₀ _ (Real.rpow_pos_of_pos hnr r).ne'
  have hstep : f (n+1) ≤ C*((n : ℝ)+1)^r := by
    have hh := hmax (n+1) (by omega)
    simp only [Nat.cast_add,Nat.cast_one] at hh
    rw [div_le_iff₀ (Real.rpow_pos_of_pos (show (0 : ℝ) < n+1 by positivity) r)] at hh
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  have hu := hM n (by dsimp [K] at hn; omega)
  have hpow : (n : ℝ)*(n : ℝ)^(r-1) = (n : ℝ)^r := by
    rw [Real.rpow_sub hnr,Real.rpow_one]
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hu (show 0 ≤ (n : ℝ)*C by positivity)
  have hmul2 := mul_le_mul_of_nonneg_left hstep hnr.le
  have hex : (n : ℝ)*C*((n : ℝ)^r) = (n : ℝ)*f n := by rw [mul_assoc,he]
  have hex2 : (n : ℝ)*C*(s*(n : ℝ)^(r-1)) = s*f n := by
    calc
      _ = s*C*((n : ℝ)*(n : ℝ)^(r-1)) := by ring
      _ = s*f n := by rw [hpow,mul_assoc,he]
  rw [hex2] at hmul
  nlinarith

lemma exists_small_increment_with_past {f : ℕ → ℝ} {α c a s : ℝ}
    (hα : 1 ≤ α) (hc : 0 < c) (haa : a < α) (hαs : α < s)
    (h : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) (N : ℕ) :
    ∃ n, N ≤ n ∧ 0 < n ∧ 0 < f n ∧
      (∀ j, 0 < j → j ≤ n → f j/(j : ℝ)^a ≤ f n/(n : ℝ)^a) ∧
      (n : ℝ)*(f (n+1)-f n) ≤ s*f n := by
  obtain ⟨r,har,hrs⟩ := exists_between hαs
  obtain ⟨M,hM⟩ := eventually_atTop.mp (eventual_increment_upper (hα.trans har.le) hrs)
  obtain ⟨n,hn,hnp,hnf,hpast,hfuture⟩ := exists_two_sided_record haa har hc h (max N M)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnp
  refine ⟨n,by omega,hnp,hnf,hpast,?_⟩
  let C : ℝ := f n/(n : ℝ)^r
  have hC : 0 < C := div_pos hnf (Real.rpow_pos_of_pos hnr r)
  have he : C*(n : ℝ)^r = f n := div_mul_cancel₀ _ (Real.rpow_pos_of_pos hnr r).ne'
  have hstep : f (n+1) ≤ C*((n : ℝ)+1)^r := by
    have hh := hfuture (n+1) (by omega)
    simp only [Nat.cast_add,Nat.cast_one] at hh
    rw [div_le_iff₀ (Real.rpow_pos_of_pos (show (0 : ℝ) < n+1 by positivity) r)] at hh
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  have hu := hM n (by omega)
  have hpow : (n : ℝ)*(n : ℝ)^(r-1) = (n : ℝ)^r := by
    rw [Real.rpow_sub hnr,Real.rpow_one]
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hu (show 0 ≤ (n : ℝ)*C by positivity)
  have hmul2 := mul_le_mul_of_nonneg_left hstep hnr.le
  have hex : (n : ℝ)*C*((n : ℝ)^r) = (n : ℝ)*f n := by rw [mul_assoc,he]
  have hex2 : (n : ℝ)*C*(s*(n : ℝ)^(r-1)) = s*f n := by
    calc
      _ = s*C*((n : ℝ)*(n : ℝ)^(r-1)) := by ring
      _ = s*f n := by rw [hpow,mul_assoc,he]
  rw [hex2] at hmul
  nlinarith


#print axioms exists_two_sided_record
#print axioms exists_small_increment_with_past
#print axioms exists_tail_max
#print axioms exists_small_increment
end Erdos713FutureRecords
