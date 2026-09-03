import Submission.GreedyBatchProfiles

/-! The coarse conditions for all scaled error estimates hold for the
actual ceiling profiles throughout the prescribed large-d regime. -/
namespace Erdos773.GreedyBatchProfileConditions
open GreedyBatchCertificate GreedyBatchProfiles GreedyBatchProfileStep GreedyBatchScaledErrors
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

lemma power_slack (m i j : ℕ) (c : ℝ) (hm : 100≤ m) (hc : c≤100) (hij : i<j) :
    c*(m:ℝ)^i≤(m:ℝ)^j := by
  have hmR : (100:ℝ)≤ m := by exact_mod_cast hm
  have hm1 : (1:ℝ)≤ m := by linarith only [hmR]
  calc
    _ ≤ (m:ℝ)*(m:ℝ)^i := mul_le_mul_of_nonneg_right (hc.trans hmR) (by positivity)
    _ = (m:ℝ)^(i+1) := by ring
    _ ≤ _ := pow_le_pow_right₀ hm1 (by omega)

lemma step_weighted (m : ℕ) (t : ℝ) (hm : 1≤ m) (ht : 1≤t) :
    step m t*t^2≤1/(m:ℝ)^2 ∧ step m t*t≤1/(m:ℝ)^2 ∧ step m t≤1 := by
  have hmR : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have hpos := (step_pos m t (by omega)).le
  have hsq : step m t*t^2≤1/(m:ℝ)^2 := by
    have hh : t^2/(1+t^2)≤1 := (div_le_one (by positivity)).mpr (by linarith)
    calc
      _ = (1/(m:ℝ)^2)*(t^2/(1+t^2)) := by unfold step; field_simp
      _ ≤ (1/(m:ℝ)^2)*1 := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := mul_one _
  refine ⟨hsq,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_left (by nlinarith only [ht] : t≤t^2) hpos).trans hsq
  · apply (step_bound m t hm).trans
    have hm1 : (1:ℝ)≤ m := by exact_mod_cast hm
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ hm1)

structure WeightedBounds (c : Caps) (m : ℕ) (d t p h : ℝ) : Prop where
  graph : (c.D2:ℝ)*p≤4*h*t^2
  three_one : (c.D3:ℝ)*p≤4*d*t*h
  three_two : (c.D3:ℝ)*p^2≤4*t*h^2
  four_one : (c.D4:ℝ)*p≤2*d^2*h
  four_two : (c.D4:ℝ)*p^2≤2*d*h^2
  four_three : (c.D4:ℝ)*p^3≤2*h^3
  shared : (c.B:ℝ)*p≤2*(m:ℝ)^50*h

lemma weighted_bounds (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    WeightedBounds (caps m d t C P) m d t (probability m d t) (step m t) := by
  have hp := (probability_pos m d t C P h).le
  have he := probability_mul m d t (ne_of_gt h.d_pos)
  obtain ⟨h2l,h2,h3l,h3,h4l,h4,hBl,hB⟩ := cap_bounds m d t C P h
  constructor
  · calc
      _ ≤ (4*d*t^2)*probability m d t := mul_le_mul_of_nonneg_right h2 hp
      _ = 4*(probability m d t*d)*t^2 := by ring
      _ = _ := by rw [he]
  · calc
      _ ≤ (4*d^2*t)*probability m d t := mul_le_mul_of_nonneg_right h3 hp
      _ = 4*d*t*(probability m d t*d) := by ring
      _ = _ := by rw [he]
  · calc
      _ ≤ (4*d^2*t)*(probability m d t)^2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
      _ = 4*t*(probability m d t*d)^2 := by ring
      _ = _ := by rw [he]
  · calc
      _ ≤ (2*d^3)*probability m d t := mul_le_mul_of_nonneg_right h4 hp
      _ = 2*d^2*(probability m d t*d) := by ring
      _ = _ := by rw [he]
  · calc
      _ ≤ (2*d^3)*(probability m d t)^2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
      _ = 2*d*(probability m d t*d)^2 := by ring
      _ = _ := by rw [he]
  · calc
      _ ≤ (2*d^3)*(probability m d t)^3 := mul_le_mul_of_nonneg_right h4 (pow_nonneg hp _)
      _ = 2*(probability m d t*d)^3 := by ring
      _ = _ := by rw [he]
  · calc
      _ ≤ (2*(m:ℝ)^50*d)*probability m d t := mul_le_mul_of_nonneg_right hB hp
      _ = 2*(m:ℝ)^50*(probability m d t*d) := by ring
      _ = _ := by rw [he]

/-- All old-family incidence ratios follow from the ceiling profile sizes. -/
lemma incidence_ratios (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    m^52≤(caps m d t C P).D2 ∧ m^52≤(caps m d t C P).D3 ∧
    m^30*C≤(caps m d t C P).D2 ∧
    m^30*((caps m d t C P).D2*P)≤(caps m d t C P).D3 ∧
    m^30*((caps m d t C P).D2*P)≤(caps m d t C P).D4 ∧
    m^30*((caps m d t C P).D2*P)≤(caps m d t C P).B := by
  obtain ⟨h2,h2u,h3,h3u,h4,h4u,hB,hBu⟩ := cap_bounds m d t C P h
  have hd := h.d_pos.le
  have hd1 : 1≤d := by have := h.d_large; linarith
  have ht := h.t_one
  have hm := h.m_pos.le
  have ht0 : 0≤t := by linarith only [ht]
  have ht2 : (1:ℝ)≤t^2 := one_le_pow₀ ht
  have hdt := mul_le_mul_of_nonneg_left ht2 hd
  have hd2t := mul_le_mul_of_nonneg_left ht (sq_nonneg d)
  have hd2 : d≤d^2 := by nlinarith only [hd1]
  have hD2 : d≤((caps m d t C P).D2:ℝ) := by nlinarith only [h2,hdt,hd]
  have hD3 : d^2≤((caps m d t C P).D3:ℝ) := by nlinarith only [h3,hd2t,sq_nonneg d]
  have hP : (P:ℝ)≤ m := by exact_mod_cast h.pair_upper
  have htupper : t^2≤(m:ℝ)^2 := pow_le_pow_left₀ ht0 h.t_upper 2
  have hDP : ((caps m d t C P).D2:ℝ)*P≤4*d*(m:ℝ)^3 := by
    have hh := mul_le_mul h2u hP (Nat.cast_nonneg P) (show 0≤4*d*t^2 by positivity)
    have hh' := mul_le_mul_of_nonneg_left htupper (show 0≤4*d*m by positivity)
    nlinarith only [hh,hh']
  have hsmall : 4*(m:ℝ)^33≤d :=
    (power_slack m 33 34 4 h.large (by norm_num) (by decide)).trans (h.power_le_d 34 (by decide))
  have hmass : (m:ℝ)^30*((caps m d t C P).D2:ℝ)*P≤d^2 := by
    have hh := mul_le_mul_of_nonneg_left hDP (pow_nonneg hm 30)
    have hh' := mul_le_mul_of_nonneg_left hsmall hd
    nlinarith only [hh,hh']
  have hmassB : (m:ℝ)^30*((caps m d t C P).D2:ℝ)*P≤(m:ℝ)^50*d := by
    have hh := mul_le_mul_of_nonneg_left hDP (pow_nonneg hm 30)
    have hh' := mul_le_mul_of_nonneg_right (power_slack m 33 50 4 h.large (by norm_num) (by decide)) hd
    nlinarith only [hh,hh']
  have hmassC : (m:ℝ)^30*C≤d := by
    have hC : (C:ℝ)≤(m:ℝ)^60 := by exact_mod_cast h.common
    have hh := mul_le_mul_of_nonneg_left hC (pow_nonneg hm 30)
    have hd90 := h.power_le_d 90 (by decide)
    nlinarith only [hh,hd90]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact_mod_cast (h.power_le_d 52 (by decide)).trans hD2
  · exact_mod_cast (h.power_le_d 52 (by decide)).trans (hd2.trans hD3)
  · exact_mod_cast hmassC.trans hD2
  · rw [← Nat.mul_assoc]
    exact_mod_cast hmass.trans hD3
  · rw [← Nat.mul_assoc]
    have hh : d^2≤d^3 := pow_le_pow_right₀ hd1 (by decide)
    exact_mod_cast hmass.trans (hh.trans h4)
  · rw [← Nat.mul_assoc]
    exact_mod_cast hmassB.trans hB

lemma graph_load (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    ((caps m d t C P).D2:ℝ)*probability m d t≤4/(m:ℝ)^2 := by
  have hw := (weighted_bounds m d t C P h).graph
  have hs := (step_weighted m t (by have := h.large; omega) h.t_one).1
  ring_nf at hw hs ⊢
  linarith only [hw,hs]

lemma base_lower (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    d≤((caps m d t C P).D2:ℝ) ∧ d^2≤((caps m d t C P).D3:ℝ) := by
  obtain ⟨h2,_,h3,_⟩ := cap_bounds m d t C P h
  have hd := h.d_pos.le
  have ht := h.t_one
  have ht2 : (1:ℝ)≤t^2 := one_le_pow₀ ht
  have hdt := mul_le_mul_of_nonneg_left ht2 hd
  have hd2t := mul_le_mul_of_nonneg_left ht (sq_nonneg d)
  exact ⟨by nlinarith only [h2,hdt,hd],by nlinarith only [h3,hd2t,sq_nonneg d]⟩

lemma promotion_means (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    2*((caps m d t C P).D3:ℝ)*probability m d t≤10*(caps m d t C P).D2/(m:ℝ)^2 ∧
    3*((caps m d t C P).D4:ℝ)*probability m d t≤10*(caps m d t C P).D3/(m:ℝ)^2 ∧
    3*((caps m d t C P).D4:ℝ)*(probability m d t)^2≤10*(caps m d t C P).D2/(m:ℝ)^2 := by
  have hw := weighted_bounds m d t C P h
  have hs := step_bound m t (by have := h.large; omega)
  have hs1 := (step_weighted m t (by have := h.large; omega) h.t_one).2.2
  have hs0 := (step_pos m t (by have := h.large; omega)).le
  have hs2 : (step m t)^2≤1/(m:ℝ)^2 := by
    have hh : (step m t)^2≤step m t := by nlinarith only [hs0,hs1]
    exact hh.trans hs
  have hd := h.d_pos.le
  have ht : 0≤t := by have := h.t_one; linarith
  have hdt : d*t≤d*t^2 := mul_le_mul_of_nonneg_left (by have := h.t_one; nlinarith : t≤t^2) hd
  have h2 := (cap_bounds m d t C P h).1
  obtain ⟨hb2,hb3⟩ := base_lower m d t C P h
  have hcoef2 : 8*d*t≤10*((caps m d t C P).D2:ℝ) := by
    have hh : 0≤d*t := mul_nonneg hd ht
    nlinarith only [h2,hdt,hh]
  have hcoef3 : 6*d^2≤10*((caps m d t C P).D3:ℝ) := by nlinarith only [hb3,sq_nonneg d]
  have hcoef4 : 6*d≤10*((caps m d t C P).D2:ℝ) := by nlinarith only [hb2,hd]
  have hdiv2 := div_le_div_of_nonneg_right hcoef2 (sq_nonneg (m:ℝ))
  have hdiv3 := div_le_div_of_nonneg_right hcoef3 (sq_nonneg (m:ℝ))
  have hdiv4 := div_le_div_of_nonneg_right hcoef4 (sq_nonneg (m:ℝ))
  have hstep2 := mul_le_mul_of_nonneg_left hs (show 0≤8*d*t by positivity)
  have hstep3 := mul_le_mul_of_nonneg_left hs (show 0≤6*d^2 by positivity)
  have hstep4 := mul_le_mul_of_nonneg_left hs2 (show 0≤6*d by positivity)
  have hw2 := hw.three_one
  have hw3 := hw.four_one
  have hw4 := hw.four_two
  ring_nf at hstep2 hstep3 hstep4 hdiv2 hdiv3 hdiv4 hw2 hw3 hw4 ⊢
  exact ⟨by linarith only [hw2,hstep2,hdiv2],by linarith only [hw3,hstep3,hdiv3],
    by linarith only [hw4,hstep4,hdiv4]⟩

lemma shared_means (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    ((caps m d t C P).D3:ℝ)*P*probability m d t≤(m:ℝ)*d/4 ∧
    3*((caps m d t C P).D4:ℝ)*P*(probability m d t)^2≤(m:ℝ)*d/4 ∧
    (m:ℝ)^46≤(m:ℝ)*d/4 := by
  have hw := weighted_bounds m d t C P h
  have hmR : (100:ℝ)≤ m := by exact_mod_cast h.large
  have hm0 := h.m_pos
  have hd := h.d_pos.le
  have ht : 0≤t := by have := h.t_one; linarith
  have hs := (step_pos m t (by have := h.large; omega)).le
  have hP : (P:ℝ)≤ m := by exact_mod_cast h.pair_upper
  have h1 := mul_le_mul hw.three_one hP (Nat.cast_nonneg P) (show 0≤4*d*t*step m t by positivity)
  have h2 := mul_le_mul hw.four_two hP (Nat.cast_nonneg P) (show 0≤2*d*(step m t)^2 by positivity)
  have hst := (step_weighted m t (by have := h.large; omega) h.t_one).2.1
  have hs2 := step_squared m t (by have := h.large; omega)
  have ht1 := mul_le_mul_of_nonneg_left hst (show 0≤4*(m:ℝ)*d by positivity)
  have ht2 := mul_le_mul_of_nonneg_left hs2 (show 0≤6*(m:ℝ)*d by positivity)
  have hm2 : (10000:ℝ)≤(m:ℝ)^2 := by nlinarith only [hmR]
  have hm4 : (10000:ℝ)≤(m:ℝ)^4 := hm2.trans (pow_le_pow_right₀ h.m_one (by decide))
  have hc1 : (4:ℝ)/(m:ℝ)^2≤1/4 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hm2])
  have hc2 : (6:ℝ)/(m:ℝ)^4≤1/4 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hm4])
  have hfinal1 := mul_le_mul_of_nonneg_left hc1 (show 0≤(m:ℝ)*d by positivity)
  have hfinal2 := mul_le_mul_of_nonneg_left hc2 (show 0≤(m:ℝ)*d by positivity)
  have hsmall : 4*(m:ℝ)^45≤d :=
    (power_slack m 45 46 4 h.large (by norm_num) (by decide)).trans (h.power_le_d 46 (by decide))
  have hfinal3 := mul_le_mul_of_nonneg_left hsmall hm0.le
  ring_nf at h1 h2 ht1 ht2 hfinal1 hfinal2 hfinal3 ⊢
  exact ⟨by linarith only [h1,ht1,hfinal1],by linarith only [h2,ht2,hfinal2],by linarith only [hfinal3]⟩

lemma common_means (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    ∀ r∈Finset.Icc 1 4,
      (GreedyBatchCommonBudgets.masses (caps m d t C P).D2 (caps m d t C P).D3
        (caps m d t C P).D4 P (caps m d t C P).B r:ℝ)*(probability m d t)^r≤(m:ℝ)^52/4 := by
  let c := caps m d t C P
  let p := probability m d t
  have hp : 0≤p := (probability_pos m d t C P h).le
  have hp1 : p≤1 := probability_le_one m d t C P h
  have hm := h.m_pos
  have hm1 := h.m_one
  have hs := (step_weighted m t (by have := h.large; omega) h.t_one).2.2
  have hs0 := (step_pos m t (by have := h.large; omega)).le
  have ht : 0≤t := by have := h.t_one; linarith
  have hP : (P:ℝ)≤ m := by exact_mod_cast h.pair_upper
  have hw := weighted_bounds m d t C P h
  have hload := graph_load m d t C P h
  have h4div : (4:ℝ)/(m:ℝ)^2≤4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh : (1:ℝ)≤(m:ℝ)^2 := one_le_pow₀ hm1
    linarith only [hh]
  have h4div4 : (4:ℝ)/(m:ℝ)^4≤4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh : (1:ℝ)≤(m:ℝ)^4 := one_le_pow₀ hm1
    linarith only [hh]
  have h2p : (c.D2:ℝ)*p≤4 := hload.trans h4div
  have h2p2 : (c.D2:ℝ)*p^2≤4 := by
    have hh := mul_le_mul h2p hp1 hp (by norm_num : (0:ℝ)≤4)
    nlinarith only [hh]
  have h2p3 : (c.D2:ℝ)*p^3≤4 := by
    have hh := mul_le_mul h2p2 hp1 hp (by norm_num : (0:ℝ)≤4)
    nlinarith only [hh]
  have h3p2 : (c.D3:ℝ)*p^2≤4 := by
    have hh := hw.three_two
    have ht := step_squared_time m t (by have := h.large; omega) h.t_one
    change (c.D3:ℝ)*p^2≤_ at hh
    ring_nf at hh ht h4div4 ⊢
    linarith only [hh,ht,h4div4]
  have h3p3 : (c.D3:ℝ)*p^3≤4 := by
    have hh := mul_le_mul h3p2 hp1 hp (by norm_num : (0:ℝ)≤4)
    nlinarith only [hh]
  have h4p3 : (c.D4:ℝ)*p^3≤2 := by
    have hh := hw.four_three
    have ht := pow_le_one₀ hs0 hs (n := 3)
    change (c.D4:ℝ)*p^3≤_ at hh
    nlinarith only [hh,ht]
  have hBp : (c.B:ℝ)*p≤2*(m:ℝ)^48 := by
    have hh := hw.shared
    have hs := mul_le_mul_of_nonneg_left (step_bound m t (by have := h.large; omega))
      (show (0:ℝ)≤2*(m:ℝ)^50 by positivity)
    have he : 2*(m:ℝ)^50*(1/(m:ℝ)^2)=2*(m:ℝ)^48 := by field_simp
    rw [he] at hs
    exact hh.trans hs
  have hmass1 : ((2*c.D2*P+2*c.B:ℕ):ℝ)*p≤(m:ℝ)^50 := by
    have hh := mul_le_mul h2p hP (Nat.cast_nonneg P) (by norm_num : (0:ℝ)≤4)
    have hmpow : (m:ℝ)≤(m:ℝ)^48 := by simpa only [pow_one] using pow_le_pow_right₀ hm1 (by decide : 1≤48)
    have hslack := power_slack m 48 50 12 h.large (by norm_num) (by decide)
    push_cast
    nlinarith only [hh,hBp,hmpow,hslack]
  have hmass2 : ((4*(c.D2+c.D3)*P:ℕ):ℝ)*p^2≤(m:ℝ)^50 := by
    have hh := mul_le_mul (add_le_add h2p2 h3p2) hP (Nat.cast_nonneg P) (by norm_num : (0:ℝ)≤4+4)
    have hslack := power_slack m 1 50 32 h.large (by norm_num) (by decide)
    push_cast
    norm_num only [pow_one] at hslack
    nlinarith only [hh,hslack]
  have hmass3 : ((3*(c.D2+c.D3+c.D4)*P:ℕ):ℝ)*p^3≤(m:ℝ)^50 := by
    have hh := mul_le_mul (add_le_add (add_le_add h2p3 h3p3) h4p3) hP
      (Nat.cast_nonneg P) (by norm_num : (0:ℝ)≤4+4+2)
    have hslack := power_slack m 1 50 30 h.large (by norm_num) (by decide)
    push_cast
    norm_num only [pow_one] at hslack
    nlinarith only [hh,hslack]
  have hmass4 : ((3*(c.D2+c.D3+c.D4)*P:ℕ):ℝ)*p^4≤(m:ℝ)^50 := by
    have hh := mul_le_mul hmass3 hp1 hp (by positivity : (0:ℝ)≤(m:ℝ)^50)
    nlinarith only [hh]
  have hquarter : (m:ℝ)^50≤(m:ℝ)^52/4 := by
    have hh := power_slack m 50 52 4 h.large (by norm_num) (by decide)
    linarith only [hh]
  intro r hr
  have hsmall : (GreedyBatchCommonBudgets.masses c.D2 c.D3 c.D4 P c.B r:ℝ)*p^r≤(m:ℝ)^50 := by
    obtain ⟨hr1,hr4⟩ := Finset.mem_Icc.mp hr
    interval_cases r
    · simpa [GreedyBatchCommonBudgets.masses] using hmass1
    · simpa [GreedyBatchCommonBudgets.masses] using hmass2
    · simpa [GreedyBatchCommonBudgets.masses] using hmass3
    · simpa [GreedyBatchCommonBudgets.masses] using hmass4
  exact hsmall.trans hquarter

/-- The actual ceiling profiles supply every coarse condition needed for
all fourteen exp(-m^7) local estimates. -/
theorem conditions (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    Conditions (caps m d t C P) m (probability m d t) d := by
  obtain ⟨hd2,hd3,ho2,ho3,ho4,hoB⟩ := incidence_ratios m d t C P h
  obtain ⟨hp31,hp41,hp42⟩ := promotion_means m d t C P h
  obtain ⟨hs34,hs44,hsE⟩ := shared_means m d t C P h
  have hD2 : 0<(caps m d t C P).D2 := by
    exact_mod_cast h.d_pos.trans_le (base_lower m d t C P h).1
  have hP : 0<P := by have := h.pair_one; omega
  exact {
    large := h.large
    p_nonneg := (probability_pos m d t C P h).le
    p_le_one := probability_le_one m d t C P h
    common_pos := by have := h.common_one; change 0<C; omega
    dp_pos := Nat.mul_pos hD2 hP
    pair := h.pair_upper
    degree2 := hd2
    degree3 := hd3
    old2 := ho2
    old3 := ho3
    old4 := ho4
    oldShared := hoB
    graph_load := graph_load m d t C P h
    promotion31 := hp31
    promotion41 := hp41
    promotion42 := hp42
    shared34 := hs34
    shared44 := hs44
    shared_overlap := hsE
    common := common_means m d t C P h }

#print axioms step_weighted
#print axioms weighted_bounds
#print axioms incidence_ratios
#print axioms graph_load
#print axioms promotion_means
#print axioms shared_means
#print axioms common_means
#print axioms conditions
end
end Erdos773.GreedyBatchProfileConditions
