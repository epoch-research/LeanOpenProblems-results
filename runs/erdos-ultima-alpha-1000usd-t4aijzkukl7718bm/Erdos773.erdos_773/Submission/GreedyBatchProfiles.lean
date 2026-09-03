import Submission.GreedyBatchProfileStep

/-! The actual ceiling profiles used by the proposed shrinking-batch
schedule, and their elementary size bounds. -/
namespace Erdos773.GreedyBatchProfiles
open GreedyBatchCertificate GreedyBatchProfileStep
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section

def f2 (m : ℕ) (d t : ℝ) : ℝ := A m*d*t^2
def f3 (m : ℕ) (d t : ℝ) : ℝ := B m*d^2*t
def f4 (d : ℝ) : ℝ := d^3
def fb (m : ℕ) (d : ℝ) : ℝ := (m:ℝ)^50*d

def probability (m : ℕ) (d t : ℝ) : ℝ := step m t/d

def nextD (m : ℕ) (d t : ℝ) : ℝ := d*Real.exp (-a m*GreedyBatchProfileLower.delta t (step m t))

def caps (m : ℕ) (d t : ℝ) (C P : ℕ) : Caps where
  D2 := ⌈f2 m d t⌉₊
  D3 := ⌈f3 m d t⌉₊
  D4 := ⌈f4 d⌉₊
  P := P
  C := C
  B := ⌈fb m d⌉₊

structure Range (m : ℕ) (d t : ℝ) (C P : ℕ) : Prop where
  large : 100≤ m
  d : (m:ℝ)^1000≤d
  t_one : 1≤t
  t_upper : t≤ m
  common : C≤ m^60
  common_one : 1≤C
  pair_one : 1≤P
  pair_upper : P≤ m

lemma Range.m_pos {m : ℕ} {d t : ℝ} {C P : ℕ} (h : Range m d t C P) : (0:ℝ)< m := by
  exact_mod_cast (show 0< m by have := h.large; omega)

lemma Range.m_one {m : ℕ} {d t : ℝ} {C P : ℕ} (h : Range m d t C P) : (1:ℝ)≤ m := by
  exact_mod_cast (show 1≤ m by have := h.large; omega)

lemma Range.power_le_d {m : ℕ} {d t : ℝ} {C P : ℕ} (h : Range m d t C P) (k : ℕ) (hk : k≤1000) :
    (m:ℝ)^k≤d := (pow_le_pow_right₀ h.m_one hk).trans h.d

lemma Range.m_le_d {m : ℕ} {d t : ℝ} {C P : ℕ} (h : Range m d t C P) : (m:ℝ)≤d := by
  simpa only [pow_one] using h.power_le_d 1 (by decide)

lemma Range.d_large {m : ℕ} {d t : ℝ} {C P : ℕ} (h : Range m d t C P) : (100:ℝ)≤d := by
  have hm : (100:ℝ)≤ m := by exact_mod_cast h.large
  exact hm.trans h.m_le_d

lemma Range.d_pos {m : ℕ} {d t : ℝ} {C P : ℕ} (h : Range m d t C P) : 0<d := by
  have hh := h.d_large
  linarith only [hh]

lemma upper_coefficient (m : ℕ) (hm : 100≤ m) : A m≤15/4 ∧ B m≤15/4 := by
  have hmR : (100:ℝ)≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ)< m := by linarith only [hmR]
  have hm2 : (10000:ℝ)≤(m:ℝ)^2 := by nlinarith only [hmR]
  have hh : (6000:ℝ)/(m:ℝ)^2≤3/4 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hm2])
  have hA : A m≤15/4 := by dsimp [A]; linarith only [hh]
  exact ⟨hA,(coefficients m hm).2.1.trans hA⟩

lemma ceil_bounds (x : ℝ) (hx : 0≤x) : x≤(⌈x⌉₊:ℝ) ∧ (⌈x⌉₊:ℝ)≤x+1 :=
  ⟨Nat.le_ceil x,(Nat.ceil_lt_add_one hx).le⟩

lemma profile_positive (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    0<f2 m d t ∧ 0<f3 m d t ∧ 0<f4 d ∧ 0<fb m d := by
  have hd := h.d_pos
  have ht : 0<t := by have := h.t_one; linarith
  have hm := h.m_pos
  have hB : (0:ℝ)<B m := lt_of_lt_of_le (by norm_num) (coefficients m h.large).1
  have hA : (0:ℝ)<A m := hB.trans_le (coefficients m h.large).2.1
  dsimp [f2,f3,f4,fb]
  exact ⟨by positivity,by positivity,by positivity,by positivity⟩

lemma base_large (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    4≤d*t^2 ∧ 4≤d^2*t ∧ 1≤d^3 ∧ 1≤(m:ℝ)^50*d := by
  have hd := h.d_large
  have hd0 := h.d_pos.le
  have ht := h.t_one
  have ht2 : (1:ℝ)≤t^2 := one_le_pow₀ ht
  have h1 := mul_le_mul_of_nonneg_left ht2 hd0
  have h2 := mul_le_mul_of_nonneg_left ht (sq_nonneg d)
  have h3 : (1:ℝ)≤d^3 := one_le_pow₀ (by linarith only [hd])
  have h4 := mul_le_mul_of_nonneg_right (one_le_pow₀ (n := 50) h.m_one) hd0
  refine ⟨by nlinarith only [hd,h1],by nlinarith only [hd,h2],h3,by nlinarith only [hd,h4]⟩

/-- Useful coarse bounds for all four natural ceilings. -/
theorem cap_bounds (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    3*d*t^2≤((caps m d t C P).D2:ℝ) ∧ ((caps m d t C P).D2:ℝ)≤4*d*t^2 ∧
    3*d^2*t≤((caps m d t C P).D3:ℝ) ∧ ((caps m d t C P).D3:ℝ)≤4*d^2*t ∧
    d^3≤((caps m d t C P).D4:ℝ) ∧ ((caps m d t C P).D4:ℝ)≤2*d^3 ∧
    (m:ℝ)^50*d≤((caps m d t C P).B:ℝ) ∧ ((caps m d t C P).B:ℝ)≤2*(m:ℝ)^50*d := by
  obtain ⟨hpos2,hpos3,hpos4,hposB⟩ := profile_positive m d t C P h
  obtain ⟨hl2,hu2⟩ := ceil_bounds (f2 m d t) hpos2.le
  obtain ⟨hl3,hu3⟩ := ceil_bounds (f3 m d t) hpos3.le
  obtain ⟨hl4,hu4⟩ := ceil_bounds (f4 d) hpos4.le
  obtain ⟨hlB,huB⟩ := ceil_bounds (fb m d) hposB.le
  obtain ⟨hb2,hb3,hb4,hbB⟩ := base_large m d t C P h
  have hd := h.d_pos.le
  have ht : 0≤t := by have := h.t_one; linarith
  have hc := coefficients m h.large
  have hlA : 3≤A m := hc.1.trans hc.2.1
  obtain ⟨huA,huB'⟩ := upper_coefficient m h.large
  have hAlo := mul_le_mul_of_nonneg_right hlA (show 0≤d*t^2 by positivity)
  have hAhi := mul_le_mul_of_nonneg_right huA (show 0≤d*t^2 by positivity)
  have hBlo := mul_le_mul_of_nonneg_right hc.1 (show 0≤d^2*t by positivity)
  have hBhi := mul_le_mul_of_nonneg_right huB' (show 0≤d^2*t by positivity)
  dsimp [caps]
  dsimp [f2,f3,f4,fb] at hl2 hu2 hl3 hu3 hl4 hu4 hlB huB ⊢
  exact ⟨by nlinarith only [hl2,hAlo],by nlinarith only [hu2,hAhi,hb2],
    by nlinarith only [hl3,hBlo],by nlinarith only [hu3,hBhi,hb3],hl4,
    by linarith only [hu4,hb4],hlB,by nlinarith only [huB,hbB]⟩

lemma probability_pos (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) : 0<probability m d t :=
  div_pos (step_pos m t (by have := h.large; omega)) h.d_pos

lemma probability_mul (m : ℕ) (d t : ℝ) (hd : d≠0) : probability m d t*d=step m t := by
  exact div_mul_cancel₀ _ hd

lemma probability_le_step (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) :
    probability m d t≤step m t := by
  have hd1 : 1≤d := by have := h.d_large; linarith
  exact div_le_self (step_pos m t (by have := h.large; omega)).le hd1

lemma probability_le_one (m : ℕ) (d t : ℝ) (C P : ℕ) (h : Range m d t C P) : probability m d t≤1 := by
  apply (probability_le_step m d t C P h).trans
  apply (step_bound m t (by have := h.large; omega)).trans
  exact (div_le_one (by have := h.m_pos; positivity)).mpr (one_le_pow₀ h.m_one)

#print axioms profile_positive
#print axioms base_large
#print axioms cap_bounds
#print axioms probability_pos
#print axioms probability_le_one
end
end Erdos773.GreedyBatchProfiles
