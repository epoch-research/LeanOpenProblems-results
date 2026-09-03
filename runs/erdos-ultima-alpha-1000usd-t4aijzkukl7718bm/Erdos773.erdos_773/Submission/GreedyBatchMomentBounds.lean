import Submission.GreedyBatchScalarTails

/-! Elementary scalar bounds for the explicit indexed moment budgets. -/
namespace Erdos773.GreedyBatchMomentBounds
open Finset IndexedBernoulliMoments GreedyBatchScalarTails
set_option maxHeartbeats 2500000
noncomputable section

/-- Separate the leading mean from an overlap error. The cap M applies only
to positive overlaps, not to the rank-zero family mass. -/
theorem budget_uniform (r q n M : ℕ) (K : ℕ → ℕ) (p : ℝ)
    (hp : 0≤p) (hp1 : p≤1) (h0 : K 0≤n) (hK : ∀ k, 1≤k → k≤r → K k≤M) :
    budget r q K p≤(n:ℝ)*p^r+(r:ℝ)*M*((r*q+1:ℕ):ℝ)^r := by
  rw [budget,sum_range_succ']
  have hfirst : ((r*q).choose 0:ℝ)*K 0*p^(r-0)≤(n:ℝ)*p^r := by
    simpa only [Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero] using
      mul_le_mul_of_nonneg_right (show (K 0:ℝ)≤n by exact_mod_cast h0) (pow_nonneg hp r)
  have hrow (k : ℕ) (hk : k∈range r) :
      ((r*q).choose (k+1):ℝ)*K (k+1)*p^(r-(k+1))≤(M:ℝ)*((r*q+1:ℕ):ℝ)^r := by
    have hkr : k+1≤r := by have := mem_range.mp hk; omega
    have hchoose : (r*q).choose (k+1)≤(r*q+1)^r :=
      ((Nat.choose_le_pow (r*q) (k+1)).trans (Nat.pow_le_pow_left (by omega : r*q≤r*q+1) _)).trans
        (Nat.pow_le_pow_right (by omega : 0<r*q+1) hkr)
    have hc : ((r*q).choose (k+1):ℝ)≤((r*q+1:ℕ):ℝ)^r := by exact_mod_cast hchoose
    have hcap : (K (k+1):ℝ)≤M := by exact_mod_cast hK (k+1) (by omega) hkr
    have hm := mul_le_mul hc hcap (Nat.cast_nonneg _) (by positivity)
    have hpow : p^(r-(k+1))≤1 := pow_le_one₀ hp hp1
    calc
      _ ≤ ((r*q).choose (k+1):ℝ)*K (k+1) := by
        exact mul_le_of_le_one_right (by positivity) hpow
      _ ≤ _ := by nlinarith only [hm]
  have hs := sum_le_sum hrow
  simp only [sum_const,card_range,nsmul_eq_mul] at hs
  linarith only [hfirst,hs]

/-- The old-hit correction retains its p factor in the one-overlap term;
dropping it would be too expensive at large mixed degrees. -/
theorem hit_budget (n s M q : ℕ) (p : ℝ) (hp : 0≤p) :
    budget 2 q (BernoulliHitCounts.overlapCaps n s M) p≤
      (n:ℝ)*s^2*p^2/2+2*q*s*M*p+2*(q:ℝ)^2*M := by
  have hs : (s.choose 2:ℝ)≤(s:ℝ)^2/2 := by
    simpa using (Nat.choose_le_pow_div (α := ℝ) 2 s)
  have hq : ((2*q).choose 2:ℝ)≤2*(q:ℝ)^2 := by
    have hh := Nat.choose_le_pow_div (α := ℝ) 2 (2*q)
    norm_num at hh
    push_cast at hh
    nlinarith only [hh]
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n)) (sq_nonneg p)
  have h2 := mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg M)
  norm_num [budget,sum_range_succ,BernoulliHitCounts.overlapCaps]
  nlinarith only [h1,h2]

/-- A near-mean budget bound yields an exponential moment tail. -/
theorem moment_exponential (r q : ℕ) (K : ℕ → ℕ) (p L u : ℝ)
    (hp : 0≤p) (hL : 0<L) (hu : 0≤u) (hu1 : u≤1)
    (hbudget : budget r q K p≤(1-u)*L) :
    (budget r q K p/L)^q≤Real.exp (-(q:ℝ)*u) := by
  have hb : budget r q K p/L≤1-u := (div_le_iff₀ hL).mpr hbudget
  have he : 1-u≤Real.exp (-u) := by simpa only [neg_add_eq_sub,add_comm] using Real.add_one_le_exp (-u)
  have hpw := pow_le_pow_left₀ (div_nonneg (budget_nonneg r q K hp) hL.le) (hb.trans he) q
  simpa only [← Real.exp_nat_mul,mul_neg,neg_mul] using hpw

/-- Matching exponential and moment errors for old-hit survival. -/
theorem hit_exponential (n s M q : ℕ) (p η L u : ℝ)
    (hp : 0≤p) (hL : 0<L) (hu : 0≤u) (hu1 : u≤1)
    (hexp : (q:ℝ)*u≤η^2*L/(2*M))
    (hbudget : budget 2 q (BernoulliHitCounts.overlapCaps n s M) p≤(1-u)*L) :
    hitError n s M q p η L≤2*Real.exp (-(q:ℝ)*u) := by
  have h1 : Real.exp (-η^2*L/(2*M))≤Real.exp (-(q:ℝ)*u) := by
    apply Real.exp_le_exp.mpr
    convert neg_le_neg hexp using 1 <;> ring
  have h2 := moment_exponential 2 q _ p L u hp hL hu hu1 hbudget
  dsimp [hitError]
  linarith only [h1,h2]

/-- The proposed moment order m^10 resolves relative errors of order m^-2
with an exp(-m^7) bound, uniformly for m>=20. -/
lemma shrinking_scale (m : ℕ) (hm : 20≤ m) :
    Real.exp (-((m^10:ℕ):ℝ)*(1/(20*(m:ℝ)^2)))≤Real.exp (-(m:ℝ)^7) := by
  have hmR : (20:ℝ)≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ)< m := by linarith only [hmR]
  have hmne : (m:ℝ)≠0 := ne_of_gt hm0
  have he : ((m^10:ℕ):ℝ)*(1/(20*(m:ℝ)^2))=(m:ℝ)^8/20 := by
    push_cast
    field_simp
  rw [show -((m^10:ℕ):ℝ)*(1/(20*(m:ℝ)^2))= -(((m^10:ℕ):ℝ)*(1/(20*(m:ℝ)^2))) by ring,he]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hmR (pow_nonneg hm0.le 7)
  nlinarith only [hh]

#print axioms budget_uniform
#print axioms hit_budget
#print axioms moment_exponential
#print axioms hit_exponential
#print axioms shrinking_scale
end
end Erdos773.GreedyBatchMomentBounds
