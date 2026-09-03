import Submission.GreedyTrackedVariance

/-!
Explicit mean-field error estimates from uniform local-degree envelopes.
These quantify the drift hypotheses needed by the recorded concentration
lemmas; no trajectory or envelope is assumed to be typical.
-/
namespace Erdos773.GreedyProfileDrift
open Finset GreedyHypergraphState GreedyLinearDrift GreedyLinearLocal
open GreedyLinearHigherDrift GreedyCommonNeighbors
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma incident_eq_empty_of_unavailable {H : Finset (Finset α)} {I : Finset α}
    {u : α} (hu : u ∉ available H I) (j : ℕ) : incident H I j u = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  exact hu ((mem_incident.mp he).2.1 (mem_incident.mp he).2.2.2)

lemma safeChoices_eq_empty_of_unavailable {H : Finset (Finset α)} {I : Finset α}
    {u : α} (hu : u ∉ available H I) : safeChoices H I u = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro w hw
  exact hu (available_antitone (subset_insert w I) (mem_filter.mp hw).2)

lemma survivalDrift_eq_zero_of_unavailable {H : Finset (Finset α)} {I : Finset α}
    {u : α} (hu : u ∉ available H I) (j : ℕ) : survivalDrift H I j u = 0 := by
  simp [survivalDrift,safeChoices_eq_empty_of_unavailable hu]

lemma incident_eq_empty_of_size {H : Finset (Finset α)} (r : ℕ)
    (hr : ∀ e ∈ H, e.card ≤ r) (I : Finset α) (j : ℕ) (hj : r < j) (u : α) :
    incident H I j u = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hs,hj',hu⟩ := mem_incident.mp he
  have hh := (card_le_card (sdiff_subset : e \ I ⊆ e)).trans (hr e he)
  omega

/-- Safe choices for u are exactly the vertices left available after choosing u. -/
lemma safeChoices_eq_available {H : Finset (Finset α)} {I : Finset α} {u : α}
    (hu : u ∈ available H I) : safeChoices H I u = available H (insert u I) := by
  rw [safeChoices_eq hu,available_insert hu]

/-- The safe-choice count carries the same exact 1+d_2 decrement as Q. -/
lemma safeChoices_card {H : Finset (Finset α)} (hlin : Linear H)
    {I : Finset α} {u : α} (hu : u ∈ available H I) :
    ((safeChoices H I u).card:ℝ) =
      (available H I).card-1-(incident H I 2 u).card := by
  have hh := available_card_step hu
  rw [← hlin.incident_two_card I u hu,← safeChoices_eq_available hu] at hh
  have hhR : ((safeChoices H I u).card:ℝ)+1+(incident H I 2 u).card =
      (available H I).card := by exact_mod_cast hh
  linarith

omit [Fintype α] [DecidableEq α] in
/-- Transfer an error around the actual linearized drift to an error around
    deterministic degree profiles. -/
lemma drift_transfer (R a k f x y X Y ex ey K : ℝ)
    (ha : 0 ≤ a) (hk : 0 ≤ k) (hf : 0 ≤ f) (hK : 0 ≤ K)
    (hx : |x-X| ≤ ex) (hy : |y-Y| ≤ ey)
    (hR : |R-(a*y-k*f*x)| ≤ K*x) :
    |R-(a*Y-k*f*X)| ≤ a*ey+k*f*ex+K*(X+ex) := by
  have hxupper : x ≤ X+ex := by have hh := (abs_le.mp hx).2; linarith
  have heq : R-(a*Y-k*f*X) = (R-(a*y-k*f*x))+(a*(y-Y)-k*f*(x-X)) := by ring
  rw [heq]
  calc
    _ ≤ |R-(a*y-k*f*x)|+|a*(y-Y)-k*f*(x-X)| := abs_add_le _ _
    _ ≤ K*x+(|a*(y-Y)|+|k*f*(x-X)|) := add_le_add hR (abs_sub _ _)
    _ = K*x+(a*|y-Y|+k*f*|x-X|) := by
      rw [abs_mul a,abs_of_nonneg ha,abs_mul (k*f),abs_of_nonneg (mul_nonneg hk hf)]
    _ ≤ K*(X+ex)+(a*ey+k*f*ex) := add_le_add
      (mul_le_mul_of_nonneg_left hxupper hK)
      (add_le_add (mul_le_mul_of_nonneg_left hy ha) (mul_le_mul_of_nonneg_left hx (mul_nonneg hk hf)))
    _ = _ := by ring

/-- Uniform two-degree envelopes control the two-degree drift, including
    its direct +d_2 and common-neighbor corrections. -/
theorem two_drift_envelope {H : Finset (Finset α)} (hlin : Linear H)
    {I : Finset α} {u : α} (hu : u ∈ available H I)
    (f2 f3 e2 e3 : ℝ) (hf2 : 0 ≤ f2) (he2 : 0 ≤ e2) (C : ℕ)
    (h2 : ∀ x ∈ available H I, |((incident H I 2 x).card:ℝ)-f2| ≤ e2)
    (h3 : |((incident H I 3 u).card:ℝ)-f3| ≤ e3)
    (hC : ∀ x ∈ closes H I u, commonDegree H I u x ≤ C) :
    |survivalDrift H I 2 u-(2*f3-f2*f2)| ≤
      2*e3+f2*e2+(e2+1+C)*(f2+e2) := by
  have hl (x : α) (hx : x ∈ closes H I u) : f2-e2 ≤ ((incident H I 2 x).card:ℝ) := by
    have hh := (abs_le.mp (h2 x (closes_subset H I u hx))).1
    linarith
  have hh (x : α) (hx : x ∈ closes H I u) : ((incident H I 2 x).card:ℝ) ≤ f2+e2 := by
    have hh := (abs_le.mp (h2 x (closes_subset H I u hx))).2
    linarith
  have hr := survival_drift_two_bounds hlin hu (f2-e2) (f2+e2) C hl hh hC
  have herr : |survivalDrift H I 2 u-
      (2*(incident H I 3 u).card-f2*(incident H I 2 u).card)| ≤
        (e2+1+C)*(incident H I 2 u).card := by
    apply abs_le.mpr
    have hn : (0:ℝ) ≤ (C+2:ℝ)*(incident H I 2 u).card := by positivity
    constructor <;> nlinarith only [hr.1,hr.2,hn]
  simpa only [one_mul] using drift_transfer _ 2 1 f2 _ _ f2 f3 e2 e3 (e2+1+C)
    (by norm_num) (by norm_num) hf2 (by positivity) (h2 u hu) h3 (by simpa only [one_mul] using herr)

/-- Higher-degree envelopes retain both the direct-loss and common-neighbor
    terms. The leading mean field is j*f_next-(j-1)*f_2*f_j. -/
theorem higher_drift_envelope {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (j : ℕ) (hj : 3 ≤ j) (u : α)
    (f2 fj fn e2 ej en : ℝ) (hf2 : 0 ≤ f2) (he2 : 0 ≤ e2) (C : ℕ)
    (h2 : ∀ x ∈ available H I, |((incident H I 2 x).card:ℝ)-f2| ≤ e2)
    (hlocal : |((incident H I j u).card:ℝ)-fj| ≤ ej)
    (hnext : |((incident H I (j+1) u).card:ℝ)-fn| ≤ en)
    (hC : ∀ x ∈ available H I, ∀ y ∈ available H I, x ≠ y → commonDegree H I x y ≤ C) :
    |survivalDrift H I j u-((j:ℝ)*fn-(j-1:ℕ)*f2*fj)| ≤
      (j:ℝ)*en+(j-1:ℕ)*f2*ej+((j-1:ℕ)*(e2+1)+(j.choose 2:ℝ)*C)*(fj+ej) := by
  have hl (x : α) (hx : x ∈ available H I) : f2-e2 ≤ ((incident H I 2 x).card:ℝ) := by
    have hh := (abs_le.mp (h2 x hx)).1
    linarith
  have hh (x : α) (hx : x ∈ available H I) : ((incident H I 2 x).card:ℝ) ≤ f2+e2 := by
    have hh := (abs_le.mp (h2 x hx)).2
    linarith
  have hr := survival_drift_profile_bounds hlin I j hj u (f2-e2) (f2+e2) C hl hh hC
  have herr : |survivalDrift H I j u-
      ((j:ℝ)*(incident H I (j+1) u).card-(j-1:ℕ)*f2*(incident H I j u).card)| ≤
        ((j-1:ℕ)*(e2+1)+(j.choose 2:ℝ)*C)*(incident H I j u).card := by
    apply abs_le.mpr
    have hnc : (0:ℝ) ≤ (j.choose 2:ℝ)*C*(incident H I j u).card := by positivity
    have hnk : (0:ℝ) ≤ (j-1:ℕ)*(incident H I j u).card := by positivity
    constructor <;> nlinarith only [hr.1,hr.2,hnc,hnk]
  exact drift_transfer _ j (j-1:ℕ) f2 _ _ fj fn ej en
    ((j-1:ℕ)*(e2+1)+(j.choose 2:ℝ)*C)
    (by positivity) (by positivity) hf2 (by positivity) hlocal hnext herr

/-- Envelope for the survival count around Q's deterministic profile. -/
theorem safe_count_envelope {H : Finset (Finset α)} (hlin : Linear H)
    {I : Finset α} {u : α} (hu : u ∈ available H I)
    (q eq f2 e2 : ℝ) (hq : |((available H I).card:ℝ)-q| ≤ eq)
    (hd : |((incident H I 2 u).card:ℝ)-f2| ≤ e2) :
    |((safeChoices H I u).card:ℝ)-q| ≤ eq+1+f2+e2 := by
  rw [safeChoices_card hlin hu]
  have hdu : ((incident H I 2 u).card:ℝ) ≤ f2+e2 := by
    have hh := (abs_le.mp hd).2
    linarith
  have heq : ((available H I).card:ℝ)-1-(incident H I 2 u).card-q =
      (((available H I).card:ℝ)-q)-(1+(incident H I 2 u).card) := by ring
  rw [heq]
  calc
    _ ≤ |((available H I).card:ℝ)-q|+|1+((incident H I 2 u).card:ℝ)| := abs_sub _ _
    _ = |((available H I).card:ℝ)-q|+(1+(incident H I 2 u).card) := by rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 1+((incident H I 2 u).card:ℝ))]
    _ ≤ _ := by linarith

omit [Fintype α] [DecidableEq α] in
/-- Error budget for subtracting a deterministic profile increment. -/
lemma numerator_envelope (R M S q slope D E : ℝ)
    (hR : |R-M| ≤ D) (hS : |S-q| ≤ E) :
    |R-S*slope| ≤ D+|M-q*slope|+E*|slope| := by
  have he : R-S*slope = (R-M)+(M-q*slope)-(S-q)*slope := by ring
  rw [he]
  calc
    _ ≤ |(R-M)+(M-q*slope)|+|(S-q)*slope| := abs_sub _ _
    _ ≤ (|R-M|+|M-q*slope|)+|(S-q)*slope| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by
      rw [abs_mul]
      exact add_le_add (add_le_add hR le_rfl) (mul_le_mul_of_nonneg_right hS (abs_nonneg _))

omit [Fintype α] [DecidableEq α] in
/-- Growing envelopes absorb the entire guarded drift error. This gives
    upper and lower supermartingale signs without a critical-region premise. -/
lemma envelope_drift_signs (R S slope growth A smin : ℝ)
    (hR : |R-S*slope| ≤ A) (hS : smin ≤ S) (hg : 0 ≤ growth)
    (hdom : A ≤ smin*growth) :
    R-S*(slope+growth) ≤ 0 ∧ -(R-S*(slope-growth)) ≤ 0 := by
  have hgS := mul_le_mul_of_nonneg_right hS hg
  obtain ⟨hlo,hhi⟩ := abs_le.mp hR
  constructor <;> nlinarith only [hlo,hhi,hdom,hgS]

#print axioms incident_eq_empty_of_unavailable
#print axioms incident_eq_empty_of_size
#print axioms safeChoices_card
#print axioms two_drift_envelope
#print axioms higher_drift_envelope
#print axioms safe_count_envelope
#print axioms numerator_envelope
#print axioms envelope_drift_signs
end
end Erdos773.GreedyProfileDrift
