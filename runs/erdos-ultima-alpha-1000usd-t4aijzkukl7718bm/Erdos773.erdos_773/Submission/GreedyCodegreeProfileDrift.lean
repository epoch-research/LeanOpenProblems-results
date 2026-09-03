import Submission.GreedyCodegreeTwoDrift
import Submission.GreedyProfileDrift

/-!
Nonlinear profile drift with explicit promotion and duplicate guards.
These are conditional estimates, not long-time trajectory claims.
-/
namespace Erdos773.GreedyCodegreeProfileDrift
open Finset GreedyHypergraphState GreedyCommonNeighbors GreedyLinearLocal
open GreedyCodegreeDrift GreedyCodegreeTwoDrift GreedyProfileDrift
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Safe choices have the simple closure decrement, with multiplicity
    excess added back if expressed in terms of incident two-degrees. -/
lemma safeChoices_card {H : Finset (Finset α)} {I : Finset α} {u : α}
    (hu : u ∈ available H I) :
    ((safeChoices H I u).card:ℝ) = (available H I).card-1-(incident H I 2 u).card+
      (duplicateExcess H I u:ℝ) := by
  have hh := available_card_step hu
  rw [← safeChoices_eq_available hu] at hh
  have hhR : ((safeChoices H I u).card:ℝ)+1+(closes H I u).card =
      (available H I).card := by exact_mod_cast hh
  have hd : ((incident H I 2 u).card:ℝ) = (closes H I u).card+(duplicateExcess H I u:ℝ) := by
    exact_mod_cast incident_card_eq_closes_add_excess hu
  linarith only [hhR,hd]

/-- No extra duplicate penalty is needed for the safe-count envelope:
    counting actual closures can only decrease the decrement. -/
theorem safe_count_envelope {H : Finset (Finset α)}
    {I : Finset α} {u : α} (hu : u ∈ available H I)
    (q eq f2 e2 : ℝ) (hq : |((available H I).card:ℝ)-q| ≤ eq)
    (hd : |((incident H I 2 u).card:ℝ)-f2| ≤ e2) :
    |((safeChoices H I u).card:ℝ)-q| ≤ eq+1+f2+e2 := by
  have hh := available_card_step hu
  rw [← safeChoices_eq_available hu] at hh
  have hhR : ((safeChoices H I u).card:ℝ)+1+(closes H I u).card =
      (available H I).card := by exact_mod_cast hh
  have hc : ((closes H I u).card:ℝ) ≤ (incident H I 2 u).card := by
    exact_mod_cast closes_card_le_incident hu
  have he : ((safeChoices H I u).card:ℝ)-q =
      (((available H I).card:ℝ)-q)-(1+(closes H I u).card) := by linarith only [hhR]
  rw [he]
  calc
    _ ≤ |((available H I).card:ℝ)-q|+|1+((closes H I u).card:ℝ)| := abs_sub _ _
    _ = |((available H I).card:ℝ)-q|+(1+(closes H I u).card) := by
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 1+((closes H I u).card:ℝ))]
    _ ≤ _ := by have hdu := (abs_le.mp hd).2; linarith only [hq,hc,hdu]

/-- Two-degree profile error, with promotion deficit P and duplicate guard E. -/
theorem two_drift_envelope {H : Finset (Finset α)}
    {I : Finset α} {u : α} (hu : u ∈ available H I)
    (f2 f3 e2 e3 E P : ℝ) (hf2 : 0 ≤ f2) (he2 : 0 ≤ e2) (hE0 : 0 ≤ E) (C : ℕ)
    (h2 : ∀ x ∈ available H I, |((incident H I 2 x).card:ℝ)-f2| ≤ e2)
    (h3 : |((incident H I 3 u).card:ℝ)-f3| ≤ e3)
    (hE : ∀ x ∈ closes H I u, (duplicateExcess H I x:ℝ) ≤ E)
    (hC : ∀ x ∈ closes H I u, commonDegree H I u x ≤ C)
    (hP : (promotionDefect H I 2 u:ℝ) ≤ P) :
    |survivalDrift H I 2 u-(2*f3-f2*f2)| ≤
      2*e3+f2*e2+(e2+E+1+C)*(f2+e2)+P := by
  have hl (x : α) (hx : x ∈ closes H I u) : f2-e2 ≤ ((incident H I 2 x).card:ℝ) := by
    have hh := (abs_le.mp (h2 x (closes_subset H I u hx))).1
    linarith only [hh]
  have hh (x : α) (hx : x ∈ closes H I u) : ((incident H I 2 x).card:ℝ) ≤ f2+e2 := by
    have hh := (abs_le.mp (h2 x (closes_subset H I u hx))).2
    linarith only [hh]
  have hr := survival_two_profile_bounds hu (f2-e2) (f2+e2) E C hl hh hE hC
  have herr : |(survivalDrift H I 2 u+(promotionDefect H I 2 u:ℝ))-
      (2*(incident H I 3 u).card-f2*(incident H I 2 u).card)| ≤
        (e2+E+1+C)*(incident H I 2 u).card := by
    apply abs_le.mpr
    have hn : (0:ℝ) ≤ (E+2+C)*(incident H I 2 u).card := by positivity
    constructor <;> nlinarith only [hr.1,hr.2,hn]
  have ht : |(survivalDrift H I 2 u+(promotionDefect H I 2 u:ℝ))-(2*f3-f2*f2)| ≤
      2*e3+f2*e2+(e2+E+1+C)*(f2+e2) := by
    simpa only [one_mul] using drift_transfer _ 2 1 f2 _ _ f2 f3 e2 e3 (e2+E+1+C)
      (by norm_num) (by norm_num) hf2 (by positivity) (h2 u hu) h3 (by simpa only [one_mul] using herr)
  have he : survivalDrift H I 2 u-(2*f3-f2*f2) =
      ((survivalDrift H I 2 u+(promotionDefect H I 2 u:ℝ))-(2*f3-f2*f2))-
        (promotionDefect H I 2 u:ℝ) := by ring
  rw [he]
  calc
    _ ≤ |(survivalDrift H I 2 u+(promotionDefect H I 2 u:ℝ))-(2*f3-f2*f2)|+
        |(promotionDefect H I 2 u:ℝ)| := abs_sub _ _
    _ ≤ _ := add_le_add ht (by rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ promotionDefect H I 2 u)]; exact hP)

/-- Higher-degree envelopes have the same mean field, with the nonlinear
    errors retained at their actual scales. -/
theorem higher_drift_envelope {H : Finset (Finset α)}
    (I : Finset α) (j : ℕ) (hj : 3 ≤ j) (u : α)
    (f2 fj fn e2 ej en E P : ℝ) (hf2 : 0 ≤ f2) (he2 : 0 ≤ e2) (hE0 : 0 ≤ E) (C : ℕ)
    (h2 : ∀ x ∈ available H I, |((incident H I 2 x).card:ℝ)-f2| ≤ e2)
    (hlocal : |((incident H I j u).card:ℝ)-fj| ≤ ej)
    (hnext : |((incident H I (j+1) u).card:ℝ)-fn| ≤ en)
    (hE : ∀ x ∈ available H I, (duplicateExcess H I x:ℝ) ≤ E)
    (hC : ∀ x ∈ available H I, ∀ y ∈ available H I, x ≠ y → commonDegree H I x y ≤ C)
    (hP : (promotionDefect H I j u:ℝ) ≤ P) :
    |survivalDrift H I j u-((j:ℝ)*fn-(j-1:ℕ)*f2*fj)| ≤
      (j:ℝ)*en+(j-1:ℕ)*f2*ej+((j-1:ℕ)*(e2+E+1)+(j.choose 2:ℝ)*C)*(fj+ej)+P := by
  have hl (x : α) (hx : x ∈ available H I) : f2-e2 ≤ ((incident H I 2 x).card:ℝ) := by
    have hh := (abs_le.mp (h2 x hx)).1
    linarith only [hh]
  have hh (x : α) (hx : x ∈ available H I) : ((incident H I 2 x).card:ℝ) ≤ f2+e2 := by
    have hh := (abs_le.mp (h2 x hx)).2
    linarith only [hh]
  have hr := GreedyCodegreeHigherDrift.survival_drift_profile_bounds I j hj u (f2-e2) (f2+e2) E C hl hh hE hC
  have herr : |(survivalDrift H I j u+(promotionDefect H I j u:ℝ))-
      ((j:ℝ)*(incident H I (j+1) u).card-(j-1:ℕ)*f2*(incident H I j u).card)| ≤
        ((j-1:ℕ)*(e2+E+1)+(j.choose 2:ℝ)*C)*(incident H I j u).card := by
    apply abs_le.mpr
    have hn : (0:ℝ) ≤ ((j-1:ℕ)*E+(j.choose 2:ℝ)*C)*(incident H I j u).card := by positivity
    constructor <;> nlinarith only [hr.1,hr.2,hn]
  have ht := drift_transfer _ j (j-1:ℕ) f2 _ _ fj fn ej en
    ((j-1:ℕ)*(e2+E+1)+(j.choose 2:ℝ)*C)
    (by positivity) (by positivity) hf2 (by positivity) hlocal hnext herr
  have he : survivalDrift H I j u-((j:ℝ)*fn-(j-1:ℕ)*f2*fj) =
      ((survivalDrift H I j u+(promotionDefect H I j u:ℝ))-((j:ℝ)*fn-(j-1:ℕ)*f2*fj))-
        (promotionDefect H I j u:ℝ) := by ring
  rw [he]
  calc
    _ ≤ |(survivalDrift H I j u+(promotionDefect H I j u:ℝ))-((j:ℝ)*fn-(j-1:ℕ)*f2*fj)|+
        |(promotionDefect H I j u:ℝ)| := abs_sub _ _
    _ ≤ _ := add_le_add ht (by rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ promotionDefect H I j u)]; exact hP)

#print axioms safeChoices_card
#print axioms safe_count_envelope
#print axioms two_drift_envelope
#print axioms higher_drift_envelope
end
end Erdos773.GreedyCodegreeProfileDrift
