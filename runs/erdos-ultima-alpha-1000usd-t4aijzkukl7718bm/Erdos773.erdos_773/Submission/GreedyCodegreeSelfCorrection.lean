import Submission.GreedyCodegreeProfileDrift

/-!
Local drift estimates retaining the negative multiple of the tracked degree
error. These are one-step estimates, not a long-time concentration theorem.
The critical-interval bounds keep every duplicate and promotion error.
-/
namespace Erdos773.GreedyCodegreeSelfCorrection
open Finset GreedyHypergraphState GreedyCommonNeighbors GreedyLinearLocal
open GreedyCodegreeDrift GreedyCodegreeTwoDrift GreedyCodegreeHigherDrift
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Transfer the exact restoring term instead of bounding it in absolute
value along with the other profile errors. -/
lemma damped_transfer (R a b f x y g en K P : ℝ)
    (ha : 0 ≤ a) (hP : 0 ≤ P) (hPbound : P ≤ b)
    (hn : |y-g| ≤ en)
    (hr : |(R+P)-(a*y-f*x)| ≤ K*x) :
    |R-a*g+f*x| ≤ a*en+K*x+b := by
  have he : R-a*g+f*x = ((R+P)-(a*y-f*x))+a*(y-g)-P := by ring
  rw [he]
  calc
    _ ≤ |(R+P)-(a*y-f*x)|+|a*(y-g)|+|P| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ K*x+a*en+b := by
      rw [abs_mul,abs_of_nonneg ha,abs_of_nonneg hP]
      exact add_le_add (add_le_add hr (mul_le_mul_of_nonneg_left hn ha)) hPbound
    _ = _ := by ring

/-- Two-degree restoring drift, with its signed local error retained. -/
theorem two_damped {H : Finset (Finset α)} {I : Finset α} {u : α}
    (hu : u ∈ available H I)
    (f2 f3 e2 e3 E P : ℝ) (hE0 : 0 ≤ E) (C : ℕ)
    (h2 : ∀ x ∈ available H I, |((incident H I 2 x).card:ℝ)-f2| ≤ e2)
    (h3 : |((incident H I 3 u).card:ℝ)-f3| ≤ e3)
    (hE : ∀ x ∈ closes H I u, (duplicateExcess H I x:ℝ) ≤ E)
    (hC : ∀ x ∈ closes H I u, commonDegree H I u x ≤ C)
    (hP : (promotionDefect H I 2 u:ℝ) ≤ P) :
    |survivalDrift H I 2 u-(2*f3-f2^2)+
        f2*((incident H I 2 u).card-f2)| ≤
      2*e3+(e2+E+1+C)*(incident H I 2 u).card+P := by
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
  have ht := damped_transfer (survivalDrift H I 2 u) 2 P f2
    ((incident H I 2 u).card:ℝ) ((incident H I 3 u).card:ℝ) f3 e3
    (e2+E+1+C) (promotionDefect H I 2 u:ℝ)
    (by norm_num) (by positivity) hP h3 herr
  have he : survivalDrift H I 2 u-(2*f3-f2^2)+f2*((incident H I 2 u).card-f2) =
      survivalDrift H I 2 u-2*f3+f2*(incident H I 2 u).card := by ring
  rw [he]
  exact ht

/-- Higher-degree restoring drift, including the actual per-edge nonlinear
errors but not charging the self-error a second time. -/
theorem higher_damped {H : Finset (Finset α)}
    (I : Finset α) (j : ℕ) (hj : 3 ≤ j) (u : α)
    (f2 fj fn e2 en E P : ℝ) (hE0 : 0 ≤ E) (C : ℕ)
    (h2 : ∀ x ∈ available H I, |((incident H I 2 x).card:ℝ)-f2| ≤ e2)
    (hnext : |((incident H I (j+1) u).card:ℝ)-fn| ≤ en)
    (hE : ∀ x ∈ available H I, (duplicateExcess H I x:ℝ) ≤ E)
    (hC : ∀ x ∈ available H I, ∀ y ∈ available H I, x ≠ y → commonDegree H I x y ≤ C)
    (hP : (promotionDefect H I j u:ℝ) ≤ P) :
    |survivalDrift H I j u-((j:ℝ)*fn-(j-1:ℕ)*f2*fj)+
        (j-1:ℕ)*f2*((incident H I j u).card-fj)| ≤
      (j:ℝ)*en+((j-1:ℕ)*(e2+E+1)+(j.choose 2:ℝ)*C)*(incident H I j u).card+P := by
  have hl (x : α) (hx : x ∈ available H I) : f2-e2 ≤ ((incident H I 2 x).card:ℝ) := by
    have hh := (abs_le.mp (h2 x hx)).1
    linarith only [hh]
  have hh (x : α) (hx : x ∈ available H I) : ((incident H I 2 x).card:ℝ) ≤ f2+e2 := by
    have hh := (abs_le.mp (h2 x hx)).2
    linarith only [hh]
  have hr := survival_drift_profile_bounds I j hj u (f2-e2) (f2+e2) E C hl hh hE hC
  have herr : |(survivalDrift H I j u+(promotionDefect H I j u:ℝ))-
      ((j:ℝ)*(incident H I (j+1) u).card-(j-1:ℕ)*f2*(incident H I j u).card)| ≤
        ((j-1:ℕ)*(e2+E+1)+(j.choose 2:ℝ)*C)*(incident H I j u).card := by
    apply abs_le.mpr
    have hn : (0:ℝ) ≤ ((j-1:ℕ)*E+(j.choose 2:ℝ)*C)*(incident H I j u).card := by positivity
    constructor <;> nlinarith only [hr.1,hr.2,hn]
  have ht := damped_transfer (survivalDrift H I j u) j P ((j-1:ℕ)*f2)
    ((incident H I j u).card:ℝ) ((incident H I (j+1) u).card:ℝ) fn en
    ((j-1:ℕ)*(e2+E+1)+(j.choose 2:ℝ)*C) (promotionDefect H I j u:ℝ)
    (by positivity) (by positivity) hP hnext herr
  have he : survivalDrift H I j u-((j:ℝ)*fn-(j-1:ℕ)*f2*fj)+
      (j-1:ℕ)*f2*((incident H I j u).card-fj) =
      survivalDrift H I j u-(j:ℝ)*fn+(j-1:ℕ)*f2*(incident H I j u).card := by ring
  rw [he]
  exact ht

/-- Critical-interval conversion of a restoring estimate. Both signs get
negative drift from being a positive distance away from the center. -/
lemma critical_sides (R F a x K c : ℝ) (ha : 0 ≤ a)
    (h : |R-F+a*x| ≤ K) :
    (c ≤ x → R-F ≤ K-a*c) ∧ (x ≤ -c → F-R ≤ K-a*c) := by
  obtain ⟨hlo,hhi⟩ := abs_le.mp h
  constructor
  · intro hx
    have hm := mul_le_mul_of_nonneg_left hx ha
    linarith only [hm,hhi]
  · intro hx
    have hm := mul_le_mul_of_nonneg_left hx ha
    nlinarith only [hm,hlo]

/-- The two-degree critical-interval budget saves the restoring term f2*c
in BOTH signs. This is not the older absolute-error budget. -/
theorem two_critical {H : Finset (Finset α)} {I : Finset α} {u : α}
    (hu : u ∈ available H I)
    (f2 f3 e2 e3 E P c : ℝ) (hf2 : 0 ≤ f2) (he2 : 0 ≤ e2) (hE0 : 0 ≤ E) (C : ℕ)
    (h2 : ∀ x ∈ available H I, |((incident H I 2 x).card:ℝ)-f2| ≤ e2)
    (h3 : |((incident H I 3 u).card:ℝ)-f3| ≤ e3)
    (hE : ∀ x ∈ closes H I u, (duplicateExcess H I x:ℝ) ≤ E)
    (hC : ∀ x ∈ closes H I u, commonDegree H I u x ≤ C)
    (hP : (promotionDefect H I 2 u:ℝ) ≤ P) :
    (c ≤ ((incident H I 2 u).card:ℝ)-f2 →
      survivalDrift H I 2 u-(2*f3-f2^2) ≤
        2*e3+(e2+E+1+C)*(f2+e2)+P-f2*c) ∧
    (((incident H I 2 u).card:ℝ)-f2 ≤ -c →
      (2*f3-f2^2)-survivalDrift H I 2 u ≤
        2*e3+(e2+E+1+C)*(f2+e2)+P-f2*c) := by
  have hd := two_damped hu f2 f3 e2 e3 E P hE0 C h2 h3 hE hC hP
  have hupper : ((incident H I 2 u).card:ℝ) ≤ f2+e2 := by
    have := (abs_le.mp (h2 u hu)).2
    linarith only [this]
  have hm := mul_le_mul_of_nonneg_left hupper
    (show (0:ℝ) ≤ e2+E+1+C by positivity)
  have hb : |survivalDrift H I 2 u-(2*f3-f2^2)+
      f2*((incident H I 2 u).card-f2)| ≤ 2*e3+(e2+E+1+C)*(f2+e2)+P := by
    linarith only [hd,hm]
  exact critical_sides _ _ _ _ _ c hf2 hb

/-- The higher-degree critical-interval budget saves (j-1)*f2*c. -/
theorem higher_critical {H : Finset (Finset α)}
    (I : Finset α) (j : ℕ) (hj : 3 ≤ j) (u : α)
    (f2 fj fn e2 ej en E P c : ℝ) (hf2 : 0 ≤ f2) (he2 : 0 ≤ e2) (hE0 : 0 ≤ E) (C : ℕ)
    (h2 : ∀ x ∈ available H I, |((incident H I 2 x).card:ℝ)-f2| ≤ e2)
    (hlocal : |((incident H I j u).card:ℝ)-fj| ≤ ej)
    (hnext : |((incident H I (j+1) u).card:ℝ)-fn| ≤ en)
    (hE : ∀ x ∈ available H I, (duplicateExcess H I x:ℝ) ≤ E)
    (hC : ∀ x ∈ available H I, ∀ y ∈ available H I, x ≠ y → commonDegree H I x y ≤ C)
    (hP : (promotionDefect H I j u:ℝ) ≤ P) :
    (c ≤ ((incident H I j u).card:ℝ)-fj →
      survivalDrift H I j u-((j:ℝ)*fn-(j-1:ℕ)*f2*fj) ≤
        (j:ℝ)*en+((j-1:ℕ)*(e2+E+1)+(j.choose 2:ℝ)*C)*(fj+ej)+P-(j-1:ℕ)*f2*c) ∧
    (((incident H I j u).card:ℝ)-fj ≤ -c →
      ((j:ℝ)*fn-(j-1:ℕ)*f2*fj)-survivalDrift H I j u ≤
        (j:ℝ)*en+((j-1:ℕ)*(e2+E+1)+(j.choose 2:ℝ)*C)*(fj+ej)+P-(j-1:ℕ)*f2*c) := by
  have hd := higher_damped I j hj u f2 fj fn e2 en E P hE0 C h2 hnext hE hC hP
  have hupper : ((incident H I j u).card:ℝ) ≤ fj+ej := by
    have := (abs_le.mp hlocal).2
    linarith only [this]
  have hm := mul_le_mul_of_nonneg_left hupper
    (show (0:ℝ) ≤ (j-1:ℕ)*(e2+E+1)+(j.choose 2:ℝ)*C by positivity)
  have hb : |survivalDrift H I j u-((j:ℝ)*fn-(j-1:ℕ)*f2*fj)+
      (j-1:ℕ)*f2*((incident H I j u).card-fj)| ≤
      (j:ℝ)*en+((j-1:ℕ)*(e2+E+1)+(j.choose 2:ℝ)*C)*(fj+ej)+P := by
    linarith only [hd,hm]
  exact critical_sides _ _ _ _ _ c (by positivity) hb

#print axioms damped_transfer
#print axioms two_damped
#print axioms higher_damped
#print axioms critical_sides
#print axioms two_critical
#print axioms higher_critical
end
end Erdos773.GreedyCodegreeSelfCorrection
