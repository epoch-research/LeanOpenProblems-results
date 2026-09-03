import Submission.EulerMassMonotoneQuadrature
import Submission.BuchstabProfileSectors
import Submission.ContinuousBuchstabRectangles

/-! Quantitative, mesh-free comparison of the actual first-hit prime measure
with a continuous monotone profile. This controls the arithmetic quadrature
itself, not the difference between a recursively refined sieve and its model.
The low-prime part below the displayed cutoff is not omitted silently. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg ContinuousBuchstab MeasureTheory Set
set_option maxHeartbeats 1600000

lemma profileBin_child_coordinate (L a b : ℝ) (ha : 0 ≤ a) (p : ℕ)
    (hp : p ∈ profileBin L a b) : a ≤ L/log (p : ℝ)-1 := by
  have hpp := (mem_filter.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hl : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hpp.one_lt)
  have hh := log_le_log (exp_pos _) (profileBin_child_level L a b ha p hp)
  rw [log_exp,log_div (exp_ne_zero _) hp0.ne',log_exp] at hh
  have ht : a+1 ≤ L/log (p : ℝ) := (le_div_iff₀ hl).mpr (by nlinarith only [hh])
  linarith only [ht]

/-- A direct profile integral bound. All parameters s,M,L may vary subject to
the explicit size conditions. The remainder is independent of the mesh and
uses only the profile value at s-1; no differentiability is required. -/
theorem prime_profile_le_tailIntegral (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A)
    (s M L : ℝ) (hs : 1 ≤ s) (hsM : s < M) (hL : 2 ≤ L)
    (hcut : 2 ≤ (s/M)*L) (hlarge : 2*(A+C) ≤ C*((s/M)*L))
    (f : ℝ → ℝ) (hf : AntitoneOn f (Ici (s-1)))
    (hf0 : ∀ x, s-1 ≤ x → 0 ≤ f x) (hfi : IntegrableOn f (Ioi (s-1))) :
    initialEulerMass (expFloor 1 L)*
      (∑ p ∈ (Finset.Ioc (expFloor (s/M) L) (expFloor 1 L)).filter Nat.Prime,
        ((1/(p : ℝ))*(1/eulerMass p.primesBelow))*f (s*L/log (p : ℝ)-1)) ≤
      tailIntegral f (s-1)/s+
        (4*(A+C)/(C*((s/M)*L)))*(1+1/(s/M))*f (s-1) := by
  have hs0 : 0 < s := by linarith
  have hM : 0 < M := hs0.trans hsM
  have hL0 : 0 < L := by linarith
  have ha : 0 < s/M := div_pos hs0 hM
  let F : ℕ → ℝ := fun p =>
    ((1/(p : ℝ))*(1/eulerMass p.primesBelow))*f (s*L/log (p : ℝ)-1)
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨N,hN,hrect⟩ := exists_rectangular_upper f (s-1) (M-1) (ε*s)
    (by linarith) (mul_pos hε hs0) hf hf0 hfi
  let h : ℝ := (M-s)/(N : ℝ)
  let v : ℕ → ℝ := fun j => s-1+h*j
  let t : ℕ → ℝ := fun j => s/(v j+1)
  let b : ℕ → ℝ := fun j => f (v j)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : 0 < h := div_pos (sub_pos.mpr hsM) hNr
  have hv : Monotone v := by
    intro i j hij
    have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
    dsimp only [v]
    nlinarith only [hh,hijR]
  have hv0 : v 0=s-1 := by simp [v]
  have hvN : v N=M-1 := by dsimp [v,h]; field_simp; ring
  have hvlow (j : ℕ) : s-1 ≤ v j := by simpa only [hv0] using hv (Nat.zero_le j)
  have hvnonneg (j : ℕ) : 0 ≤ v j := by linarith only [hvlow j,hs]
  have ht : ∀ i, i ≤ N → s/M ≤ t i := by
    intro i hi
    have hh := hv hi
    rw [hvN] at hh
    exact div_le_div_of_nonneg_left hs0.le (by linarith [hvnonneg i]) (by linarith)
  have htanti : ∀ i, i < N → t (i+1) ≤ t i := by
    intro i hi
    exact div_le_div_of_nonneg_left hs0.le (by linarith [hvnonneg i])
      (by linarith [hv (Nat.le_succ i)])
  have hb : ∀ i, 0 ≤ b i := fun i => hf0 _ (hvlow i)
  have hbanti : Antitone b := fun i j hij => hf (hvlow i) (hvlow j) (hv hij)
  have hbin : ∀ i ∈ range N, ∀ p ∈ profileBin (s*L) (v i) (v (i+1)),
      F p ≤ b i*((1/(p : ℝ))*(1/eulerMass p.primesBelow)) := by
    intro i hi p hp
    have hc := profileBin_child_coordinate (s*L) (v i) (v (i+1)) (hvnonneg i) p hp
    have hprof := hf (hvlow i) ((hvlow i).trans hc) hc
    have hw : 0 ≤ (1/(p : ℝ))*(1/eulerMass p.primesBelow) := by
      have he := (eulerMass_pos p.primesBelow (fun q hq => (Nat.mem_primesBelow.mp hq).2)).le
      positivity
    have hm := mul_le_mul_of_nonneg_left hprof hw
    simpa only [F,b,mul_comm] using hm
  have hbin' : ∀ i ∈ range N, ∀ p ∈
      (Finset.Ioc (expFloor (t (i+1)) L) (expFloor (t i) L)).filter Nat.Prime,
      F p ≤ b i*((1/(p : ℝ))*(1/eulerMass p.primesBelow)) := by
    simpa only [profileBin,profileCut_scaled,t] using hbin
  have hquad := firstHit_monotone_profile_majorant C A hC hA hrem (s/M) 1 L ha
    (by norm_num) hL0 (by simpa only [one_mul] using hL) hcut hlarge N t b ht htanti hb hbanti F hbin'
  have hquad' : initialEulerMass (expFloor 1 L)*
      (∑ i ∈ range N, ∑ p ∈ profileBin (s*L) (v i) (v (i+1)), F p) ≤
      (∑ i ∈ range N, b i*(1/t (i+1)-1/t i))+
        (4*(A+C)/(C*((s/M)*L)))*(1+1/(s/M))*b 0 := by
    simpa only [profileBin,profileCut_scaled,t] using hquad
  have hpart := profileBins_sum (s*L) (by positivity) v hv (hvnonneg 0) N F
  have hstart : profileCut (s*L) (v 0)=expFloor 1 L := by
    rw [hv0,profileCut_scaled,sub_add_cancel,div_self hs0.ne']
  have hend : profileCut (s*L) (v N)=expFloor (s/M) L := by
    rw [hvN,profileCut_scaled,sub_add_cancel]
  rw [hstart,hend] at hpart
  rw [hpart] at hquad'
  have hsum : (∑ i ∈ range N, b i*(1/t (i+1)-1/t i)) =
      (∑ i ∈ range N, h*f (v i))/s := by
    rw [sum_div]
    apply sum_congr rfl
    intro i hi
    dsimp only [t,b]
    rw [profile_sector_mass s _ _ hs0 (hvnonneg i) (hv (Nat.le_succ i))]
    have hstep : v (i+1)-v i=h := by dsimp [v]; push_cast; ring
    rw [hstep]
    ring
  have hbzero : b 0=f (s-1) := by dsimp [b]; rw [hv0]
  rw [hsum,hbzero] at hquad'
  have hrect' : (∑ i ∈ range N, h*f (v i)) < tailIntegral f (s-1)+ε*s := by
    have hid : M-1-(s-1)=M-s := by ring
    simpa only [hid,h,v] using hrect
  have hdiv := div_lt_div_of_pos_right hrect' hs0
  rw [add_div,mul_div_cancel_right₀ _ hs0.ne'] at hdiv
  change initialEulerMass (expFloor 1 L)*
      (∑ p ∈ (Finset.Ioc (expFloor (s/M) L) (expFloor 1 L)).filter Nat.Prime, F p) < _
  linarith only [hquad',hdiv]

#print axioms profileBin_child_coordinate
#print axioms prime_profile_le_tailIntegral
end Erdos970.RecursiveSieve.Buchstab
