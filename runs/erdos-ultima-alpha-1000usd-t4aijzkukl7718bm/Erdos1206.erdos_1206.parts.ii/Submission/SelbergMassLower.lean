import Submission.PrimeBoxSelberg

/-!
A lower bound for the truncated Selberg mass from a logarithmic first moment.
This does not supply the requisite prime-distribution estimates.
-/
namespace Erdos1206.SelbergMassLower
open Finset FiniteThinnedSieve FiniteSelbergWeights PrimeBoxSelberg
open scoped Classical
variable {ι : Type*} [DecidableEq ι]

noncomputable def fullMass (P : Finset ι) (r : ι → ℝ) : ℝ := ∏ p ∈ P, (1+odds r p)

lemma one_add_odds_mul {r : ℝ} (hr : r ≠ 1) :
    (1+r/(1-r))*(1-r)=1 ∧ (1+r/(1-r))*r=r/(1-r) := by
  have h : 1-r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  constructor <;> field_simp <;> ring

lemma fullMass_mul_weight (P S : Finset ι) (r : ι → ℝ)
    (hS : S ⊆ P) (hr : ∀ p ∈ P, r p ≠ 1) :
    fullMass P r*weight P r S=localMass r S := by
  have hprod := prod_sdiff (f := fun p => 1+odds r p) hS
  have hout : (∏ p ∈ P \ S, ((1+odds r p)*(1-r p)))=1 := by
    apply prod_eq_one
    intro p hp
    exact (one_add_odds_mul (hr p (mem_sdiff.mp hp).1)).1
  have hin : (∏ p ∈ S, ((1+odds r p)*r p))=localMass r S := by
    apply prod_congr rfl
    intro p hp
    exact (one_add_odds_mul (hr p (hS hp))).2
  simp only [prod_mul_distrib] at hout hin
  dsimp only [fullMass,weight]
  rw [← hprod]
  calc
    _ = ((∏ p ∈ P \ S, (1+odds r p))*(∏ p ∈ P \ S, (1-r p)))*
        ((∏ p ∈ S, (1+odds r p))*(∏ p ∈ S, r p)) := by ring
    _ = _ := by rw [hout,hin,one_mul]

omit [DecidableEq ι] in
lemma fullMass_eq_sum (P : Finset ι) (r : ι → ℝ) :
    fullMass P r=∑ S ∈ P.powerset, localMass r S := by
  simp only [fullMass,localMass]
  simpa only [add_comm] using (prod_add_one (f := odds r) P)

lemma expectation_sum_members (P : Finset ι) (r w : ι → ℝ) :
    (∑ J ∈ P.powerset, weight P r J*(∑ p ∈ J, w p)) = ∑ p ∈ P, r p*w p := by
  calc
    _ = ∑ J ∈ P.powerset, ∑ p ∈ P, if p ∈ J then weight P r J*w p else 0 := by
      apply sum_congr rfl
      intro J hJ
      have he : (∑ p ∈ P, if p ∈ J then w p else 0)=∑ p ∈ J, w p := by
        rw [sum_ite_mem,inter_eq_right.mpr (mem_powerset.mp hJ)]
      rw [← he,mul_sum]
      exact sum_congr rfl (fun p hp => by split_ifs <;> simp)
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p hp
      have hh := sum_weight_supersets P {p} r (singleton_subset_iff.mpr hp)
      simp only [singleton_subset_iff,prod_singleton] at hh
      calc
        _ = (∑ J ∈ P.powerset, if p ∈ J then weight P r J else 0)*w p := by
          rw [sum_mul]
          exact sum_congr rfl (fun J hJ => by split_ifs <;> simp)
        _ = _ := by rw [hh]

lemma mass_sum_members (P : Finset ι) (r w : ι → ℝ) (hr : ∀ p ∈ P, r p ≠ 1) :
    (∑ S ∈ P.powerset, localMass r S*(∑ p ∈ S, w p)) =
      fullMass P r*(∑ p ∈ P, r p*w p) := by
  rw [← expectation_sum_members P r w,mul_sum]
  apply sum_congr rfl
  intro S hS
  rw [← fullMass_mul_weight P S r (mem_powerset.mp hS) hr]
  ring

omit [DecidableEq ι] in
lemma fullMass_pos (P : Finset ι) (r : ι → ℝ)
    (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p < 1) : 0 < fullMass P r := by
  apply prod_pos
  intro p hp
  have ho : 0 ≤ odds r p := div_nonneg (hr p hp).1 (sub_pos.mpr (hr p hp).2).le
  linarith

/-- A logarithmic first-moment bound retains at least half the full Euler
product in the level truncation. -/
theorem half_fullMass_le_sieveMass (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℝ) (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p < 1) (z : ℕ) (hz : 1 < z)
    (hmoment : 2*(∑ p ∈ P, r p*Real.log p) ≤ Real.log z) :
    fullMass P r/2 ≤ sieveMass r (level P z) := by
  have hzR : (1:ℝ)<z := by exact_mod_cast hz
  have hlog : 0 < Real.log z := Real.log_pos hzR
  have hfull := fullMass_pos P r hr
  have hpt (S : Finset ℕ) (hS : S ∈ P.powerset) :
      localMass r S*Real.log z ≤
        (if S ∈ level P z then localMass r S*Real.log z else 0)+
          localMass r S*(∑ p ∈ S, Real.log p) := by
    have hSP := mem_powerset.mp hS
    have hm0 := localMass_nonneg P S r hSP hr
    have hl0 : 0 ≤ ∑ p ∈ S, Real.log p := by
      apply sum_nonneg
      intro p hp
      apply Real.log_nonneg
      exact_mod_cast (hP p (hSP hp)).one_lt.le
    by_cases hlevel : S ∈ level P z
    · rw [if_pos hlevel]
      have := mul_nonneg hm0 hl0
      linarith
    · rw [if_neg hlevel,zero_add]
      have hh : z < ∏ p ∈ S, p := by
        by_contra hn
        exact hlevel (mem_filter.mpr ⟨hS,by omega⟩)
      have hhR : (z:ℝ) ≤ ∏ p ∈ S, (p:ℝ) := by
        have hnat : (z:ℝ) ≤ ((∏ p ∈ S, p:ℕ):ℝ) := by exact_mod_cast hh.le
        simpa only [Nat.cast_prod] using hnat
      have hl := Real.log_le_log (by positivity : (0:ℝ)<z) hhR
      rw [Real.log_prod (fun p hp => by exact_mod_cast (hP p (hSP hp)).ne_zero)] at hl
      exact mul_le_mul_of_nonneg_left hl hm0
  have hs := sum_le_sum hpt
  rw [sum_add_distrib,← sum_mul,← fullMass_eq_sum,mass_sum_members P r (fun p => Real.log p)
    (fun p hp => (hr p hp).2.ne)] at hs
  have he : (∑ S ∈ P.powerset, if S ∈ level P z then localMass r S*Real.log z else 0) =
      sieveMass r (level P z)*Real.log z := by
    rw [sum_ite_mem]
    have hsub : level P z ⊆ P.powerset := filter_subset _ _
    rw [inter_eq_right.mpr hsub,← sum_mul]
    rfl
  rw [he] at hs
  have hh := mul_le_mul_of_nonneg_left hmoment hfull.le
  nlinarith

lemma exp_le_one_add_odds {r : ℝ} (hr : r < 1) :
    Real.exp r ≤ 1+r/(1-r) := by
  have hpos : 0 < 1-r := sub_pos.mpr hr
  have hl := Real.log_le_sub_one_of_pos hpos
  have he : Real.exp r ≤ Real.exp (-Real.log (1-r)) := Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_neg,Real.exp_log hpos] at he
  have hid : (1-r)⁻¹=1+r/(1-r) := by field_simp; ring
  rwa [hid] at he

omit [DecidableEq ι] in
lemma exp_sum_le_fullMass (P : Finset ι) (r : ι → ℝ)
    (hr : ∀ p ∈ P, r p < 1) : Real.exp (∑ p ∈ P, r p) ≤ fullMass P r := by
  rw [Real.exp_sum]
  apply prod_le_prod (fun p _ => (Real.exp_pos (r p)).le)
  intro p hp
  exact exp_le_one_add_odds (hr p hp)

theorem exp_sum_le_twice_sieveMass (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℝ) (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p < 1) (z : ℕ) (hz : 1 < z)
    (hmoment : 2*(∑ p ∈ P, r p*Real.log p) ≤ Real.log z) :
    Real.exp (∑ p ∈ P, r p) ≤ 2*sieveMass r (level P z) := by
  have hhalf := half_fullMass_le_sieveMass P hP r hr z hz hmoment
  have he := exp_sum_le_fullMass P r (fun p hp => (hr p hp).2)
  linarith

/-- A finite exponential upper bound, conditional only on a logarithmic
first moment and the exact local densities of the residue sets. -/
theorem few_hits_exponential (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (B : (p : ℕ) → Finset (ZMod p × ZMod p))
    (hB : ∀ p ∈ P, 0 < PrimeBoxCRT.localDensity B p ∧ PrimeBoxCRT.localDensity B p ≤ 1/2)
    (N z k : ℕ) (hz : 1 < z) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hmoment : 2*(∑ p ∈ P, (q*PrimeBoxCRT.localDensity B p)*Real.log p) ≤ Real.log z) :
    (((((range N) ×ˢ (range N)).filter (fun x => (hits P B x).card ≤ k)).card:ℝ)*(1-q)^k) ≤
      2*(N:ℝ)^2*Real.exp (-(∑ p ∈ P, q*PrimeBoxCRT.localDensity B p)) +
        2*(N:ℝ)*(z:ℝ)^6+(z:ℝ)^8 := by
  let r : ℕ → ℝ := fun p => q*PrimeBoxCRT.localDensity B p
  have hr (p : ℕ) (hp : p ∈ P) : 0 ≤ r p ∧ r p < 1 := by
    have hlo := mul_pos hq0 (hB p hp).1
    have hhi : r p ≤ 1/2 :=
      (mul_le_of_le_one_left (hB p hp).1.le hq1).trans (hB p hp).2
    exact ⟨hlo.le,hhi.trans_lt (by norm_num)⟩
  have he := exp_sum_le_twice_sieveMass P hP r hr z hz hmoment
  have hden : Real.exp (∑ p ∈ P, r p)/2 ≤ sieveMass r (level P z) := by linarith
  have hm := div_le_div_of_nonneg_left (sq_nonneg (N:ℝ)) (by positivity :
    0 < Real.exp (∑ p ∈ P, r p)/2) hden
  have heq : (N:ℝ)^2/(Real.exp (∑ p ∈ P, r p)/2) =
      2*(N:ℝ)^2*Real.exp (-(∑ p ∈ P, r p)) := by
    rw [Real.exp_neg]
    ring
  rw [heq] at hm
  have hh := few_hits_bound P hP B hB N z k hz.le hq0 hq1
  change _ ≤ (N:ℝ)^2/sieveMass r (level P z)+2*(N:ℝ)*(z:ℝ)^6+(z:ℝ)^8 at hh
  dsimp only [r] at hm
  linarith

#print axioms mass_sum_members
#print axioms half_fullMass_le_sieveMass
#print axioms exp_sum_le_twice_sieveMass
#print axioms few_hits_exponential
end Erdos1206.SelbergMassLower
