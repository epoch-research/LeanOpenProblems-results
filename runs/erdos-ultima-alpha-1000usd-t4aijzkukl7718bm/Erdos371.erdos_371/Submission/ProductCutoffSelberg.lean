import Submission.TruncatedEulerMass

/-! A Selberg upper sieve with an elementary Euler-product lower bound for
its denominator. -/

namespace Erdos371
namespace FiniteSieve
open Finset
variable {ι : Type*} [DecidableEq ι]

noncomputable def productSieveFamily (S : Finset ι) (s : ι → ℕ) (Z : ℝ) : Finset (Finset ι) :=
  S.powerset.filter (fun T => (∏ i ∈ T, (s i : ℝ)) ≤ Z)

lemma mem_productSieveFamily (S : Finset ι) (s : ι → ℕ) (Z : ℝ) (T : Finset ι) :
    T ∈ productSieveFamily S s Z ↔ T ⊆ S ∧ (∏ i ∈ T, (s i : ℝ)) ≤ Z := by
  classical
  simp [productSieveFamily]

lemma productSieveFamily_empty (S : Finset ι) (s : ι → ℕ) (Z : ℝ) (hZ : 1 ≤ Z) :
    ∅ ∈ productSieveFamily S s Z := by
  rw [mem_productSieveFamily]
  simpa using And.intro (empty_subset S) hZ

lemma selbergMass_product_lower (S : Finset ι) (s : ι → ℕ) (R : ι → Finset ℕ)
    (hr : ∀ i ∈ S, 0 < (R i).card ∧ (R i).card < s i) (Z : ℝ) (hZ : 1 < Z)
    (hm : (∑ i ∈ S, Real.log (s i) * ((R i).card : ℝ)/(s i)) ≤ Real.log Z/2) :
    (∏ i ∈ S, (1+((R i).card : ℝ)/((s i : ℝ)-(R i).card)))/2 ≤
      selbergMass s R (productSieveFamily S s Z) := by
  classical
  let h : ι → ℝ := fun i => ((R i).card : ℝ)/((s i : ℝ)-(R i).card)
  have hh (i : ι) (hi : i ∈ S) : 0 ≤ h i := by
    apply div_nonneg (Nat.cast_nonneg _)
    exact sub_nonneg.mpr (by exact_mod_cast (hr i hi).2.le)
  have hc (i : ι) (hi : i ∈ S) : 0 ≤ Real.log (s i) := Real.log_natCast_nonneg _
  have hs0 (i : ι) (hi : i ∈ S) : (0 : ℝ) < s i := by
    exact_mod_cast (lt_trans (hr i hi).1 (hr i hi).2)
  have hlocal (i : ι) (hi : i ∈ S) :
      Real.log (s i)*h i/(1+h i) = Real.log (s i)*((R i).card : ℝ)/(s i) := by
    have hp : (s i : ℝ)-(R i).card ≠ 0 := (sub_pos.mpr (by exact_mod_cast (hr i hi).2)).ne'
    dsimp only [h]
    field_simp
    ring
  have hmoment : (∑ i ∈ S, Real.log (s i)*h i/(1+h i)) ≤ Real.log Z/2 := by
    rwa [sum_congr rfl hlocal]
  have ht := truncated_subset_mass_lower S h (fun i => Real.log (s i)) hh hc
    (Real.log Z) (Real.log_pos hZ) hmoment
  have he : selbergMass s R (productSieveFamily S s Z) =
      ∑ T ∈ S.powerset, if (∑ i ∈ T, Real.log (s i)) ≤ Real.log Z then ∏ i ∈ T, h i else 0 := by
    unfold selbergMass productSieveFamily
    rw [sum_filter]
    apply sum_congr rfl
    intro T hT
    have hTS := mem_powerset.mp hT
    have hprod : (0 : ℝ) < ∏ i ∈ T, (s i : ℝ) := prod_pos fun i hi => hs0 i (hTS hi)
    have hlog : Real.log (∏ i ∈ T, (s i : ℝ)) = ∑ i ∈ T, Real.log (s i) :=
      Real.log_prod fun i hi => (hs0 i (hTS hi)).ne'
    have hi : (∏ i ∈ T, (s i : ℝ)) ≤ Z ↔ (∑ i ∈ T, Real.log (s i)) ≤ Real.log Z := by
      rw [← hlog]
      exact (Real.log_le_log_iff hprod (by linarith)).symm
    simp only [hi]
    rfl
  rwa [he]

lemma selbergMass_reciprocal_le_exp (S : Finset ι) (s : ι → ℕ) (R : ι → Finset ℕ)
    (hr : ∀ i ∈ S, 0 < (R i).card ∧ (R i).card < s i) (Z : ℝ) (hZ : 1 < Z)
    (hm : (∑ i ∈ S, Real.log (s i)*((R i).card : ℝ)/(s i)) ≤ Real.log Z/2) :
    1/selbergMass s R (productSieveFamily S s Z) ≤
      2*Real.exp (-(∑ i ∈ S, ((R i).card : ℝ)/(s i))) := by
  let G := selbergMass s R (productSieveFamily S s Z)
  let A := ∏ i ∈ S, (1-((R i).card : ℝ)/(s i))
  let W := ∏ i ∈ S, (1+((R i).card : ℝ)/((s i : ℝ)-(R i).card))
  have hG : 0 < G := selbergMass_pos s R _ (productSieveFamily_empty S s Z hZ.le)
    (fun T hT i hi => hr i (((mem_productSieveFamily S s Z T).mp hT).1 hi))
  have hs0 (i : ι) (hi : i ∈ S) : (0 : ℝ) < s i := by
    exact_mod_cast (lt_trans (hr i hi).1 (hr i hi).2)
  have ha (i : ι) (hi : i ∈ S) : 0 ≤ 1-((R i).card : ℝ)/(s i) := by
    apply sub_nonneg.mpr
    exact (div_le_one (hs0 i hi)).mpr (by exact_mod_cast (hr i hi).2.le)
  have hA : 0 ≤ A := prod_nonneg ha
  have hWA : W*A=1 := by
    dsimp only [W,A]
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro i hi
    have hp : (s i : ℝ)-(R i).card ≠ 0 := (sub_pos.mpr (by exact_mod_cast (hr i hi).2)).ne'
    have hq := (hs0 i hi).ne'
    field_simp
    ring
  have hlower : W/2 ≤ G := selbergMass_product_lower S s R hr Z hZ hm
  have hmul := mul_le_mul_of_nonneg_right hlower hA
  have hrecip : 1/G ≤ 2*A := by
    apply (div_le_iff₀ hG).mpr
    nlinarith
  have hprod : A ≤ Real.exp (-(∑ i ∈ S, ((R i).card : ℝ)/(s i))) := by
    rw [← sum_neg_distrib,Real.exp_sum]
    apply prod_le_prod ha
    intro i hi
    simpa only [neg_div,neg_add_eq_sub] using Real.add_one_le_exp (-((R i).card : ℝ)/(s i))
  exact hrecip.trans (mul_le_mul_of_nonneg_left hprod (by norm_num))

/-- A finite upper-bound sieve whose main term is twice the exponential of
minus the local mass and whose error is polynomial in the product cutoff. -/
theorem residue_selberg_upper_bound (S : Finset ι) (s : ι → ℕ) (R : ι → Finset ℕ)
    (hs : ∀ i ∈ S, s i ≠ 0)
    (hc : (↑S : Set ι).Pairwise (Function.onFun Nat.Coprime s))
    (hR : ∀ i ∈ S, R i ⊆ range (s i))
    (hr : ∀ i ∈ S, 0 < (R i).card ∧ (R i).card < s i)
    (Z : ℝ) (hZ : 1 < Z)
    (hm : (∑ i ∈ S, Real.log (s i)*((R i).card : ℝ)/(s i)) ≤ Real.log Z/2) (N : ℕ) :
    (avoidanceCount (range N) (fun i n => n%s i ∈ R i) S : ℝ) ≤
      2*N*Real.exp (-(∑ i ∈ S, ((R i).card : ℝ)/(s i))) + 2*Z^4 := by
  have hb := quadratic_residue_sieve S s R hs hc hR hr (productSieveFamily S s Z)
    (fun T hT => ((mem_productSieveFamily S s Z T).mp hT).1)
    (productSieveFamily_empty S s Z hZ.le) Z (by linarith)
    (fun T hT => ((mem_productSieveFamily S s Z T).mp hT).2) N
  have he := mul_le_mul_of_nonneg_left (selbergMass_reciprocal_le_exp S s R hr Z hZ hm)
    (Nat.cast_nonneg (α := ℝ) N)
  have hm' : N/selbergMass s R (productSieveFamily S s Z) ≤
      2*N*Real.exp (-(∑ i ∈ S, ((R i).card : ℝ)/(s i))) := by
    convert he using 1 <;> ring
  exact hb.trans (add_le_add hm' le_rfl)

#print axioms residue_selberg_upper_bound
end FiniteSieve
end Erdos371
