import Submission.GaussianIdealUnionCounts

/-! Averaging over differences of two boxes cancels the first-order ideal
boundary error. These are weighted congruence estimates, not long-prime-path
estimates. The normalization is R^2, so the total weight is R^2. -/
namespace Erdos952Investigation.GaussianSmoothedCosetCounts
open GaussianIdealRepresentatives GaussianIdealBoxCounts GaussianIdealUnionCounts
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section

abbrev PairCosetPoints (g : GaussianInt) (c : GaussianInt ⧸ multiples g)
    (a b : GaussianInt) (R : ℕ) :=
  {uv : Box a R × Box b R // Submodule.Quotient.mk (uv.1.val-uv.2.val) = c}

def pairCount (g : GaussianInt) (c : GaussianInt ⧸ multiples g)
    (a b : GaussianInt) (R : ℕ) : ℕ := Nat.card (PairCosetPoints g c a b R)

def pairEquiv (g : GaussianInt) (c : GaussianInt ⧸ multiples g)
    (a b : GaussianInt) (R : ℕ) :
    PairCosetPoints g c a b R ≃ Σ q : GaussianInt ⧸ multiples g,
      CosetPoints g (q+c) a R × CosetPoints g q b R where
  toFun uv := ⟨Submodule.Quotient.mk uv.val.2.val,
    ⟨uv.val.1.val,uv.val.1.property,by
      have h := uv.property
      rw [Submodule.Quotient.mk_sub] at h
      exact sub_eq_iff_eq_add'.mp h⟩,
    ⟨uv.val.2.val,uv.val.2.property,rfl⟩⟩
  invFun uv := ⟨(⟨uv.2.1.val,uv.2.1.property.1⟩,⟨uv.2.2.val,uv.2.2.property.1⟩),by
    change Submodule.Quotient.mk (uv.2.1.val-uv.2.2.val) = c
    rw [Submodule.Quotient.mk_sub,uv.2.1.property.2,uv.2.2.property.2]
    abel⟩
  left_inv uv := by rfl
  right_inv uv := by
    rcases uv with ⟨q,⟨u,hu,huc⟩,⟨v,hv,hvc⟩⟩
    subst q
    rfl

lemma pairCount_eq_sum (g : GaussianInt) (hg : g ≠ 0)
    (c : GaussianInt ⧸ multiples g) (a b : GaussianInt) (R : ℕ) :
    letI : Finite (GaussianInt ⧸ multiples g) := quotient_finite g hg
    letI := Fintype.ofFinite (GaussianInt ⧸ multiples g)
    pairCount g c a b R =
      ∑ q : GaussianInt ⧸ multiples g, cosetCount g (q+c) a R*cosetCount g q b R := by
  letI : Finite (GaussianInt ⧸ multiples g) := quotient_finite g hg
  letI := Fintype.ofFinite (GaussianInt ⧸ multiples g)
  rw [pairCount,Nat.card_congr (pairEquiv g c a b R),Nat.card_sigma]
  simp only [Nat.card_prod,cosetCount]

lemma sum_cosetCount (g : GaussianInt) (hg : g ≠ 0) (a : GaussianInt) (R : ℕ) :
    letI : Finite (GaussianInt ⧸ multiples g) := quotient_finite g hg
    letI := Fintype.ofFinite (GaussianInt ⧸ multiples g)
    (∑ q : GaussianInt ⧸ multiples g, cosetCount g q a R) = R^2 := by
  letI : Finite (GaussianInt ⧸ multiples g) := quotient_finite g hg
  letI := Fintype.ofFinite (GaussianInt ⧸ multiples g)
  rw [← residueCount_eq_sum]
  have he : ResiduePoints g Finset.univ a R ≃ Box a R :=
    Equiv.subtypeEquivRight (fun z => by simp)
  exact (Nat.card_congr he).trans (box_card a R)

/-- The cancellation responsible for the improved error is exact. -/
lemma centered_product_sum {ι : Type*} [Fintype ι] (A B : ι → ℝ) (μ : ℝ)
    (hA : ∑ i, A i = (Fintype.card ι : ℝ)*μ)
    (hB : ∑ i, B i = (Fintype.card ι : ℝ)*μ) :
    (∑ i, A i*B i)-(Fintype.card ι : ℝ)*μ^2 = ∑ i, (A i-μ)*(B i-μ) := by
  have he (i) : (A i-μ)*(B i-μ) = A i*B i-μ*A i-μ*B i+μ^2 := by ring
  simp_rw [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hA,hB]
  ring

lemma centered_product_error {ι : Type*} [Fintype ι] (A B : ι → ℝ) (μ δ : ℝ)
    (hδ : 0 ≤ δ) (hA : ∑ i, A i = (Fintype.card ι : ℝ)*μ)
    (hB : ∑ i, B i = (Fintype.card ι : ℝ)*μ)
    (hAe : ∀ i, |A i-μ| ≤ δ) (hBe : ∀ i, |B i-μ| ≤ δ) :
    |(∑ i, A i*B i)-(Fintype.card ι : ℝ)*μ^2| ≤ (Fintype.card ι : ℝ)*δ^2 := by
  rw [centered_product_sum A B μ hA hB]
  calc
    _ ≤ ∑ i, |(A i-μ)*(B i-μ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, δ^2 := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul,pow_two]
      exact mul_le_mul (hAe i) (hBe i) (abs_nonneg _) hδ)
    _ = _ := by simp

/-- The unnormalized pair count has a quadratic discrepancy, rather than
an uncancelled first-order boundary term. -/
theorem pair_count_error (g : GaussianInt) (hg : g ≠ 0)
    (c : GaussianInt ⧸ multiples g) (a b : GaussianInt) (R : ℕ) :
    |(pairCount g c a b R : ℝ)-(R : ℝ)^4/(g.norm.natAbs : ℝ)| ≤
      (g.norm.natAbs : ℝ)*(4*(R : ℝ)/Real.sqrt (g.norm.natAbs : ℝ)+4)^2 := by
  letI : Finite (GaussianInt ⧸ multiples g) := quotient_finite g hg
  letI := Fintype.ofFinite (GaussianInt ⧸ multiples g)
  let m : ℝ := g.norm.natAbs
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast Int.natAbs_pos.mpr (GaussianInt.norm_eq_zero.not.mpr hg)
  have hc : (Fintype.card (GaussianInt ⧸ multiples g) : ℝ) = m := by
    dsimp [m]
    exact_mod_cast (Nat.card_eq_fintype_card.symm.trans (quotient_card g hg))
  let μ : ℝ := (R : ℝ)^2/m
  have hB : (∑ q : GaussianInt ⧸ multiples g, (cosetCount g q b R : ℝ)) =
      (Fintype.card (GaussianInt ⧸ multiples g) : ℝ)*μ := by
    rw [hc]
    have hh : (∑ q : GaussianInt ⧸ multiples g, (cosetCount g q b R : ℝ)) = (R : ℝ)^2 := by
      exact_mod_cast sum_cosetCount g hg b R
    rw [hh]
    dsimp [μ]
    field_simp
  have hA : (∑ q : GaussianInt ⧸ multiples g, (cosetCount g (q+c) a R : ℝ)) =
      (Fintype.card (GaussianInt ⧸ multiples g) : ℝ)*μ := by
    have he := Equiv.sum_comp (Equiv.addRight c) (fun q => (cosetCount g q a R : ℝ))
    change (∑ q, (cosetCount g (q+c) a R : ℝ)) = ∑ q, (cosetCount g q a R : ℝ) at he
    rw [he,hc]
    have hh : (∑ q : GaussianInt ⧸ multiples g, (cosetCount g q a R : ℝ)) = (R : ℝ)^2 := by
      exact_mod_cast sum_cosetCount g hg a R
    rw [hh]
    dsimp [μ]
    field_simp
  have hh := centered_product_error
    (fun q => (cosetCount g (q+c) a R : ℝ)) (fun q => (cosetCount g q b R : ℝ))
    μ (4*(R : ℝ)/Real.sqrt m+4) (by positivity) hA hB
    (fun q => coset_count_sqrt_error g hg (q+c) a R)
    (fun q => coset_count_sqrt_error g hg q b R)
  rw [hc] at hh
  have he : m*μ^2 = (R : ℝ)^4/m := by dsimp [μ]; field_simp
  rw [he] at hh
  rw [pairCount_eq_sum g hg,Nat.cast_sum]
  simpa only [Nat.cast_mul] using hh

/-- Normalized pair count, i.e. counting with the triangular weight arising
from differences of two R-by-R boxes. The total weight is R^2, not R^4. -/
def smoothedCosetCount (g : GaussianInt) (c : GaussianInt ⧸ multiples g)
    (a b : GaussianInt) (R : ℕ) : ℝ := (pairCount g c a b R : ℝ)/(R : ℝ)^2

/-- If the ideal index is at most the box area, the smoothed error is bounded
by 64, independently of the box side length and both anchors. -/
theorem smoothed_coset_error (g : GaussianInt) (hg : g ≠ 0)
    (c : GaussianInt ⧸ multiples g) (a b : GaussianInt) (R : ℕ)
    (hR : 0 < R) (hmR : g.norm.natAbs ≤ R^2) :
    |smoothedCosetCount g c a b R-(R : ℝ)^2/(g.norm.natAbs : ℝ)| ≤ 64 := by
  let m : ℝ := g.norm.natAbs
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast Int.natAbs_pos.mpr (GaussianInt.norm_eq_zero.not.mpr hg)
  have hRp : (0 : ℝ) < R := by exact_mod_cast hR
  have hsq : 0 < (R : ℝ)^2 := sq_pos_of_pos hRp
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hs : (Real.sqrt m)^2 = m := Real.sq_sqrt hm.le
  have hb : Real.sqrt m ≤ (R : ℝ) := Real.sqrt_le_iff.mpr
    ⟨hRp.le,by dsimp [m]; exact_mod_cast hmR⟩
  have hbound : m*(4*(R : ℝ)/Real.sqrt m+4)^2 ≤ 64*(R : ℝ)^2 := by
    calc
      _ = (Real.sqrt m)^2*(4*(R : ℝ)/Real.sqrt m+4)^2 := by rw [hs]
      _ = (4*(R : ℝ)+4*Real.sqrt m)^2 := by
        field_simp
      _ ≤ _ := by nlinarith [mul_nonneg (hRp.le) hsm.le]
  have hh := (pair_count_error g hg c a b R).trans hbound
  have he : smoothedCosetCount g c a b R-(R : ℝ)^2/(g.norm.natAbs : ℝ) =
      ((pairCount g c a b R : ℝ)-(R : ℝ)^4/(g.norm.natAbs : ℝ))/(R : ℝ)^2 := by
    dsimp [smoothedCosetCount]
    field_simp
  rw [he,abs_div,abs_of_pos hsq]
  exact (div_le_iff₀ hsq).mpr hh

#print axioms pair_count_error
#print axioms smoothed_coset_error
end
end Erdos952Investigation.GaussianSmoothedCosetCounts
