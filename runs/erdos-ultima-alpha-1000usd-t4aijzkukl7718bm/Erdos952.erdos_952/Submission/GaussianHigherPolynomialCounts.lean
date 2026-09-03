import Submission.GaussianHigherSmoothingUpper
import Submission.GaussianSmoothedPolynomialCounts

/-! Polynomial congruence counts for the exact higher-order kernel used in
the prime-ray lower bound. The full root-count discrepancy and a coarser
uniform modulus-level discrepancy are both retained explicitly. -/
namespace Erdos952Investigation.GaussianHigherPolynomialCounts
open GaussianIdealRepresentatives GaussianIdealBoxCounts GaussianPolynomialBoxCounts
open GaussianIteratedSmoothing FiniteSampleSmoothing GaussianHigherSmoothingLower
open GaussianHigherSmoothingUpper GaussianWeightedSieve
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0
local instance (a : GaussianInt) (R : ℕ) : Fintype (Box a R) := Fintype.ofFinite _

lemma kernelCount_sum {Ω : Type*} [Fintype Ω] (f : Ω → GaussianInt)
    (p : GaussianInt → Prop) (a : GaussianInt) (R : ℕ) :
    kernelCount f p a R =
      (∑ s : KernelSample Ω a R, if p (kernelValue f a R s) then 1 else 0)/
        ((R : ℝ)^2*(Fintype.card Ω : ℝ)^2) := by
  rw [kernelCount,Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.sum_boole]

lemma kernelCount_congr {Ω : Type*} [Fintype Ω] (f : Ω → GaussianInt)
    (p q : GaussianInt → Prop) (h : ∀ z, p z ↔ q z) (a : GaussianInt) (R : ℕ) :
    kernelCount f p a R = kernelCount f q a R := by
  have he : p = q := funext (fun z => propext (h z))
  rw [he]

lemma kernelCount_mono {Ω : Type*} [Fintype Ω] (f : Ω → GaussianInt)
    (p q : GaussianInt → Prop) (h : ∀ z, p z → q z) (a : GaussianInt) (R : ℕ) :
    kernelCount f p a R ≤ kernelCount f q a R := by
  simp only [kernelCount_sum]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro s hs
  by_cases hp : p (kernelValue f a R s)
  · simp [hp,h _ hp]
  · simp only [if_neg hp]
    split_ifs <;> norm_num

lemma kernelCount_le_add {Ω : Type*} [Fintype Ω] (f : Ω → GaussianInt)
    (p q r : GaussianInt → Prop) (h : ∀ z, p z → q z ∨ r z) (a : GaussianInt) (R : ℕ) :
    kernelCount f p a R ≤ kernelCount f q a R+kernelCount f r a R := by
  simp only [kernelCount_sum,← add_div,← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro s hs
  by_cases hp : p (kernelValue f a R s)
  · rcases h _ hp with hq | hr
    · simp only [if_pos hp,if_pos hq]
      split_ifs <;> norm_num
    · simp only [if_pos hp,if_pos hr]
      split_ifs <;> norm_num
  · rw [if_neg hp]
    split_ifs <;> norm_num

/-- The extra smoothing does not increase the mass of any finite exceptional set. -/
lemma kernelCount_finset_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → GaussianInt)
    (E : Finset GaussianInt) (a : GaussianInt) (R : ℕ) (hR : 0 < R) :
    kernelCount f (fun z => z ∈ E) a R ≤ E.card := by
  let F : {s : KernelSample Ω a R // kernelValue f a R s ∈ E} →
      E × (Box 0 R × (Ω × Ω)) :=
    fun s => (⟨kernelValue f a R s.val,s.property⟩,(s.val.1.2,s.val.2))
  have hF : Function.Injective F := by
    intro s t he
    have hz := congrArg (fun v : E × (Box 0 R × (Ω × Ω)) => v.1.val) he
    have hb := congrArg (fun v : E × (Box 0 R × (Ω × Ω)) => v.2.1) he
    have ho := congrArg (fun v : E × (Box 0 R × (Ω × Ω)) => v.2.2) he
    change s.val.1.2 = t.val.1.2 at hb
    change s.val.2 = t.val.2 at ho
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        change kernelValue f a R s.val = kernelValue f a R t.val at hz
        dsimp [kernelValue] at hz
        rw [hb,ho] at hz
        linear_combination hz
      · exact hb
    · exact ho
  have hh := Nat.card_le_card_of_injective F hF
  have hE : Nat.card E = E.card := by simp
  rw [Nat.card_prod,Nat.card_prod,Nat.card_prod,hE,box_card,Nat.card_eq_fintype_card] at hh
  have hcast : (Nat.card {s : KernelSample Ω a R // kernelValue f a R s ∈ E} : ℝ) ≤
      (E.card : ℝ)*((R : ℝ)^2*(Fintype.card Ω : ℝ)^2) := by
    exact_mod_cast (by simpa only [pow_two,Nat.card_eq_fintype_card] using hh)
  have hden : 0 < (R : ℝ)^2*(Fintype.card Ω : ℝ)^2 := by
    have hRp : (0 : ℝ) < R := by exact_mod_cast hR
    have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
    positivity
  exact (div_le_iff₀ hden).mpr hcast

def higherCount (p : GaussianInt → Prop) (a : GaussianInt) (R n : ℕ) : ℝ :=
  kernelCount (tupleValue 0 R n) p a R

lemma higherResidueCount_eq_sum (g : GaussianInt)
    (S : Finset (GaussianInt ⧸ multiples g)) (a : GaussianInt) (R n : ℕ) :
    higherCount (fun z => Submodule.Quotient.mk z ∈ S) a R n =
      ∑ c ∈ S, higherCosetWeight g c a R n := by
  let f := tupleValue 0 R n
  let e := Equiv.sigmaSubtypeFiberEquivSubtype
    (fun s : KernelSample (Sample (Box 0 R) n) a R =>
      (Submodule.Quotient.mk (kernelValue f a R s) : GaussianInt ⧸ multiples g))
    (p := fun s => Submodule.Quotient.mk (kernelValue f a R s) ∈ S)
    (q := fun c => c ∈ S) (fun _ => Iff.rfl)
  unfold higherCount higherCosetWeight kernelCount
  rw [Nat.card_congr e.symm,Nat.card_sigma,Nat.cast_sum,Finset.sum_div]
  exact Finset.sum_coe_sort S (fun c => higherCosetWeight g c a R n)

lemma higher_residue_error (g : GaussianInt) (hg : g ≠ 0)
    (S : Finset (GaussianInt ⧸ multiples g)) (a : GaussianInt) (R n : ℕ)
    (hR : 0 < R) (hmR : g.norm.natAbs ≤ R^2) :
    |higherCount (fun z => Submodule.Quotient.mk z ∈ S) a R n-
      (S.card : ℝ)*(R : ℝ)^2/(g.norm.natAbs : ℝ)| ≤
      ((S.card : ℝ)*(R : ℝ)^2/(g.norm.natAbs : ℝ))*
        (8*Real.sqrt (g.norm.natAbs : ℝ)/(R : ℝ))^(2*(n+2)) := by
  rw [higherResidueCount_eq_sum]
  have he : (∑ c ∈ S, higherCosetWeight g c a R n)-
      (S.card : ℝ)*(R : ℝ)^2/(g.norm.natAbs : ℝ) =
      ∑ c ∈ S, (higherCosetWeight g c a R n-(R : ℝ)^2/(g.norm.natAbs : ℝ)) := by
    rw [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]
    ring
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun c _ => higher_coset_error g hg c a R n hR hmR)).trans_eq
  rw [Finset.sum_const,nsmul_eq_mul]
  ring

/-- Polynomial congruence error, with the exact root count. -/
theorem higher_eval_error (g : GaussianInt) (hg : g ≠ 0)
    (P : Polynomial GaussianInt) (a : GaussianInt) (R n : ℕ)
    (hR : 0 < R) (hmR : g.norm.natAbs ≤ R^2) :
    |higherCount (fun z => g ∣ P.eval z) a R n-
      (rho P g : ℝ)*(R : ℝ)^2/(g.norm.natAbs : ℝ)| ≤
      ((rho P g : ℝ)*(R : ℝ)^2/(g.norm.natAbs : ℝ))*
        (8*Real.sqrt (g.norm.natAbs : ℝ)/(R : ℝ))^(2*(n+2)) := by
  have he := kernelCount_congr (tupleValue 0 R n) (fun z => g ∣ P.eval z)
    (fun z => Submodule.Quotient.mk z ∈ rootClasses g hg P)
    (fun z => (mem_rootClasses g hg P z).symm) a R
  change higherCount (fun z => g ∣ P.eval z) a R n = _ at he
  rw [he,rho_of_ne_zero P g hg]
  exact higher_residue_error g hg (rootClasses g hg P) a R n hR hmR

lemma rho_le_norm (g : GaussianInt) (hg : g ≠ 0) (P : Polynomial GaussianInt) :
    rho P g ≤ g.norm.natAbs := by
  letI : Finite (GaussianInt ⧸ multiples g) := quotient_finite g hg
  letI := Fintype.ofFinite (GaussianInt ⧸ multiples g)
  rw [rho_of_ne_zero P g hg,rootCount,← quotient_card g hg,Nat.card_eq_fintype_card]
  exact Finset.card_le_univ _

/-- Uniform level bound: if norm(g)<=A^2 and A<=R, the polynomial degree
and root count can be eliminated from this discrepancy bound. -/
theorem higher_eval_error_uniform (g : GaussianInt) (hg : g ≠ 0)
    (P : Polynomial GaussianInt) (a : GaussianInt) (R n A : ℕ)
    (hR : 0 < R) (hAR : A ≤ R) (hmA : g.norm.natAbs ≤ A^2) :
    |higherCount (fun z => g ∣ P.eval z) a R n-
      (rho P g : ℝ)*(R : ℝ)^2/(g.norm.natAbs : ℝ)| ≤
      (R : ℝ)^2*(8*(A : ℝ)/(R : ℝ))^(2*(n+2)) := by
  have hmR : g.norm.natAbs ≤ R^2 := hmA.trans (Nat.pow_le_pow_left hAR 2)
  have hm : (0 : ℝ) < g.norm.natAbs := by
    exact_mod_cast Int.natAbs_pos.mpr (GaussianInt.norm_eq_zero.not.mpr hg)
  have hRp : (0 : ℝ) < R := by exact_mod_cast hR
  have hρ : (rho P g : ℝ) ≤ g.norm.natAbs := by exact_mod_cast rho_le_norm g hg P
  have hmass : (rho P g : ℝ)*(R : ℝ)^2/(g.norm.natAbs : ℝ) ≤ (R : ℝ)^2 := by
    apply (div_le_iff₀ hm).mpr
    nlinarith [sq_nonneg (R : ℝ)]
  have hsqrt : Real.sqrt (g.norm.natAbs : ℝ) ≤ (A : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg _,by exact_mod_cast hmA⟩
  have hκ : 8*Real.sqrt (g.norm.natAbs : ℝ)/(R : ℝ) ≤ 8*(A : ℝ)/(R : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hRp.le
  exact (higher_eval_error g hg P a R n hR hmR).trans
    (mul_le_mul hmass (pow_le_pow_left₀ (by positivity) hκ _) (by positivity) (by positivity))

#print axioms kernelCount_finset_le
#print axioms higher_eval_error
#print axioms higher_eval_error_uniform
end
end Erdos952Investigation.GaussianHigherPolynomialCounts
