import Submission.FiniteSampleSmoothing
import Submission.GaussianSmoothedCosetCounts

/-! Higher-order smoothing of Gaussian ideal cosets using actual finite
tuples of box points. If m is the ideal index and k=n+1 is the number of
factors, the normalized error is at most (R^2/m)*(8*sqrt(m)/R)^k.
This is a lattice estimate, not an estimate of long prime-path counts. -/
namespace Erdos952Investigation.GaussianIteratedSmoothing
open FiniteConvolutionSmoothing FiniteSampleSmoothing
open GaussianIdealRepresentatives GaussianIdealBoxCounts GaussianSmoothedCosetCounts
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section
local instance (a : GaussianInt) (R : ℕ) : Fintype (Box a R) := Fintype.ofFinite _

def boxDensity (g : GaussianInt) (a : GaussianInt) (R : ℕ)
    (c : GaussianInt ⧸ multiples g) : ℝ := (cosetCount g c a R : ℝ)/(R : ℝ)^2

lemma boxDensity_eq_density (g a : GaussianInt) (R : ℕ) (c : GaussianInt ⧸ multiples g) :
    boxDensity g a R c = density (fun z : Box a R => (Submodule.Quotient.mk z.val : GaussianInt ⧸ multiples g)) c := by
  have he := Equiv.subtypeSubtypeEquivSubtypeInter (InBox a R)
    (fun z => (Submodule.Quotient.mk z : GaussianInt ⧸ multiples g) = c)
  have hc : Nat.card {z : Box a R // (Submodule.Quotient.mk z.val : GaussianInt ⧸ multiples g) = c} =
      cosetCount g c a R := Nat.card_congr he
  have hb : Fintype.card (Box a R) = R^2 := by
    rw [← Nat.card_eq_fintype_card]
    exact box_card a R
  simp only [boxDensity,density,hc,hb,Nat.cast_pow]

lemma box_nonempty (a : GaussianInt) (R : ℕ) (hR : 0 < R) : Nonempty (Box a R) := by
  refine ⟨⟨a,?_⟩⟩
  dsimp [InBox]
  omega

/-- A single normalized box is within (8 sqrt(m)/R)/m of the uniform
measure whenever m<=R^2. -/
lemma box_density_error (g : GaussianInt) (hg : g ≠ 0) (a : GaussianInt) (R : ℕ)
    (hR : 0 < R) (hmR : g.norm.natAbs ≤ R^2) (c : GaussianInt ⧸ multiples g) :
    |boxDensity g a R c-1/(g.norm.natAbs : ℝ)| ≤
      (8*Real.sqrt (g.norm.natAbs : ℝ)/(R : ℝ))/(g.norm.natAbs : ℝ) := by
  let m : ℝ := g.norm.natAbs
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast Int.natAbs_pos.mpr (GaussianInt.norm_eq_zero.not.mpr hg)
  have hRp : (0 : ℝ) < R := by exact_mod_cast hR
  have hR2 : 0 < (R : ℝ)^2 := sq_pos_of_pos hRp
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hs2 : (Real.sqrt m)^2 = m := Real.sq_sqrt hm.le
  have hsR : Real.sqrt m ≤ (R : ℝ) := Real.sqrt_le_iff.mpr
    ⟨hRp.le,by dsimp [m]; exact_mod_cast hmR⟩
  have he : boxDensity g a R c-1/m =
      ((cosetCount g c a R : ℝ)-(R : ℝ)^2/m)/(R : ℝ)^2 := by
    dsimp [boxDensity]
    field_simp
  change |boxDensity g a R c-1/m| ≤ (8*Real.sqrt m/(R : ℝ))/m
  rw [he,abs_div,abs_of_pos hR2]
  calc
    _ ≤ (4*(R : ℝ)/Real.sqrt m+4)/(R : ℝ)^2 :=
      div_le_div_of_nonneg_right (coset_count_sqrt_error g hg c a R) hR2.le
    _ ≤ (8*(R : ℝ)/Real.sqrt m)/(R : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ hR2.le
      have hh : 4 ≤ 4*(R : ℝ)/Real.sqrt m := (le_div_iff₀ hs).mpr (by nlinarith)
      have he8 : 8*(R : ℝ)/Real.sqrt m = 2*(4*(R : ℝ)/Real.sqrt m) := by ring
      rw [he8]
      linarith
    _ = _ := by
      field_simp
      nlinarith [hs2]

/-- The actual Gaussian value of an (n+1)-tuple: the first entry minus all
remaining entries. -/
def tupleValue (a : GaussianInt) (R n : ℕ) : Sample (Box a R) n → GaussianInt :=
  value (fun z : Box a R => z.val) n

lemma quotient_tupleValue (g a : GaussianInt) (R n : ℕ) (s : Sample (Box a R) n) :
    (Submodule.Quotient.mk (tupleValue a R n s) : GaussianInt ⧸ multiples g) =
      value (fun z : Box a R => (Submodule.Quotient.mk z.val : GaussianInt ⧸ multiples g)) n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Submodule.Quotient.mk (tupleValue a R n s.1-s.2.val) = _
    rw [Submodule.Quotient.mk_sub,ih]
    rfl

/-- The total mass remains R^2, regardless of how many factors are used. -/
def tupleCosetWeight (g : GaussianInt) (c : GaussianInt ⧸ multiples g)
    (a : GaussianInt) (R n : ℕ) : ℝ :=
  (R : ℝ)^2*density (fun s : Sample (Box a R) n =>
    (Submodule.Quotient.mk (tupleValue a R n s) : GaussianInt ⧸ multiples g)) c

/-- Higher-order error for genuine finite tuple counts. The number of
factors n+1 and the index-to-side ratio both remain explicit. -/
theorem tuple_coset_error (g : GaussianInt) (hg : g ≠ 0)
    (c : GaussianInt ⧸ multiples g) (a : GaussianInt) (R n : ℕ)
    (hR : 0 < R) (hmR : g.norm.natAbs ≤ R^2) :
    |tupleCosetWeight g c a R n-(R : ℝ)^2/(g.norm.natAbs : ℝ)| ≤
      ((R : ℝ)^2/(g.norm.natAbs : ℝ))*(8*Real.sqrt (g.norm.natAbs : ℝ)/(R : ℝ))^(n+1) := by
  letI : Finite (GaussianInt ⧸ multiples g) := quotient_finite g hg
  letI := Fintype.ofFinite (GaussianInt ⧸ multiples g)
  letI : Nonempty (Box a R) := box_nonempty a R hR
  let f : Box a R → GaussianInt ⧸ multiples g := fun z => Submodule.Quotient.mk z.val
  have hc : Fintype.card (GaussianInt ⧸ multiples g) = g.norm.natAbs :=
    Nat.card_eq_fintype_card.symm.trans (quotient_card g hg)
  have hf (q) : |density f q-1/(Fintype.card (GaussianInt ⧸ multiples g) : ℝ)| ≤
      (8*Real.sqrt (g.norm.natAbs : ℝ)/(R : ℝ))/(Fintype.card (GaussianInt ⧸ multiples g) : ℝ) := by
    rw [hc]
    change |density (fun z : Box a R => (Submodule.Quotient.mk z.val : GaussianInt ⧸ multiples g)) q-1/(g.norm.natAbs : ℝ)| ≤ _
    rw [← boxDensity_eq_density]
    exact box_density_error g hg a R hR hmR q
  have hh := sample_error_ratio f (8*Real.sqrt (g.norm.natAbs : ℝ)/(R : ℝ))
    (by positivity) hf n c
  rw [hc] at hh
  have hv : (fun s : Sample (Box a R) n =>
      (Submodule.Quotient.mk (tupleValue a R n s) : GaussianInt ⧸ multiples g)) = value f n :=
    funext (quotient_tupleValue g a R n)
  have he : tupleCosetWeight g c a R n-(R : ℝ)^2/(g.norm.natAbs : ℝ) =
      (R : ℝ)^2*(density (value f n) c-1/(g.norm.natAbs : ℝ)) := by
    rw [tupleCosetWeight,hv]
    ring
  rw [he,abs_mul,abs_of_nonneg (sq_nonneg (R : ℝ))]
  apply (mul_le_mul_of_nonneg_left hh (sq_nonneg (R : ℝ))).trans_eq
  ring

/-- If R>=16 sqrt(m), each additional factor saves at least another factor
of two in the normalized discrepancy. This estimate alone does not control
the growing support or the prime-path sieve main term. -/
theorem tuple_coset_error_half (g : GaussianInt) (hg : g ≠ 0)
    (c : GaussianInt ⧸ multiples g) (a : GaussianInt) (R n : ℕ)
    (hR : 0 < R) (hmR : 16*Real.sqrt (g.norm.natAbs : ℝ) ≤ (R : ℝ)) :
    |tupleCosetWeight g c a R n-(R : ℝ)^2/(g.norm.natAbs : ℝ)| ≤
      ((R : ℝ)^2/(g.norm.natAbs : ℝ))*(1/2 : ℝ)^(n+1) := by
  have hRp : (0 : ℝ) < R := by exact_mod_cast hR
  have hm0 : (0 : ℝ) ≤ g.norm.natAbs := Nat.cast_nonneg _
  have hs0 := Real.sqrt_nonneg (g.norm.natAbs : ℝ)
  have hs2 := Real.sq_sqrt hm0
  have hsR : Real.sqrt (g.norm.natAbs : ℝ) ≤ (R : ℝ) := by linarith
  have hm : g.norm.natAbs ≤ R^2 := by
    have hh : (g.norm.natAbs : ℝ) ≤ (R : ℝ)^2 := by nlinarith
    exact_mod_cast hh
  apply (tuple_coset_error g hg c a R n hR hm).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  exact (div_le_iff₀ hRp).mpr (by linarith)

#print axioms box_density_error
#print axioms quotient_tupleValue
#print axioms tuple_coset_error
#print axioms tuple_coset_error_half
end
end Erdos952Investigation.GaussianIteratedSmoothing
