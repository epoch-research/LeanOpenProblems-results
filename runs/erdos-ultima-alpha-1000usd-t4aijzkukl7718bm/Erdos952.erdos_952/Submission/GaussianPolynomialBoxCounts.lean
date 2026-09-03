import Submission.GaussianIdealUnionCounts

/-! Counts of polynomial divisibility conditions in Gaussian integer squares.
The error is explicit in the number of root classes. For a product of
translated linear factors, the root classes at a Gaussian prime are counted
without replacing collisions by distinct roots. -/
namespace Erdos952Investigation.GaussianPolynomialBoxCounts
open GaussianIdealRepresentatives GaussianIdealBoxCounts GaussianIdealUnionCounts
open scoped BigOperators
set_option maxHeartbeats 0

noncomputable section

local instance (g : GaussianInt) :
    DecidableEq (GaussianInt ⧸ multiples g) := Classical.decEq _

noncomputable def rootClasses (g : GaussianInt) (hg : g ≠ 0)
    (P : Polynomial GaussianInt) : Finset (GaussianInt ⧸ multiples g) := by
  classical
  letI : Finite (GaussianInt ⧸ multiples g) := quotient_finite g hg
  letI := Fintype.ofFinite (GaussianInt ⧸ multiples g)
  exact Finset.univ.filter (fun q => g ∣ P.eval (representative g hg q))

lemma mem_rootClasses (g : GaussianInt) (hg : g ≠ 0)
    (P : Polynomial GaussianInt) (t : GaussianInt) :
    Submodule.Quotient.mk t ∈ rootClasses g hg P ↔ g ∣ P.eval t := by
  classical
  have hd : g ∣ representative g hg (Submodule.Quotient.mk t)-t :=
    (quotient_eq_iff_dvd g _ _).mp (representative_class g hg _)
  have he := hd.trans (Polynomial.sub_dvd_eval_sub
    (representative g hg (Submodule.Quotient.mk t)) t P)
  simpa [rootClasses] using dvd_iff_dvd_of_dvd_sub he

noncomputable def rootCount (g : GaussianInt) (hg : g ≠ 0)
    (P : Polynomial GaussianInt) : ℕ := (rootClasses g hg P).card

noncomputable def evalCount (g : GaussianInt) (P : Polynomial GaussianInt)
    (a : GaussianInt) (R : ℕ) : ℕ :=
  Nat.card {t : GaussianInt // InBox a R t ∧ g ∣ P.eval t}

lemma evalCount_eq_residueCount (g : GaussianInt) (hg : g ≠ 0)
    (P : Polynomial GaussianInt) (a : GaussianInt) (R : ℕ) :
    evalCount g P a R = residueCount g (rootClasses g hg P) a R := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro t
  rw [mem_rootClasses]

/-- Polynomial divisibility has density rho(g)/norm(g), with an error that
retains rho(g). This statement is uniform in the box anchor. -/
theorem eval_count_sqrt_error (g : GaussianInt) (hg : g ≠ 0)
    (P : Polynomial GaussianInt) (a : GaussianInt) (R : ℕ) :
    |(evalCount g P a R : ℝ)-(rootCount g hg P : ℝ)*(R : ℝ)^2/(g.norm.natAbs : ℝ)| ≤
      (rootCount g hg P : ℝ)*(4*(R : ℝ)/Real.sqrt (g.norm.natAbs : ℝ)+4) := by
  rw [evalCount_eq_residueCount]
  exact residue_count_sqrt_error g hg (rootClasses g hg P) a R

lemma evalCount_of_isUnit (g : GaussianInt) (P : Polynomial GaussianInt)
    (hu : IsUnit g) (a : GaussianInt) (R : ℕ) : evalCount g P a R = R^2 := by
  have he : {t : GaussianInt // InBox a R t ∧ g ∣ P.eval t} ≃ Box a R :=
    Equiv.subtypeEquivRight (fun t => and_iff_left (hu.dvd : g ∣ P.eval t))
  exact (Nat.card_congr he).trans (box_card a R)

lemma rootCount_of_isUnit (g : GaussianInt) (hg : g ≠ 0)
    (P : Polynomial GaussianInt) (hu : IsUnit g) : rootCount g hg P = 1 := by
  classical
  letI : Finite (GaussianInt ⧸ multiples g) := quotient_finite g hg
  letI := Fintype.ofFinite (GaussianInt ⧸ multiples g)
  have he : rootClasses g hg P = Finset.univ := by
    ext q
    simp [rootClasses,hu.dvd]
  rw [rootCount,he,Finset.card_univ,← Nat.card_eq_fintype_card,quotient_card g hg]
  have hn : g.norm = 1 :=
    (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) g).mpr hu
  simp [hn]

noncomputable def patternPolynomial {ι : Type*} [Fintype ι]
    (z : ι → GaussianInt) : Polynomial GaussianInt :=
  ∏ i, (Polynomial.X+Polynomial.C (z i))

lemma patternPolynomial_eval {ι : Type*} [Fintype ι] (z : ι → GaussianInt)
    (t : GaussianInt) : (patternPolynomial z).eval t = ∏ i, (t+z i) := by
  simp [patternPolynomial,Polynomial.eval_prod]

/-- At a prime ideal, the roots are exactly the distinct negatives of the
pattern vertices. Distinct vertices may collide in this quotient. -/
theorem rootClasses_prime_pattern {ι : Type*} [Fintype ι]
    (z : ι → GaussianInt) (g : GaussianInt) (hg : Prime g) :
    rootClasses g hg.ne_zero (patternPolynomial z) =
      Finset.univ.image (fun i => (Submodule.Quotient.mk (-z i) : GaussianInt ⧸ multiples g)) := by
  classical
  ext q
  induction q using Quotient.inductionOn' with
  | h t =>
    change (Submodule.Quotient.mk t : GaussianInt ⧸ multiples g) ∈ _ ↔ _
    rw [mem_rootClasses,patternPolynomial_eval,hg.dvd_finset_prod_iff]
    simp only [Finset.mem_univ,true_and,Finset.mem_image]
    apply exists_congr
    intro i
    rw [eq_comm]
    change g ∣ t+z i ↔
      (Submodule.Quotient.mk t : GaussianInt ⧸ multiples g) = Submodule.Quotient.mk (-z i)
    rw [quotient_eq_iff_dvd,sub_neg_eq_add]

/-- No collision-free assumption is needed for this upper bound. -/
theorem rootCount_prime_pattern_le {ι : Type*} [Fintype ι]
    (z : ι → GaussianInt) (g : GaussianInt) (hg : Prime g) :
    rootCount g hg.ne_zero (patternPolynomial z) ≤ Fintype.card ι := by
  classical
  rw [rootCount,rootClasses_prime_pattern z g hg]
  simpa using (Finset.card_image_le (s := (Finset.univ : Finset ι))
    (f := fun i => (Submodule.Quotient.mk (-z i) : GaussianInt ⧸ multiples g)))

lemma quotient_injective_of_norm_bound {ι : Type*} (z : ι → GaussianInt)
    (hz : Function.Injective z) (g : GaussianInt) (hg : g ≠ 0)
    (hb : ∀ i j, (z i-z j).norm < g.norm) :
    Function.Injective (fun i => (Submodule.Quotient.mk (z i) : GaussianInt ⧸ multiples g)) := by
  intro i j he
  obtain ⟨w,hw⟩ := (quotient_eq_iff_dvd g _ _).mp he
  have hgn := GaussianInt.norm_pos.mpr hg
  have hn := hb i j
  rw [hw,Zsqrtd.norm_mul] at hn
  have hw0 : w.norm = 0 := by
    have hwp := GaussianInt.norm_nonneg w
    by_contra hne
    have hwp1 : 1 ≤ w.norm := by omega
    nlinarith
  have hwz : w = 0 := GaussianInt.norm_eq_zero.mp hw0
  rw [hwz,mul_zero] at hw
  exact hz (sub_eq_zero.mp hw)

/-- In the collision-free norm range, the number of roots is exactly the
number of vertices. -/
theorem rootCount_prime_pattern_of_norm_bound {ι : Type*} [Fintype ι]
    (z : ι → GaussianInt) (hz : Function.Injective z) (g : GaussianInt) (hg : Prime g)
    (hb : ∀ i j, (z i-z j).norm < g.norm) :
    rootCount g hg.ne_zero (patternPolynomial z) = Fintype.card ι := by
  classical
  have hi := quotient_injective_of_norm_bound (fun i => -z i)
    (neg_injective.comp hz) g hg.ne_zero (fun i j => by
      simpa only [neg_sub_neg] using hb j i)
  rw [rootCount,rootClasses_prime_pattern z g hg,Finset.card_image_of_injective _ hi,Finset.card_univ]

#print axioms eval_count_sqrt_error
#print axioms evalCount_of_isUnit
#print axioms rootCount_of_isUnit
#print axioms rootCount_prime_pattern_le
#print axioms rootCount_prime_pattern_of_norm_bound
end
end Erdos952Investigation.GaussianPolynomialBoxCounts
