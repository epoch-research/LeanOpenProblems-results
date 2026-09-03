import Submission.SeparatedCollisionVariance

/-! Exact Fourier normalization of the conditional residue variance.
The Fourier energy is over the nonzero frequencies. It equals p² times
classVariance, not p times classVariance. No large-sieve bound is assumed
or established in the identity. -/
namespace Erdos970.Resampling
open Finset Complex

noncomputable def residueFourier (S : Finset ℕ) (p : ℕ) [NeZero p] (a : ZMod p) : ℂ :=
  ∑ x ∈ S, ZMod.stdAddChar ((x : ZMod p) * a)

lemma residueFourier_zero (S : Finset ℕ) (p : ℕ) [NeZero p] :
    residueFourier S p 0 = (S.card : ℂ) := by
  simp [residueFourier]

lemma stdAddChar_sum_mul (p : ℕ) [NeZero p] (b : ZMod p) :
    (∑ a : ZMod p, ZMod.stdAddChar (b*a)) = if b = 0 then (p : ℂ) else 0 := by
  split_ifs with hb
  · simp [hb]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p hb)

lemma stdAddChar_mul_conj (p : ℕ) [NeZero p] (a b : ZMod p) :
    ZMod.stdAddChar a * (starRingEnd ℂ) (ZMod.stdAddChar b) =
      ZMod.stdAddChar (a-b) := by
  rw [← AddChar.inv_apply_eq_conj, ← div_eq_mul_inv, AddChar.map_sub_eq_div]

lemma residueFourier_normSq_sum (S : Finset ℕ) (p : ℕ) [NeZero p] :
    (∑ a : ZMod p, normSq (residueFourier S p a)) =
      (p : ℝ) * (∑ a : Fin p, classHits S p a ^ 2) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj, residueFourier, map_sum, sum_mul_sum]
  rw [sum_comm]
  have hex (x : ℕ) :
      (∑ a : ZMod p, ∑ y ∈ S,
        ZMod.stdAddChar ((x : ZMod p)*a) *
          (starRingEnd ℂ) (ZMod.stdAddChar ((y : ZMod p)*a))) =
      ∑ y ∈ S, if x % p = y % p then (p : ℂ) else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro y hy
    simp_rw [stdAddChar_mul_conj, ← sub_mul, stdAddChar_sum_mul,
      sub_eq_zero, ZMod.natCast_eq_natCast_iff']
  simp_rw [hex]
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hc := congrArg Complex.ofReal (classHits_square_sum S p hp)
  push_cast at hc
  rw [hc]
  simp only [mul_sum]
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro y hy
  split_ifs <;> simp

/-- The nonzero-frequency energy; the definition also makes sense at p=0,
where its indexing type is empty. No zero modulus is used in the theorems. -/
noncomputable def residueFourierEnergy (S : Finset ℕ) (p : ℕ) : ℝ :=
  if h : p = 0 then 0 else
    letI : NeZero p := ⟨h⟩
    ∑ a : Fin p, if a.val = 0 then 0 else normSq (residueFourier S p (a.val : ZMod p))

lemma residueFourierEnergy_nonneg (S : Finset ℕ) (p : ℕ) :
    0 ≤ residueFourierEnergy S p := by
  unfold residueFourierEnergy
  split_ifs with h
  · exact le_rfl
  · apply sum_nonneg
    intro a ha
    split_ifs
    · exact le_rfl
    · exact normSq_nonneg _

/-- Exact Parseval identity, with the zero frequency removed. -/
theorem residueFourierEnergy_eq (S : Finset ℕ) (p : ℕ) (hp : 0 < p) :
    residueFourierEnergy S p = (p : ℝ)^2 * classVariance S p := by
  letI : NeZero p := ⟨hp.ne'⟩
  have heq : (∑ a : Fin p, normSq (residueFourier S p (a.val : ZMod p))) =
      ∑ a : ZMod p, normSq (residueFourier S p a) := by
    apply Fintype.sum_equiv (ZMod.finEquiv p).toEquiv
    intro a
    congr 2
    apply ZMod.val_injective
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]
    cases p with
    | zero => omega
    | succ p => rfl
  have hz : (∑ a : Fin p, if a.val = 0 then
      normSq (residueFourier S p (a.val : ZMod p)) else 0) = (S.card : ℝ)^2 := by
    have hid (a : Fin p) : (a.val = 0) ↔ a = ⟨0,hp⟩ := by
      exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    simp_rw [hid]
    simp [residueFourier_zero, normSq_apply, pow_two]
  have hadd : residueFourierEnergy S p + (S.card : ℝ)^2 =
      (p : ℝ) * ∑ a : Fin p, classHits S p a ^ 2 := by
    rw [← residueFourier_normSq_sum S p, ← heq, ← hz, residueFourierEnergy, dif_neg hp.ne',
      ← sum_add_distrib]
    apply sum_congr rfl
    intro a ha
    split_ifs <;> simp
  have hv := prime_mul_classVariance S p hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hdiv : (p : ℝ) * ((S.card : ℝ)^2 / p) = (S.card : ℝ)^2 := by
    field_simp
  nlinarith only [hv, hadd, hdiv]

/-- One selected residue uses p times its squared discrepancy, whereas
Parseval sums over all nonzero frequencies with the weight p². -/
lemma selected_centeredHits_sq_le_energy (S : Finset ℕ) (p : ℕ) (hp : 0 < p)
    (a : Fin p) :
    (p : ℝ) * centeredHits S p a ^ 2 ≤ residueFourierEnergy S p := by
  rw [residueFourierEnergy_eq S p hp]
  have hs := single_le_sum (s := (univ : Finset (Fin p)))
    (f := fun b => centeredHits S p b ^ 2) (fun b _ => sq_nonneg _) (mem_univ a)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hv : (p : ℝ)^2 * classVariance S p =
      (p : ℝ) * ∑ b : Fin p, centeredHits S p b ^ 2 := by
    unfold classVariance residueMean
    field_simp
  rw [hv]
  exact mul_le_mul_of_nonneg_left hs hpR.le

/-- Weighted Cauchy--Schwarz for arbitrarily selected residues. This is an
exact deterministic inequality, not a phase-average statement. -/
theorem selected_centeredHits_sum_sq_le_energy
    (S P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (r : GapAverages.Phase P) :
    (∑ p : P, centeredHits S p.val (r p)) ^ 2 ≤
      (∑ p : P, 1 / (p.val : ℝ)) * ∑ p : P, residueFourierEnergy S p.val := by
  have hc := sum_sq_le_sum_mul_sum_of_sq_eq_mul (univ : Finset P)
    (r := fun p => centeredHits S p.val (r p))
    (f := fun p => 1 / (p.val : ℝ))
    (g := fun p => (p.val : ℝ) * centeredHits S p.val (r p)^2)
    (fun p _ => by positivity) (fun p _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (fun p _ => by
      have hp0 : (p.val : ℝ) ≠ 0 := by exact_mod_cast (hP p.val p.property).ne'
      field_simp)
  exact hc.trans (mul_le_mul_of_nonneg_left
    (sum_le_sum (fun p _ => selected_centeredHits_sq_le_energy S p.val
      (hP p.val p.property) (r p))) (sum_nonneg (fun p _ => by positivity)))

/-- A covering phase must pay this much Fourier energy. The reciprocal-mass
hypothesis is explicit; the statement does not assert a large-sieve bound. -/
theorem cover_energy_lower (S P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (r : GapAverages.Phase P)
    (hcover : ∀ x ∈ S, ∃ p : P, x % p.val = (r p).val)
    (hμ : (∑ p : P, 1 / (p.val : ℝ)) ≤ 1) :
    ((S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ))) ^ 2 ≤
      (∑ p : P, 1 / (p.val : ℝ)) * ∑ p : P, residueFourierEnergy S p.val := by
  have hc := card_le_total_hits_of_cover S P r hcover
  have hid : (∑ p : P, centeredHits S p.val (r p)) =
      (∑ p : P, classHits S p.val (r p)) -
        (S.card : ℝ) * ∑ p : P, 1 / (p.val : ℝ) := by
    simp only [centeredHits, sum_sub_distrib, mul_sum, mul_one_div]
  have hlo : (S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ)) ≤
      ∑ p : P, centeredHits S p.val (r p) := by rw [hid]; linarith
  have hzero : 0 ≤ (S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hμ)
  exact (pow_le_pow_left₀ hzero hlo 2).trans
    (selected_centeredHits_sum_sq_le_energy S P hP r)

/-- A lower bound on all moduli converts an aggregate Fourier bound into an
aggregate conditional-variance bound with divisor y², not y. -/
theorem variance_sum_le_energy_div_sq (S P : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) (y : ℝ) (hy : 0 < y)
    (hmin : ∀ p ∈ P, y ≤ p) :
    (∑ p ∈ P, classVariance S p) ≤
      (∑ p ∈ P, residueFourierEnergy S p) / y^2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hy)).mpr
  calc
    _ = ∑ p ∈ P, y^2 * classVariance S p := by rw [mul_comm, mul_sum]
    _ ≤ ∑ p ∈ P, (p : ℝ)^2 * classVariance S p := by
      apply sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy.le (hmin p hp) 2)
        (classVariance_nonneg S p)
    _ = _ := sum_congr rfl (fun p hp => (residueFourierEnergy_eq S p (hP p hp)).symm)

/-- The existing conditional Bennett inequality written with its precise
Fourier-energy weights. No averaged variance replaces a conditional one. -/
theorem populationCoveredFraction_fourier_bennett (S P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (t : ℝ) (ht : 0 ≤ t) (B : P → ℝ)
    (hupper : ∀ (p : P) (a : Fin p.val), centeredHits S p.val a ≤ B p) :
    populationCoveredFraction S P ≤ Real.exp
      (-t * (S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ)) +
        ∑ p : P, bennettFactor t (B p) * residueFourierEnergy S p.val / (p.val : ℝ)^2) := by
  have h := populationCoveredFraction_bennett S P hP t ht B hupper
  convert h using 2
  congr 1
  apply sum_congr rfl
  intro p hp
  rw [residueFourierEnergy_eq S p.val (hP p.val p.property).pos]
  have hp0 : (p.val : ℝ) ≠ 0 := by exact_mod_cast (hP p.val p.property).ne_zero
  field_simp

#print axioms residueFourier_normSq_sum
#print axioms residueFourierEnergy_eq
#print axioms selected_centeredHits_sum_sq_le_energy
#print axioms cover_energy_lower
#print axioms variance_sum_le_energy_div_sq
#print axioms populationCoveredFraction_fourier_bennett
end Erdos970.Resampling
