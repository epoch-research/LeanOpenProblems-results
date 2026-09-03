import Submission.PrimeReciprocalsAP
import Submission.UpperCounting

/-! Finite residue sieves for sums of two squares. Auxiliary work on Erdős 773. -/

namespace Erdos773

open Finset Filter Topology

noncomputable def squareSumResidues (q : ℕ) [NeZero q] : Finset (ZMod q) :=
  (univ ×ˢ univ).image (fun ab : ZMod q × ZMod q => ab.1 ^ 2 + ab.2 ^ 2)

lemma mem_squareSumResidues {q : ℕ} [NeZero q] (r : ZMod q) :
    r ∈ squareSumResidues q ↔ ∃ a b : ZMod q, a ^ 2 + b ^ 2 = r := by
  simp [squareSumResidues]

lemma squareSumResidues_card_mul_le (m n : ℕ) [NeZero m] [NeZero n]
    (hc : m.Coprime n) :
    (squareSumResidues (m * n)).card ≤
      (squareSumResidues m).card * (squareSumResidues n).card := by
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (ZMod.chineseRemainder hc)
  · intro r hr
    obtain ⟨a, b, rfl⟩ := (mem_squareSumResidues r).mp hr
    rw [map_add, map_pow, map_pow]
    apply Finset.mem_product.mpr
    constructor
    · exact (mem_squareSumResidues _).mpr ⟨(ZMod.chineseRemainder hc a).1,
        (ZMod.chineseRemainder hc b).1, rfl⟩
    · exact (mem_squareSumResidues _).mpr ⟨(ZMod.chineseRemainder hc a).2,
        (ZMod.chineseRemainder hc b).2, rfl⟩
  · exact fun _ _ _ _ h => (ZMod.chineseRemainder hc).injective h

lemma inert_prime_dvd_sq_add_sq {p a b : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3)
    (h : p ∣ a ^ 2 + b ^ 2) : p ∣ a ∧ p ∣ b := by
  letI : Fact p.Prime := ⟨hp⟩
  have hz : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff (a ^ 2 + b ^ 2) p).mpr h
  have ha : (a : ZMod p) = 0 := by
    by_contra ha
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq ha (eq_neg_iff_add_eq_zero.mpr hz) hp3
  have hb : (b : ZMod p) = 0 := by
    by_contra hb
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hb (eq_neg_iff_add_eq_zero.mpr hz) hp3
  exact ⟨(ZMod.natCast_eq_zero_iff a p).mp ha, (ZMod.natCast_eq_zero_iff b p).mp hb⟩

lemma inert_prime_sq_dvd_sq_add_sq {p a b : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3)
    (h : p ∣ a ^ 2 + b ^ 2) : p ^ 2 ∣ a ^ 2 + b ^ 2 := by
  obtain ⟨ha, hb⟩ := inert_prime_dvd_sq_add_sq hp hp3 h
  exact dvd_add (pow_dvd_pow_of_dvd ha 2) (pow_dvd_pow_of_dvd hb 2)

lemma inert_prime_forbidden_residue {p j : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3)
    (hj : 0 < j) (hjp : j < p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (p * j : ZMod (p ^ 2)) ∉ squareSumResidues (p ^ 2) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro h
  obtain ⟨a, b, hab⟩ := (mem_squareSumResidues _).mp h
  have hc : ((a.val ^ 2 + b.val ^ 2 : ℕ) : ZMod (p ^ 2)) = (p * j : ℕ) := by
    simpa using hab
  let f : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom (dvd_pow_self p (by omega : 2 ≠ 0)) _
  have hc' := congrArg f hc
  simp only [map_natCast] at hc'
  have hz : ((a.val ^ 2 + b.val ^ 2 : ℕ) : ZMod p) = 0 := by
    simpa using hc'
  have hd := (ZMod.natCast_eq_zero_iff (a.val ^ 2 + b.val ^ 2) p).mp hz
  have hd2 := inert_prime_sq_dvd_sq_add_sq hp hp3 hd
  have hz2 := (ZMod.natCast_eq_zero_iff (a.val ^ 2 + b.val ^ 2) (p ^ 2)).mpr hd2
  rw [hc] at hz2
  have hdj := (ZMod.natCast_eq_zero_iff (p * j) (p ^ 2)).mp hz2
  rw [pow_two, Nat.mul_dvd_mul_iff_left hp.pos] at hdj
  exact (Nat.le_of_dvd hj hdj).not_gt hjp

lemma squareSumResidues_card_prime_sq (p : ℕ) (hp : p.Prime) (hp3 : p % 4 = 3) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (squareSumResidues (p ^ 2)).card ≤ p ^ 2 - p + 1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let B : Finset (ZMod (p ^ 2)) := (Ico 1 p).image (fun j : ℕ => (p * j : ZMod (p ^ 2)))
  have hB : B.card = p - 1 := by
    rw [Finset.card_image_iff.mpr, Nat.card_Ico]
    intro i hi j hj hij
    have hi' : p * i < p ^ 2 := by
      rw [pow_two]; exact Nat.mul_lt_mul_of_pos_left (Finset.mem_Ico.mp hi).2 hp.pos
    have hj' : p * j < p ^ 2 := by
      rw [pow_two]; exact Nat.mul_lt_mul_of_pos_left (Finset.mem_Ico.mp hj).2 hp.pos
    have hv := congrArg ZMod.val hij
    have he : p * i = p * j := by
      simpa only [← Nat.cast_mul, ZMod.val_natCast_of_lt hi', ZMod.val_natCast_of_lt hj'] using hv
    exact Nat.eq_of_mul_eq_mul_left hp.pos he
  have hd : Disjoint (squareSumResidues (p ^ 2)) B := by
    apply Finset.disjoint_left.mpr
    intro r hr hB
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
    exact inert_prime_forbidden_residue hp hp3 (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2 hr
  have hle : (squareSumResidues (p ^ 2)).card + B.card ≤ p ^ 2 := by
    rw [← Finset.card_union_of_disjoint hd]
    simpa using Finset.card_le_univ (squareSumResidues (p ^ 2) ∪ B)
  rw [hB] at hle
  have hpp : p ≤ p ^ 2 := by nlinarith [hp.two_le]
  omega

noncomputable def squareResidueDensity (q : ℕ) : ℝ :=
  if h : q = 0 then 1 else
    letI : NeZero q := ⟨h⟩
    (squareSumResidues q).card / (q : ℝ)

lemma squareResidueDensity_eq (q : ℕ) [NeZero q] :
    squareResidueDensity q = (squareSumResidues q).card / (q : ℝ) := by
  simp [squareResidueDensity, NeZero.ne q]

lemma squareResidueDensity_nonneg (q : ℕ) : 0 ≤ squareResidueDensity q := by
  unfold squareResidueDensity
  split <;> positivity

lemma squareResidueDensity_le_one (q : ℕ) [NeZero q] : squareResidueDensity q ≤ 1 := by
  rw [squareResidueDensity_eq]
  apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))).mpr
  exact_mod_cast (by simpa using Finset.card_le_univ (squareSumResidues q) :
    (squareSumResidues q).card ≤ q)

lemma squareResidueDensity_mul_le (m n : ℕ) [NeZero m] [NeZero n]
    (hc : m.Coprime n) :
    squareResidueDensity (m * n) ≤ squareResidueDensity m * squareResidueDensity n := by
  simp only [squareResidueDensity_eq, Nat.cast_mul, div_mul_div_comm]
  exact div_le_div_of_nonneg_right (by exact_mod_cast squareSumResidues_card_mul_le m n hc)
    (by positivity)

lemma squareResidueDensity_prime_sq_le_exp (p : ℕ) (hp : p.Prime) (hp3 : p % 4 = 3) :
    squareResidueDensity (p ^ 2) ≤ Real.exp (-(1 / 2) * (1 / (p : ℝ))) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpp : p ≤ p ^ 2 := by nlinarith [hp.two_le]
  have hc : ((squareSumResidues (p ^ 2)).card : ℝ) ≤ (p : ℝ) ^ 2 - p + 1 := by
    exact_mod_cast squareSumResidues_card_prime_sq p hp hp3
  calc
    squareResidueDensity (p ^ 2) ≤ ((p : ℝ) ^ 2 - p + 1) / (p : ℝ) ^ 2 := by
      rw [squareResidueDensity_eq, Nat.cast_pow]
      exact div_le_div_of_nonneg_right hc (by positivity)
    _ ≤ 1 - 1 / (2 * (p : ℝ)) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (p : ℝ) ^ 2)).mpr
      field_simp
      nlinarith
    _ = 1 + (-(1 / 2) * (1 / (p : ℝ))) := by ring
    _ ≤ Real.exp (-(1 / 2) * (1 / (p : ℝ))) := by
      simpa [add_comm] using Real.add_one_le_exp (-(1 / 2) * (1 / (p : ℝ)))

lemma squareResidueDensity_prod_le (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime ∧ p % 4 = 3) :
    squareResidueDensity (∏ p ∈ F, p ^ 2) ≤
      Real.exp (-(1 / 2) * ∑ p ∈ F, (1 / (p : ℝ))) := by
  induction F using Finset.induction_on with
  | empty => simpa using squareResidueDensity_le_one 1
  | @insert p F hpF ih =>
    have hp := hF p (Finset.mem_insert_self p F)
    have hF' : ∀ r ∈ F, r.Prime ∧ r % 4 = 3 :=
      fun r hr => hF r (Finset.mem_insert_of_mem hr)
    have hQ : (∏ r ∈ F, r ^ 2) ≠ 0 := Finset.prod_ne_zero_iff.mpr
      (fun r hr => pow_ne_zero 2 (hF' r hr).1.ne_zero)
    letI : NeZero p := ⟨hp.1.ne_zero⟩
    letI : NeZero (∏ r ∈ F, r ^ 2) := ⟨hQ⟩
    have hc : (p ^ 2).Coprime (∏ r ∈ F, r ^ 2) := by
      apply Nat.Coprime.prod_right
      intro r hr
      apply Nat.Coprime.pow
      exact (hp.1.coprime_iff_not_dvd).mpr (by
        intro hd
        have he : p = r := (Nat.prime_dvd_prime_iff_eq hp.1 (hF' r hr).1).mp hd
        exact hpF (he ▸ hr))
    rw [Finset.prod_insert hpF, Finset.sum_insert hpF, mul_add, Real.exp_add]
    exact (squareResidueDensity_mul_le _ _ hc).trans
      (mul_le_mul (squareResidueDensity_prime_sq_le_exp p hp.1 hp.2) (ih hF')
        (squareResidueDensity_nonneg _) (Real.exp_nonneg _))

lemma exists_small_squareResidueDensity (δ : ℝ) (hδ : 0 < δ) :
    ∃ Q : ℕ, 0 < Q ∧ squareResidueDensity Q < δ := by
  have hunit : IsUnit (3 : ZMod 4) := by decide
  have hnotsum := not_summable_prime_reciprocals_residue_class hunit
  have hcast (p : ℕ) : (p : ZMod 4) = 3 ↔ p % 4 = 3 := by
    change (p : ZMod 4) = ((3 : ℕ) : ZMod 4) ↔ _
    rw [ZMod.natCast_eq_natCast_iff]
    rfl
  simp_rw [hcast] at hnotsum
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun p : ℕ => show 0 ≤ (if p.Prime ∧ p % 4 = 3 then (1 : ℝ) / p else 0) by
      split <;> positivity)).mp hnotsum
  obtain ⟨k, hk⟩ := (ht.eventually (eventually_gt_atTop (-2 * Real.log δ))).exists
  let F := (Finset.range k).filter (fun p => p.Prime ∧ p % 4 = 3)
  have hF : ∀ p ∈ F, p.Prime ∧ p % 4 = 3 :=
    fun p hp => (Finset.mem_filter.mp hp).2
  have hQ : 0 < ∏ p ∈ F, p ^ 2 := Finset.prod_pos (fun p hp => pow_pos (hF p hp).1.pos 2)
  refine ⟨∏ p ∈ F, p ^ 2, hQ, (squareResidueDensity_prod_le F hF).trans_lt ?_⟩
  rw [← Real.exp_log hδ, Real.exp_lt_exp]
  have hk' : -2 * Real.log δ < ∑ p ∈ F, (1 : ℝ) / p := by
    simpa [F, Finset.sum_filter] using hk
  linarith

lemma maxSidon_card_choose_le_squareSumResidues (N Q : ℕ) [NeZero Q] :
    (Finset.maxSidonSubsetCard
      ((Finset.Icc 1 N).image (fun n : ℕ => n ^ 2)) + 1).choose 2 ≤
        (squareSumResidues Q).card * (2 * N ^ 2 / Q + 1) := by
  let C : Finset ℕ := (squareSumResidues Q).image ZMod.val
  have hC : C.card = (squareSumResidues Q).card :=
    Finset.card_image_of_injective _ (ZMod.val_injective Q)
  rw [← hC]
  apply maxSidon_card_choose_le_residue_capacity N Q C
  intro a ha b hb
  apply Finset.mem_image.mpr
  refine ⟨((a ^ 2 + b ^ 2 : ℕ) : ZMod Q), ?_, ZMod.val_natCast _ _⟩
  exact (mem_squareSumResidues _).mpr ⟨a, b, by push_cast; rfl⟩

lemma maxSidon_card_sq_le_squareResidueDensity (N Q : ℕ) [NeZero Q] :
    (Finset.maxSidonSubsetCard
      ((Finset.Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) ^ 2 ≤
      4 * squareResidueDensity Q * (N : ℝ) ^ 2 + 2 * (squareSumResidues Q).card := by
  let M := Finset.maxSidonSubsetCard ((Finset.Icc 1 N).image (fun n : ℕ => n ^ 2))
  have hb : (((M + 1).choose 2 : ℕ) : ℝ) ≤
      ((squareSumResidues Q).card : ℝ) * (((2 * N ^ 2 / Q : ℕ) : ℝ) + 1) := by
    exact_mod_cast maxSidon_card_choose_le_squareSumResidues N Q
  rw [Nat.cast_choose_two, Nat.cast_add, Nat.cast_one] at hb
  have hdiv : ((2 * N ^ 2 / Q : ℕ) : ℝ) ≤ 2 * (N : ℝ) ^ 2 / (Q : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
      (Nat.cast_div_le (m := 2 * N ^ 2) (n := Q) :
        ((2 * N ^ 2 / Q : ℕ) : ℝ) ≤ (2 * N ^ 2 : ℕ) / (Q : ℝ))
  have hdiv' := mul_le_mul_of_nonneg_left hdiv
    (Nat.cast_nonneg (α := ℝ) (squareSumResidues Q).card)
  rw [squareResidueDensity_eq]
  change (M : ℝ) ^ 2 ≤ _
  simp only [div_eq_mul_inv] at hb hdiv' ⊢
  nlinarith [Nat.cast_nonneg (α := ℝ) M]

lemma square_sidon_eventually_small_linear (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      (Finset.maxSidonSubsetCard
        ((Finset.Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) ≤ δ * N := by
  obtain ⟨Q, hQ, hsmall⟩ := exists_small_squareResidueDensity (δ ^ 2 / 8) (by positivity)
  letI : NeZero Q := ⟨hQ.ne'⟩
  have hNlim : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hNlim.eventually (eventually_ge_atTop (1 : ℝ)),
    hNlim.eventually (eventually_ge_atTop
      (4 * ((squareSumResidues Q).card : ℝ) / δ ^ 2))] with N hN1 hNc
  have hmain := maxSidon_card_sq_le_squareResidueDensity N Q
  have hsmall' : 4 * squareResidueDensity Q ≤ δ ^ 2 / 2 := by linarith
  have hsmallN := mul_le_mul_of_nonneg_right hsmall' (sq_nonneg (N : ℝ))
  have hNc' := (div_le_iff₀ (sq_pos_of_pos hδ)).mp hNc
  have hNsq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hNsq' := mul_le_mul_of_nonneg_left hNsq (sq_nonneg δ)
  apply (sq_le_sq₀ (Nat.cast_nonneg _) (mul_nonneg hδ.le (Nat.cast_nonneg N))).mp
  nlinarith

lemma square_sidon_density_zero :
    Tendsto (fun N : ℕ =>
      (Finset.maxSidonSubsetCard
        ((Finset.Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) / N) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [square_sidon_eventually_small_linear (ε / 2) (by positivity),
    eventually_ge_atTop 1] with N hN hN1
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  apply lt_of_le_of_lt ((div_le_iff₀ hNp).mpr hN)
  linarith

#print axioms square_sidon_density_zero

end Erdos773
