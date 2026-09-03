import Submission.PrimeDilutionGeneral
import Submission.FiniteThinningApproximation

/-! General finite thinning with explicit errors. These are auxiliary identities
and approximation results, not an unconditional Jacobsthal estimate. -/
namespace Erdos970.GapAverages.FiniteThinning
open Finset Real Erdos970.PrimeDilution
set_option maxHeartbeats 2000000

lemma laplace_expansion (P : Finset ℕ) (t : ℝ) (m : ℕ) :
    countLaplace P t m = ∑ A ∈ (range m).powerset,
      (-1 : ℝ)^A.card * (1-exp (-t))^A.card * joint P A := by
  classical
  have hp (r : Phase P) (x : ℕ) :
      exp (-t * point P x r) = 1-(1-exp (-t))*point P x r := by
    rcases point_eq_zero_or_one P x r with h | h <;> rw [h]
    · norm_num
    · simp
  have he (r : Phase P) : exp (-t * intervalCount P m r) =
      ∏ x ∈ range m, (1-(1-exp (-t))*point P x r) := by
    unfold intervalCount
    rw [mul_sum, exp_sum]
    exact prod_congr rfl (fun x _ => hp r x)
  unfold countLaplace
  simp_rw [he, prod_sub]
  simp only [prod_const_one, mul_one, prod_mul_distrib, prod_const]
  rw [phaseMean_sum]
  apply sum_congr rfl
  intro A hA
  simp_rw [← mul_assoc]
  exact phaseMean_mul P (((-1 : ℝ)^A.card)*(1-exp (-t))^A.card) _


lemma reciprocal_square_sum_le_general (R : Finset ℕ) (B : ℕ) (hB : 0 < B)
    (hR : ∀ p ∈ R, B ≤ p) (K : ℝ) (hs : (∑ p ∈ R, 1/(p : ℝ)) ≤ K) :
    (∑ p ∈ R, (1/(p : ℝ))^2) ≤ K/(B : ℝ) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hsum : (∑ p ∈ R, (1/(p : ℝ))^2) ≤
      (1/(B : ℝ)) * ∑ p ∈ R, 1/(p : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hpB : (B : ℝ) ≤ p := by exact_mod_cast hR p hp
    have hh := one_div_le_one_div_of_le hB0 hpB
    nlinarith [mul_le_mul_of_nonneg_right hh (show 0 ≤ 1/(p : ℝ) by positivity)]
  exact hsum.trans (by simpa only [one_div_mul_eq_div] using mul_le_mul_of_nonneg_left hs (show 0 ≤ 1/(B : ℝ) by positivity))

lemma joint_product_target_error_general (R : Finset ℕ) (B s : ℕ) (d K : ℝ) (hd1 : d ≤ 1) (hB : 2 ≤ B)
    (hsB : s ≤ B) (hR : ∀ p ∈ R, B ≤ p)
    (hlo : d-1/(B : ℝ) ≤ ∏ p ∈ R, (1-1/(p : ℝ)))
    (hhi : (∏ p ∈ R, (1-1/(p : ℝ))) ≤ d)
    (hsum : (∑ p ∈ R, 1/(p : ℝ)) ≤ K) :
    0 ≤ d^s - ∏ p ∈ R, (1-(s : ℝ)/p) ∧
      d^s - ∏ p ∈ R, (1-(s : ℝ)/p) ≤
        ((s : ℝ)^2*K+s)/(B : ℝ) := by
  let e : ℝ := ∏ p ∈ R, (1-1/(p : ℝ))
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hd0 : 0 ≤ e := by
    apply prod_nonneg
    intro p hp
    have hpB : (B : ℝ) ≤ p := by exact_mod_cast hR p hp
    have hp0 : (0 : ℝ) < p := hB0.trans_le hpB
    have hb : (2 : ℝ) ≤ B := by exact_mod_cast hB
    exact sub_nonneg.mpr ((div_le_one hp0).mpr (by linarith))
  have hprod := joint_product_error R s (fun p hp => ⟨by have := hR p hp; omega, hsB.trans (hR p hp)⟩)
  have hsq := reciprocal_square_sum_le_general R B (by omega) hR K hsum
  have hpowers := prod_difference_le_sum (range s) (fun _ => e) (fun _ => d)
    (fun _ _ => hd0) (fun _ _ => hhi) (fun _ _ => hd1)
  simp only [prod_const, card_range, sum_const, nsmul_eq_mul] at hpowers
  have hu : e^s - ∏ p ∈ R, (1-(s : ℝ)/p) ≤ (s : ℝ)^2*K/(B : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hsq (sq_nonneg (s : ℝ))
    dsimp only [e]
    exact hprod.2.trans (by simpa only [mul_div_assoc] using hh)
  have hn : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hb := mul_le_mul_of_nonneg_left (show d-e ≤ 1/(B : ℝ) by linarith) hn
  change 0 ≤ e^s - ∏ p ∈ R, (1-(s : ℝ)/p) ∧ _ at hprod
  constructor
  · linarith [hprod.1, hpowers.1]
  · rw [add_div]
    simp only [mul_one_div] at hb
    linarith [hpowers.2]

/-- Uniform error for all interval lengths up to B. -/
theorem covered_laplace_error_general (P R : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (B m : ℕ) (t K : ℝ) (hK : 0 ≤ K) (hB : 2 ≤ B) (hmB : m ≤ B) (hdis : Disjoint P R)
    (hR : ∀ p ∈ R, B ≤ p)
    (hlo : (1-exp (-t))-1/(B : ℝ) ≤ ∏ p ∈ R, (1-1/(p : ℝ)))
    (hhi : (∏ p ∈ R, (1-1/(p : ℝ))) ≤ (1-exp (-t)))
    (hsum : (∑ p ∈ R, 1/(p : ℝ)) ≤ K) :
    |coveredFraction (P ∪ R) m - countLaplace P t m| ≤
      (2 : ℝ)^m * ((m : ℝ)^2*K+m)/(B : ℝ) := by
  classical
  rw [covered_expansion, laplace_expansion, ← sum_sub_distrib]
  have hterm (A : Finset ℕ) (hA : A ∈ (range m).powerset) :
      |(-1 : ℝ)^A.card * joint (P ∪ R) A -
        (-1 : ℝ)^A.card * (1-exp (-t))^A.card * joint P A| ≤
          ((m : ℝ)^2*K+m)/(B : ℝ) := by
    have hAsub : A ⊆ range m := mem_powerset.mp hA
    have hAm : A.card ≤ m := (card_le_card hAsub).trans_eq (card_range _)
    have he := joint_union_large P R A hdis (fun p hp =>
      ⟨by have := hR p hp; omega, hAsub.trans (range_mono (hmB.trans (hR p hp)))⟩)
    have hh := joint_product_target_error_general R B A.card (1-exp (-t)) K (by linarith [exp_pos (-t)]) hB (hAm.trans hmB) hR hlo hhi hsum
    rw [he]
    have heq : (-1 : ℝ)^A.card * (joint P A * ∏ p ∈ R, (1-(A.card : ℝ)/p)) -
        (-1 : ℝ)^A.card * (1-exp (-t))^A.card * joint P A =
        -((-1 : ℝ)^A.card * joint P A *
          ((1-exp (-t))^A.card - ∏ p ∈ R, (1-(A.card : ℝ)/p))) := by ring
    rw [heq, abs_neg, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (joint_nonneg P A), abs_of_nonneg hh.1]
    have hu := mul_le_mul_of_nonneg_right (joint_le_one P A hP) hh.1
    have hcast : (A.card : ℝ) ≤ m := by exact_mod_cast hAm
    have hn : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
    have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    calc
      _ ≤ (1-exp (-t))^A.card - ∏ p ∈ R, (1-(A.card : ℝ)/p) := by simpa only [one_mul] using hu
      _ ≤ ((A.card : ℝ)^2*K+A.card)/(B : ℝ) := hh.2
      _ ≤ ((m : ℝ)^2*K+m)/(B : ℝ) := div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right (show (A.card : ℝ)^2 ≤ (m : ℝ)^2 by nlinarith) hK]) hB0.le
  calc
    _ ≤ ∑ A ∈ (range m).powerset,
        |(-1 : ℝ)^A.card * joint (P ∪ R) A - (-1 : ℝ)^A.card * (1-exp (-t))^A.card * joint P A| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _A ∈ (range m).powerset, ((m : ℝ)^2*K+m)/(B : ℝ) := sum_le_sum hterm
    _ = _ := by simp [card_powerset, card_range]; ring


/-- Simultaneous approximation at every specified finite length, retaining
also the density. The fresh primes may all be chosen arbitrarily large. -/
theorem exists_padding_approx_general (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t : ℝ) (ht : 0 < t) (M : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ R : Finset ℕ, Disjoint P R ∧ (∀ p ∈ R, p.Prime ∧ M ≤ p) ∧
      |density (P ∪ R) - density P*(1-exp (-t))| < η ∧
      ∀ m ≤ M, |coveredFraction (P ∪ R) m - countLaplace P t m| < η := by
  classical
  let d : ℝ := 1-exp (-t)
  have hd : 0 < d := by
    apply sub_pos.mpr
    simpa only [exp_zero] using exp_lt_exp.mpr (show -t < (0 : ℝ) by linarith)
  have hd1 : d < 1 := by dsimp [d]; linarith [exp_pos (-t)]
  let K : ℝ := (2 : ℝ)^M * ((M : ℝ)^2*(2/d)+M)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨b,hb⟩ := exists_nat_gt (max (2/d) ((K+1)/η))
  let B : ℕ := max 2 (max M (max (P.sup id + 1) b))
  have hB2 : 2 ≤ B := le_max_left _ _
  have hMB : M ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hsB : P.sup id + 1 ≤ B :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hbB : b ≤ B :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hbB' : (b : ℝ) ≤ B := by exact_mod_cast hbB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hBd : 2/(B : ℝ) ≤ d := by
    have hh := (div_lt_iff₀ hd).mp ((le_max_left _ _).trans_lt hb)
    apply (div_le_iff₀ hB0).mpr
    nlinarith only [hh,mul_le_mul_of_nonneg_left hbB' hd.le]
  have hKB : K+1 < η*(B : ℝ) := by
    have hh := (div_lt_iff₀ hη).mp ((le_max_right _ _).trans_lt hb)
    nlinarith only [hh,mul_le_mul_of_nonneg_left hbB' hη.le]
  have hηB : 1/(B : ℝ) < η := (div_lt_iff₀ hB0).mpr (by linarith only [hKB,hK])
  obtain ⟨R,hR,hlo,hhi,hsum⟩ := exists_dilution_primes_target B hB2 d hd hd1 hBd
  have hdis : Disjoint P R := by
    apply disjoint_left.mpr
    intro p hpP hpR
    have hp : p ≤ P.sup id := le_sup (f := id) hpP
    have hpB := (hR p hpR).2
    omega
  refine ⟨R,hdis,fun p hp => ⟨(hR p hp).1,hMB.trans (hR p hp).2⟩,?_,?_⟩
  · change |density (P ∪ R) - density P*d| < η
    have he : density (P ∪ R) = density P * ∏ p ∈ R, (1-1/(p : ℝ)) :=
      prod_union hdis
    rw [he,← mul_sub,abs_mul,abs_of_nonneg (density_pos P hP).le,
      abs_of_nonpos (sub_nonpos.mpr hhi)]
    have hh := mul_le_mul_of_nonneg_left (show -(∏ p ∈ R, (1-1/(p : ℝ)) - d) ≤ 1/(B : ℝ) by linarith)
      (density_pos P hP).le
    have hh' := mul_le_mul_of_nonneg_right (density_le_one P hP) (show 0 ≤ 1/(B : ℝ) by positivity)
    simp only [one_mul] at hh'
    exact hh.trans_lt (hh'.trans_lt hηB)
  · intro m hm
    have he := covered_laplace_error_general P R hP B m t (2/d) (by positivity)
      hB2 (hm.trans hMB) hdis (fun p hp => (hR p hp).2) hlo hhi hsum
    have hmn : (m : ℝ) ≤ M := by exact_mod_cast hm
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hpow : (2 : ℝ)^m ≤ 2^M := pow_le_pow_right₀ (by norm_num) hm
    have hsq : (m : ℝ)^2 ≤ (M : ℝ)^2 := by nlinarith only [hmn,hm0]
    have hK' : (2 : ℝ)^m * ((m : ℝ)^2*(2/d)+m) ≤ K :=
      mul_le_mul hpow (by nlinarith [mul_le_mul_of_nonneg_right hsq (show 0 ≤ 2/d by positivity)])
        (by positivity) (by positivity)
    exact he.trans_lt ((div_le_div_of_nonneg_right hK' hB0.le).trans_lt
      ((div_lt_iff₀ hB0).mpr (by linarith only [hKB])))

#print axioms laplace_expansion
#print axioms covered_laplace_error_general
#print axioms exists_padding_approx_general
end Erdos970.GapAverages.FiniteThinning
