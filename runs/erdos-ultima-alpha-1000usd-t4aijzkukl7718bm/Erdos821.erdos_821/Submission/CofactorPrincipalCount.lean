import Submission.CofactorMeanScales

/-!
# The exact coprime cofactor count and its elementary density

Deleting primes from an interval gives a uniform error exponential only
in the number of distinct local factors. This is a subpower loss in the
modulus, and does not charge one error for each reduced residue class.
-/
open Nat Finset ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def siftedCofactorWeight (P : Finset ℕ) (A B : ℕ) : ℝ :=
  ∑ n ∈ Icc (A+1) B, if ∀ p ∈ P, ¬p ∣ n then 1 else 0

lemma siftedCofactorWeight_insert (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (p : ℕ) (hp : p.Prime) (hpP : p ∉ P) (A B : ℕ) :
    siftedCofactorWeight (insert p P) A B =
      siftedCofactorWeight P A B-siftedCofactorWeight P (A/p) (B/p) := by
  have hpoint (n : ℕ) : (if ∀ q ∈ insert p P, ¬q ∣ n then (1 : ℝ) else 0) =
      (if ∀ q ∈ P, ¬q ∣ n then (1 : ℝ) else 0)-
        (if p ∣ n then (if ∀ q ∈ P, ¬q ∣ n then (1 : ℝ) else 0) else 0) := by
    simp only [Finset.forall_mem_insert]
    split_ifs <;> simp_all
  have havoid (n : ℕ) : (∀ q ∈ P, ¬q ∣ p*n) ↔ (∀ q ∈ P, ¬q ∣ n) := by
    apply forall₂_congr
    intro q hq
    have hqp : ¬q ∣ p := by
      intro hh
      have he := (Nat.prime_dvd_prime_iff_eq (hP q hq) hp).mp hh
      exact hpP (he ▸ hq)
    rw [(hP q hq).dvd_mul]
    simp only [hqp,false_or]
  unfold siftedCofactorWeight
  simp_rw [hpoint]
  rw [sum_sub_distrib]
  congr 1
  rw [← sum_filter,sum_multiples_natural_interval _ A B p hp.pos]
  simp only [havoid]

lemma floor_interval_length_error (A B p : ℕ) (hp : 0 < p) :
    |((B/p-A/p : ℕ) : ℝ)-((B-A : ℕ) : ℝ)/(p : ℝ)| ≤ 1 := by
  by_cases hAB : A ≤ B
  · have hpR : (0 : ℝ)<p := by exact_mod_cast hp
    have hAlo : ((A/p : ℕ) : ℝ)*p ≤ A := by exact_mod_cast Nat.div_mul_le_self A p
    have hBlo : ((B/p : ℕ) : ℝ)*p ≤ B := by exact_mod_cast Nat.div_mul_le_self B p
    have hAhi : (A : ℝ) < (((A/p : ℕ) : ℝ)+1)*p := by
      exact_mod_cast (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self (A/p))
    have hBhi : (B : ℝ) < (((B/p : ℕ) : ℝ)+1)*p := by
      exact_mod_cast (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self (B/p))
    rw [Nat.cast_sub (Nat.div_le_div_right hAB),Nat.cast_sub hAB]
    have he : (p : ℝ)*(((B/p : ℕ) : ℝ)-((A/p : ℕ) : ℝ)-((B : ℝ)-(A : ℝ))/p) =
        (p : ℝ)*(((B/p : ℕ) : ℝ)-((A/p : ℕ) : ℝ))-((B : ℝ)-(A : ℝ)) := by field_simp
    apply abs_le.mpr
    constructor
    · apply (mul_le_mul_iff_right₀ hpR).mp
      rw [he]
      nlinarith only [hBhi,hAlo]
    · apply (mul_le_mul_iff_right₀ hpR).mp
      rw [he]
      nlinarith only [hBlo,hAhi]
  · have hBA : B ≤ A := Nat.le_of_lt (Nat.lt_of_not_ge hAB)
    simp only [Nat.sub_eq_zero_of_le hBA,Nat.sub_eq_zero_of_le (Nat.div_le_div_right hBA),
      Nat.cast_zero,zero_div,sub_self,abs_zero]
    norm_num

lemma cofactor_local_density_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    0 ≤ (∏ p ∈ P, (1-(p : ℝ)⁻¹)) ∧ (∏ p ∈ P, (1-(p : ℝ)⁻¹)) ≤ 1 := by
  have hpoint (p : ℕ) (hp : p ∈ P) : 0 ≤ 1-(p : ℝ)⁻¹ ∧ 1-(p : ℝ)⁻¹ ≤ 1 := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
    constructor
    · exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp1)
    · linarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) p)]
  exact ⟨prod_nonneg (fun p hp => (hpoint p hp).1),prod_le_one (fun p hp => (hpoint p hp).1)
    (fun p hp => (hpoint p hp).2)⟩

/-- A coarse but uniform local-factor error; its base three is harmless
under the existing subpower estimate for prime-factor counts. -/
theorem siftedCofactorWeight_density_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (A B : ℕ) :
    |siftedCofactorWeight P A B-((B-A : ℕ) : ℝ)*(∏ p ∈ P, (1-(p : ℝ)⁻¹))| ≤ (3 : ℝ)^P.card := by
  induction P using Finset.induction generalizing A B with
  | empty => simp [siftedCofactorWeight]
  | @insert p P hpP ih =>
    have hp : p.Prime := hP p (mem_insert_self _ _)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    let V : ℝ := ∏ q ∈ P, (1-(q : ℝ)⁻¹)
    have hV := cofactor_local_density_bounds P hP'
    change 0 ≤ V ∧ V ≤ 1 at hV
    have h1 := ih hP' A B
    have h2 := ih hP' (A/p) (B/p)
    have he : siftedCofactorWeight (insert p P) A B-
        ((B-A : ℕ) : ℝ)*(∏ q ∈ insert p P, (1-(q : ℝ)⁻¹)) =
        (siftedCofactorWeight P A B-((B-A : ℕ) : ℝ)*V)-
          (siftedCofactorWeight P (A/p) (B/p)-((B/p-A/p : ℕ) : ℝ)*V)-
            (((B/p-A/p : ℕ) : ℝ)-((B-A : ℕ) : ℝ)/(p : ℝ))*V := by
      rw [siftedCofactorWeight_insert P hP' p hp hpP,prod_insert hpP]
      dsimp [V]
      ring
    have herr : |(((B/p-A/p : ℕ) : ℝ)-((B-A : ℕ) : ℝ)/(p : ℝ))*V| ≤ 1 := by
      rw [abs_mul,abs_of_nonneg hV.1]
      exact (mul_le_mul (floor_interval_length_error A B p hp.pos) hV.2 hV.1 (by norm_num)).trans_eq (one_mul 1)
    rw [he,card_insert_of_notMem hpP,pow_succ]
    apply (abs_sub _ _).trans
    apply (add_le_add (abs_sub _ _) le_rfl).trans
    have hb := _root_.add_le_add (_root_.add_le_add h1 h2) herr
    have hpow : (1 : ℝ) ≤ 3^P.card := one_le_pow₀ (by norm_num)
    linarith only [hb,hpow]

lemma coprimeCofactorCount_eq_sifted (d A B : ℕ) (hd : d ≠ 0) :
    (coprimeCofactorCount d A B : ℝ) = siftedCofactorWeight d.primeFactors A B := by
  simp only [siftedCofactorWeight,← coprime_iff_avoid_primeFactors _ d hd,← sum_filter,
    sum_const,nsmul_eq_mul,mul_one,coprimeCofactorCount]

lemma totient_div_eq_cofactor_density (d : ℕ) (hd : 0 < d) :
    (d.totient : ℝ)/(d : ℝ) = ∏ p ∈ d.primeFactors, (1-(p : ℝ)⁻¹) := by
  have hh := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors d)
  push_cast at hh
  rw [hh]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

/-- The error is subpower in d, rather than of order phi(d). -/
theorem coprimeCofactorCount_density_error (d A B : ℕ) (hd : 0 < d) :
    |(coprimeCofactorCount d A B : ℝ)-((B-A : ℕ) : ℝ)*(d.totient : ℝ)/(d : ℝ)| ≤
      (3 : ℝ)^d.primeFactors.card := by
  have hh := siftedCofactorWeight_density_error d.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) A B
  rw [← coprimeCofactorCount_eq_sifted d A B hd.ne',← totient_div_eq_cofactor_density d hd] at hh
  simpa only [mul_div_assoc] using hh

end Erdos821.AnalyticSieve
