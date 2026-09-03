import Submission.SquarefreeInput
import Submission.Sieve

/-!
# Cost of imposing a common divisor in the prime-subset construction

These bounds quantify the multiplicity lost when a fixed divisor is required
to divide every selected input. They do not settle Erdős 821.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

lemma choose_ratio_pow_bound (N k h : ℕ) (hk : k ≤ N) (hh : h ≤ k) :
    N ^ h * k.choose h ≤ k ^ h * N.choose h := by
  have hprod : N ^ h * k.descFactorial h ≤ k ^ h * N.descFactorial h := by
    have hlocal (i : ℕ) (hi : i ∈ Finset.range h) :
        N * (k - i) ≤ k * (N - i) := by
      have hi' := Finset.mem_range.mp hi
      have hkadd := Nat.sub_add_cancel (show i ≤ k by omega)
      have hNadd := Nat.sub_add_cancel (show i ≤ N by omega)
      have hmul := Nat.mul_le_mul_left i hk
      nlinarith
    have h := Finset.prod_le_prod' hlocal
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      ← Nat.descFactorial_eq_prod_range] using h
  apply Nat.le_of_mul_le_mul_left (c := h.factorial) _ (Nat.factorial_pos _)
  calc
    h.factorial * (N ^ h * k.choose h) = N ^ h * k.descFactorial h := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      ring
    _ ≤ k ^ h * N.descFactorial h := hprod
    _ = _ := by rw [Nat.descFactorial_eq_factorial_mul_choose]; ring

/-- Requiring a fixed `h`-element core in a uniformly chosen `k`-subset costs
at least the factor `(N/k)^h`. This is expressed without division. -/
lemma choose_common_core_pow_bound (N k h : ℕ) (hk : k ≤ N) (hh : h ≤ k) :
    N ^ h * (N - h).choose (k - h) ≤ k ^ h * N.choose k := by
  have hchoose : 0 < N.choose h := Nat.choose_pos (hh.trans hk)
  apply Nat.le_of_mul_le_mul_left (c := N.choose h) _ hchoose
  calc
    N.choose h * (N ^ h * (N - h).choose (k - h)) =
        N ^ h * (N.choose h * (N - h).choose (k - h)) := by ring
    _ = N ^ h * (N.choose k * k.choose h) := by rw [← Nat.choose_mul hh]
    _ = (N ^ h * k.choose h) * N.choose k := by ring
    _ ≤ (k ^ h * N.choose h) * N.choose k :=
      Nat.mul_le_mul_right _ (choose_ratio_pow_bound N k h hk hh)
    _ = _ := by ring

/-- Deleting the prime support of a fixed divisor injects the corresponding
subfamily into subsets of the remaining prime pool. -/
lemma card_common_divisor_subfamily_le_choose (P R : Finset ℕ) (k d : ℕ)
    (hR : ∀ m ∈ R, Squarefree m ∧ m.primeFactors.card = k ∧ m.primeFactors ⊆ P)
    (hcore : (R.filter (fun m => d ∣ m)).Nonempty) :
    (R.filter (fun m => d ∣ m)).card ≤
      (P.card - d.primeFactors.card).choose (k - d.primeFactors.card) := by
  obtain ⟨m, hm⟩ := hcore
  obtain ⟨hmR, hdm⟩ := Finset.mem_filter.mp hm
  have hdP : d.primeFactors ⊆ P :=
    (Nat.primeFactors_mono hdm (hR m hmR).1.ne_zero).trans (hR m hmR).2.2
  rw [← Finset.card_sdiff_of_subset hdP, ← Finset.card_powersetCard]
  apply Finset.card_le_card_of_injOn (fun a : ℕ => a.primeFactors \ d.primeFactors)
  · intro a ha
    obtain ⟨haR, hda⟩ := Finset.mem_filter.mp ha
    have hdA := Nat.primeFactors_mono hda (hR a haR).1.ne_zero
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.sdiff_subset_sdiff (hR a haR).2.2 (Finset.Subset.refl _), ?_⟩
    rw [Finset.card_sdiff_of_subset hdA, (hR a haR).2.1]
  · intro a ha b hb hab
    obtain ⟨haR, hda⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbR, hdb⟩ := Finset.mem_filter.mp hb
    have hdA := Nat.primeFactors_mono hda (hR a haR).1.ne_zero
    have hdB := Nat.primeFactors_mono hdb (hR b hbR).1.ne_zero
    have hsupport : a.primeFactors = b.primeFactors := by
      calc
        a.primeFactors = (a.primeFactors \ d.primeFactors) ∪ d.primeFactors :=
          (Finset.sdiff_union_of_subset hdA).symm
        _ = (b.primeFactors \ d.primeFactors) ∪ d.primeFactors :=
          congrArg (fun s : Finset ℕ => s ∪ d.primeFactors) hab
        _ = b.primeFactors := Finset.sdiff_union_of_subset hdB
    rw [← Nat.prod_primeFactors_of_squarefree (hR a haR).1,
      ← Nat.prod_primeFactors_of_squarefree (hR b hbR).1, hsupport]

lemma common_divisor_subfamily_pow_bound (P R : Finset ℕ) (k d : ℕ)
    (hR : ∀ m ∈ R, Squarefree m ∧ m.primeFactors.card = k ∧ m.primeFactors ⊆ P) :
    P.card ^ d.primeFactors.card * (R.filter (fun m => d ∣ m)).card ≤
      k ^ d.primeFactors.card * P.card.choose k := by
  by_cases hcore : (R.filter (fun m => d ∣ m)).Nonempty
  · have hbound := card_common_divisor_subfamily_le_choose P R k d hR hcore
    obtain ⟨m, hm⟩ := hcore
    obtain ⟨hmR, hdm⟩ := Finset.mem_filter.mp hm
    have h := hR m hmR
    have hdk : d.primeFactors.card ≤ k := by
      rw [← h.2.1]
      exact Finset.card_le_card (Nat.primeFactors_mono hdm h.1.ne_zero)
    have hkP : k ≤ P.card := by rw [← h.2.1]; exact Finset.card_le_card h.2.2
    exact (Nat.mul_le_mul_left _ hbound).trans
      (choose_common_core_pow_bound P.card k d.primeFactors.card hkP hdk)
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hcore, Finset.card_empty, mul_zero,
      Nat.zero_le]

/-- If the prime pool has at least `k * X^s` members and every prime used is
at most `X`, requiring `d` to divide an input costs a factor of at least `d^s`
relative to the total number of available `k`-subsets. -/
lemma common_divisor_subfamily_rpow_bound (P R : Finset ℕ) (k d : ℕ) (X s : ℝ)
    (hk : 0 < k) (hX : 0 ≤ X) (hs : 0 ≤ s)
    (hP : ∀ p ∈ P, (p : ℝ) ≤ X) (hscale : (k : ℝ) * X ^ s ≤ P.card)
    (hR : ∀ m ∈ R, Squarefree m ∧ m.primeFactors.card = k ∧ m.primeFactors ⊆ P) :
    (d : ℝ) ^ s * ((R.filter (fun m => d ∣ m)).card : ℝ) ≤ (P.card.choose k : ℝ) := by
  by_cases hcore : (R.filter (fun m => d ∣ m)).Nonempty
  · obtain ⟨m, hm⟩ := hcore
    obtain ⟨hmR, hdm⟩ := Finset.mem_filter.mp hm
    have hdSq : Squarefree d := (hR m hmR).1.squarefree_of_dvd hdm
    have hdP : d.primeFactors ⊆ P :=
      (Nat.primeFactors_mono hdm (hR m hmR).1.ne_zero).trans (hR m hmR).2.2
    have hdle : (d : ℝ) ≤ X ^ d.primeFactors.card := by
      calc
        (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
          rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hdSq]
        _ ≤ _ := by
          simpa only [Finset.prod_const] using
            Finset.prod_le_prod (fun p _ => Nat.cast_nonneg p)
              (fun p hp => hP p (hdP hp))
    have hdspow : (d : ℝ) ^ s ≤ (X ^ s) ^ d.primeFactors.card := by
      calc
        (d : ℝ) ^ s ≤ (X ^ d.primeFactors.card) ^ s :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hdle hs
        _ = _ := (Real.rpow_pow_comm hX s d.primeFactors.card).symm
    have hscalePow : (k : ℝ) ^ d.primeFactors.card * (d : ℝ) ^ s ≤
        (P.card : ℝ) ^ d.primeFactors.card := by
      calc
        (k : ℝ) ^ d.primeFactors.card * (d : ℝ) ^ s ≤
            (k : ℝ) ^ d.primeFactors.card * (X ^ s) ^ d.primeFactors.card :=
          mul_le_mul_of_nonneg_left hdspow (by positivity)
        _ = ((k : ℝ) * X ^ s) ^ d.primeFactors.card := (mul_pow _ _ _).symm
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hscale _
    have hcoreR : (P.card : ℝ) ^ d.primeFactors.card *
        ((R.filter (fun m => d ∣ m)).card : ℝ) ≤
          (k : ℝ) ^ d.primeFactors.card * (P.card.choose k : ℝ) := by
      exact_mod_cast common_divisor_subfamily_pow_bound P R k d hR
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    apply (mul_le_mul_iff_right₀ (pow_pos hkR d.primeFactors.card)).mp
    calc
      (k : ℝ) ^ d.primeFactors.card *
          ((d : ℝ) ^ s * ((R.filter (fun m => d ∣ m)).card : ℝ)) =
          ((k : ℝ) ^ d.primeFactors.card * (d : ℝ) ^ s) *
            ((R.filter (fun m => d ∣ m)).card : ℝ) := by ring
      _ ≤ (P.card : ℝ) ^ d.primeFactors.card *
          ((R.filter (fun m => d ∣ m)).card : ℝ) :=
        mul_le_mul_of_nonneg_right hscalePow (Nat.cast_nonneg _)
      _ ≤ _ := hcoreR
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hcore, Finset.card_empty,
      Nat.cast_zero, mul_zero, Nat.cast_nonneg]

/-- If the selected family loses at most a factor `D` relative to the whole
prime-subset pool, this bounds the relative frequency of every common divisor.
The hypothesis on `D` is explicit; no asymptotic estimate is assumed. -/
lemma common_divisor_relative_frequency_bound (P R : Finset ℕ) (k d : ℕ) (X s D : ℝ)
    (hk : 0 < k) (hX : 0 ≤ X) (hs : 0 ≤ s)
    (hP : ∀ p ∈ P, (p : ℝ) ≤ X) (hscale : (k : ℝ) * X ^ s ≤ P.card)
    (hR : ∀ m ∈ R, Squarefree m ∧ m.primeFactors.card = k ∧ m.primeFactors ⊆ P)
    (hD : (P.card.choose k : ℝ) ≤ D * (R.card : ℝ)) :
    (d : ℝ) ^ s * ((R.filter (fun m => d ∣ m)).card : ℝ) ≤ D * (R.card : ℝ) :=
  (common_divisor_subfamily_rpow_bound P R k d X s hk hX hs hP hscale hR).trans hD

/-- Comparison with the reduced output: the normalized multiplicity at
exponent `s` can increase by at most the pool-to-fiber loss factor `D` under
this common-divisor restriction and division. This is a finite bound for this
construction, not a universal obstruction to amplification. -/
lemma common_divisor_reduction_score_bound (P R : Finset ℕ) (k n d : ℕ) (X s D : ℝ)
    (hk : 0 < k) (hX : 0 ≤ X) (hs : 0 ≤ s)
    (hP : ∀ p ∈ P, (p : ℝ) ≤ X) (hscale : (k : ℝ) * X ^ s ≤ P.card)
    (hR : ∀ m ∈ R, Squarefree m ∧ m.primeFactors.card = k ∧ m.primeFactors ⊆ P)
    (hD : (P.card.choose k : ℝ) ≤ D * (R.card : ℝ)) (hd : totient d ∣ n) :
    (((R.filter (fun m => d ∣ m)).image (fun m => m / d)).card : ℝ) * (n : ℝ) ^ s ≤
      D * (R.card : ℝ) * ((n / totient d : ℕ) : ℝ) ^ s := by
  have hcore := common_divisor_relative_frequency_bound P R k d X s D
    hk hX hs hP hscale hR hD
  have hφle : (totient d : ℝ) ^ s ≤ (d : ℝ) ^ s :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.totient_le d) hs
  have hweighted : (totient d : ℝ) ^ s * ((R.filter (fun m => d ∣ m)).card : ℝ) ≤
      D * (R.card : ℝ) :=
    (mul_le_mul_of_nonneg_right hφle (Nat.cast_nonneg _)).trans hcore
  have hnid : (n : ℝ) ^ s =
      ((n / totient d : ℕ) : ℝ) ^ s * (totient d : ℝ) ^ s := by
    rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    congr 1
    exact_mod_cast (Nat.div_mul_cancel hd).symm
  have hcardimage : (((R.filter (fun m => d ∣ m)).image (fun m => m / d)).card : ℝ) ≤
      ((R.filter (fun m => d ∣ m)).card : ℝ) := by exact_mod_cast Finset.card_image_le
  calc
    (((R.filter (fun m => d ∣ m)).image (fun m => m / d)).card : ℝ) * (n : ℝ) ^ s ≤
        ((R.filter (fun m => d ∣ m)).card : ℝ) * (n : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right hcardimage (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = ((totient d : ℝ) ^ s * ((R.filter (fun m => d ∣ m)).card : ℝ)) *
        ((n / totient d : ℕ) : ℝ) ^ s := by rw [hnid]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hweighted
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Selecting a largest fiber makes the factor `D` concrete: it is at most
the cardinality of the finite output set used in pigeonholing. This theorem
still makes no asymptotic claim about that cardinality. -/
lemma exists_fiber_with_common_divisor_score_bound (P A T : Finset ℕ) (k : ℕ)
    (X s : ℝ) (hk : 0 < k) (hX : 0 ≤ X) (hs : 0 ≤ s)
    (hP : ∀ p ∈ P, (p : ℝ) ≤ X) (hscale : (k : ℝ) * X ^ s ≤ P.card)
    (hA : ∀ m ∈ A, Squarefree m ∧ m.primeFactors.card = k ∧ m.primeFactors ⊆ P)
    (hAcard : A.card = P.card.choose k) (hAnonempty : A.Nonempty)
    (hmap : ∀ m ∈ A, totient m ∈ T) :
    ∃ n ∈ T, ∃ R : Finset ℕ, R ⊆ A ∧ R.Nonempty ∧
      (∀ m ∈ R, totient m = n) ∧
      (P.card.choose k : ℝ) ≤ (T.card : ℝ) * (R.card : ℝ) ∧
      ∀ d : ℕ, totient d ∣ n →
        (((R.filter (fun m => d ∣ m)).image (fun m => m / d)).card : ℝ) * (n : ℝ) ^ s ≤
          (T.card : ℝ) * (R.card : ℝ) * ((n / totient d : ℕ) : ℝ) ^ s := by
  obtain ⟨a, ha⟩ := hAnonempty
  obtain ⟨n, hnT, hmax⟩ := Finset.exists_max_image T
    (fun n => (A.filter (fun m => totient m = n)).card) ⟨totient a, hmap a ha⟩
  let R := A.filter (fun m => totient m = n)
  have hsub : R ⊆ A := Finset.filter_subset _ _
  have hcard : A.card ≤ T.card * R.card := by
    calc
      A.card = ∑ b ∈ T, (A.filter (fun m => totient m = b)).card :=
        Finset.card_eq_sum_card_fiberwise hmap
      _ ≤ ∑ _b ∈ T, R.card := Finset.sum_le_sum hmax
      _ = _ := by simp
  have hRnonempty : R.Nonempty := by
    have hApos := Finset.card_pos.mpr (show A.Nonempty from ⟨a, ha⟩)
    apply Finset.card_pos.mp
    by_contra h
    have hz : R.card = 0 := by omega
    simp only [hz, mul_zero] at hcard
    omega
  have hcardR : (P.card.choose k : ℝ) ≤ (T.card : ℝ) * (R.card : ℝ) := by
    rw [hAcard] at hcard
    exact_mod_cast hcard
  refine ⟨n, hnT, R, hsub, hRnonempty, ?_, hcardR, ?_⟩
  · intro m hm
    exact (Finset.mem_filter.mp hm).2
  · intro d hd
    exact common_divisor_reduction_score_bound P R k n d X s T.card hk hX hs hP hscale
      (fun m hm => hA m (hsub hm)) hcardR hd

/-- The output-count bound in the old dyadic construction is subpower
relative to its lower bound for the output. Here this is an exact integer
inequality, valid for every prescribed root parameter `r` at large enough `L`. -/
lemma dyadic_output_bound_pow_le_totient_lower (t L r : ℕ) (ht : 6 ≤ t)
    (hL : 4 ≤ L) (htL : t ≤ L) (hrL : t * r + 2 ≤ L) :
    ((t * L * 2 ^ ((t - 4) * L) + 1) ^ (2 ^ ((t - 5) * L))) ^ r ≤
      2 ^ (2 ^ ((t - 4) * L) - 1) := by
  let k := 2 ^ ((t - 4) * L)
  let y := 2 ^ ((t - 5) * L)
  have hy : 0 < y := by dsimp [y]; positivity
  have hLp : L ≤ 2 ^ L := Nat.lt_two_pow_self.le
  have htp : t ≤ 2 ^ L := htL.trans hLp
  have hsmall : t * L * k ≤ 2 ^ ((t - 2) * L) := by
    calc
      t * L * k ≤ 2 ^ L * 2 ^ L * 2 ^ ((t - 4) * L) :=
        Nat.mul_le_mul_right k (Nat.mul_le_mul htp hLp)
      _ = _ := by
        rw [← pow_add, ← pow_add]
        congr 1
        have hcoeff : t - 4 + 2 = t - 2 := by omega
        nlinarith
  have hbase : t * L * k + 1 ≤ 2 ^ (t * L) := by
    calc
      t * L * k + 1 ≤ 2 ^ ((t - 2) * L) + 2 ^ ((t - 2) * L) :=
        Nat.add_le_add hsmall (Nat.one_le_pow _ _ (by decide))
      _ = 2 ^ ((t - 2) * L + 1) := by rw [pow_succ]; omega
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
        have hcoeff : t - 2 + 2 = t := by omega
        nlinarith)
  have hky : k = 2 ^ L * y := by
    dsimp [k, y]
    rw [← pow_add]
    congr 1
    have hcoeff : t - 5 + 1 = t - 4 := by omega
    nlinarith
  have hrsmall : t * L * r + 1 ≤ 2 ^ L := by
    apply le_trans ?_ (Sieve.sq_le_two_pow L hL)
    have hprod := Nat.mul_le_mul_right L hrL
    nlinarith
  have hexp : t * L * y * r ≤ k - 1 := by
    have hle : t * L * y * r + 1 ≤ k := by
      calc
        t * L * y * r + 1 ≤ (t * L * r + 1) * y := by nlinarith
        _ ≤ 2 ^ L * y := Nat.mul_le_mul_right y hrsmall
        _ = k := hky.symm
    omega
  calc
    ((t * L * k + 1) ^ y) ^ r ≤ ((2 ^ (t * L)) ^ y) ^ r :=
      Nat.pow_le_pow_left (Nat.pow_le_pow_left hbase y) r
    _ = 2 ^ (t * L * y * r) := by rw [← pow_mul, ← pow_mul]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp

#print axioms choose_common_core_pow_bound
#print axioms common_divisor_subfamily_pow_bound
#print axioms common_divisor_subfamily_rpow_bound
#print axioms common_divisor_relative_frequency_bound
#print axioms common_divisor_reduction_score_bound
#print axioms exists_fiber_with_common_divisor_score_bound
#print axioms dyadic_output_bound_pow_le_totient_lower

end Erdos821
