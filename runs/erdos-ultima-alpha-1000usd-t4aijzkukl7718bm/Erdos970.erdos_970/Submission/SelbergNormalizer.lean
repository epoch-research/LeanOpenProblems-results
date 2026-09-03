import Submission.SelbergPrimes

/-! The harmonic lower bound for the Selberg normalizing sum. -/
namespace Erdos970.FiniteSelberg

noncomputable def reciprocalHom : ℕ →* ℝ where
  toFun n := 1 / (n : ℝ)
  map_one' := by norm_num
  map_mul' m n := by simp [Nat.cast_mul, mul_comm]

theorem reciprocalHom_prime_norm_lt_one (p : ℕ) (hp : p.Prime) :
    ‖reciprocalHom p‖ < 1 := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  change ‖1 / (p : ℝ)‖ < 1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (div_lt_iff₀ (by linarith : (0 : ℝ) < p)).mpr (by simpa using hp')

theorem factored_reciprocal_hasSum (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    HasSum (fun n : Nat.factoredNumbers Q => 1 / ((n : ℕ) : ℝ))
      (∏ p ∈ Q, (1 - 1 / (p : ℝ))⁻¹) := by
  have hh := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocalHom) (fun {p} hp => reciprocalHom_prime_norm_lt_one p hp) Q).2
  simpa only [Finset.filter_true_of_mem hQ, reciprocalHom, MonoidHom.coe_mk,
    OneHom.coe_mk] using hh

/-- The reciprocal sum of any finite family with a fixed prime support is at most the
corresponding Euler factor. -/
theorem primeFactors_fiber_sum_le (Q s : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (hs : ∀ n ∈ s, n ≠ 0 ∧ n.primeFactors = Q) :
    (∑ n ∈ s, 1 / (n : ℝ)) ≤ ∏ p ∈ Q, (1 / ((p : ℝ) - 1)) := by
  classical
  let d := ∏ p ∈ Q, p
  have hd : 0 < d := Finset.prod_pos (fun p hp => (hQ p hp).pos)
  have hdiv (n : s) : d ∣ n.val := by
    dsimp [d]
    rw [← (hs n.val n.property).2]
    exact Nat.prod_primeFactors_dvd n.val
  have hfact (n : s) : n.val ∈ Nat.factoredNumbers Q :=
    Nat.mem_factoredNumbers_of_primeFactors_subset (hs n.val n.property).1
      (by rw [(hs n.val n.property).2])
  let f (n : s) : Nat.factoredNumbers Q :=
    ⟨n.val / d, Nat.mem_factoredNumbers_of_dvd (hfact n) (Nat.div_dvd_of_dvd (hdiv n))⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have heq : a.val / d = b.val / d := congrArg Subtype.val hab
    calc
      a.val = d * (a.val / d) := (Nat.mul_div_cancel' (hdiv a)).symm
      _ = d * (b.val / d) := by rw [heq]
      _ = b.val := Nat.mul_div_cancel' (hdiv b)
  have heq (n : s) : 1 / (n.val : ℝ) = (1 / (d : ℝ)) * (1 / ((f n).val : ℝ)) := by
    have hn : (n.val : ℝ) = (d : ℝ) * ((f n).val : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (hdiv n)).symm
    rw [hn]
    ring
  have hsum := (factored_reciprocal_hasSum Q hQ).mul_left (1 / (d : ℝ))
  have hle := Summable.tsum_le_tsum_of_inj f hf
    (fun n hn => by positivity : ∀ n ∉ Set.range f, 0 ≤ (1 / (d : ℝ)) * (1 / (n.val : ℝ)))
    (fun n => (heq n).le) Summable.of_finite hsum.summable
  rw [tsum_fintype, Finset.sum_coe_sort s (fun n : ℕ => 1 / (n : ℝ)), hsum.tsum_eq] at hle
  apply hle.trans_eq
  dsimp [d]
  rw [Nat.cast_prod, one_div, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hQ p hp).ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have hh : (1 : ℝ) < p := by exact_mod_cast (hQ p hp).one_lt
    linarith
  field_simp

noncomputable def smallDivisorFamily (P : Finset ℕ) (R : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun Q => ∏ p ∈ Q, p ≤ R)

theorem mem_smallDivisorFamily (P Q : Finset ℕ) (R : ℕ) :
    Q ∈ smallDivisorFamily P R ↔ Q ⊆ P ∧ (∏ p ∈ Q, p) ≤ R := by
  simp [smallDivisorFamily]

/-- Grouping positive integers by their radical gives a lower bound for the Selberg sum. -/
theorem reciprocal_sum_le_smallDivisorFamily (P s : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (R : ℕ)
    (hs : ∀ n ∈ s, 0 < n ∧ n ≤ R ∧ n.primeFactors ⊆ P) :
    (∑ n ∈ s, 1 / (n : ℝ)) ≤
      ∑ Q ∈ smallDivisorFamily P R, ∏ p ∈ Q, (1 / ((p : ℝ) - 1)) := by
  classical
  have hmap : ∀ n ∈ s, n.primeFactors ∈ smallDivisorFamily P R := by
    intro n hn
    rw [mem_smallDivisorFamily]
    exact ⟨(hs n hn).2.2,
      (Nat.le_of_dvd (hs n hn).1 (Nat.prod_primeFactors_dvd n)).trans (hs n hn).2.1⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun n => 1 / (n : ℝ))]
  apply Finset.sum_le_sum
  intro Q hQ
  have hQP := ((mem_smallDivisorFamily P Q R).mp hQ).1
  apply primeFactors_fiber_sum_le Q _ (fun p hp => hP p (hQP hp))
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  exact ⟨(hs n hn'.1).1.ne', hn'.2⟩

/-- If all primes up to the cutoff are present, the Selberg sum dominates the harmonic sum. -/
theorem harmonic_le_smallDivisorFamily (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (R : ℕ) (hfull : ∀ p, p.Prime → p ≤ R → p ∈ P) :
    (harmonic R : ℝ) ≤
      ∑ Q ∈ smallDivisorFamily P R, ∏ p ∈ Q, (1 / ((p : ℝ) - 1)) := by
  have hh := reciprocal_sum_le_smallDivisorFamily P (Finset.Icc 1 R) hP R (fun n hn => ?_)
  · simpa [harmonic_eq_sum_Icc, one_div] using hh
  · have hn' := Finset.mem_Icc.mp hn
    refine ⟨hn'.1, hn'.2, ?_⟩
    intro p hp
    have hpf := Nat.mem_primeFactors.mp hp
    exact hfull p hpf.1 ((Nat.le_of_dvd hn'.1 hpf.2.1).trans hn'.2)

section Finite

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem normalizer_eq_prime_sum (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (D : Finset (Finset ι)) :
    normalizer (fun i => 1 / (p i : ℝ)) D =
      ∑ T ∈ D, ∏ i ∈ T, (1 / ((p i : ℝ) - 1)) := by
  unfold normalizer variance
  apply Finset.sum_congr rfl
  intro T hT
  simp only [one_div, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  have hp0 : (p i : ℝ) ≠ 0 := by exact_mod_cast (hp i).ne_zero
  field_simp

theorem normalizer_eq_smallDivisorFamily (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) (R : ℕ) :
    normalizer (fun i => 1 / (p i : ℝ)) (divisorSupport p R) =
      ∑ Q ∈ smallDivisorFamily (Finset.univ.image p) R,
        ∏ a ∈ Q, (1 / ((a : ℝ) - 1)) := by
  classical
  rw [normalizer_eq_prime_sum p hp]
  apply Finset.sum_bij (fun T hT => T.image p)
  · intro T hT
    rw [mem_smallDivisorFamily]
    refine ⟨Finset.image_subset_image (Finset.subset_univ T), ?_⟩
    rw [Finset.prod_image hpinj.injOn]
    exact (mem_divisorSupport p R T).mp hT
  · intro A hA B hB hAB
    exact Finset.image_injective hpinj hAB
  · intro Q hQ
    obtain ⟨T, hT, heq⟩ := Finset.subset_image_iff.mp
      ((mem_smallDivisorFamily (Finset.univ.image p) Q R).mp hQ).1
    refine ⟨T, ?_, heq⟩
    rw [mem_divisorSupport]
    have hh := ((mem_smallDivisorFamily (Finset.univ.image p) Q R).mp hQ).2
    rw [← heq, Finset.prod_image hpinj.injOn] at hh
    exact hh
  · intro T hT
    exact (Finset.prod_image (f := fun a : ℕ => 1 / ((a : ℝ) - 1)) hpinj.injOn).symm

/-- The normalizer for a complete initial set of primes is at least the harmonic sum. -/
theorem harmonic_le_normalizer (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) (R : ℕ)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a) :
    (harmonic R : ℝ) ≤ normalizer (fun i => 1 / (p i : ℝ)) (divisorSupport p R) := by
  rw [normalizer_eq_smallDivisorFamily p hp hpinj R]
  apply harmonic_le_smallDivisorFamily
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact hp i
  · intro a ha haR
    obtain ⟨i, hi⟩ := hfull a ha haR
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩

/-- Explicit logarithmic Selberg upper bound for arbitrary prime residue classes. -/
theorem prime_survivors_le_log (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) (r : ℕ → ℕ) (m R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a) :
    (((Finset.range m).filter (fun j => ∀ i, ¬j ≡ r (p i) [MOD p i])).card : ℝ) ≤
      (m : ℝ) / Real.log (R + 1) + (R : ℝ)^2 := by
  apply (prime_survivors_le_cutoff p hp hpinj r m R hR).trans
  have hlog : 0 < Real.log (R + 1) := Real.log_pos (by exact_mod_cast Nat.lt_succ_of_le hR)
  have hnorm : Real.log (R + 1) ≤
      normalizer (fun i => 1 / (p i : ℝ)) (divisorSupport p R) :=
    (show Real.log (R + 1) ≤ (harmonic R : ℝ) by
      exact_mod_cast log_add_one_le_harmonic R).trans (harmonic_le_normalizer p hp hpinj R hfull)
  have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg m) hlog hnorm
  linarith

end Finite

#print axioms primeFactors_fiber_sum_le
#print axioms harmonic_le_normalizer
#print axioms prime_survivors_le_log

end Erdos970.FiniteSelberg
