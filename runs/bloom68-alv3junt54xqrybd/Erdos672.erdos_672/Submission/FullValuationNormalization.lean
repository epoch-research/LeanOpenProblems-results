import Submission.ArithmeticProgressions

/-!
# Full-valuation normalization of arithmetic-progression powers

This is a supporting theorem, not a proof of the Erdős 672 target. It imports
neither `Submission.Spec` nor any conjecture declaration.

At each prime, all off-peak valuations are placed in the numerator coefficients
and their sum in a single peak denominator. The full root exponent is placed
at that peak. Consequently the roots are pairwise coprime for every positive
exponent, while the common coefficient product still divides `(k - 1)!`.
No positivity hypothesis on the progression step is required.
-/

namespace Erdos672.Progression.FullValuation

open Finset

private def primeProd (P : Finset ℕ) (e : ℕ → ℕ) : ℕ := ∏ p ∈ P, p ^ e p

private lemma primeProd_ne_zero {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (e : ℕ → ℕ) :
    primeProd P e ≠ 0 := by
  exact prod_ne_zero_iff.2 (fun p hp => pow_ne_zero _ (hP p hp).ne_zero)

private lemma primeProd_factorization {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (e : ℕ → ℕ) (p : ℕ) :
    (primeProd P e).factorization p = if p ∈ P then e p else 0 := by
  classical
  calc
    _ = ∑ r ∈ P, (r ^ e r).factorization p :=
      Nat.factorization_prod_apply (fun r hr => pow_ne_zero _ (hP r hr).ne_zero)
    _ = ∑ r ∈ P, if r = p then e r else 0 := by
      apply sum_congr rfl
      intro r hr
      simp only [(hP r hr).factorization_pow, Finsupp.single_apply]
    _ = if p ∈ P then e p else 0 := sum_ite_eq' P p e

private lemma coprime_of_min_factorization_eq_zero {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p : ℕ, min (a.factorization p) (b.factorization p) = 0) : a.Coprime b := by
  apply Nat.coprime_iff_gcd_eq_one.2
  apply Nat.eq_of_factorization_eq
    (Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha)).ne' one_ne_zero
  intro p
  simpa only [Nat.factorization_gcd ha hb, Finsupp.inf_apply,
    Nat.factorization_one, Finsupp.zero_apply] using h p

/- The full off-peak valuations are moved to the peak denominator. At each
prime the root exponent is supported at just one index. -/
private structure ExponentBalance {k : ℕ} (l : ℕ) (a : Fin k → ℕ) (j : Fin k) where
  u : Fin k → ℕ
  v : Fin k → ℕ
  w : Fin k → ℕ
  R : ℕ
  equation : ∀ i, a i + v i = u i + l * w i
  sum_u : (∑ i, u i) = R
  sum_v : (∑ i, v i) = R
  disjoint_uv : ∀ i, min (u i) (v i) = 0
  disjoint_vv : ∀ i i', i ≠ i' → min (v i) (v i') = 0
  disjoint_ww : ∀ i i', i ≠ i' → min (w i) (w i') = 0
  off_peak_sum : R = ∑ i ∈ (univ : Finset (Fin k)).erase j, a i

private def balanceAtPeak {k l : ℕ} (a : Fin k → ℕ) (j : Fin k)
    (hdiv : l ∣ ∑ i, a i) : ExponentBalance l a j := by
  classical
  let R := ∑ i ∈ (univ : Finset (Fin k)).erase j, a i
  let u : Fin k → ℕ := fun i => if i = j then 0 else a i
  let v : Fin k → ℕ := fun i => if i = j then R else 0
  let w : Fin k → ℕ := fun i => if i = j then (∑ i, a i) / l else 0
  have hu : (∑ i, u i) = R := by
    rw [← sum_erase (univ : Finset (Fin k)) (show u j = 0 by simp [u])]
    apply sum_congr rfl
    intro i hi
    simp only [u, if_neg (mem_erase.mp hi).1]
  have hv : (∑ i, v i) = R := by
    simp only [v, sum_ite_eq', mem_univ, if_true]
  have htotal : a j + R = ∑ i, a i := by
    have hs := sum_erase_add (univ : Finset (Fin k)) a (mem_univ j)
    omega
  have heq : ∀ i, a i + v i = u i + l * w i := by
    intro i
    by_cases hi : i = j
    · subst i
      simpa only [u, v, w, if_pos rfl, zero_add, htotal] using
        (Nat.mul_div_cancel' hdiv).symm
    · simp [u, v, w, hi]
  have huv : ∀ i, min (u i) (v i) = 0 := by
    intro i
    by_cases hi : i = j <;> simp [u, v, hi]
  have hvv : ∀ i i', i ≠ i' → min (v i) (v i') = 0 := by
    intro i i' hii'
    by_cases hi : i = j
    · have hi' : i' ≠ j := fun h => hii' (hi.trans h.symm)
      simp [v, hi, hi']
    · simp [v, hi]
  have hww : ∀ i i', i ≠ i' → min (w i) (w i') = 0 := by
    intro i i' hii'
    by_cases hi : i = j
    · have hi' : i' ≠ j := fun h => hii' (hi.trans h.symm)
      simp [w, hi, hi']
    · simp [w, hi]
  exact {
    u := u, v := v, w := w, R := R
    equation := heq
    sum_u := hu
    sum_v := hv
    disjoint_uv := huv
    disjoint_vv := hvv
    disjoint_ww := hww
    off_peak_sum := rfl
  }

/-- Full-valuation coefficient/root normalization. This retains all conclusions
of `Progression.exists_coefficient_root_bundle` and additionally gives pairwise
coprime roots and `V i ∣ w i ^ l`.

For every prime of the product choose one term with maximal valuation. Moving
all other valuations to that term's denominator fits the factorial budget by
`Progression.off_peak_sum_le_factorial`. Only the chosen term receives a root
exponent for that prime, so distinct roots share no prime factor. -/
theorem exists_full_coefficient_root_bundle {n d k l q : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hcop : n.gcd d = 1) (hl : 0 < l)
    (hpower : (∏ i : Fin k, (n + i.val * d)) = q ^ l) :
    ∃ U V w : Fin k → ℕ, ∃ D : ℕ,
      (∀ i, 0 < U i) ∧ (∀ i, 0 < V i) ∧ (∀ i, 0 < w i) ∧ 0 < D ∧
      (∀ i, V i * (n + i.val * d) = U i * w i ^ l) ∧
      (∀ i, (U i).gcd (V i) = 1) ∧
      (∏ i, U i) = D ∧ (∏ i, V i) = D ∧ D ∣ (k - 1).factorial ∧
      Pairwise (fun i j => (V i).Coprime (V j)) ∧
      (∏ i, w i) = q ∧
      (∀ i j, ((w i).gcd (w j)) ^ l ∣ Nat.dist i.val j.val) ∧
      Pairwise (fun i j => (w i).Coprime (w j)) ∧
      (∀ i, V i ∣ w i ^ l) := by
  classical
  let t : Fin k → ℕ := fun i => term n d i.val
  let T := ∏ i, t i
  let a : ℕ → Fin k → ℕ := fun p i => (t i).factorization p
  have htpos : ∀ i, 0 < t i := fun i => term_pos hn i.val
  have hTpos : 0 < T := prod_pos (fun i _ => htpos i)
  have hTpower : T = q ^ l := hpower
  have hatotal : ∀ p, T.factorization p = ∑ i, a p i := fun p =>
    factorization_product_terms hn k p
  have hadiv : ∀ p, l ∣ ∑ i, a p i := by
    intro p
    rw [← hatotal p, hTpower]
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  have hmaxexists : ∀ p : ℕ, ∃ j : Fin k, ∀ i : Fin k, a p i ≤ a p j := by
    intro p
    obtain ⟨j, _, hj⟩ := exists_max_image (univ : Finset (Fin k)) (a p)
      ⟨⟨0, hk⟩, mem_univ _⟩
    exact ⟨j, fun i => hj i (mem_univ i)⟩
  choose peak hpeak using hmaxexists
  let B : (p : ℕ) → ExponentBalance l (a p) (peak p) :=
    fun p => balanceAtPeak (a p) (peak p) (hadiv p)
  have hbudget : ∀ p, (B p).R ≤ (k - 1).factorial.factorization p := by
    intro p
    rw [(B p).off_peak_sum]
    exact off_peak_sum_le_factorial hn hcop p (peak p) (hpeak p)
  let P := T.primeFactors
  have hP : ∀ p ∈ P, p.Prime := fun _ hp => Nat.prime_of_mem_primeFactors hp
  have haout : ∀ p, p ∉ P → ∀ i, a p i = 0 := by
    intro p hp i
    have hzero : T.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    have hi : a p i ≤ T.factorization p :=
      (Nat.factorization_le_iff_dvd (htpos i).ne' hTpos.ne').2
        (dvd_prod_of_mem t (mem_univ i)) p
    rw [hzero] at hi
    exact Nat.le_zero.mp hi
  let U : Fin k → ℕ := fun i => primeProd P (fun p => (B p).u i)
  let V : Fin k → ℕ := fun i => primeProd P (fun p => (B p).v i)
  let w : Fin k → ℕ := fun i => primeProd P (fun p => (B p).w i)
  let D := primeProd P (fun p => (B p).R)
  have hUpos : ∀ i, 0 < U i := fun _ => Nat.pos_of_ne_zero (primeProd_ne_zero hP _)
  have hVpos : ∀ i, 0 < V i := fun _ => Nat.pos_of_ne_zero (primeProd_ne_zero hP _)
  have hwpos : ∀ i, 0 < w i := fun _ => Nat.pos_of_ne_zero (primeProd_ne_zero hP _)
  have hDpos : 0 < D := Nat.pos_of_ne_zero (primeProd_ne_zero hP _)
  have hUf : ∀ p i, (U i).factorization p = if p ∈ P then (B p).u i else 0 :=
    fun _ _ => primeProd_factorization hP _ _
  have hVf : ∀ p i, (V i).factorization p = if p ∈ P then (B p).v i else 0 :=
    fun _ _ => primeProd_factorization hP _ _
  have hwf : ∀ p i, (w i).factorization p = if p ∈ P then (B p).w i else 0 :=
    fun _ _ => primeProd_factorization hP _ _
  have hDf : ∀ p, D.factorization p = if p ∈ P then (B p).R else 0 :=
    fun _ => primeProd_factorization hP _ _
  have hUprod : (∏ i, U i) = D := by
    apply Nat.eq_of_factorization_eq (prod_ne_zero_iff.2 (fun i _ => (hUpos i).ne')) hDpos.ne'
    intro p
    rw [Nat.factorization_prod_apply (fun i _ => (hUpos i).ne'), hDf p]
    by_cases hp : p ∈ P
    · simpa only [hUf, hp, if_true] using (B p).sum_u
    · simp only [hUf, hp, if_false, sum_const_zero]
  have hVprod : (∏ i, V i) = D := by
    apply Nat.eq_of_factorization_eq (prod_ne_zero_iff.2 (fun i _ => (hVpos i).ne')) hDpos.ne'
    intro p
    rw [Nat.factorization_prod_apply (fun i _ => (hVpos i).ne'), hDf p]
    by_cases hp : p ∈ P
    · simpa only [hVf, hp, if_true] using (B p).sum_v
    · simp only [hVf, hp, if_false, sum_const_zero]
  have hDdvd : D ∣ (k - 1).factorial := by
    apply (Nat.factorization_le_iff_dvd hDpos.ne' (Nat.factorial_ne_zero _)).1
    intro p
    rw [hDf p]
    split_ifs
    · exact hbudget p
    · exact zero_le _
  have heq : ∀ i, V i * t i = U i * w i ^ l := by
    intro i
    apply Nat.eq_of_factorization_eq (mul_ne_zero (hVpos i).ne' (htpos i).ne')
      (mul_ne_zero (hUpos i).ne' (pow_ne_zero l (hwpos i).ne'))
    intro p
    rw [Nat.factorization_mul (hVpos i).ne' (htpos i).ne',
      Nat.factorization_mul (hUpos i).ne' (pow_ne_zero l (hwpos i).ne'),
      Nat.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [hVf p i, hUf p i, hwf p i]
    by_cases hp : p ∈ P
    · simpa only [hp, if_true, add_comm] using (B p).equation i
    · simpa only [hp, if_false, zero_add, mul_zero, add_zero] using haout p hp i
  have hUV : ∀ i, (U i).gcd (V i) = 1 := by
    intro i
    apply Nat.coprime_iff_gcd_eq_one.1
    apply coprime_of_min_factorization_eq_zero (hUpos i).ne' (hVpos i).ne'
    intro p
    rw [hUf p i, hVf p i]
    split_ifs
    · exact (B p).disjoint_uv i
    · exact min_self 0
  have hVV : Pairwise (fun i j => (V i).Coprime (V j)) := by
    intro i j hij
    apply coprime_of_min_factorization_eq_zero (hVpos i).ne' (hVpos j).ne'
    intro p
    rw [hVf p i, hVf p j]
    split_ifs
    · exact (B p).disjoint_vv i j hij
    · exact min_self 0
  have hwprod : (∏ i, w i) = q := by
    have hp : (∏ i, V i * t i) = ∏ i, U i * w i ^ l :=
      prod_congr rfl (fun i _ => heq i)
    rw [prod_mul_distrib, prod_mul_distrib, prod_pow, hUprod, hVprod] at hp
    have hpow : T = (∏ i, w i) ^ l := Nat.mul_left_cancel hDpos hp
    exact Nat.pow_left_injective hl.ne' (hpow.symm.trans hTpower)
  have hww : Pairwise (fun i j => (w i).Coprime (w j)) := by
    intro i j hij
    apply coprime_of_min_factorization_eq_zero (hwpos i).ne' (hwpos j).ne'
    intro p
    rw [hwf p i, hwf p j]
    split_ifs
    · exact (B p).disjoint_ww i j hij
    · exact min_self 0
  have hwgcd : ∀ i j, ((w i).gcd (w j)) ^ l ∣ Nat.dist i.val j.val := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [Nat.dist_self, dvd_zero]
    · rw [Nat.coprime_iff_gcd_eq_one.1 (hww hij), one_pow]
      exact one_dvd _
  have hVdvd : ∀ i, V i ∣ w i ^ l := by
    intro i
    have hc : (V i).Coprime (U i) := (Nat.coprime_iff_gcd_eq_one.2 (hUV i)).symm
    apply hc.dvd_mul_left.mp
    rw [← heq i]
    exact dvd_mul_right _ _
  refine ⟨U, V, w, D, hUpos, hVpos, hwpos, hDpos, ?_, hUV,
    hUprod, hVprod, hDdvd, hVV, hwprod, hwgcd, hww, hVdvd⟩
  exact heq

/-- The same bundle theorem with a product over `range k` as input. -/
theorem exists_full_coefficient_root_bundle_range {n d k l q : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hcop : n.gcd d = 1) (hl : 0 < l)
    (hpower : (∏ i ∈ range k, (n + i * d)) = q ^ l) :
    ∃ U V w : Fin k → ℕ, ∃ D : ℕ,
      (∀ i, 0 < U i) ∧ (∀ i, 0 < V i) ∧ (∀ i, 0 < w i) ∧ 0 < D ∧
      (∀ i, V i * (n + i.val * d) = U i * w i ^ l) ∧
      (∀ i, (U i).gcd (V i) = 1) ∧
      (∏ i, U i) = D ∧ (∏ i, V i) = D ∧ D ∣ (k - 1).factorial ∧
      Pairwise (fun i j => (V i).Coprime (V j)) ∧
      (∏ i, w i) = q ∧
      (∀ i j, ((w i).gcd (w j)) ^ l ∣ Nat.dist i.val j.val) ∧
      Pairwise (fun i j => (w i).Coprime (w j)) ∧
      (∀ i, V i ∣ w i ^ l) := by
  apply exists_full_coefficient_root_bundle hn hk hcop hl
  exact (Fin.prod_univ_eq_prod_range (fun i : ℕ => n + i * d) k).trans hpower

/- ## Verified examples -/

/-- The full theorem applies to `18, 25, 32`, whose product is `120²`. -/
theorem example_18_25_32 :
    ∃ U V w : Fin 3 → ℕ, ∃ D : ℕ,
      (∀ i, 0 < U i) ∧ (∀ i, 0 < V i) ∧ (∀ i, 0 < w i) ∧ 0 < D ∧
      (∀ i, V i * (18 + i.val * 7) = U i * w i ^ 2) ∧
      (∀ i, (U i).gcd (V i) = 1) ∧
      (∏ i, U i) = D ∧ (∏ i, V i) = D ∧ D ∣ 2 ∧
      Pairwise (fun i j => (V i).Coprime (V j)) ∧
      (∏ i, w i) = 120 ∧
      (∀ i j, ((w i).gcd (w j)) ^ 2 ∣ Nat.dist i.val j.val) ∧
      Pairwise (fun i j => (w i).Coprime (w j)) ∧
      (∀ i, V i ∣ w i ^ 2) := by
  have hp : (∏ i : Fin 3, (18 + i.val * 7)) = 120 ^ 2 := by
    norm_num [Fin.prod_univ_three]
  simpa using exists_full_coefficient_root_bundle (by norm_num : 0 < 18)
    (by norm_num : 0 < 3) (by norm_num : Nat.gcd 18 7 = 1)
    (by norm_num : 0 < 2) hp

/-- Concrete full-valuation witnesses: `U = (2,1,1)`, `V = (1,1,2)`,
`w = (3,5,8)`, and `D = 2`. In particular the actual roots are pairwise coprime. -/
theorem example_18_25_32_explicit :
    let U : Fin 3 → ℕ := ![2, 1, 1]
    let V : Fin 3 → ℕ := ![1, 1, 2]
    let w : Fin 3 → ℕ := ![3, 5, 8]
    (∀ i, 0 < U i) ∧ (∀ i, 0 < V i) ∧ (∀ i, 0 < w i) ∧ 0 < (2 : ℕ) ∧
      (∀ i, V i * (18 + i.val * 7) = U i * w i ^ 2) ∧
      (∀ i, (U i).gcd (V i) = 1) ∧
      (∏ i, U i) = 2 ∧ (∏ i, V i) = 2 ∧ 2 ∣ (3 - 1).factorial ∧
      Pairwise (fun i j => (V i).Coprime (V j)) ∧
      (∏ i, w i) = 120 ∧
      (∀ i j, ((w i).gcd (w j)) ^ 2 ∣ Nat.dist i.val j.val) ∧
      Pairwise (fun i j => (w i).Coprime (w j)) ∧
      (∀ i, V i ∣ w i ^ 2) := by
  norm_num [Pairwise, Fin.forall_fin_succ, Fin.prod_univ_three, Nat.Coprime, Nat.dist]
  decide

/-- The endpoint `k = l = 1` and zero step requires no extra hypotheses. -/
example : ∃ D : ℕ, 0 < D ∧ D ∣ Nat.factorial 0 := by
  have hp : (∏ i : Fin 1, (1 + i.val * 0)) = 1 ^ 1 := by simp
  obtain ⟨U, V, w, D, _, _, _, hD, _, _, _, _, hDdvd, _, _, _, _, _⟩ :=
    exists_full_coefficient_root_bundle (by norm_num : 0 < 1)
      (by norm_num : 0 < 1) (by norm_num : Nat.gcd 1 0 = 1)
      (by norm_num : 0 < 1) hp
  exact ⟨D, hD, hDdvd⟩

/-- Pairwise-coprime roots also exist for exponent one. -/
example : ∃ w : Fin 3 → ℕ,
    (∀ i, 0 < w i) ∧ (∏ i, w i) = 14400 ∧
      Pairwise (fun i j => (w i).Coprime (w j)) := by
  have hp : (∏ i : Fin 3, (18 + i.val * 7)) = 14400 ^ 1 := by
    norm_num [Fin.prod_univ_three]
  obtain ⟨U, V, w, D, _, _, hwpos, _, _, _, _, _, _, _, hwprod, _, hww, _⟩ :=
    exists_full_coefficient_root_bundle (by norm_num : 0 < 18)
      (by norm_num : 0 < 3) (by norm_num : Nat.gcd 18 7 = 1)
      (by norm_num : 0 < 1) hp
  exact ⟨w, hwpos, hwprod, hww⟩

/-- Zero step with coprime initial term is covered even for several terms
and a nontrivial exponent. -/
example : ∃ w : Fin 3 → ℕ,
    (∀ i, 0 < w i) ∧ (∏ i, w i) = 1 ∧
      Pairwise (fun i j => (w i).Coprime (w j)) := by
  have hp : (∏ i : Fin 3, (1 + i.val * 0)) = 1 ^ 2 := by simp
  obtain ⟨U, V, w, D, _, _, hwpos, _, _, _, _, _, _, _, hwprod, _, hww, _⟩ :=
    exists_full_coefficient_root_bundle (by norm_num : 0 < 1)
      (by norm_num : 0 < 3) (by norm_num : Nat.gcd 1 0 = 1)
      (by norm_num : 0 < 2) hp
  exact ⟨w, hwpos, hwprod, hww⟩

end Erdos672.Progression.FullValuation

namespace Erdos672.Progression

-- Convenient public aliases; the proof implementation remains in `FullValuation`.
export FullValuation (exists_full_coefficient_root_bundle
  exists_full_coefficient_root_bundle_range)

end Erdos672.Progression
