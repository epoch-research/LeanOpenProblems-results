import FormalConjecturesUtil
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Arithmetic-progression power decompositions

This file is independent of the conjecture declarations in `Submission.Spec`.
For a coprime positive arithmetic progression whose product is an `l`-th power,
we construct reduced rational coefficients with a common factorial budget,
and positive roots whose pairwise common factors have controlled `l`-th powers.
-/

namespace Erdos672.Progression

open Finset

/-- The `i`-th term of the progression, indexed from zero. -/
def term (n d i : ℕ) : ℕ := n + i * d

lemma term_pos {n d : ℕ} (hn : 0 < n) (i : ℕ) : 0 < term n d i := by
  unfold term
  omega

lemma term_coprime_step {n d : ℕ} (hcop : n.Coprime d) (i : ℕ) :
    (term n d i).Coprime d := by
  simpa [term] using (Nat.coprime_add_mul_right_left n d i).2 hcop

private lemma gcd_term_sub {n d i j : ℕ} (hcop : n.Coprime d) (hij : i ≤ j) :
    (term n d i).gcd (term n d j) = (term n d i).gcd (j - i) := by
  have hterm : term n d j = (j - i) * d + term n d i := by
    unfold term
    rw [Nat.sub_mul]
    have : i * d ≤ j * d := Nat.mul_le_mul_right d hij
    omega
  rw [hterm, Nat.gcd_add_self_right]
  exact (term_coprime_step hcop i).symm.gcd_mul_right_cancel_right (j - i)

/-- The gcd of two progression terms is their gcd with the index distance. -/
theorem gcd_terms_eq_gcd_distance {n d : ℕ} (hcop : n.Coprime d) (i j : ℕ) :
    (term n d i).gcd (term n d j) = (term n d i).gcd (Nat.dist i j) := by
  rcases le_total i j with hij | hji
  · rw [Nat.dist_eq_sub_of_le hij]
    exact gcd_term_sub hcop hij
  · have hterm : term n d i = (i - j) * d + term n d j := by
      unfold term
      rw [Nat.sub_mul]
      have : j * d ≤ i * d := Nat.mul_le_mul_right d hji
      omega
    rw [Nat.dist_eq_sub_of_le_right hji, hterm, Nat.gcd_add_self_left]
    rw [Nat.gcd_mul_left_add_left, Nat.gcd_comm ((i - j) * d)]
    exact (term_coprime_step hcop j).symm.gcd_mul_right_cancel_right (i - j)

/-- In particular, a common divisor of two terms divides the index distance. -/
lemma gcd_terms_dvd_distance {n d : ℕ} (hcop : n.Coprime d) (i j : ℕ) :
    (term n d i).gcd (term n d j) ∣ Nat.dist i j := by
  rw [gcd_terms_eq_gcd_distance hcop]
  exact Nat.gcd_dvd_right _ _

/-- A valuation form of the gcd-distance bound. -/
lemma min_factorization_le_distance {n d : ℕ} (hn : 0 < n) (hcop : n.Coprime d)
    {i j : ℕ} (hij : i ≠ j) (p : ℕ) :
    min ((term n d i).factorization p) ((term n d j).factorization p) ≤
      (Nat.dist i j).factorization p := by
  have hi := (term_pos (d := d) hn i).ne'
  have hj := (term_pos (d := d) hn j).ne'
  have hg : (term n d i).gcd (term n d j) ≠ 0 :=
    (Nat.gcd_pos_of_pos_left _ (term_pos (d := d) hn i)).ne'
  have hd := (Nat.dist_pos_of_ne hij).ne'
  have h := (Nat.factorization_le_iff_dvd hg hd).2 (gcd_terms_dvd_distance hcop i j)
  simpa only [Nat.factorization_gcd hi hj, Finsupp.inf_apply] using h p

/-- Relative to a term of maximal valuation, every other valuation is the minimum
of that maximal valuation and the valuation of the index distance. -/
lemma off_peak_factorization {n d : ℕ} (hn : 0 < n) (hcop : n.Coprime d)
    {i j : ℕ} (hij : i ≠ j) (p : ℕ)
    (hmax : (term n d i).factorization p ≤ (term n d j).factorization p) :
    (term n d i).factorization p =
      min ((term n d j).factorization p) ((Nat.dist i j).factorization p) := by
  have h := congrArg (fun x : ℕ => x.factorization p)
    (gcd_terms_eq_gcd_distance hcop j i)
  change ((term n d j).gcd (term n d i)).factorization p =
    ((term n d j).gcd (Nat.dist j i)).factorization p at h
  rw [Nat.factorization_gcd (term_pos (d := d) hn j).ne' (term_pos (d := d) hn i).ne',
    Nat.factorization_gcd (term_pos (d := d) hn j).ne'
      (Nat.dist_pos_of_ne hij.symm).ne'] at h
  simpa only [Finsupp.inf_apply, min_eq_right hmax, Nat.dist_comm] using h

private lemma distance_product_range {k j : ℕ} (hj : j < k) :
    (∏ i ∈ range k, if i = j then 1 else Nat.dist i j) =
      j.factorial * (k - 1 - j).factorial := by
  have hleft : (∏ i ∈ range j, if i = j then 1 else Nat.dist i j) = j.factorial := by
    calc
      _ = ∏ i ∈ range j, ((j - 1 - i) + 1) := by
        apply prod_congr rfl
        intro i hi
        have hi' := mem_range.mp hi
        rw [if_neg (by omega), Nat.dist_eq_sub_of_le (by omega)]
        omega
      _ = ∏ i ∈ range j, (i + 1) := prod_range_reflect (fun i : ℕ => i + 1) j
      _ = j.factorial := prod_range_add_one_eq_factorial j
  have hright :
      (∏ i ∈ range (k - 1 - j),
        if j + 1 + i = j then 1 else Nat.dist (j + 1 + i) j) =
        (k - 1 - j).factorial := by
    calc
      _ = ∏ i ∈ range (k - 1 - j), (i + 1) := by
        apply prod_congr rfl
        intro i _
        rw [if_neg (by omega), Nat.dist_eq_sub_of_le_right (by omega)]
        omega
      _ = (k - 1 - j).factorial := prod_range_add_one_eq_factorial _
  calc
    _ = (∏ i ∈ range (j + 1), if i = j then 1 else Nat.dist i j) *
        ∏ i ∈ range (k - 1 - j),
          if j + 1 + i = j then 1 else Nat.dist (j + 1 + i) j := by
      have hk : k = (j + 1) + (k - 1 - j) := by omega
      conv_lhs => rw [hk]
      rw [prod_range_add]
    _ = j.factorial * (k - 1 - j).factorial := by
      rw [prod_range_succ, if_pos rfl, mul_one, hleft, hright]

/-- The product of distances from a fixed index to all the other indices. -/
theorem distance_product {k : ℕ} (j : Fin k) :
    (∏ i ∈ (univ : Finset (Fin k)).erase j, Nat.dist i.val j.val) =
      j.val.factorial * (k - 1 - j.val).factorial := by
  calc
    _ = ∏ i ∈ (univ : Finset (Fin k)).erase j,
        if i = j then 1 else Nat.dist i.val j.val := by
      apply prod_congr rfl
      intro i hi
      rw [if_neg (mem_erase.mp hi).1]
    _ = ∏ i : Fin k, if i = j then 1 else Nat.dist i.val j.val :=
      prod_erase _ (if_pos rfl)
    _ = ∏ i : Fin k, if i.val = j.val then 1 else Nat.dist i.val j.val := by
      simp only [Fin.val_inj]
    _ = ∏ i ∈ range k, if i = j.val then 1 else Nat.dist i j.val :=
      Fin.prod_univ_eq_prod_range (fun i : ℕ => if i = j.val then 1 else Nat.dist i j.val) k
    _ = j.val.factorial * (k - 1 - j.val).factorial := distance_product_range j.isLt

/-- The distance product has the factorial budget `(k - 1)!`. -/
lemma distance_product_dvd_factorial {k : ℕ} (j : Fin k) :
    (∏ i ∈ (univ : Finset (Fin k)).erase j, Nat.dist i.val j.val) ∣
      (k - 1).factorial := by
  rw [distance_product]
  exact Nat.factorial_mul_factorial_dvd_factorial (by omega)

/-- The sum of the off-peak valuations fits within the factorial budget. -/
lemma off_peak_sum_le_factorial {n d k : ℕ} (hn : 0 < n) (hcop : n.Coprime d)
    (p : ℕ) (j : Fin k)
    (hmax : ∀ i : Fin k, (term n d i.val).factorization p ≤
      (term n d j.val).factorization p) :
    (∑ i ∈ (univ : Finset (Fin k)).erase j, (term n d i.val).factorization p) ≤
      (k - 1).factorial.factorization p := by
  have hd : ∀ i ∈ (univ : Finset (Fin k)).erase j, Nat.dist i.val j.val ≠ 0 := by
    intro i hi
    exact (Nat.dist_pos_of_ne ((Fin.ne_iff_vne i j).mp (mem_erase.mp hi).1)).ne'
  calc
    _ ≤ ∑ i ∈ (univ : Finset (Fin k)).erase j, (Nat.dist i.val j.val).factorization p := by
      apply sum_le_sum
      intro i hi
      have hij : i.val ≠ j.val := (Fin.ne_iff_vne i j).mp (mem_erase.mp hi).1
      have h := min_factorization_le_distance hn hcop hij p
      simpa only [min_eq_left (hmax i)] using h
    _ = (∏ i ∈ (univ : Finset (Fin k)).erase j,
        Nat.dist i.val j.val).factorization p := (Nat.factorization_prod_apply hd).symm
    _ ≤ (k - 1).factorial.factorization p :=
      (Nat.factorization_le_iff_dvd (prod_ne_zero_iff.2 hd) (Nat.factorial_ne_zero _)).2
        (distance_product_dvd_factorial j) p

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

/- The following data are the arithmetic performed separately at each prime.
The off-peak remainders are moved to the single peak denominator. -/
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
  budget : R ≤ ∑ i ∈ (univ : Finset (Fin k)).erase j, a i
  common_roots : ∀ i i', i ≠ i' → l * min (w i) (w i') ≤ min (a i) (a i')

private def balanceAtPeak {k l : ℕ} (a : Fin k → ℕ) (j : Fin k)
    (hmax : ∀ i, a i ≤ a j) (hdiv : l ∣ ∑ i, a i) : ExponentBalance l a j := by
  classical
  let R := ∑ i ∈ (univ : Finset (Fin k)).erase j, a i % l
  let u : Fin k → ℕ := fun i => if i = j then 0 else a i % l
  let v : Fin k → ℕ := fun i => if i = j then R else 0
  let w : Fin k → ℕ := fun i => if i = j then (a i + R) / l else a i / l
  have hu : (∑ i, u i) = R := by
    rw [← sum_erase (univ : Finset (Fin k)) (show u j = 0 by simp [u])]
    apply sum_congr rfl
    intro i hi
    simp only [u, if_neg (mem_erase.mp hi).1]
  have hv : (∑ i, v i) = R := by
    simp only [v, sum_ite_eq', mem_univ, if_true]
  have hoff : (∑ i ∈ (univ : Finset (Fin k)).erase j, a i) =
      R + l * ∑ i ∈ (univ : Finset (Fin k)).erase j, a i / l := by
    calc
      _ = ∑ i ∈ (univ : Finset (Fin k)).erase j, (a i % l + l * (a i / l)) :=
        sum_congr rfl (fun i _ => (Nat.mod_add_div (a i) l).symm)
      _ = _ := by rw [sum_add_distrib, mul_sum]
  have htotal : (∑ i, a i) =
      (a j + R) + l * ∑ i ∈ (univ : Finset (Fin k)).erase j, a i / l := by
    have hs := sum_erase_add (univ : Finset (Fin k)) a (mem_univ j)
    omega
  have hpeak : l ∣ a j + R := by
    have hs := Nat.dvd_sub hdiv
      (dvd_mul_right l (∑ i ∈ (univ : Finset (Fin k)).erase j, a i / l))
    have he : (∑ i, a i) - l * (∑ i ∈ (univ : Finset (Fin k)).erase j, a i / l) =
        a j + R := by omega
    rwa [he] at hs
  have heq : ∀ i, a i + v i = u i + l * w i := by
    intro i
    by_cases hi : i = j
    · subst i
      simpa only [u, v, w, if_pos rfl, zero_add] using (Nat.mul_div_cancel' hpeak).symm
    · simpa only [u, v, w, if_neg hi, add_zero] using (Nat.mod_add_div (a i) l).symm
  have huv : ∀ i, min (u i) (v i) = 0 := by
    intro i
    by_cases hi : i = j <;> simp [u, v, hi]
  have hvv : ∀ i i', i ≠ i' → min (v i) (v i') = 0 := by
    intro i i' hii'
    by_cases hi : i = j
    · have hi' : i' ≠ j := fun h => hii' (hi.trans h.symm)
      simp [v, hi, hi']
    · simp [v, hi]
  have hw : ∀ i, i ≠ j → l * w i ≤ a i := by
    intro i hi
    simpa only [w, if_neg hi] using Nat.mul_div_le (a i) l
  have hcommon_left : ∀ i i', i ≠ i' → l * min (w i) (w i') ≤ a i := by
    intro i i' hii'
    by_cases hi : i = j
    · have hi' : i' ≠ j := fun h => hii' (hi.trans h.symm)
      exact (Nat.mul_le_mul_left l (min_le_right _ _)).trans
        ((hw i' hi').trans (by simpa only [hi] using hmax i'))
    · exact (Nat.mul_le_mul_left l (min_le_left _ _)).trans (hw i hi)
  have hcommon : ∀ i i', i ≠ i' → l * min (w i) (w i') ≤ min (a i) (a i') := by
    intro i i' hii'
    exact le_min (hcommon_left i i' hii')
      (by simpa only [min_comm] using hcommon_left i' i hii'.symm)
  exact {
    u := u, v := v, w := w, R := R
    equation := heq
    sum_u := hu
    sum_v := hv
    disjoint_uv := huv
    disjoint_vv := hvv
    budget := sum_le_sum (fun i _ => Nat.mod_le (a i) l)
    common_roots := hcommon
  }

/-- A progression with positive first term has a positive product. -/
lemma product_terms_pos {n d : ℕ} (hn : 0 < n) (k : ℕ) :
    0 < ∏ i : Fin k, term n d i.val :=
  prod_pos (fun i _ => term_pos hn i.val)

/-- Prime exponents add across the product of the progression. -/
lemma factorization_product_terms {n d : ℕ} (hn : 0 < n) (k p : ℕ) :
    (∏ i : Fin k, term n d i.val).factorization p =
      ∑ i : Fin k, (term n d i.val).factorization p :=
  Nat.factorization_prod_apply (fun i _ => (term_pos hn i.val).ne')

/-- Coefficient/root decomposition of a progression whose product is a power.

For each prime of the product, choose a term of maximal valuation. The off-peak
remainders modulo `l` are the numerator exponents, and their sum is the sole
peak denominator exponent. The common coefficient product divides `(k - 1)!`.
No positivity assumption on `d` is needed for this decomposition. -/
theorem exists_coefficient_root_bundle {n d k l q : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hcop : n.gcd d = 1) (hl : 0 < l)
    (hpower : (∏ i : Fin k, (n + i.val * d)) = q ^ l) :
    ∃ U V w : Fin k → ℕ, ∃ D : ℕ,
      (∀ i, 0 < U i) ∧ (∀ i, 0 < V i) ∧ (∀ i, 0 < w i) ∧ 0 < D ∧
      (∀ i, V i * (n + i.val * d) = U i * w i ^ l) ∧
      (∀ i, (U i).gcd (V i) = 1) ∧
      (∏ i, U i) = D ∧ (∏ i, V i) = D ∧ D ∣ (k - 1).factorial ∧
      Pairwise (fun i j => (V i).Coprime (V j)) ∧
      (∏ i, w i) = q ∧
      (∀ i j, ((w i).gcd (w j)) ^ l ∣ Nat.dist i.val j.val) := by
  classical
  let t : Fin k → ℕ := fun i => term n d i.val
  let T := ∏ i, t i
  let a : ℕ → Fin k → ℕ := fun p i => (t i).factorization p
  have htpos : ∀ i, 0 < t i := fun i => term_pos hn i.val
  have hTpos : 0 < T := prod_pos (fun i _ => htpos i)
  have hTpower : T = q ^ l := hpower
  have hatotal : ∀ p, T.factorization p = ∑ i, a p i := fun _ =>
    Nat.factorization_prod_apply (fun i _ => (htpos i).ne')
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
    fun p => balanceAtPeak (a p) (peak p) (hpeak p) (hadiv p)
  have hbudget : ∀ p, (B p).R ≤ (k - 1).factorial.factorization p := by
    intro p
    exact (B p).budget.trans (off_peak_sum_le_factorial hn hcop p (peak p) (hpeak p))
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
  have hwgcd : ∀ i j, ((w i).gcd (w j)) ^ l ∣ Nat.dist i.val j.val := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [Nat.dist_self, dvd_zero]
    · have hd : Nat.dist i.val j.val ≠ 0 :=
        (Nat.dist_pos_of_ne ((Fin.ne_iff_vne i j).mp hij)).ne'
      have hg : (w i).gcd (w j) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (hwpos i)).ne'
      apply (Nat.factorization_le_iff_dvd (pow_ne_zero l hg) hd).1
      intro p
      rw [Nat.factorization_pow, Nat.factorization_gcd (hwpos i).ne' (hwpos j).ne']
      simp only [Finsupp.smul_apply, Finsupp.inf_apply, smul_eq_mul]
      rw [hwf p i, hwf p j]
      by_cases hp : p ∈ P
      · simp only [hp, if_true]
        exact ((B p).common_roots i j hij).trans
          (min_factorization_le_distance hn hcop ((Fin.ne_iff_vne i j).mp hij) p)
      · simp only [hp, if_false, min_self, mul_zero, zero_le]
  refine ⟨U, V, w, D, hUpos, hVpos, hwpos, hDpos, ?_, hUV,
    hUprod, hVprod, hDdvd, hVV, hwprod, hwgcd⟩
  exact heq

/-- The same bundle theorem with a product over `range k` as input. -/
theorem exists_coefficient_root_bundle_range {n d k l q : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hcop : n.gcd d = 1) (hl : 0 < l)
    (hpower : (∏ i ∈ range k, (n + i * d)) = q ^ l) :
    ∃ U V w : Fin k → ℕ, ∃ D : ℕ,
      (∀ i, 0 < U i) ∧ (∀ i, 0 < V i) ∧ (∀ i, 0 < w i) ∧ 0 < D ∧
      (∀ i, V i * (n + i.val * d) = U i * w i ^ l) ∧
      (∀ i, (U i).gcd (V i) = 1) ∧
      (∏ i, U i) = D ∧ (∏ i, V i) = D ∧ D ∣ (k - 1).factorial ∧
      Pairwise (fun i j => (V i).Coprime (V j)) ∧
      (∏ i, w i) = q ∧
      (∀ i j, ((w i).gcd (w j)) ^ l ∣ Nat.dist i.val j.val) := by
  apply exists_coefficient_root_bundle hn hk hcop hl
  exact (Fin.prod_univ_eq_prod_range (fun i : ℕ => n + i * d) k).trans hpower

/- ## Canonical finite progressions and the finite-set formulation -/

/-- The finite set `{n, n + d, ..., n + (k - 1)d}`. -/
def canonicalFinset (n d k : ℕ) : Finset ℕ := (range k).image (term n d)

lemma term_injective (n : ℕ) {d : ℕ} (hd : 0 < d) : Function.Injective (term n d) := by
  intro i j hij
  exact Nat.mul_right_cancel hd (Nat.add_left_cancel hij)

lemma canonicalFinset_card (n k : ℕ) {d : ℕ} (hd : 0 < d) :
    (canonicalFinset n d k).card = k := by
  rw [canonicalFinset, card_image_of_injective _ (term_injective n hd), card_range]

lemma mem_canonicalFinset {n d k x : ℕ} :
    x ∈ canonicalFinset n d k ↔ ∃ i < k, n + i * d = x := by
  simp only [canonicalFinset, mem_image, mem_range, term]

/-- The canonical finite progression satisfies the library's AP predicate. -/
theorem canonicalFinset_isAP (n k : ℕ) {d : ℕ} (hd : 0 < d) :
    Set.IsAPOfLengthWith (canonicalFinset n d k : Set ℕ) k n d := by
  constructor
  · simp only [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
      canonicalFinset_card n k hd]
  · ext x
    simp only [mem_coe, mem_canonicalFinset, Set.mem_setOf_eq, ENat.coe_lt_coe,
      nsmul_eq_mul, Nat.cast_id, exists_prop]

/-- The set equality in the AP predicate identifies the canonical finite set. -/
lemma finset_eq_canonical {n d k : ℕ} {s : Finset ℕ}
    (hAP : Set.IsAPOfLengthWith (s : Set ℕ) k n d) : s = canonicalFinset n d k := by
  apply Finset.coe_injective
  rw [hAP.eq]
  ext x
  simp only [Set.mem_setOf_eq, mem_coe, mem_canonicalFinset, ENat.coe_lt_coe,
    nsmul_eq_mul, Nat.cast_id, exists_prop]

/-- For a positive step, the AP predicate is exactly equality to the canonical set. -/
theorem isAP_iff_eq_canonical {n d k : ℕ} {s : Finset ℕ} (hd : 0 < d) :
    Set.IsAPOfLengthWith (s : Set ℕ) k n d ↔ s = canonicalFinset n d k := by
  constructor
  · exact finset_eq_canonical
  · intro h
    rw [h]
    exact canonicalFinset_isAP n k hd

/-- The product of the canonical finite set is the indexed progression product. -/
lemma product_canonicalFinset (n k : ℕ) {d : ℕ} (hd : 0 < d) :
    (∏ x ∈ canonicalFinset n d k, x) = ∏ i : Fin k, (n + i.val * d) := by
  calc
    _ = ∏ i ∈ range k, term n d i :=
      prod_image (f := fun x : ℕ => x) (g := term n d) (term_injective n hd).injOn
    _ = ∏ i : Fin k, (n + i.val * d) := (Fin.prod_univ_eq_prod_range (term n d) k).symm

/-- Products in the finite-set AP formulation can be replaced by `Fin k` products. -/
lemma product_eq_of_isAP {n d k : ℕ} {s : Finset ℕ} (hd : 0 < d)
    (hAP : Set.IsAPOfLengthWith (s : Set ℕ) k n d) :
    (∏ x ∈ s, x) = ∏ i : Fin k, (n + i.val * d) := by
  rw [finset_eq_canonical hAP]
  exact product_canonicalFinset n k hd

/-- Equivalence of the finite-set/AP and indexed-product assertions.
This has the same finite-set left side as `Erdos672With`, but does not import or
use that declaration (nor either conjecture theorem). -/
theorem forall_ap_product_ne_iff (k l : ℕ) :
    (∀ (s : Finset ℕ), s.card = k → ∀ (n : ℕ), 0 < n → ∀ (d : ℕ), 0 < d →
      n.gcd d = 1 → Set.IsAPOfLengthWith (s : Set ℕ) k n d →
        ∀ q, (∏ x ∈ s, x) ≠ q ^ l) ↔
    (∀ (n : ℕ), 0 < n → ∀ (d : ℕ), 0 < d → n.gcd d = 1 →
      ∀ q, (∏ i : Fin k, (n + i.val * d)) ≠ q ^ l) := by
  constructor
  · intro h n hn d hd hcop q
    have hne := h (canonicalFinset n d k) (canonicalFinset_card n k hd)
      n hn d hd hcop (canonicalFinset_isAP n k hd) q
    rwa [product_canonicalFinset n k hd] at hne
  · intro h s _ n hn d hd hcop hAP q
    rw [product_eq_of_isAP hd hAP]
    exact h n hn d hd hcop q

/- ## Reduction to prime exponents -/

/-- Any perfect power of exponent greater than one is a perfect prime power. -/
theorem power_eq_prime_power {N q l : ℕ} (hl : 1 < l) (hpower : N = q ^ l) :
    ∃ p r : ℕ, p.Prime ∧ p ∣ l ∧ N = r ^ p := by
  obtain ⟨p, hp, hpl⟩ := Nat.exists_prime_and_dvd (by omega : l ≠ 1)
  refine ⟨p, q ^ (l / p), hp, hpl, ?_⟩
  rw [hpower, ← pow_mul, Nat.div_mul_cancel hpl]

/-- To exclude all nontrivial perfect powers it suffices to exclude prime exponents. -/
theorem no_powers_iff_no_prime_powers (N : ℕ) :
    (∀ l, 1 < l → ∀ q, N ≠ q ^ l) ↔ (∀ p, p.Prime → ∀ r, N ≠ r ^ p) := by
  constructor
  · intro h p hp r
    exact h p hp.one_lt r
  · intro h l hl q hpower
    obtain ⟨p, r, hp, _, hpr⟩ := power_eq_prime_power hl hpower
    exact h p hp r hpr

end Erdos672.Progression
