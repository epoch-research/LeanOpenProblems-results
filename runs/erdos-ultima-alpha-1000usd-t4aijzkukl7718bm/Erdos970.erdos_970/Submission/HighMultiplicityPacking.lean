import Submission.MultiplicityLinearObstruction

/-! Deterministic bounds on high-overlap positions. Distinct positions share
only primes dividing their difference. A finite incidence argument then
bounds large hit patterns. No quadratic Jacobsthal bound is asserted. -/
namespace Erdos970.HighMultiplicityPacking
open Finset

/-- Constant-weight incidence packing with bounded pairwise intersections. -/
theorem incidence_packing {ι α : Type*} [Fintype ι] [DecidableEq α]
    (P : Finset α) (A : ι → Finset α) (B t : ℕ)
    (hAP : ∀ x, A x ⊆ P) (hB : ∀ x, (A x).card = B)
    (hinter : ∀ x y, x ≠ y → (A x ∩ A y).card ≤ t)
    (htB : t ≤ B) :
    (Fintype.card ι : ℝ) * ((B : ℝ) ^ 2 - P.card * t) ≤
      (P.card : ℝ) * (B - (t : ℝ)) := by
  classical
  let h : ι → α → ℝ := fun x p => if p ∈ A x then 1 else 0
  let d : α → ℝ := fun p => ∑ x, h x p
  have hsum (x : ι) : (∑ p ∈ P, h x p) = (B : ℝ) := by
    have he : P.filter (fun p => p ∈ A x) = A x := by
      ext p
      simp only [mem_filter]
      exact and_iff_right_of_imp (fun hp => hAP x hp)
    simp only [h, sum_boole, he, hB]
  have hprod (x y : ι) :
      (∑ p ∈ P, h x p * h y p) = ((A x ∩ A y).card : ℝ) := by
    have he (p : α) : h x p * h y p = if p ∈ A x ∩ A y then 1 else 0 := by
      simp only [h, mem_inter]
      split_ifs <;> simp_all
    have hf : P.filter (fun p => p ∈ A x ∩ A y) = A x ∩ A y := by
      ext p
      simp only [mem_filter]
      exact and_iff_right_of_imp (fun hp => hAP x (mem_inter.mp hp).1)
    simp only [he, sum_boole, hf]
  have htotal : (∑ p ∈ P, d p) = (Fintype.card ι : ℝ) * B := by
    simp only [d]
    rw [sum_comm]
    simp only [hsum, sum_const, card_univ, nsmul_eq_mul]
  have hsq : (∑ p ∈ P, d p ^ 2) =
      ∑ x : ι, ∑ y : ι, ((A x ∩ A y).card : ℝ) := by
    simp only [d, sq, sum_mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro x hx
    rw [sum_comm]
    exact sum_congr rfl (fun y hy => hprod x y)
  have hsqle : (∑ p ∈ P, d p ^ 2) ≤
      (Fintype.card ι : ℝ) * (B + ((Fintype.card ι : ℝ) - 1) * t) := by
    rw [hsq]
    calc
      _ ≤ ∑ x : ι, ∑ y : ι, if x = y then (B : ℝ) else t := by
        apply sum_le_sum
        intro x hx
        apply sum_le_sum
        intro y hy
        by_cases hxy : x = y
        · simp [hxy, hB]
        · rw [if_neg hxy]
          exact_mod_cast hinter x y hxy
      _ = _ := by
        have he (x y : ι) : (if x = y then (B : ℝ) else t) =
            (t : ℝ) + if y = x then (B : ℝ) - t else 0 := by
          by_cases hh : x = y <;> simp [hh, eq_comm]
        simp_rw [he]
        simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
          sum_ite_eq', mem_univ, if_true]
        ring
  have hcs : (∑ p ∈ P, d p) ^ 2 ≤ (P.card : ℝ) * ∑ p ∈ P, d p ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [htotal] at hcs
  have hh := hcs.trans (mul_le_mul_of_nonneg_left hsqle (Nat.cast_nonneg P.card))
  by_cases hn : Fintype.card ι = 0
  · rw [hn, Nat.cast_zero, zero_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast htB))
  · have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    apply (mul_le_mul_iff_right₀ hn0).mp
    nlinarith only [hh]

noncomputable def hitPrimes (P : Finset ℕ) (r : ℕ → ℕ) (x : ℕ) : Finset ℕ :=
  P.filter (fun p => x ≡ r p [MOD p])

noncomputable def highPositions (P : Finset ℕ) (r : ℕ → ℕ) (m B : ℕ) : Finset ℕ :=
  (range m).filter (fun x => B ≤ (hitPrimes P r x).card)

/-- No averaging over residue phases is used in this comparison. -/
lemma common_hits_factorial_bound (P : Finset ℕ) (r : ℕ → ℕ) (m t x y : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (ht : 0 < t) (hm : m ≤ t.factorial)
    (hx : x < m) (hy : y < m) (hne : x ≠ y) :
    (hitPrimes P r x ∩ hitPrimes P r y).card ≤ t := by
  wlog hxy : x < y generalizing x y
  · simpa only [inter_comm] using this y x hy hx hne.symm (by omega)
  have hsub : hitPrimes P r x ∩ hitPrimes P r y ⊆ (y - x).primeFactors := by
    intro p hp
    obtain ⟨hxp, hyp⟩ := mem_inter.mp hp
    obtain ⟨hpP, hxr⟩ := mem_filter.mp hxp
    have hyr := (mem_filter.mp hyp).2
    exact Nat.mem_primeFactors.mpr ⟨hP p hpP,
      (Nat.modEq_iff_dvd' hxy.le).mp (hxr.trans hyr.symm), by omega⟩
  exact (card_le_card hsub).trans
    (MultiplicityObstruction.primeFactors_card_le_of_le_factorial ht (by omega)
      (by omega))

/-- Pair-product separation improves the common-hit budget to one. -/
lemma common_hits_separated_bound (P : Finset ℕ) (r : ℕ → ℕ) (m x y : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hprod : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → m ≤ p * q)
    (hx : x < m) (hy : y < m) (hne : x ≠ y) :
    (hitPrimes P r x ∩ hitPrimes P r y).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro p hp q hq
  by_contra hpq
  obtain ⟨hpX, hpY⟩ := mem_inter.mp hp
  obtain ⟨hqX, hqY⟩ := mem_inter.mp hq
  obtain ⟨hpP, hxp⟩ := mem_filter.mp hpX
  obtain ⟨hqP, hxq⟩ := mem_filter.mp hqX
  have hyp := (mem_filter.mp hpY).2
  have hyq := (mem_filter.mp hqY).2
  have hc := (Nat.coprime_primes (hP p hpP) (hP q hqP)).mpr hpq
  have he := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp
    ⟨hxp.trans hyp.symm, hxq.trans hyq.symm⟩
  have hb := hprod p hpP q hqP hpq
  exact hne (he.eq_of_lt_of_lt (hx.trans_le hb) (hy.trans_le hb))

/-- A bound on shared hits gives a bound on the number of high-overlap points.
The right side is useful only when the displayed coefficient is positive. -/
theorem high_positions_packing (P : Finset ℕ) (r : ℕ → ℕ) (m B t : ℕ)
    (htB : t ≤ B)
    (hcommon : ∀ x < m, ∀ y < m, x ≠ y →
      (hitPrimes P r x ∩ hitPrimes P r y).card ≤ t) :
    ((highPositions P r m B).card : ℝ) * ((B : ℝ) ^ 2 - P.card * t) ≤
      (P.card : ℝ) * (B - (t : ℝ)) := by
  classical
  let U := highPositions P r m B
  have hex (x : U) : ∃ A : Finset ℕ, A ⊆ hitPrimes P r x.val ∧ A.card = B :=
    exists_subset_card_eq (mem_filter.mp x.property).2
  choose A hA hB using hex
  have hAP (x : U) : A x ⊆ P := (hA x).trans (filter_subset _ _)
  have hi (x y : U) (hne : x ≠ y) : (A x ∩ A y).card ≤ t := by
    have hsub : A x ∩ A y ⊆ hitPrimes P r x.val ∩ hitPrimes P r y.val :=
      inter_subset_inter (hA x) (hA y)
    exact (card_le_card hsub).trans (hcommon x.val
      (mem_range.mp (mem_filter.mp x.property).1) y.val
      (mem_range.mp (mem_filter.mp y.property).1)
      (fun h => hne (Subtype.ext h)))
  simpa only [Fintype.card_coe] using incidence_packing P A B t hAP hB hi htB

/-- A convenient numerical consequence, still for deterministic phases. -/
theorem high_positions_card_mul_le (P : Finset ℕ) (r : ℕ → ℕ) (m B t : ℕ)
    (hB : 0 < B) (htB : t ≤ B) (hBt : 2 * P.card * t ≤ B ^ 2)
    (hcommon : ∀ x < m, ∀ y < m, x ≠ y →
      (hitPrimes P r x ∩ hitPrimes P r y).card ≤ t) :
    (highPositions P r m B).card * B ≤ 2 * P.card := by
  have hh := high_positions_packing P r m B t htB hcommon
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hbtR : 2 * (P.card : ℝ) * t ≤ (B : ℝ) ^ 2 := by exact_mod_cast hBt
  have hscaled := mul_le_mul_of_nonneg_left hbtR
    (Nat.cast_nonneg (highPositions P r m B).card)
  have hKt : 0 ≤ (P.card : ℝ) * t := by positivity
  have hfin : ((highPositions P r m B).card : ℝ) * B ≤ 2 * P.card := by
    apply (mul_le_mul_iff_right₀ hBR).mp
    nlinarith only [hh, hscaled, hKt]
  exact_mod_cast hfin

/-- For arbitrary prime phases the factorial condition bounds all common-hit sets. -/
theorem high_positions_factorial_card_mul_le
    (P : Finset ℕ) (r : ℕ → ℕ) (m B t : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (ht : 0 < t) (hm : m ≤ t.factorial)
    (hB : 0 < B) (htB : t ≤ B) (hBt : 2 * P.card * t ≤ B ^ 2) :
    (highPositions P r m B).card * B ≤ 2 * P.card :=
  high_positions_card_mul_le P r m B t hB htB hBt
    (fun x hx y hy hne => common_hits_factorial_bound P r m t x y hP ht hm hx hy hne)

/-- For separated primes, at most 2k/B positions have at least B hits
as soon as B²≥2k. This does not assert that all covers have low multiplicity. -/
theorem high_positions_separated_card_mul_le
    (P : Finset ℕ) (r : ℕ → ℕ) (m B : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hprod : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → m ≤ p * q)
    (hB : 0 < B) (hBt : 2 * P.card ≤ B ^ 2) :
    (highPositions P r m B).card * B ≤ 2 * P.card := by
  apply high_positions_card_mul_le P r m B 1 hB hB (by simpa using hBt)
  exact fun x hx y hy hne => common_hits_separated_bound P r m x y hP hprod hx hy hne

/-- The first two incidence counts bound the total size of a set family.
The intersection premise is only needed for distinct family indices. -/
lemma two_sum_card_le_union {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (U : Finset ι) (A : ι → Finset α) (t : ℕ)
    (hinter : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → (A x ∩ A y).card ≤ t) :
    2 * (∑ x ∈ U, ((A x).card : ℝ)) ≤
      2 * ((U.biUnion A).card : ℝ) + (U.card : ℝ) * (U.card - (1 : ℝ)) * t := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | @insert x U hx ih =>
    have hi : ∀ y ∈ U, ∀ z ∈ U, y ≠ z → (A y ∩ A z).card ≤ t :=
      fun y hy z hz hne => hinter y (mem_insert_of_mem hy) z (mem_insert_of_mem hz) hne
    have ih' := ih hi
    have hsub : A x ∩ U.biUnion A ⊆ U.biUnion (fun y => A x ∩ A y) := by
      intro p hp
      obtain ⟨hpx, hpu⟩ := mem_inter.mp hp
      obtain ⟨y, hy, hpy⟩ := mem_biUnion.mp hpu
      exact mem_biUnion.mpr ⟨y, hy, mem_inter.mpr ⟨hpx, hpy⟩⟩
    have hic : (A x ∩ U.biUnion A).card ≤ U.card * t := by
      calc
        _ ≤ (U.biUnion (fun y => A x ∩ A y)).card := card_le_card hsub
        _ ≤ ∑ y ∈ U, (A x ∩ A y).card := card_biUnion_le
        _ ≤ ∑ _y ∈ U, t := sum_le_sum (fun y hy =>
          hinter x (mem_insert_self _ _) y (mem_insert_of_mem hy)
            (fun he => hx (he.symm ▸ hy)))
        _ = _ := by simp
    have hcr : ((A x ∩ U.biUnion A).card : ℝ) ≤ (U.card : ℝ) * t := by
      exact_mod_cast hic
    have huc : ((A x ∪ U.biUnion A).card : ℝ) + (A x ∩ U.biUnion A).card =
        (A x).card + ((U.biUnion A).card : ℝ) := by
      exact_mod_cast card_union_add_card_inter (A x) (U.biUnion A)
    simp only [sum_insert hx, biUnion_insert, card_insert_of_notMem hx,
      Nat.cast_add, Nat.cast_one]
    nlinarith only [ih', hcr, huc]

/-- The squared number of exceptional positions times the common-hit budget
is itself small under the high-threshold hypothesis. -/
lemma high_positions_square_mul_le (P : Finset ℕ) (r : ℕ → ℕ) (m B t : ℕ)
    (hB : 0 < B) (htB : t ≤ B) (hBt : 2 * P.card * t ≤ B ^ 2)
    (hcommon : ∀ x < m, ∀ y < m, x ≠ y →
      (hitPrimes P r x ∩ hitPrimes P r y).card ≤ t) :
    ((highPositions P r m B).card : ℝ) ^ 2 * t ≤ 2 * P.card := by
  have hc := high_positions_card_mul_le P r m B t hB htB hBt hcommon
  by_cases hk : P.card = 0
  · have hzero : (highPositions P r m B).card = 0 := by
      rw [hk] at hc
      nlinarith
    simp only [hzero, hk, Nat.cast_zero, zero_pow (by omega : 2 ≠ 0), zero_mul, mul_zero, le_refl]
  · have hkR : (0 : ℝ) < P.card := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hs : (((highPositions P r m B).card : ℝ) * B) ^ 2 ≤
        (2 * (P.card : ℝ)) ^ 2 := by exact_mod_cast (Nat.pow_le_pow_left hc 2)
    have hbR : 2 * (P.card : ℝ) * t ≤ (B : ℝ) ^ 2 := by exact_mod_cast hBt
    have hb := mul_le_mul_of_nonneg_left hbR
      (sq_nonneg ((highPositions P r m B).card : ℝ))
    apply (mul_le_mul_iff_left₀ (show 0 < 2 * (P.card : ℝ) by positivity)).mp
    nlinarith only [hs, hb]

/-- High-overlap positions account for at most 2k total hits. This bound
is deterministic and allows arbitrary residues and arbitrary interval phases. -/
theorem high_positions_total_hits_le (P : Finset ℕ) (r : ℕ → ℕ) (m B t : ℕ)
    (hB : 0 < B) (htB : t ≤ B) (hBt : 2 * P.card * t ≤ B ^ 2)
    (hcommon : ∀ x < m, ∀ y < m, x ≠ y →
      (hitPrimes P r x ∩ hitPrimes P r y).card ≤ t) :
    (∑ x ∈ highPositions P r m B, ((hitPrimes P r x).card : ℝ)) ≤ 2 * P.card := by
  classical
  let U := highPositions P r m B
  have hu (x : ℕ) (hx : x ∈ U) : x < m := mem_range.mp (mem_filter.mp hx).1
  have hh := two_sum_card_le_union U (hitPrimes P r) t
    (fun x hx y hy hne => hcommon x (hu x hx) y (hu y hy) hne)
  have hsub : U.biUnion (hitPrimes P r) ⊆ P := by
    intro p hp
    obtain ⟨x, hx, hxp⟩ := mem_biUnion.mp hp
    exact (mem_filter.mp hxp).1
  have hc : ((U.biUnion (hitPrimes P r)).card : ℝ) ≤ P.card := by
    exact_mod_cast card_le_card hsub
  have hs := high_positions_square_mul_le P r m B t hB htB hBt hcommon
  change (U.card : ℝ) ^ 2 * t ≤ 2 * P.card at hs
  have ht : 0 ≤ (U.card : ℝ) * t := by positivity
  change (∑ x ∈ U, ((hitPrimes P r x).card : ℝ)) ≤ 2 * P.card
  nlinarith only [hh, hc, hs, ht]

/-- The total quadratic hit mass on the discarded high-overlap positions
is at most 2k². This alone does not control a general sieve polynomial. -/
theorem high_positions_square_hits_le (P : Finset ℕ) (r : ℕ → ℕ) (m B t : ℕ)
    (hB : 0 < B) (htB : t ≤ B) (hBt : 2 * P.card * t ≤ B ^ 2)
    (hcommon : ∀ x < m, ∀ y < m, x ≠ y →
      (hitPrimes P r x ∩ hitPrimes P r y).card ≤ t) :
    (∑ x ∈ highPositions P r m B, ((hitPrimes P r x).card : ℝ) ^ 2) ≤
      2 * (P.card : ℝ) ^ 2 := by
  have hh := high_positions_total_hits_le P r m B t hB htB hBt hcommon
  calc
    _ ≤ ∑ x ∈ highPositions P r m B, (P.card : ℝ) * (hitPrimes P r x).card := by
      apply sum_le_sum
      intro x hx
      have hc : ((hitPrimes P r x).card : ℝ) ≤ P.card := by
        exact_mod_cast card_le_card (show hitPrimes P r x ⊆ P from filter_subset _ _)
      have hmul := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (hitPrimes P r x).card)
      nlinarith only [hmul]
    _ = (P.card : ℝ) * ∑ x ∈ highPositions P r m B, ((hitPrimes P r x).card : ℝ) :=
      (mul_sum _ _ _).symm
    _ ≤ (P.card : ℝ) * (2 * P.card) :=
      mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg P.card)
    _ = _ := by ring

#print axioms high_positions_total_hits_le
#print axioms high_positions_square_hits_le

#print axioms incidence_packing
#print axioms high_positions_packing
#print axioms high_positions_factorial_card_mul_le
#print axioms high_positions_separated_card_mul_le
end Erdos970.HighMultiplicityPacking
