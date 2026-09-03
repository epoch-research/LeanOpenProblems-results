import Submission.DoubleCoverQuadratic

/-!
A quadratic interval bound under the explicit reciprocal-prime budget
sum(1/p) <= 1. Multiplicities of the cover are unrestricted. The reciprocal
budget is not part of Erdős 970, so this is only a restricted theorem.
-/
namespace Erdos970.ReciprocalBudget
open Finset Erdos970.BlockSieve SievePolynomial
open Erdos970.DoubleCover (hits prime_pair_inverse)
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- On a pattern with H hits this polynomial is (H-1)(H-k). -/
noncomputable def probe (p : ι → ℕ) : SievePolynomial where
  Term := Unit ⊕ (ι ⊕ (ι × ι))
  fintypeTerm := inferInstance
  primes := fun t => match t with
    | .inl _ => ∅
    | .inr (.inl i) => {p i}
    | .inr (.inr (i,j)) => {p i, p j}
  coefficient := fun t => match t with
    | .inl _ => Fintype.card ι
    | .inr (.inl _) => -(Fintype.card ι + 1)
    | .inr (.inr _) => 1

omit [DecidableEq ι] in
lemma probe_value (p : ι → ℕ) (r : ℕ → ℕ) (x : ℕ) :
    (probe p).value r x = (hits p r x - 1) * (hits p r x - Fintype.card ι) := by
  classical
  let h : ι → ℝ := fun i => if x ≡ r (p i) [MOD p i] then 1 else 0
  have he (i j : ι) : (if ∀ q ∈ ({p i, p j} : Finset ℕ), x ≡ r q [MOD q]
      then (1 : ℝ) else 0) = h i * h j := by
    simp only [forall_mem_insert, mem_singleton, forall_eq, h]
    split_ifs <;> simp_all
  have hs (i : ι) : (if ∀ q ∈ ({p i} : Finset ℕ), x ≡ r q [MOD q]
      then (1 : ℝ) else 0) = h i := by simp [h]
  have hz : (if ∀ q ∈ (∅ : Finset ℕ), x ≡ r q [MOD q]
      then (1 : ℝ) else 0) = 1 := by simp
  simp only [value, probe, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_unique, hz, hs, mul_one, he, one_mul]
  rw [← mul_sum, ← sum_mul_sum]
  change (Fintype.card ι : ℝ) + (-(Fintype.card ι + 1) * hits p r x +
    hits p r x * hits p r x) = _
  ring

lemma probe_mean (p : ι → ℕ) (hinj : Function.Injective p) :
    (probe p).mean = (Fintype.card ι : ℝ) * (1 - ∑ i, 1 / (p i : ℝ)) +
      (∑ i, 1 / (p i : ℝ)) ^ 2 - ∑ i, (1 / (p i : ℝ)) ^ 2 := by
  classical
  have hpairs : (∑ i, ∑ j, 1 / (∏ q ∈ ({p i, p j} : Finset ℕ), (q : ℝ))) =
      (∑ i, 1 / (p i : ℝ)) ^ 2 + (∑ i, 1 / (p i : ℝ)) -
        ∑ i, (1 / (p i : ℝ)) ^ 2 := by
    simp_rw [prime_pair_inverse p hinj]
    simp only [sum_add_distrib, sum_ite_eq, mem_univ, if_true, sum_sub_distrib]
    rw [← sum_mul_sum]
    ring
  have he : (probe p).mean = Fintype.card ι - (Fintype.card ι + 1 : ℝ) *
      (∑ i, 1 / (p i : ℝ)) +
      (∑ i, ∑ j, 1 / (∏ q ∈ ({p i, p j} : Finset ℕ), (q : ℝ))) := by
    simp only [mean, probe, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fintype.sum_unique, prod_empty, div_one, prod_singleton]
    simp only [div_eq_mul_inv]
    simp_rw [← mul_sum]
    ring
  rw [he, hpairs]
  ring

omit [DecidableEq ι] in
lemma probe_cost (p : ι → ℕ) : (probe p).cost =
    2 * (Fintype.card ι : ℝ) ^ 2 + 2 * Fintype.card ι := by
  have hk : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  simp only [cost, probe, Fintype.sum_sum_type, abs_neg, abs_of_nonneg hk,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Fintype.card ι + 1), abs_one,
    sum_const, card_univ, nsmul_eq_mul, mul_one, Fintype.card_unique,
    Fintype.card_prod, Nat.cast_one, Nat.cast_mul, one_mul]
  ring

omit [DecidableEq ι] in
lemma probe_prime_support (p : ι → ℕ) (hp : ∀ i, (p i).Prime) :
    ∀ t, ∀ q ∈ (probe p).primes t, q.Prime := by
  intro t q hq
  rcases t with u | (i | ij)
  · simp [probe] at hq
  · have he : q = p i := by simpa [probe] using hq
    exact he ▸ hp i
  · have he : q = p ij.1 ∨ q = p ij.2 := by simpa [probe] using hq
    rcases he with rfl | rfl
    · exact hp _
    · exact hp _

omit [DecidableEq ι] in
lemma probe_nonpos_of_hit (p : ι → ℕ) (r : ℕ → ℕ) (x : ℕ)
    (hhit : ∃ i, x ≡ r (p i) [MOD p i]) : (probe p).value r x ≤ 0 := by
  classical
  have hlo : 1 ≤ hits p r x := by
    obtain ⟨i, hi⟩ := hhit
    have hh := single_le_sum (s := (univ : Finset ι))
      (f := fun i => if x ≡ r (p i) [MOD p i] then (1 : ℝ) else 0)
      (fun j _ => by dsimp only; split_ifs <;> norm_num) (mem_univ i)
    simpa only [hi, if_true] using hh
  have hhi : hits p r x ≤ Fintype.card ι := by
    calc
      _ ≤ ∑ _i : ι, (1 : ℝ) := sum_le_sum (fun i _ => by split_ifs <;> norm_num)
      _ = _ := by simp
  rw [probe_value]
  exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlo) (sub_nonpos.mpr hhi)

/-- A necessary inequality for every cover, with no reciprocal restriction. -/
theorem cover_moment_budget (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (r : ℕ → ℕ) (m : ℕ)
    (hcover : ∀ x < m, ∃ i, x ≡ r (p i) [MOD p i]) :
    (m : ℝ) * ((Fintype.card ι : ℝ) * (1 - ∑ i, 1 / (p i : ℝ)) +
      (∑ i, 1 / (p i : ℝ)) ^ 2 - ∑ i, (1 / (p i : ℝ)) ^ 2) ≤
      2 * (Fintype.card ι : ℝ) ^ 2 + 2 * Fintype.card ι := by
  have he := (abs_le.mp (interval_error (probe p) (probe_prime_support p hp) r m)).1
  have hn : (∑ x ∈ range m, (probe p).value r x) ≤ 0 :=
    sum_nonpos (fun x hx => probe_nonpos_of_hit p r x (hcover x (mem_range.mp hx)))
  rw [probe_mean p hinj, probe_cost] at he
  linarith

lemma reciprocal_budget_mean_lower (k : ℕ) (hk : 1 ≤ k) (s t : ℝ)
    (hs : s ≤ 1) (hsk : s ≤ (k : ℝ) / 2) (ht : t ≤ s / 2) :
    1 / 2 ≤ (k : ℝ) * (1 - s) + s ^ 2 - t := by
  by_cases hk1 : k = 1
  · subst k
    norm_num only [Nat.cast_one] at *
    nlinarith [mul_nonneg (sub_nonneg.mpr hsk) (sub_nonneg.mpr hs)]
  · have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    have hh := mul_le_mul_of_nonneg_right hk2 (sub_nonneg.mpr hs)
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ 3 / 2 - s by linarith)]

omit [DecidableEq ι] in
lemma prime_reciprocal_bounds (p : ι → ℕ) (hp : ∀ i, (p i).Prime) :
    (∑ i, 1 / (p i : ℝ)) ≤ (Fintype.card ι : ℝ) / 2 ∧
    (∑ i, (1 / (p i : ℝ)) ^ 2) ≤ (∑ i, 1 / (p i : ℝ)) / 2 := by
  have hb (i : ι) : 0 ≤ 1 / (p i : ℝ) ∧ (1 / (p i : ℝ)) ≤ 1 / 2 := by
    refine ⟨by positivity, ?_⟩
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (hp i).two_le)
  constructor
  · have hh := sum_le_sum (s := (univ : Finset ι)) (fun i _ => (hb i).2)
    simpa using hh
  · rw [sum_div]
    apply sum_le_sum
    intro i hi
    nlinarith [mul_le_mul_of_nonneg_right (hb i).2 (hb i).1]

/-- No multiplicity bound is imposed: the reciprocal budget alone suffices. -/
theorem cover_length_le_eight_square (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (r : ℕ → ℕ) (m : ℕ)
    (hs : (∑ i, 1 / (p i : ℝ)) ≤ 1)
    (hcover : ∀ x < m, ∃ i, x ≡ r (p i) [MOD p i]) :
    m ≤ 8 * Fintype.card ι ^ 2 := by
  by_cases hm : m = 0
  · simp [hm]
  have hk : 1 ≤ Fintype.card ι := by
    obtain ⟨i, _⟩ := hcover 0 (by omega)
    exact Fintype.card_pos_iff.mpr ⟨i⟩
  obtain ⟨hs', ht⟩ := prime_reciprocal_bounds p hp
  have hlo := reciprocal_budget_mean_lower (Fintype.card ι) hk _ _ hs hs' ht
  have hbudget := cover_moment_budget p hp hinj r m hcover
  have hh := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg m)
  have hkR : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hk
  have hfinal : (m : ℝ) ≤ 8 * (Fintype.card ι : ℝ) ^ 2 := by nlinarith
  exact_mod_cast hfinal

theorem prime_cover_quadratic_of_reciprocal_budget (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (r : ℕ → ℕ) (m : ℕ)
    (hs : (∑ p ∈ P, 1 / (p : ℝ)) ≤ 1)
    (hcover : ∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p]) :
    m ≤ 8 * P.card ^ 2 := by
  have hs' : (∑ p : P, 1 / (p.val : ℝ)) ≤ 1 := by
    rw [← sum_attach P (fun p : ℕ => 1 / (p : ℝ))] at hs
    exact hs
  have hh := cover_length_le_eight_square (fun p : P => p.val)
    (fun p => hP p.val p.property) Subtype.val_injective r m hs'
    (fun x hx => by obtain ⟨p, hp, hpx⟩ := hcover x hx; exact ⟨⟨p,hp⟩, hpx⟩)
  simpa only [Fintype.card_coe] using hh

#print axioms cover_moment_budget
#print axioms cover_length_le_eight_square
#print axioms prime_cover_quadratic_of_reciprocal_budget
end Erdos970.ReciprocalBudget
