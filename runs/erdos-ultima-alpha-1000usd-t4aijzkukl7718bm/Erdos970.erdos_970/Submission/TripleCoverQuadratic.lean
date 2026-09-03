import Submission.DoubleCoverQuadratic

/-! A deterministic quadratic probe for covers of multiplicity at most three.
The final robust inequality keeps the contribution of larger overlaps explicit;
no unrestricted Jacobsthal bound is claimed. -/
namespace Erdos970.TripleCover
open Finset Erdos970.BlockSieve SievePolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def probe (p : ι → ℕ) : SievePolynomial where
  Term := Unit ⊕ (ι ⊕ (ι × ι))
  fintypeTerm := inferInstance
  primes := fun t => match t with
    | .inl _ => ∅
    | .inr (.inl i) => {p i}
    | .inr (.inr (i,j)) => {p i, p j}
  coefficient := fun t => match t with
    | .inl _ => 3
    | .inr (.inl _) => -4
    | .inr (.inr _) => 1

omit [DecidableEq ι] in
lemma probe_value (p : ι → ℕ) (r : ℕ → ℕ) (x : ℕ) :
    (probe p).value r x =
      (DoubleCover.hits p r x - 1) * (DoubleCover.hits p r x - 3) := by
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
  change 3 + (-4 * DoubleCover.hits p r x +
    DoubleCover.hits p r x * DoubleCover.hits p r x) = _
  ring

lemma probe_mean (p : ι → ℕ) (hinj : Function.Injective p) :
    (probe p).mean = 3 - 3 * (∑ i, 1 / (p i : ℝ)) +
      (∑ i, 1 / (p i : ℝ)) ^ 2 - ∑ i, (1 / (p i : ℝ)) ^ 2 := by
  classical
  have hpairs : (∑ i, ∑ j, 1 / (∏ q ∈ ({p i, p j} : Finset ℕ), (q : ℝ))) =
      (∑ i, 1 / (p i : ℝ)) ^ 2 + (∑ i, 1 / (p i : ℝ)) -
        ∑ i, (1 / (p i : ℝ)) ^ 2 := by
    simp_rw [DoubleCover.prime_pair_inverse p hinj]
    simp only [sum_add_distrib, sum_ite_eq, mem_univ, if_true, sum_sub_distrib]
    rw [← sum_mul_sum]
    ring
  have he : (probe p).mean = 3 - 4 * (∑ i, 1 / (p i : ℝ)) +
      (∑ i, ∑ j, 1 / (∏ q ∈ ({p i, p j} : Finset ℕ), (q : ℝ))) := by
    simp only [mean, probe, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fintype.sum_unique, prod_empty, div_one, prod_singleton]
    simp only [div_eq_mul_inv]
    rw [← mul_sum]
    ring
  rw [he, hpairs]
  ring

/-- Separating the only possible prime 2 improves the elementary square bound
just enough for a uniformly positive three-hit probe. -/
lemma reciprocal_square_bound (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) :
    (∑ i, (1 / (p i : ℝ)) ^ 2) ≤ (1 / 3 : ℝ) * ∑ i, 1 / (p i : ℝ) + 1 / 12 := by
  classical
  have hs : (∑ i, if p i = 2 then (1 : ℝ) else 0) ≤ 1 := by
    rw [sum_boole]
    have hc : ((univ : Finset ι).filter (fun i => p i = 2)).card ≤ 1 := by
      apply card_le_one.mpr
      intro i hi j hj
      exact hinj ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
    exact_mod_cast hc
  have hpoint (i : ι) : (1 / (p i : ℝ)) ^ 2 ≤
      (1 / 3 : ℝ) * (1 / (p i : ℝ)) +
        (1 / 12 : ℝ) * (if p i = 2 then 1 else 0) := by
    by_cases hi : p i = 2
    · norm_num [hi]
    · have hp3 : (3 : ℝ) ≤ p i := by
        exact_mod_cast (show 3 ≤ p i by have := (hp i).two_le; omega)
      have hq : (1 / (p i : ℝ)) ≤ (1 / 3 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) hp3
      have hq0 : (0 : ℝ) ≤ 1 / (p i : ℝ) := by positivity
      rw [if_neg hi, mul_zero, add_zero]
      nlinarith only [mul_le_mul_of_nonneg_right hq hq0]
  have hh := sum_le_sum (s := univ) (fun i _ => hpoint i)
  simp only [sum_add_distrib, ← mul_sum] at hh
  linarith

lemma probe_mean_lower (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) : (5 : ℝ) / 36 ≤ (probe p).mean := by
  have hh := reciprocal_square_bound p hp hinj
  rw [probe_mean p hinj]
  nlinarith only [hh, sq_nonneg ((∑ i, 1 / (p i : ℝ)) - 5 / 3)]

omit [DecidableEq ι] in
lemma probe_cost (p : ι → ℕ) : (probe p).cost =
    3 + 4 * Fintype.card ι + (Fintype.card ι : ℝ) ^ 2 := by
  simp only [cost, probe, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_unique]
  norm_num [sum_const, mul_comm, pow_two]
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

/-- Valid for every phase, without any covering or multiplicity premise. -/
theorem total_probe_lower (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (r : ℕ → ℕ) (m : ℕ) :
    (m : ℝ) * (5 / 36 : ℝ) -
      (3 + 4 * Fintype.card ι + (Fintype.card ι : ℝ) ^ 2) ≤
      ∑ x ∈ range m, (DoubleCover.hits p r x - 1) * (DoubleCover.hits p r x - 3) := by
  have he := (abs_le.mp (interval_error (probe p) (probe_prime_support p hp) r m)).1
  rw [probe_cost] at he
  simp_rw [probe_value] at he
  have hm := mul_le_mul_of_nonneg_left (probe_mean_lower p hp hinj) (Nat.cast_nonneg m)
  linarith

lemma subtype_hits (P : Finset ℕ) (r : ℕ → ℕ) (x : ℕ) :
    DoubleCover.hits (fun p : P => p.val) r x =
      ((P.filter (fun p => x ≡ r p [MOD p])).card : ℝ) := by
  classical
  unfold DoubleCover.hits
  rw [sum_boole]
  congr 1
  change (P.attach.filter (fun p => x ≡ r p.val [MOD p.val])).card = _
  rw [filter_attach (fun p : ℕ => x ≡ r p [MOD p]) P, card_map, card_attach]

/-- Covers whose overlap never exceeds three satisfy an absolute quadratic bound. -/
theorem prime_triple_cover_quadratic (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℕ) (m : ℕ) (hcover : ∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p])
    (htriple : ∀ x < m, (P.filter (fun p => x ≡ r p [MOD p])).card ≤ 3) :
    m ≤ 60 * P.card ^ 2 := by
  classical
  by_cases hm : m = 0
  · simp [hm]
  have hk : 1 ≤ P.card := by
    obtain ⟨p, hp, _⟩ := hcover 0 (by omega)
    exact card_pos.mpr ⟨p, hp⟩
  have hz : (∑ x ∈ range m,
      (DoubleCover.hits (fun p : P => p.val) r x - 1) *
        (DoubleCover.hits (fun p : P => p.val) r x - 3)) ≤ 0 := by
    apply sum_nonpos
    intro x hx
    have hxm := mem_range.mp hx
    have hpos : 1 ≤ (P.filter (fun p => x ≡ r p [MOD p])).card := by
      obtain ⟨p, hp, hpx⟩ := hcover x hxm
      exact card_pos.mpr ⟨p, mem_filter.mpr ⟨hp, hpx⟩⟩
    rw [subtype_hits]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (by exact_mod_cast hpos))
      (by have hh : ((P.filter (fun p => x ≡ r p [MOD p])).card : ℝ) ≤ 3 :=
            by exact_mod_cast htriple x hxm
          linarith)
  have hh := (total_probe_lower (fun p : P => p.val)
    (fun p => hP p.val p.property) Subtype.val_injective r m).trans hz
  simp only [Fintype.card_coe] at hh
  have hkR : (1 : ℝ) ≤ P.card := by exact_mod_cast hk
  have hfinal : (m : ℝ) ≤ 60 * (P.card : ℝ) ^ 2 := by nlinarith
  exact_mod_cast hfinal

#print axioms total_probe_lower
#print axioms prime_triple_cover_quadratic
end Erdos970.TripleCover
