import Submission.SievePolynomial

/-!
A quadratic bound for prime-class covers with multiplicity at most two.
Unlike an exact cover, these covers may overlap. The multiplicity restriction
is essential to the argument and is not part of the Jacobsthal conjecture.
-/
namespace Erdos970.DoubleCover
open Finset Erdos970.BlockSieve
open SievePolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def probe (p : ι → ℕ) : SievePolynomial where
  Term := Unit ⊕ (ι ⊕ (ι × ι))
  fintypeTerm := inferInstance
  primes := fun t => match t with
    | .inl _ => ∅
    | .inr (.inl i) => {p i}
    | .inr (.inr (i,j)) => {p i, p j}
  coefficient := fun t => match t with
    | .inl _ => 1
    | .inr (.inl _) => -(3 / 2)
    | .inr (.inr _) => 1 / 2

noncomputable def hits (p : ι → ℕ) (r : ℕ → ℕ) (x : ℕ) : ℝ :=
  ∑ i, if x ≡ r (p i) [MOD p i] then 1 else 0

omit [DecidableEq ι] in
lemma probe_value (p : ι → ℕ) (r : ℕ → ℕ) (x : ℕ) :
    (probe p).value r x = (hits p r x - 1) * (hits p r x - 2) / 2 := by
  classical
  let h : ι → ℝ := fun i => if x ≡ r (p i) [MOD p i] then 1 else 0
  have he (i j : ι) : (if ∀ q ∈ ({p i, p j} : Finset ℕ), x ≡ r q [MOD q]
      then (1 : ℝ) else 0) = h i * h j := by
    simp only [forall_mem_insert, mem_singleton, forall_eq, h]
    split_ifs <;> simp_all
  have hsingle (i : ι) : (if ∀ q ∈ ({p i} : Finset ℕ), x ≡ r q [MOD q]
      then (1 : ℝ) else 0) = h i := by simp [h]
  have hempty : (if ∀ q ∈ (∅ : Finset ℕ), x ≡ r q [MOD q]
      then (1 : ℝ) else 0) = 1 := by simp
  simp only [value, probe, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_unique, hempty, hsingle, mul_one, he]
  change 1 + ((∑ i, -(3 / 2 : ℝ) * h i) +
    ∑ i, ∑ j, (1 / 2 : ℝ) * (h i * h j)) = _
  rw [← mul_sum]
  simp_rw [← mul_sum]
  rw [← sum_mul]
  change 1 + (-(3 / 2 : ℝ) * hits p r x + 1 / 2 * (hits p r x * hits p r x)) = _
  ring

omit [Fintype ι] in
lemma prime_pair_inverse (p : ι → ℕ) (hinj : Function.Injective p) (i j : ι) :
    1 / (∏ q ∈ ({p i, p j} : Finset ℕ), (q : ℝ)) =
      (1 / (p i : ℝ)) * (1 / (p j : ℝ)) +
        if i = j then (1 / (p i : ℝ) - (1 / (p i : ℝ)) ^ 2) else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [insert_eq_of_mem (mem_singleton_self _), prod_singleton, if_true]
    ring
  · rw [prod_pair (fun hh => hij (hinj hh)), if_neg hij]
    ring

lemma probe_mean (p : ι → ℕ) (hinj : Function.Injective p) :
    (probe p).mean = 1 - (∑ i, 1 / (p i : ℝ)) +
      ((∑ i, 1 / (p i : ℝ)) ^ 2 - ∑ i, (1 / (p i : ℝ)) ^ 2) / 2 := by
  classical
  have hpairs : (∑ i, ∑ j, 1 / (∏ q ∈ ({p i, p j} : Finset ℕ), (q : ℝ))) =
      (∑ i, 1 / (p i : ℝ)) ^ 2 + (∑ i, 1 / (p i : ℝ)) -
        ∑ i, (1 / (p i : ℝ)) ^ 2 := by
    simp_rw [prime_pair_inverse p hinj]
    simp only [sum_add_distrib, sum_ite_eq, mem_univ, if_true, sum_sub_distrib]
    rw [← sum_mul_sum]
    ring
  have he : (probe p).mean = 1 - (3 / 2 : ℝ) * (∑ i, 1 / (p i : ℝ)) +
      (1 / 2 : ℝ) * (∑ i, ∑ j, 1 / (∏ q ∈ ({p i, p j} : Finset ℕ), (q : ℝ))) := by
    simp only [mean, probe, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fintype.sum_unique, prod_empty, div_one, prod_singleton]
    simp only [div_eq_mul_inv]
    simp_rw [← mul_sum]
    ring
  rw [he, hpairs]
  ring

/-- No analytic estimate is needed here: each prime marginal is at most 1/2. -/
lemma probe_mean_lower (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) : (7 : ℝ) / 32 ≤ (probe p).mean := by
  have hsq : (∑ i, (1 / (p i : ℝ)) ^ 2) ≤ (1 / 2 : ℝ) * ∑ i, 1 / (p i : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have hp2 : (2 : ℝ) ≤ p i := by exact_mod_cast (hp i).two_le
    have hh : (1 / (p i : ℝ)) ≤ (1 / 2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hp2
    have h0 : (0 : ℝ) ≤ 1 / (p i : ℝ) := by positivity
    nlinarith only [mul_le_mul_of_nonneg_right hh h0]
  rw [probe_mean p hinj]
  nlinarith [sq_nonneg ((∑ i, 1 / (p i : ℝ)) - 5 / 4)]

omit [DecidableEq ι] in
lemma probe_cost (p : ι → ℕ) : (probe p).cost =
    1 + (3 / 2 : ℝ) * Fintype.card ι + (1 / 2 : ℝ) * (Fintype.card ι : ℝ) ^ 2 := by
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

/-- A general lower bound on the total quadratic overlap probe, for every
prime-class configuration, whether or not it covers the interval. -/
theorem total_probe_lower (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (r : ℕ → ℕ) (m : ℕ) :
    (m : ℝ) * (7 / 32 : ℝ) -
      (1 + (3 / 2 : ℝ) * Fintype.card ι + (1 / 2 : ℝ) * (Fintype.card ι : ℝ) ^ 2) ≤
      ∑ x ∈ range m, (hits p r x - 1) * (hits p r x - 2) / 2 := by
  have he := (abs_le.mp (interval_error (probe p) (probe_prime_support p hp) r m)).1
  rw [probe_cost] at he
  simp_rw [probe_value] at he
  have hm := mul_le_mul_of_nonneg_left (probe_mean_lower p hp hinj) (Nat.cast_nonneg m)
  linarith

/-- The double-cover bound, with the multiplicity restriction explicit. -/
theorem cover_length_le_sixteen_square (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (r : ℕ → ℕ) (m : ℕ)
    (hcover : ∀ x < m, ∃ i, x ≡ r (p i) [MOD p i])
    (hdouble : ∀ x < m, ((univ : Finset ι).filter
      (fun i => x ≡ r (p i) [MOD p i])).card ≤ 2) :
    m ≤ 16 * Fintype.card ι ^ 2 := by
  classical
  by_cases hm : m = 0
  · simp [hm]
  have hk : 1 ≤ Fintype.card ι := by
    obtain ⟨i, _⟩ := hcover 0 (by omega)
    exact Fintype.card_pos_iff.mpr ⟨i⟩
  have hz : (∑ x ∈ range m, (hits p r x - 1) * (hits p r x - 2) / 2) = 0 := by
    apply sum_eq_zero
    intro x hx
    have hxm := mem_range.mp hx
    have hpos : 0 < ((univ : Finset ι).filter
        (fun i => x ≡ r (p i) [MOD p i])).card := by
      obtain ⟨i, hi⟩ := hcover x hxm
      exact card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
    have htwo := hdouble x hxm
    have hc : ((univ : Finset ι).filter
        (fun i => x ≡ r (p i) [MOD p i])).card = 1 ∨
        ((univ : Finset ι).filter (fun i => x ≡ r (p i) [MOD p i])).card = 2 := by omega
    unfold hits
    rw [sum_boole]
    rcases hc with hc | hc <;> rw [hc] <;> norm_num
  have hh := total_probe_lower p hp hinj r m
  rw [hz] at hh
  have hkR : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hk
  have hfinal : (m : ℝ) ≤ 16 * (Fintype.card ι : ℝ) ^ 2 := by nlinarith
  exact_mod_cast hfinal

/-- Finite-set specialization, allowing overlaps but no triple hit. -/
theorem prime_double_cover_quadratic (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℕ) (m : ℕ) (hcover : ∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p])
    (hdouble : ∀ x < m, (P.filter (fun p => x ≡ r p [MOD p])).card ≤ 2) :
    m ≤ 16 * P.card ^ 2 := by
  have hc := cover_length_le_sixteen_square (fun p : P => p.val)
    (fun p => hP p.val p.property) Subtype.val_injective r m
    (fun x hx => by obtain ⟨p, hp, hpx⟩ := hcover x hx; exact ⟨⟨p,hp⟩, hpx⟩)
  have hh : ∀ x < m, ((univ : Finset P).filter
      (fun p => x ≡ r p.val [MOD p.val])).card ≤ 2 := by
    intro x hx
    have he : ((univ : Finset P).filter (fun p => x ≡ r p.val [MOD p.val])).card =
        (P.filter (fun p => x ≡ r p [MOD p])).card := by
      change (P.attach.filter (fun p => x ≡ r p.val [MOD p.val])).card = _
      rw [filter_attach (fun p : ℕ => x ≡ r p [MOD p]) P, card_map, card_attach]
    exact he.trans_le (hdouble x hx)
  simpa only [Fintype.card_coe] using hc hh

#print axioms total_probe_lower
#print axioms cover_length_le_sixteen_square
#print axioms prime_double_cover_quadratic
end Erdos970.DoubleCover
