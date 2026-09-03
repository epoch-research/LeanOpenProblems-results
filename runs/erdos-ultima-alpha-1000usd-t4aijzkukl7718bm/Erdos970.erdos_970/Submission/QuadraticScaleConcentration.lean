import Submission.LongIntervalConcentration

/-! Failure of a relative-plus-constant counting estimate even at an exact
quadratic interval scale. This does not settle the Jacobsthal conjecture. -/
namespace Erdos970.LongIntervalConcentration
open OptimalCoverCore

/-- Euler's divergent prime reciprocal sum implies a subquadratic subsequence
of the enumerated primes; no prime number theorem is needed here. -/
lemma exists_nth_prime_small (D N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ D * Nat.nth Nat.Prime n < n ^ 2 := by
  classical
  by_contra h
  push_neg at h
  have hs : Summable (fun n : ℕ => (1 : ℝ) / Nat.nth Nat.Prime n) := by
    apply ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left (D : ℝ)).of_norm_bounded_eventually
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_ge_atTop (max N 1)] with n hn
    have hn0 : 0 < n := by omega
    have hprime := Nat.prime_nth_prime n
    have hnR : (0 : ℝ) < n := by positivity
    have hpR : (0 : ℝ) < Nat.nth Nat.Prime n := by exact_mod_cast hprime.pos
    have hh : (n : ℝ) ^ 2 ≤ (D : ℝ) * Nat.nth Nat.Prime n := by exact_mod_cast h n (by omega)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [mul_one_div, div_le_div_iff₀ hpR (by positivity)]
    simpa using hh
  let e : ℕ ≃ Nat.Primes :=
    { toFun := fun n => ⟨Nat.nth Nat.Prime n, Nat.prime_nth_prime n⟩
      invFun := fun p => p.val.primeCounting'
      left_inv := Nat.primeCounting'_nth_eq
      right_inv := fun p => Subtype.ext (Nat.nth_count p.property) }
  exact Nat.Primes.not_summable_one_div (e.summable_iff.mp hs)

/-- Extend any fixed prime tail to arbitrarily large prime sets whose largest
member is small relative to the square of the cardinality. -/
lemma exists_large_prime_tail (P₀ : Finset ℕ) (T L K : ℕ)
    (hP₀ : ∀ q ∈ P₀, q.Prime ∧ T < q) :
    ∃ P : Finset ℕ, P₀ ⊆ P ∧ K ≤ P.card ∧
      ∀ q ∈ P, q.Prime ∧ T < q ∧ L * q < P.card ^ 2 := by
  classical
  obtain ⟨n, hn, hsmall⟩ := exists_nth_prime_small (4 * L)
    (2 * (T + 1 + K + P₀.sup id))
  let R := (Nat.nth Nat.Prime n).primesBelow
  let E := (T + 1).primesBelow
  let P := R \ E
  have hRcard : R.card = n := by
    change (Finset.filter Nat.Prime (Finset.range (Nat.nth Nat.Prime n))).card = n
    rw [← Nat.count_eq_card_filter_range]
    exact Nat.primeCounting'_nth_eq n
  have hEcard : E.card ≤ T + 1 := by
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have hER : E ⊆ R := by
    intro q hq
    obtain ⟨hqT, hqpr⟩ := Nat.mem_primesBelow.mp hq
    apply Nat.mem_primesBelow.mpr
    have := Nat.add_two_le_nth_prime n
    exact ⟨by omega, hqpr⟩
  have hcard := Finset.card_sdiff_add_card_eq_card hER
  change P.card + E.card = R.card at hcard
  rw [hRcard] at hcard
  have hnP : n ≤ 2 * P.card := by omega
  refine ⟨P, ?_, by omega, ?_⟩
  · intro q hq
    have hqbound : q ≤ P₀.sup id := Finset.le_sup (f := id) hq
    have := Nat.add_two_le_nth_prime n
    apply Finset.mem_sdiff.mpr
    refine ⟨Nat.mem_primesBelow.mpr ⟨by omega, (hP₀ q hq).1⟩, ?_⟩
    intro he
    have := (Nat.mem_primesBelow.mp he).1
    have := (hP₀ q hq).2
    omega
  · intro q hq
    obtain ⟨hqR, hqE⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hqn, hqpr⟩ := Nat.mem_primesBelow.mp hqR
    have hqT : T < q := by
      by_contra hh
      exact hqE (Nat.mem_primesBelow.mpr ⟨by omega, hqpr⟩)
    refine ⟨hqpr, hqT, ?_⟩
    have hh := Nat.mul_le_mul_left (4 * L) hqn.le
    nlinarith [Nat.pow_le_pow_left hnP 2]

/-- The relative-plus-constant error is unbounded even at exactly `C*(k+1)^2`
positions, with arbitrarily large old-prime cardinality `k` and a larger new prime. -/
theorem unbounded_at_exact_quadratic_scale (A B C K : ℕ) (hC : 0 < C) :
    ∃ (P : Finset ℕ) (p m : ℕ), K ≤ P.card ∧ m = C * (P.card + 1) ^ 2 ∧
      (∀ q ∈ P, q.Prime ∧ q < p) ∧ p.Prime ∧
      B * (survivors m P (fun _ => 0)).card + A * p <
        p * ((survivors m P (fun _ => 0)).filter (fun i => i ≡ 0 [MOD p])).card := by
  classical
  let T := A + 2
  let L := 2 * (T + 1)
  have hL : 0 < L := by dsimp [L, T]; omega
  obtain ⟨P₀, hP₀, hden⟩ := ConstructiveCover.exists_prime_tail_density T (2 * (B + 1) * L)
  let N := ∏ q ∈ P₀, q
  let F := ∏ q ∈ P₀, (q - 1)
  have hN : 0 < N := Finset.prod_pos (fun q hq => (hP₀ q hq).1.pos)
  obtain ⟨P, hsub, hsize, hP⟩ := exists_large_prime_tail P₀ T L (K + L + 2 * B * F) hP₀
  let m := C * (P.card + 1) ^ 2
  have hm : P.card ^ 2 ≤ m := by
    have hh := Nat.mul_le_mul_right ((P.card + 1) ^ 2) (show 1 ≤ C by omega)
    dsimp [m]
    nlinarith
  have hkL : L ≤ P.card := by omega
  have hkm : P.card * L ≤ m := by nlinarith
  let x := m / L
  have hkx : P.card ≤ x := (Nat.le_div_iff_mul_le hL).mpr hkm
  have hx : x ≠ 0 := by omega
  obtain ⟨p, hp, hxp, hpx⟩ := Nat.exists_prime_lt_and_le_two_mul x hx
  have hqp (q : ℕ) (hq : q ∈ P) : q < p := by
    have hqL := (hP q hq).2.2
    have hqx : q ≤ x := (Nat.le_div_iff_mul_le hL).mpr (by nlinarith)
    omega
  have hTm : (T + 1) * p ≤ m := by
    have hd : x * L ≤ m := Nat.div_mul_le_self m L
    have hh := Nat.mul_le_mul_left (T + 1) hpx
    dsimp only [L] at hd
    nlinarith only [hd, hh]
  have hmLp : m < L * p := by
    have hd := Nat.lt_mul_div_succ m hL
    change m < L * (x + 1) at hd
    have hh := Nat.mul_le_mul_left L (show x + 1 ≤ p by omega)
    omega
  have hBF : 2 * B * F ≤ p := by omega
  have hcounts : (survivors m P (fun _ => 0)).card ≤
      (survivors m P₀ (fun _ => 0)).card := by
    apply Finset.card_le_card
    intro i hi
    obtain ⟨him, hiP⟩ := (mem_survivors _ _ _ _).mp hi
    exact (mem_survivors _ _ _ _).mpr ⟨him, fun q hq => hiP q (hsub hq)⟩
  have hsmall : B * (survivors m P (fun _ => 0)).card ≤ p := by
    have hcount := (Nat.mul_le_mul_left N hcounts).trans
      (zero_survivors_scaled_le m P₀ (fun q hq => (hP₀ q hq).1))
    change N * (survivors m P (fun _ => 0)).card ≤ F * (m + N) at hcount
    have hcount' : N * (survivors m P (fun _ => 0)).card ≤ F * (L * p + N) :=
      hcount.trans (Nat.mul_le_mul_left F (by omega))
    change 2 * (B + 1) * L * F ≤ N at hden
    have hd : 2 * B * L * F ≤ N := by nlinarith
    have hd' := Nat.mul_le_mul_right p hd
    have hBF' := Nat.mul_le_mul_right N hBF
    have hcount'' := Nat.mul_le_mul_left (2 * B) hcount'
    nlinarith
  have hremoved : T ≤ ((survivors m P (fun _ => 0)).filter
      (fun i => i ≡ 0 [MOD p])).card := by
    apply (many_removed T p P hp (fun q hq => ⟨(hP q hq).1, (hP q hq).2.1, hqp q hq⟩)).trans
    apply Finset.card_le_card
    intro i hi
    obtain ⟨his, hip⟩ := Finset.mem_filter.mp hi
    obtain ⟨hit, hiP⟩ := (mem_survivors _ _ _ _).mp his
    exact Finset.mem_filter.mpr ⟨(mem_survivors _ _ _ _).mpr ⟨hit.trans_le hTm, hiP⟩, hip⟩
  refine ⟨P, p, m, by omega, rfl, (fun q hq => ⟨(hP q hq).1, hqp q hq⟩), hp, ?_⟩
  have := Nat.mul_le_mul_left p hremoved
  have := hp.pos
  dsimp only [T] at *
  nlinarith

/-- Arbitrary real constants do not give such an estimate at an exact quadratic
scale, even if all sufficiently small cardinalities are discarded. -/
theorem not_uniform_relative_estimate_exact (C K : ℕ) (hC : 0 < C) :
    ¬∃ A B : ℝ, ∀ (P : Finset ℕ) (p m : ℕ), K ≤ P.card →
      m = C * (P.card + 1) ^ 2 →
      (∀ q ∈ P, q.Prime ∧ q < p) → p.Prime →
      (((survivors m P (fun _ => 0)).filter
        (fun i => i ≡ 0 [MOD p])).card : ℝ) ≤
          B * (survivors m P (fun _ => 0)).card / p + A := by
  rintro ⟨A, B, h⟩
  obtain ⟨a, ha⟩ := exists_nat_gt A
  obtain ⟨b, hb⟩ := exists_nat_gt B
  obtain ⟨P, p, m, hK, hm, hP, hp, hbad⟩ := unbounded_at_exact_quadratic_scale a b C K hC
  have hu := h P p m hK hm hP hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hu' := mul_le_mul_of_nonneg_right hu hpR.le
  rw [add_mul, div_mul_cancel₀ _ hpR.ne'] at hu'
  have hbadR : (b : ℝ) * (survivors m P (fun _ => 0)).card + (a : ℝ) * p <
      (p : ℝ) * ((survivors m P (fun _ => 0)).filter (fun i => i ≡ 0 [MOD p])).card := by
    exact_mod_cast hbad
  have hA := mul_le_mul_of_nonneg_right ha.le hpR.le
  have hB := mul_le_mul_of_nonneg_right hb.le
    (Nat.cast_nonneg (survivors m P (fun _ => 0)).card)
  nlinarith only [hu', hbadR, hA, hB]

#print axioms exists_nth_prime_small
#print axioms exists_large_prime_tail
#print axioms unbounded_at_exact_quadratic_scale
#print axioms not_uniform_relative_estimate_exact
end Erdos970.LongIntervalConcentration
