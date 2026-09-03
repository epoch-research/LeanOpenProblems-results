import FormalConjecturesUtil

/-! A limitation of a proposed variable-overlap route. There is no universal
bound `length ≤ C * number_of_primes * maximum_multiplicity` for prime-class
covers. This does NOT negate the quadratic Jacobsthal conjecture. -/
namespace Erdos970.MultiplicityObstruction
open Finset Filter Real

lemma factorial_card_succ_le_prod (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    (S.card + 1).factorial ≤ ∏ p ∈ S, p := by
  induction S using Finset.induction_on_max with
  | h0 => simp
  | @step p S hlt ih =>
    have hp : 2 ≤ p := hS p (mem_insert_self _ _)
    have hpS : p ∉ S := fun h => (hlt p h).false
    have hS' : ∀ q ∈ S, 2 ≤ q := fun q hq => hS q (mem_insert_of_mem hq)
    have hsub : S ⊆ Ico 2 p := fun q hq => mem_Ico.mpr ⟨hS' q hq, hlt q hq⟩
    have hc : S.card + 2 ≤ p := by
      have hh := card_le_card hsub
      simp only [Nat.card_Ico] at hh
      omega
    rw [card_insert_of_notMem hpS, prod_insert hpS, Nat.factorial_succ]
    exact Nat.mul_le_mul hc (ih hS')

lemma primeFactors_card_le_of_le_factorial {t n : ℕ} (ht : 0 < t)
    (hn : 0 < n) (hnt : n ≤ t.factorial) : n.primeFactors.card ≤ t := by
  have hprod := factorial_card_succ_le_prod n.primeFactors
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have hle := hprod.trans ((Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)).trans hnt)
  by_contra hbad
  have htf : t.factorial < (n.primeFactors.card + 1).factorial :=
    Nat.factorial_lt_of_lt ht (by omega)
  omega

lemma log_double_factorial_lower (t : ℕ) (ht : 0 < t) :
    (t : ℝ) * log (t : ℝ) ≤ log ((2 * t).factorial : ℝ) := by
  have hh : t ^ t ≤ (2 * t).factorial := by
    calc
      t ^ t ≤ (t + 1) ^ t := Nat.pow_le_pow_left (by omega) t
      _ ≤ t.factorial * (t + 1) ^ t := Nat.le_mul_of_pos_left _ (Nat.factorial_pos t)
      _ ≤ (2 * t).factorial := by
        simpa only [two_mul] using (Nat.factorial_mul_pow_le_factorial (m := t) (n := t))
  have hp : (0 : ℝ) < (t : ℝ) ^ t := by positivity
  have hl := log_le_log hp (show (t : ℝ) ^ t ≤ ((2 * t).factorial : ℝ) by exact_mod_cast hh)
  simpa only [log_pow] using hl

lemma shifted_hit_iff (x p : ℕ) (hp : 2 ≤ p) :
    x ≡ p - 2 [MOD p] ↔ p ∣ x + 2 := by
  have hh : p - 2 + 2 = p := by omega
  constructor
  · intro h
    have he := h.add_right 2
    rw [hh] at he
    exact Nat.modEq_zero_iff_dvd.mp (he.trans (by simp [Nat.ModEq]))
  · intro h
    have he : x + 2 ≡ p - 2 + 2 [MOD p] := by
      rw [hh]
      exact (Nat.modEq_zero_iff_dvd.mpr h).trans (by simp [Nat.ModEq])
    exact Nat.ModEq.add_right_cancel' 2 he

/-- The interval corresponding to 2,...,t! is covered by all primes ≤t!,
with pointwise overlap at most t. -/
theorem factorial_cover (t : ℕ) (ht : 2 ≤ t) :
    let P := (t.factorial + 1).primesBelow
    let m := t.factorial - 1
    (∀ p ∈ P, p.Prime) ∧ P.card = t.factorial.primeCounting ∧
      (∀ x < m, ∃ p ∈ P, x ≡ p - 2 [MOD p]) ∧
      (∀ x < m, (P.filter (fun p => x ≡ p - 2 [MOD p])).card ≤ t) := by
  classical
  dsimp only
  have hP (p : ℕ) (hp : p ∈ (t.factorial + 1).primesBelow) : p.Prime :=
    (Nat.mem_primesBelow.mp hp).2
  refine ⟨hP, ?_, ?_, ?_⟩
  · simp only [Nat.primesBelow, Nat.primeCounting, Nat.primeCounting',
      Nat.count_eq_card_filter_range]
  · intro x hx
    have hxn : x + 2 ≤ t.factorial := by omega
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : x + 2 ≠ 1)
    have hpl : p ≤ x + 2 := Nat.le_of_dvd (by omega) hpd
    refine ⟨p, Nat.mem_primesBelow.mpr ⟨by omega, hp⟩, ?_⟩
    exact (shifted_hit_iff x p hp.two_le).mpr hpd
  · intro x hx
    have hsub : ((t.factorial + 1).primesBelow.filter
        (fun p => x ≡ p - 2 [MOD p])) ⊆ (x + 2).primeFactors := by
      intro p hp
      obtain ⟨hpP, hhit⟩ := mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨hP p hpP,
        (shifted_hit_iff x p (hP p hpP).two_le).mp hhit, by omega⟩
    exact (card_le_card hsub).trans
      (primeFactors_card_le_of_le_factorial (by omega) (by omega) (by omega))

/-- An explicit family with unbounded length/(prime budget * allowed overlap).
The overlap bound is part of the conclusion, not an assumption about arbitrary covers. -/
theorem exists_cover_gt_card_mul_multiplicity (C : ℝ) (hC : 0 < C) :
    ∃ (P : Finset ℕ) (r : ℕ → ℕ) (m B : ℕ),
      (∀ p ∈ P, p.Prime) ∧
      (∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p]) ∧
      (∀ x < m, (P.filter (fun p => x ≡ r p [MOD p])).card ≤ B) ∧
      C * P.card * B < (m : ℝ) := by
  let A : ℝ := log 4 + 1
  have hA : 0 < A := by
    dsimp [A]
    have := log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    linarith
  have hcheb : ∀ᶠ n : ℕ in atTop,
      (n.primeCounting : ℝ) ≤ A * n / log n := by
    simpa only [Nat.floor_natCast, A] using
      tendsto_natCast_atTop_atTop.eventually
        (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hcheb
  have hlog : ∀ᶠ t : ℕ in atTop, 8 * C * A < log (t : ℝ) :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop _)
  obtain ⟨t, htN, ht2, htlog⟩ := (eventually_ge_atTop N |>.and
    ((eventually_ge_atTop 2).and hlog)).exists
  let F := (2 * t).factorial
  have htpos : 0 < t := by omega
  have hF : 2 ≤ F := by
    have hh := Nat.self_le_factorial (2 * t)
    dsimp [F]
    omega
  have hNF : N ≤ F := by
    have hh := Nat.self_le_factorial (2 * t)
    dsimp [F]
    omega
  have hFR : (0 : ℝ) < F := by exact_mod_cast (show 0 < F by omega)
  have htR : (0 : ℝ) < t := by exact_mod_cast htpos
  have hlogF : 0 < log (F : ℝ) := log_pos (by exact_mod_cast hF)
  have hloglower : (t : ℝ) * log (t : ℝ) ≤ log (F : ℝ) :=
    log_double_factorial_lower t htpos
  have hlargeLog : 8 * C * A * t < log (F : ℝ) := by
    have hh := mul_lt_mul_of_pos_left htlog htR
    nlinarith only [hh, hloglower]
  have hpi := hN F hNF
  have hpi' : (F.primeCounting : ℝ) * log (F : ℝ) ≤ A * F :=
    (le_div_iff₀ hlogF).mp hpi
  have hbound : C * (F.primeCounting : ℝ) * (2 * t) < (F : ℝ) / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hpi'
      (show 0 ≤ C * (2 * (t : ℝ)) by positivity)
    have hgap := mul_lt_mul_of_pos_right hlargeLog hFR
    apply (mul_lt_mul_iff_left₀ hlogF).mp
    nlinarith only [hmul, hgap, mul_pos hFR hlogF]
  obtain ⟨hP, hcard, hcover, hmult⟩ := factorial_cover (2 * t) (by omega)
  refine ⟨(F + 1).primesBelow, fun p => p - 2, F - 1, 2 * t,
    hP, hcover, hmult, ?_⟩
  rw [hcard]
  have hhalf : (F : ℝ) / 2 ≤ (F - 1 : ℕ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ F), Nat.cast_one]
    have hh : (2 : ℝ) ≤ F := by exact_mod_cast hF
    linarith
  have hh := hbound.trans_le hhalf
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh

/-- This auxiliary proposal is false; no negation of erdos_970 is claimed. -/
theorem no_uniform_linear_overlap_bound :
    ¬∃ C > (0 : ℝ), ∀ (P : Finset ℕ) (r : ℕ → ℕ) (m B : ℕ),
      (∀ p ∈ P, p.Prime) →
      (∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p]) →
      (∀ x < m, (P.filter (fun p => x ≡ r p [MOD p])).card ≤ B) →
      (m : ℝ) ≤ C * P.card * B := by
  rintro ⟨C, hC, h⟩
  obtain ⟨P, r, m, B, hP, hcover, hmult, hlt⟩ :=
    exists_cover_gt_card_mul_multiplicity C hC
  exact hlt.not_ge (h P r m B hP hcover hmult)

#print axioms factorial_cover
#print axioms exists_cover_gt_card_mul_multiplicity
#print axioms no_uniform_linear_overlap_bound
end Erdos970.MultiplicityObstruction
