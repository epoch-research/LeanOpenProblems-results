import Submission.CongruentTailSeparation

/-! Relatively close prime pairs, derived from divergence of prime reciprocals.
This is used only for an auxiliary factorial-series criterion. -/

namespace CongruentTailSeparation

open Filter

/-- There are arbitrarily large pairs of prime predecessors separated by more
than 2C, but close enough for the integer-tail separation lemma. -/
theorem prime_predecessor_pairs (C M : ℕ) :
    ∃ a ≥ M, ∃ L : ℕ, 2 * C < L ∧ (C + 1) * L + C < a ∧
      (a + 1).Prime ∧ (a + L + 1).Prime := by
  by_contra h
  push_neg at h
  let m : ℕ := 2 * C + 1
  have hm : 0 < m := by dsimp [m]; omega
  letI : NeZero m := ⟨by omega⟩
  let r : ℝ := (2 * (C + 1) : ℝ) / (2 * (C + 1) + 1)
  have hrp : 0 < r := by dsimp [r]; positivity
  have hrl : r < 1 := by dsimp [r]; apply (div_lt_one (by positivity)).mpr; linarith
  let f : ℕ → ℝ := fun n => 1 / (Nat.nth Nat.Prime n : ℝ)
  have hfpos (n : ℕ) : 0 < f n := by
    dsimp [f]
    exact one_div_pos.mpr (by exact_mod_cast (Nat.prime_nth_prime n).pos)
  have hstep (n : ℕ) (hn : max M (2 * (C + 1)) ≤ n) : f (n + m) ≤ r * f n := by
    let p := Nat.nth Nat.Prime n
    let q := Nat.nth Nat.Prime (n + m)
    have hp : p.Prime := Nat.prime_nth_prime n
    have hq : q.Prime := Nat.prime_nth_prime (n + m)
    have hpn : n + 2 ≤ p := Nat.add_two_le_nth_prime n
    have hpq : m + p ≤ q := by
      simpa [p, q, Nat.add_comm] using (Nat.nth_strictMono Nat.infinite_setOf_prime).add_le_nat m n
    have hfar : p - 1 ≤ (C + 1) * (q - p) + C := by
      by_contra hh
      have hlarge : (C + 1) * (q - p) + C < p - 1 := by omega
      have hbad := h (p - 1) (by omega) (q - p) (by dsimp [m] at hpq; omega) hlarge
      have he1 : p - 1 + 1 = p := by omega
      have he2 : p - 1 + (q - p) + 1 = q := by omega
      rw [he1, he2] at hbad
      exact hbad hp hq
    have hpbd : 2 * (C + 1) ≤ p := by omega
    have hi : ((C : ℝ) + 1) * q ≥ ((C : ℝ) + 2) * p - ((C : ℝ) + 1) := by
      have he : (C + 1) * p + p ≤ (C + 1) * q + C + 1 := by
        have he : (C + 1) * (q - p) + (C + 1) * p = (C + 1) * q := by
          rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
        omega
      have hh : ((C : ℝ) + 1) * p + p ≤ ((C : ℝ) + 1) * q + C + 1 := by
        exact_mod_cast he
      nlinarith
    have hpbd' : (2 : ℝ) * (C + 1) ≤ p := by exact_mod_cast hpbd
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq.pos
    change 1 / (q : ℝ) ≤ r * (1 / (p : ℝ))
    dsimp [r]
    apply (div_le_iff₀ hq').mpr
    field_simp
    nlinarith
  have hres (j : Fin m) : Summable (fun n : ℕ => f (n * m + j)) := by
    apply summable_of_ratio_norm_eventually_le hrl
    filter_upwards [eventually_ge_atTop (max M (2 * (C + 1)))] with n hn
    have hnm : n ≤ n * m := by nlinarith
    have hh := hstep (n * m + j) (by omega)
    simpa only [Real.norm_eq_abs, abs_of_pos (hfpos _), Nat.add_mul, Nat.one_mul,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hh
  have hprod : Summable (fun x : Fin m × ℕ => f (x.2 * m + x.1)) := by
    apply (summable_prod_of_nonneg (fun x => (hfpos _).le)).mpr
    exact ⟨hres, summable_of_finite_support (Set.toFinite _)⟩
  have hprod' : Summable (fun x : ℕ × Fin m => f (x.1 * m + x.2)) := by
    exact (Equiv.prodComm (Fin m) ℕ).symm.summable_iff.mpr hprod
  have hs : Summable f := by
    apply (Nat.divModEquiv m).symm.summable_iff.mp
    simpa only [Function.comp_def, Nat.divModEquiv_symm_apply] using hprod'
  have hc : Function.Injective (fun p : Nat.Primes => Nat.count Nat.Prime p) := by
    intro p q hpq
    exact Subtype.ext (Nat.count_injective p.property q.property hpq)
  have hsp := hs.comp_injective hc
  have hpfull : Summable (fun p : Nat.Primes => (1 : ℝ) / p) := by
    convert hsp using 1
    funext p
    dsimp [Function.comp_def, f]
    rw [Nat.nth_count p.property]
  exact Nat.Primes.not_summable_one_div hpfull

/-- Prime unit coefficients and the predecessor congruence force irrationality
when the scaled tails are nonnegative and bounded by a fixed multiple of n. -/
theorem irrational_of_linear_tails_prime_coefficients (c : ℕ → ℤ) (C N : ℕ)
    (hc : ∀ n ≥ N, (n : ℤ) ∣ c (n + 1) - 1)
    (ht : ∀ n ≥ N, 0 ≤ FactorialTailCriterion.scaledTail c n ∧
      FactorialTailCriterion.scaledTail c n ≤ (C : ℝ) * n)
    (hp : ∀ p ≥ N, p.Prime → c p = 1) :
    Irrational (∑' k : ℕ, (c k : ℝ) / k.factorial) := by
  apply irrational_of_linear_tails_and_unit_pairs c C N hc ht
  intro M
  obtain ⟨a, ha, L, hgap, hlarge, hp1, hp2⟩ := prime_predecessor_pairs C (max M N)
  exact ⟨a, by omega, L, hgap, hlarge,
    hp (a + 1) (by omega) hp1, hp (a + L + 1) (by omega) hp2⟩

#print axioms prime_predecessor_pairs
#print axioms irrational_of_linear_tails_prime_coefficients

end CongruentTailSeparation
