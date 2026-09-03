import Submission.UnitTailSeparation

/-!
An auxiliary strengthening of the congruent factorial-tail criterion.
No application to the conjecture in Spec.lean is asserted here.
-/

namespace SubquadraticTailCriterion

open Filter

set_option maxHeartbeats 2000000 in
/-- Prime predecessors have arbitrarily large pairs whose squared gap is
small relative to the first predecessor. The proof uses only divergence of
prime reciprocals, not a quantitative prime number theorem. -/
theorem prime_predecessor_pairs_square (C M : ℕ) :
    ∃ a ≥ M, ∃ L : ℕ, 0 < L ∧ (C + 1) * (L + 1) ^ 2 < a ∧
      (a + 1).Prime ∧ (a + L + 1).Prime := by
  by_contra h
  push_neg at h
  let D := C + 1
  let B := 5 * D
  let J := 4 * D + M + 2
  let P := Nat.nth Nat.Prime
  have hD : 0 < D := by dsimp [D]; omega
  have hB : 0 < B := by dsimp [B]; positivity
  letI : NeZero B := ⟨by omega⟩
  have hmono : Monotone P := (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone
  have hgap (i n : ℕ) (hiM : M ≤ P i - 1)
      (hin : D * (n + 2) ^ 2 + 1 ≤ P i) :
      P i + (n + 1) ≤ P (i + 1) := by
    have hp : (P i).Prime := Nat.prime_nth_prime i
    have hq : (P (i + 1)).Prime := Nat.prime_nth_prime (i + 1)
    have hpq : P i < P (i + 1) := Nat.nth_strictMono Nat.infinite_setOf_prime (by omega)
    let L := P (i + 1) - P i
    have hL : 0 < L := by dsimp [L]; omega
    have hfar : P i - 1 ≤ D * (L + 1) ^ 2 := by
      by_contra hh
      have hbad := h (P i - 1) hiM L hL (by dsimp [D] at *; omega)
      have he1 : P i - 1 + 1 = P i := by have := hp.two_le; omega
      have he2 : P i - 1 + L + 1 = P (i + 1) := by
        dsimp [L]
        have := hp.two_le
        omega
      rw [he1, he2] at hbad
      exact hbad hp hq
    have hs : D * (n + 2) ^ 2 ≤ D * (L + 1) ^ 2 := by omega
    have hnL := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
      (Nat.le_of_mul_le_mul_left hs hD)
    dsimp [L] at hnL
    omega
  have hgrowth (n : ℕ) : D * (n + 2) ^ 2 + M + 1 ≤ P (J + B * n) := by
    induction n with
    | zero =>
        have hp := Nat.add_two_le_nth_prime J
        dsimp [P, J] at *
        nlinarith
    | succ n ih =>
        have hwalk (j : ℕ) : P (J + B * n) + j * (n + 1) ≤ P (J + B * n + j) := by
          induction j with
          | zero => simp
          | succ j hj =>
              have hm := hmono (show J + B * n ≤ J + B * n + j by omega)
              have hh := hgap (J + B * n + j) n (by omega) (by omega)
              rw [show J + B * n + j + 1 = J + B * n + (j + 1) by omega] at hh
              nlinarith
        have hh := hwalk B
        have hi : J + B * (n + 1) = J + B * n + B := by ring
        rw [hi]
        dsimp [B] at hh
        nlinarith [Nat.zero_le (D * n)]
  have hseries : Summable (fun n : ℕ => 1 / (((n + 2 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))
  let f : ℕ → ℝ := fun n => 1 / (P n : ℝ)
  have hfpos (n : ℕ) : 0 < f n := by
    dsimp [f, P]
    exact one_div_pos.mpr (by exact_mod_cast (Nat.prime_nth_prime n).pos)
  have hres (j : Fin B) : Summable (fun n : ℕ => f (n * B + j)) := by
    apply (summable_nat_add_iff J).mp
    apply hseries.of_nonneg_of_le (fun n => (hfpos _).le)
    intro n
    dsimp [f]
    have hJB : J ≤ J * B := Nat.le_mul_of_pos_right J hB
    have hm := hmono (show J + B * n ≤ (n + J) * B + j by nlinarith)
    have hg := hgrowth n
    have hsq : (n + 2) ^ 2 ≤ P ((n + J) * B + j) := by
      have hmul := Nat.mul_le_mul_right ((n + 2) ^ 2) (show 1 ≤ D by omega)
      nlinarith
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hsq)
  have hprod : Summable (fun x : Fin B × ℕ => f (x.2 * B + x.1)) := by
    apply (summable_prod_of_nonneg (fun x => (hfpos _).le)).mpr
    exact ⟨hres, summable_of_finite_support (Set.toFinite _)⟩
  have hprod' : Summable (fun x : ℕ × Fin B => f (x.1 * B + x.2)) :=
    (Equiv.prodComm (Fin B) ℕ).symm.summable_iff.mpr hprod
  have hs : Summable f := by
    apply (Nat.divModEquiv B).symm.summable_iff.mp
    simpa only [Function.comp_def, Nat.divModEquiv_symm_apply] using hprod'
  have hc : Function.Injective (fun p : Nat.Primes => Nat.count Nat.Prime p) := by
    intro p q hpq
    exact Subtype.ext (Nat.count_injective p.property q.property hpq)
  have hsp := hs.comp_injective hc
  have hpfull : Summable (fun p : Nat.Primes => (1 : ℝ) / p) := by
    convert hsp using 1
    funext p
    dsimp [Function.comp_def, f, P]
    rw [Nat.nth_count p.property]
  exact Nat.Primes.not_summable_one_div hpfull

/-- Local interval bounds suffice; their constants may vary between pairs.
This is a criterion, not an application to the original series. -/
theorem irrational_of_local_tails_and_unit_pairs (c : ℕ → ℤ) (N : ℕ)
    (hc : ∀ n ≥ N, (n : ℤ) ∣ c (n + 1) - 1)
    (hpairs : ∀ M : ℕ, ∃ a ≥ M, ∃ L H : ℕ, 0 < L ∧
      a * L + (L + 1) * H + 1 < a ^ 2 ∧
      c (a + 1) = 1 ∧ c (a + L + 1) = 1 ∧
      ∀ i ≤ L + 1, 0 ≤ FactorialTailCriterion.scaledTail c (a + i) ∧
        FactorialTailCriterion.scaledTail c (a + i) ≤ H) :
    Irrational (∑' k : ℕ, (c k : ℝ) / k.factorial) := by
  rintro ⟨q, hq⟩
  let t : ℕ → ℤ := fun n => q.num * (n.factorial / q.den : ℕ) -
    FactorialTailCriterion.factorialPrefix c n
  have htcast (n : ℕ) (hn : q.den ≤ n) :
      (t n : ℝ) = FactorialTailCriterion.scaledTail c n := by
    have hd : q.den ∣ n.factorial := Nat.dvd_factorial q.pos hn
    have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    simp only [t, FactorialTailCriterion.scaledTail, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    rw [← hq, FactorialTailCriterion.cast_factorialPrefix, Nat.cast_div hd hden, Rat.cast_def]
    ring
  obtain ⟨a, ha, L, H, hL, hsize, hfirst, hlast, hb⟩ := hpairs (max N q.den + 1)
  have hrec (n : ℕ) (hn : a ≤ n) :
      t (n + 1) = (n + 1 : ℤ) * t n - c (n + 1) := by
    have h := FactorialTailCriterion.scaledTail_succ c n
    rw [← htcast n (by omega), ← htcast (n + 1) (by omega)] at h
    exact_mod_cast h
  apply UnitTailSeparation.no_close_unit_returns t a L H (by omega) hL hsize
  · intro i hi
    have h := hb i hi
    rw [← htcast (a + i) (by omega)] at h
    exact_mod_cast h
  · rw [hrec a le_rfl, hfirst]
  · rw [hrec (a + L) (by omega), hlast]
    push_cast
    ring
  · intro i hi
    rw [hrec (a + i) (by omega)]
    have hd := hc (a + i) (by omega)
    convert dvd_sub (dvd_mul_right (a + i : ℤ) (t (a + i))) hd using 1; push_cast; ring

/-- Elementary estimates for the interval around a close prime pair. -/
lemma local_sqrt_bounds (C a L : ℕ) (hL : 0 < L)
    (hgap : ((16 * (C + 1)) ^ 2 + 1) * (L + 1) ^ 2 < a) :
    a * L + (L + 1) * (8 * C * a * Nat.sqrt a) + 1 < a ^ 2 ∧
      ∀ i ≤ L + 1,
        C * (a + i) * (Nat.sqrt (a + i) + 1) ≤ 8 * C * a * Nat.sqrt a := by
  let s := Nat.sqrt a
  have hsa : s ^ 2 ≤ a := Nat.sqrt_le' a
  have has : a < (s + 1) ^ 2 := Nat.lt_succ_sqrt' a
  have hsA : s ≤ a := Nat.sqrt_le_self a
  have hR : 16 * (C + 1) * (L + 1) ≤ s := by
    apply Nat.le_sqrt'.mpr
    have hh : (16 * (C + 1)) ^ 2 * (L + 1) ^ 2 < a := by
      exact (Nat.mul_le_mul_right _ (Nat.le_succ _)).trans_lt hgap
    simpa only [mul_pow] using hh.le
  have hLs : L + 1 ≤ s := by nlinarith
  have hsp : 1 ≤ s := by omega
  have ha : 2 ≤ a := by omega
  have hRC : 16 * C * (L + 1) ≤ s := by nlinarith
  have h16L : 16 * L ≤ a := by nlinarith
  have hsize₁ : 16 * (a * L) ≤ a ^ 2 := by
    have hh := Nat.mul_le_mul_left a h16L
    nlinarith
  have hsize₂ : 16 * ((L + 1) * (8 * C * a * s)) ≤ 8 * a ^ 2 := by
    calc
      _ = (8 * a * s) * (16 * C * (L + 1)) := by ring
      _ ≤ (8 * a * s) * s := Nat.mul_le_mul_left _ hRC
      _ = (8 * a) * s ^ 2 := by ring
      _ ≤ (8 * a) * a := Nat.mul_le_mul_left _ hsa
      _ = _ := by ring
  constructor
  · change a * L + (L + 1) * (8 * C * a * s) + 1 < a ^ 2
    nlinarith [Nat.mul_self_le_mul_self ha]
  · intro i hi
    have hn : a + i ≤ 2 * a := by omega
    have hsqrt : Nat.sqrt (a + i) + 1 ≤ 4 * s := by
      have hh : Nat.sqrt (a + i) < 2 * s + 2 := by
        apply Nat.sqrt_lt'.mpr
        nlinarith
      omega
    calc
      _ ≤ C * (2 * a) * (4 * s) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left C hn) hsqrt
      _ = _ := by dsimp [s]; ring

/-- Congruent factorial coefficients with prime coefficients equal to one
have an irrational sum if their nonnegative scaled tails are eventually
bounded by `C * n * (sqrt n + 1)`. The square root here is the natural square
root. No target representation satisfying all these hypotheses is known in
this development. -/
theorem irrational_of_sqrt_tails_prime_coefficients (c : ℕ → ℤ) (C N : ℕ)
    (hc : ∀ n ≥ N, (n : ℤ) ∣ c (n + 1) - 1)
    (ht : ∀ n ≥ N, 0 ≤ FactorialTailCriterion.scaledTail c n ∧
      FactorialTailCriterion.scaledTail c n ≤ (C : ℝ) * n * (Nat.sqrt n + 1 : ℝ))
    (hp : ∀ p ≥ N, p.Prime → c p = 1) :
    Irrational (∑' k : ℕ, (c k : ℝ) / k.factorial) := by
  apply irrational_of_local_tails_and_unit_pairs c N hc
  intro M
  obtain ⟨a, ha, L, hL, hgap, hpa, hpb⟩ :=
    prime_predecessor_pairs_square ((16 * (C + 1)) ^ 2) (max M N)
  obtain ⟨hsize, hb⟩ := local_sqrt_bounds C a L hL hgap
  refine ⟨a, by omega, L, 8 * C * a * Nat.sqrt a, hL, hsize,
    hp (a + 1) (by omega) hpa, hp (a + L + 1) (by omega) hpb, ?_⟩
  intro i hi
  have ht' := ht (a + i) (by omega)
  refine ⟨ht'.1, ht'.2.trans ?_⟩
  exact_mod_cast hb i hi

#print axioms prime_predecessor_pairs_square
#print axioms irrational_of_local_tails_and_unit_pairs
#print axioms irrational_of_sqrt_tails_prime_coefficients

end SubquadraticTailCriterion
