import Submission.FilteredCoefficientGcd

/-!
Large-prime valuation bounds in late filtered coefficient windows.
This file does not settle Erdos 68 and does not bound integer lifts.
-/

namespace FilteredWindowGcd

open Finset FilteredCoefficientGcd BinomialFilteredLambert

/-- The factorial is included alongside the individual window coefficients. -/
def windowGcd (a : ℕ → ℤ) (H N : ℕ) : ℕ :=
  Nat.gcd N.factorial ((Finset.Icc H N).gcd (scaledCoeff a N))

lemma windowGcd_pos (a : ℕ → ℤ) (H N : ℕ) : 0 < windowGcd a H N :=
  Nat.gcd_pos_of_pos_left _ (Nat.factorial_pos N)

lemma windowGcd_dvd_factorial (a : ℕ → ℤ) (H N : ℕ) :
    windowGcd a H N ∣ N.factorial := Nat.gcd_dvd_left _ _

lemma windowGcd_dvd_scaled (a : ℕ → ℤ) (H N k : ℕ)
    (hk : k ∈ Finset.Icc H N) : windowGcd a H N ∣ scaledCoeff a N k :=
  (Nat.gcd_dvd_right _ _).trans (Finset.gcd_dvd hk)

lemma factorial_quotient_pos (u N : ℕ) (hu : u ≤ N) :
    0 < N.factorial / u.factorial :=
  Nat.div_pos (Nat.factorial_le hu) (Nat.factorial_pos u)

lemma factorial_quotient_not_dvd (p u N : ℕ) (hp : p.Prime) (hu : u ≤ N)
    (hgap : ∀ k, u < k → k ≤ N → ¬p ∣ k) : ¬p ∣ N.factorial / u.factorial := by
  induction N with
  | zero =>
    have : u=0 := by omega
    subst u
    simpa using hp.not_dvd_one
  | succ N ih =>
    by_cases he : u=N+1
    · subst u
      simpa only [Nat.div_self (Nat.factorial_pos _)] using hp.not_dvd_one
    have huN : u ≤ N := by omega
    rw [Nat.factorial_succ,
      Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial huN)]
    intro h
    rcases hp.dvd_mul.mp h with hleft | hright
    · exact hgap (N+1) (by omega) le_rfl hleft
    · exact ih huN (fun k hk hkn => hgap k hk (by omega)) hright

lemma quotient_valuation_le_last (p u N : ℕ) (hp : p.Prime)
    (hu : u ≤ N) (hN : 0 < N)
    (hgap : ∀ k, u < k → k < N → ¬p ∣ k) :
    (N.factorial / u.factorial).factorization p ≤ N.factorization p := by
  by_cases he : u=N
  · subst u
    simp only [Nat.div_self (Nat.factorial_pos _), Nat.factorization_one,
      Finsupp.zero_apply]
    omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have hun : u ≤ n := by omega
  have hq := factorial_quotient_not_dvd p u n hp hun
    (fun k hk hkn => hgap k hk (by omega))
  rw [Nat.factorial_succ,
    Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial hun),
    Nat.factorization_mul (by omega) (factorial_quotient_pos u n hun).ne',
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hq, add_zero]

lemma bound_from_unit_index (a : ℕ → ℤ) (p H N u : ℕ) (hp : p.Prime)
    (hu : u ∈ Finset.Icc H N) (hunit : Int.ModEq p (a u) 1)
    (hq : (N.factorial/u.factorial).factorization p ≤ N.factorization p) :
    (windowGcd a H N).factorization p ≤ N.factorization p := by
  have habs := modEq_one_not_dvd hp hunit
  have habs0 : (a u).natAbs ≠ 0 := by
    intro hz
    exact habs (hz ▸ dvd_zero p)
  have huN := (Finset.mem_Icc.mp hu).2
  have hqpos := factorial_quotient_pos u N huN
  have hs : scaledCoeff a N u ≠ 0 := mul_ne_zero habs0 hqpos.ne'
  have hdiv := windowGcd_dvd_scaled a H N u hu
  have hle := (Nat.factorization_le_iff_dvd
    (windowGcd_pos a H N).ne' hs).mpr hdiv
  have hpoint := hle p
  rw [scaledCoeff, Nat.factorization_mul habs0 hqpos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd habs, zero_add] at hpoint
  exact hpoint.trans hq

/-- A congruent-to-one index after the last multiple of p below N. -/
lemma exists_pred_unit_index (p H N : ℕ) (hp : p.Prime) (hH : 2 ≤ H)
    (hHN : H ≤ N) (hpr : p ≤ N-H+1) :
    ∃ u, u ∈ Finset.Icc H N ∧ 2 ≤ u ∧ p ∣ u-1 ∧
      ∀ k, u < k → k < N → ¬p ∣ k := by
  let u := p*((N-1)/p)+1
  have hp0 := hp.pos
  have hrem := Nat.mod_lt (N-1) hp0
  have hdecomp := Nat.mod_add_div (N-1) p
  have hpN : p ≤ N-1 := by omega
  have hq : 1 ≤ (N-1)/p := (Nat.one_le_div_iff hp0).mpr hpN
  have hmul : p ≤ p*((N-1)/p) := Nat.le_mul_of_pos_right p hq
  have huH : H ≤ u := by dsimp [u]; omega
  have huN : u ≤ N := by dsimp [u]; omega
  have hu2 : 2 ≤ u := by dsimp [u]; have := hp.two_le; omega
  have hpu : p ∣ u-1 := by
    dsimp [u]
    exact dvd_mul_right p _
  refine ⟨u, Finset.mem_Icc.mpr ⟨huH, huN⟩, hu2, hpu, ?_⟩
  intro k huk hkN hpk
  have hd : p ∣ k-(u-1) := Nat.dvd_sub hpk hpu
  have hlo : 0 < k-(u-1) := by omega
  have hhi : k-(u-1) < p := by dsimp [u] at *; omega
  have hle := Nat.le_of_dvd hlo hd
  omega

/-- In a window [H,N] with N>=2H, the inherited large-prime gcd factors
are removed. This is a valuation bound, not a bound on representation weights. -/
theorem window_prime_valuation_bound (a : ℕ → ℤ) (p H N : ℕ) (hp : p.Prime)
    (hH : 2 ≤ H) (hHN : 2*H ≤ N)
    (hprime : Int.ModEq p (a p) 1)
    (hpred : ∀ n, 2 ≤ n → p ∣ n-1 → Int.ModEq p (a n) 1) :
    (windowGcd a H N).factorization p ≤ N.factorization p := by
  by_cases hpN : N < p
  · have hpf : ¬p ∣ N.factorial := fun h => (not_le_of_gt hpN) (hp.dvd_factorial.mp h)
    have hg : ¬p ∣ windowGcd a H N :=
      fun h => hpf (h.trans (windowGcd_dvd_factorial a H N))
    rw [Nat.factorization_eq_zero_of_not_dvd hg]
    omega
  by_cases hpr : p ≤ N-H+1
  · obtain ⟨u, hu, hu2, hpu, hgap⟩ :=
      exists_pred_unit_index p H N hp hH (by omega) hpr
    exact bound_from_unit_index a p H N u hp hu (hpred u hu2 hpu)
      (quotient_valuation_le_last p u N hp (Finset.mem_Icc.mp hu).2 (by omega) hgap)
  · have hpH : H ≤ p := by omega
    have hN2p : N < 2*p := by omega
    have hgap (k : ℕ) (hpk : p < k) (hkN : k ≤ N) : ¬p ∣ k := by
      intro hdiv
      obtain ⟨q, hq⟩ := hdiv
      have hq2 : 2 ≤ q := by
        by_contra h
        have hq1 : q ≤ 1 := by omega
        have hle := Nat.mul_le_mul_left p hq1
        omega
      have hle := Nat.mul_le_mul_left p hq2
      omega
    have hq := factorial_quotient_not_dvd p p N hp (by omega) hgap
    apply bound_from_unit_index a p H N p hp
      (Finset.mem_Icc.mpr ⟨hpH, by omega⟩) hprime
    rw [Nat.factorization_eq_zero_of_not_dvd hq]
    omega

theorem filtered_window_prime_valuation_bound (ks : List ℕ) (p H N : ℕ)
    (hp : p.Prime) (hH : 2 ≤ H) (hHN : 2*H ≤ N)
    (hks : ∀ k ∈ ks, 2 ≤ k ∧ k < p) :
    (windowGcd (filtered ks) H N).factorization p ≤ N.factorization p := by
  apply window_prime_valuation_bound (filtered ks) p H N hp hH hHN
  · simpa only [Nat.zero_add, pow_one] using
      filtered_prime_power ks p 0 hp (fun k hk => ⟨by have := hks k hk; omega,
        by simpa only [Nat.zero_add, pow_one] using (hks k hk).2⟩)
  · exact fun n hn hpn => filtered_at_pred ks p n hp hn hpn hks

end FilteredWindowGcd

#print axioms FilteredWindowGcd.window_prime_valuation_bound
#print axioms FilteredWindowGcd.filtered_window_prime_valuation_bound
