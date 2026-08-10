import FormalConjectures.Util.ProblemImports

example (p n : ℕ) (hp : Nat.Prime p) (hnp : n < p) (hple : p ≤ (3*n - 1)/2) :
    p ^ 3 ∣ Nat.choose (3*n) n * (Nat.choose (2*n) n)^2 := by
  have hp0 : 0 < p := hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  have hn0 : 0 < n := by omega
  have h2p : 2*p < 3*n := by omega
  have hp2n : p ≤ 2*n := by omega
  have h3n_lt : 3*n < p^2 := by nlinarith [hnp, hp2]
  have h2n_lt : 2*n < p^2 := by nlinarith [hnp, hp2]
  have hchoose3_ne : Nat.choose (3*n) n ≠ 0 := Nat.choose_ne_zero (by omega)
  have hchoose2_ne : Nat.choose (2*n) n ≠ 0 := Nat.choose_ne_zero (by omega)
  rw [hp.pow_dvd_iff_le_factorization (by positivity)]
  rw [Nat.factorization_mul hchoose3_ne (pow_ne_zero 2 hchoose2_ne)]
  simp only [Finsupp.coe_add, Pi.add_apply, Nat.factorization_pow]
  have hfac2 : (Nat.choose (2*n) n).factorization p = 1 := by
    rw [Nat.factorization_choose hp (by omega) (b:=2)]
    · simp only [Finset.Ico_eq_singleton, Finset.mem_singleton, true_and, Finset.filter_true_of_mem,
        Finset.card_singleton]
      have hn_mod : n % p = n := Nat.mod_eq_of_lt hnp
      rw [hn_mod, hn_mod]
      omega
    · rw [Nat.log_lt_iff_lt_pow hp2 (by decide : 1 < 2)]
      exact h2n_lt
  have hfac3 : 1 ≤ (Nat.choose (3*n) n).factorization p := by
    rw [Nat.factorization_choose hp (by omega) (b:=2)]
    · simp only [Finset.Ico_eq_singleton, Finset.mem_singleton]
      rw [Finset.card_eq_one]
      refine ⟨1, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_singleton, true_and]
        have hn_mod : n % p = n := Nat.mod_eq_of_lt hnp
        rw [hn_mod]
        -- (3n-n)=2n; (2n)%p = 2n-p since p<=2n<2p
        have h2n_lt_2p : 2*n < 2*p := by omega
        have hmod2 : (3*n - n) % p = 2*n - p := by
          have h3 : 3*n - n = 2*n := by omega
          rw [h3]
          exact Nat.mod_eq_of_lt_of_le (by omega) hp2n
        rw [hmod2]
        omega
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_singleton] at hy
        exact hy.1
    · rw [Nat.log_lt_iff_lt_pow hp2 (by decide : 1 < 2)]
      exact h3n_lt
  rw [hfac2]
  omega
