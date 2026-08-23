import FormalConjectures.Util.ProblemImports

open Nat

lemma prime_mod_thirty_of_gt_five {q : ℕ} (hq : q.Prime) (h5 : 5 < q) :
    q % 30 = 1 ∨ q % 30 = 7 ∨ q % 30 = 11 ∨ q % 30 = 13 ∨
    q % 30 = 17 ∨ q % 30 = 19 ∨ q % 30 = 23 ∨ q % 30 = 29 := by
  have h2 : q % 2 = 1 := by
    have : q ≠ 2 := by omega
    exact (hq.eq_two_or_odd).resolve_left this
  have h3 : q % 3 ≠ 0 := by
    intro h0
    have hdvd : 3 ∣ q := Nat.dvd_iff_mod_eq_zero.2 h0
    have : 3 = q := (prime_dvd_prime_iff_eq prime_three hq).mp hdvd
    omega
  have h5m : q % 5 ≠ 0 := by
    intro h0
    have hdvd : 5 ∣ q := Nat.dvd_iff_mod_eq_zero.2 h0
    have : 5 = q := (prime_dvd_prime_iff_eq prime_five hq).mp hdvd
    omega
  have hlt : q % 30 < 30 := Nat.mod_lt _ (by decide)
  have hcases : q % 30 = 0 ∨ q % 30 = 1 ∨ q % 30 = 2 ∨ q % 30 = 3 ∨ q % 30 = 4 ∨
      q % 30 = 5 ∨ q % 30 = 6 ∨ q % 30 = 7 ∨ q % 30 = 8 ∨ q % 30 = 9 ∨
      q % 30 = 10 ∨ q % 30 = 11 ∨ q % 30 = 12 ∨ q % 30 = 13 ∨ q % 30 = 14 ∨
      q % 30 = 15 ∨ q % 30 = 16 ∨ q % 30 = 17 ∨ q % 30 = 18 ∨ q % 30 = 19 ∨
      q % 30 = 20 ∨ q % 30 = 21 ∨ q % 30 = 22 ∨ q % 30 = 23 ∨ q % 30 = 24 ∨
      q % 30 = 25 ∨ q % 30 = 26 ∨ q % 30 = 27 ∨ q % 30 = 28 ∨ q % 30 = 29 := by
    omega
  rcases hcases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inl h
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 3 = 0 := by omega
    exact (h3 this).elim
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 5 = 0 := by omega
    exact (h5m this).elim
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inl h)
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 3 = 0 := by omega
    exact (h3 this).elim
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inr (Or.inl h))
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 3 = 0 := by omega
    exact (h3 this).elim
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 3 = 0 := by omega
    exact (h3 this).elim
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 5 = 0 := by omega
    exact (h5m this).elim
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 3 = 0 := by omega
    exact (h3 this).elim
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
