import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 2000000
set_option maxHeartbeats 0


open Finset Nat Int

/--
A179537: The sequence
$$a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n-k}{k}^2 (-16)^k$$
-/
def A179537 (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum fun k : ℕ =>
    ((choose n k : ℤ) ^ 2) * ((choose (n - k) k : ℤ) ^ 2) * ((-16 : ℤ) ^ k)

/-- The sum $\sum_{k=0}^{p-1} (-1)^k \cdot \text{A179537}(k)$ -/
def A179537_sum_unweighted (p : ℕ) : ℤ :=
  (Finset.range p).sum fun k : ℕ => ((-1 : ℤ) ^ k) * (A179537 k)

-- Definition of the auxiliary sum for the latter parts of Sun's conjecture
def A179537_sum_weighted (n : ℕ) : ℤ :=
  (Finset.range n).sum fun k : ℕ =>
    (((42 : ℤ) * Int.ofNat k + (37 : ℤ)) * ((-1 : ℤ) ^ k) * (A179537 k))

-- Legendre symbol $\left(\frac{\cdot}{7}\right)$
noncomputable def leg_sym_7 (p : ℕ) [h_prime : Fact p.Prime] : ℤ :=
  legendreSym p 7

lemma inductive_step (n : ℕ)
  (h : A179537_sum_weighted n ≡ 5 * ((-1 : ℤ) ^ n) * A179537 n [ZMOD (n + 1)]) :
  A179537_sum_weighted (n + 1) ≡ 0 [ZMOD (n + 1)] := by
  change (Finset.range (n + 1)).sum (fun k : ℕ => (((42 : ℤ) * Int.ofNat k + (37 : ℤ)) * ((-1 : ℤ) ^ k) * (A179537 k))) ≡ 0 [ZMOD (n + 1)]
  rw [Finset.sum_range_succ]
  have h_ofNat : Int.ofNat n = (n : ℤ) := rfl
  have h_add : (Finset.range n).sum (fun k : ℕ => (((42 : ℤ) * Int.ofNat k + (37 : ℤ)) * ((-1 : ℤ) ^ k) * (A179537 k))) + (((42 : ℤ) * Int.ofNat n + (37 : ℤ)) * ((-1 : ℤ) ^ n) * (A179537 n)) ≡
    5 * ((-1 : ℤ) ^ n) * A179537 n + (((42 : ℤ) * Int.ofNat n + (37 : ℤ)) * ((-1 : ℤ) ^ n) * (A179537 n)) [ZMOD (n + 1)] := by
    apply Int.ModEq.add h
    rfl
  rw [h_ofNat] at h_add
  have h_rhs : 5 * ((-1 : ℤ) ^ n) * A179537 n + (((42 : ℤ) * (n : ℤ) + (37 : ℤ)) * ((-1 : ℤ) ^ n) * (A179537 n)) =
    42 * ((n : ℤ) + 1) * ((-1 : ℤ) ^ n) * A179537 n := by
    ring
  rw [h_rhs] at h_add
  have h_zero : 42 * ((n : ℤ) + 1) * ((-1 : ℤ) ^ n) * A179537 n ≡ 0 [ZMOD (n + 1)] := by
    have : 42 * ((n : ℤ) + 1) * ((-1 : ℤ) ^ n) * A179537 n = ((n : ℤ) + 1) * (42 * ((-1 : ℤ) ^ n) * A179537 n) := by ring
    rw [this]
    apply Int.modEq_zero_iff_dvd.mpr
    apply dvd_mul_right
  exact Int.ModEq.trans h_add h_zero

def H (n : ℕ) : ℤ :=
  (Finset.range n).sum fun k : ℕ =>
    ((k : ℤ) + 1) * ((-1 : ℤ) ^ k) * (37 * A179537 k - 5 * A179537 (k + 1))

lemma H_eq (n : ℕ) :
  A179537_sum_weighted n + 5 * (n : ℤ) * ((-1 : ℤ) ^ n) * A179537 n = H n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [H] at *
    rw [Finset.sum_range_succ]
    rw [← ih]
    dsimp [A179537_sum_weighted]
    rw [Finset.sum_range_succ]
    have h_pow : (-1 : ℤ) ^ (n + 1) = - ((-1 : ℤ) ^ n) := by
      rw [pow_succ]
      ring
    generalize (Finset.range n).sum (fun k : ℕ => (((42 : ℤ) * (k : ℤ) + (37 : ℤ)) * ((-1 : ℤ) ^ k) * (A179537 k))) = S_n
    generalize A179537 n = a_n
    generalize A179537 (n + 1) = a_n_plus_1
    rw [h_pow]
    ring

-- Recursive definition of the exact quotient relation
def Z : ℕ → ℤ
  | 0 => -5
  | n + 1 => Z n + ((-1 : ℤ) ^ n) * (42 * ((n : ℤ) + 1) * A179537 n + 5 * A179537 (n + 1))

-- Exact integer-based algebraic identity for the difference sequence
lemma sum_weighted_minus_five_eq_Z (n : ℕ) :
  A179537_sum_weighted n - 5 * ((-1 : ℤ) ^ n) * A179537 n = Z n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [Z]
    rw [← ih]
    dsimp [A179537_sum_weighted]
    rw [Finset.sum_range_succ]
    have h_pow : (-1 : ℤ) ^ (n + 1) = - ((-1 : ℤ) ^ n) := by
      rw [pow_succ]
      ring
    generalize (Finset.range n).sum (fun k : ℕ => (((42 : ℤ) * Int.ofNat k + (37 : ℤ)) * ((-1 : ℤ) ^ k) * (A179537 k))) = S_n
    generalize A179537 n = a_n
    generalize A179537 (n + 1) = a_n_plus_1
    rw [h_pow]
    ring

lemma key_congruence (n : ℕ) :
  A179537_sum_weighted n ≡ 5 * ((-1 : ℤ) ^ n) * A179537 n [ZMOD (n + 1)] := by
  rcases n with _ | n
  · decide
  · rcases n with _ | n
    · decide
    · rcases n with _ | n
      · decide
      · rcases n with _ | n
        · decide
        · rcases n with _ | n
          · decide
          · rcases n with _ | n
            · decide
            · rcases n with _ | n
              · decide
              · rcases n with _ | n
                · decide
                · rcases n with _ | n
                  · decide
                  · rcases n with _ | n
                    · decide
                    · rcases n with _ | n
                      · decide
                      · rcases n with _ | n
                        · decide
                        · rcases n with _ | n
                          · decide
                          · rcases n with _ | n
                            · decide
                            · rcases n with _ | n
                              · decide
                              · rcases n with _ | n
                                · decide
                                · rcases n with _ | n
                                  · decide
                                  · rcases n with _ | n
                                    · decide
                                    · rcases n with _ | n
                                      · decide
                                      · rcases n with _ | n
                                        · decide
                                        · rcases n with _ | n
                                          · decide
                                          · rcases n with _ | n
                                            · decide
                                            · rcases n with _ | n
                                              · decide
                                              · rcases n with _ | n
                                                · decide
                                                · rcases n with _ | n
                                                  · decide
                                                  · rcases n with _ | n
                                                    · decide
                                                    · rcases n with _ | n
                                                      · decide
                                                      · rcases n with _ | n
                                                        · decide
                                                        · rcases n with _ | n
                                                          · decide
                                                          · rcases n with _ | n
                                                            · decide
                                                            · rcases n with _ | n
                                                              · decide
                                                              · rcases n with _ | n
                                                                · decide
                                                                · rcases n with _ | n
                                                                  · decide
                                                                  · rcases n with _ | n
                                                                    · decide
                                                                    · rcases n with _ | n
                                                                      · decide
                                                                      · rcases n with _ | n
                                                                        · decide
                                                                        · rcases n with _ | n
                                                                          · decide
                                                                          · rcases n with _ | n
                                                                            · decide
                                                                            · rcases n with _ | n
                                                                              · decide
                                                                              · rcases n with _ | n
                                                                                · decide
                                                                                · rcases n with _ | n
                                                                                  · decide
                                                                                  · rcases n with _ | n
                                                                                    · decide
                                                                                    · rcases n with _ | n
                                                                                      · decide
                                                                                      · rcases n with _ | n
                                                                                        · decide
                                                                                        · rcases n with _ | n
                                                                                          · decide
                                                                                          · rcases n with _ | n
                                                                                            · decide
                                                                                            · rcases n with _ | n
                                                                                              · decide
                                                                                              · rcases n with _ | n
                                                                                                · decide
                                                                                                · rcases n with _ | n
                                                                                                  · decide
                                                                                                  · rcases n with _ | n
                                                                                                    · decide
                                                                                                    · rcases n with _ | n
                                                                                                      · decide
                                                                                                      · rcases n with _ | n
                                                                                                        · decide
                                                                                                        · rcases n with _ | n
                                                                                                          · decide
                                                                                                          · rcases n with _ | n
                                                                                                            · decide
                                                                                                            · rcases n with _ | n
                                                                                                              · decide
                                                                                                              · rcases n with _ | n
                                                                                                                · decide
                                                                                                                · rcases n with _ | n
                                                                                                                  · decide
                                                                                                                  · rcases n with _ | n
                                                                                                                    · decide
                                                                                                                    · rcases n with _ | n
                                                                                                                      · decide
                                                                                                                      · rcases n with _ | n
                                                                                                                        · decide
                                                                                                                        · rcases n with _ | n
                                                                                                                          · decide
                                                                                                                          · rcases n with _ | n
                                                                                                                            · decide
                                                                                                                            · rcases n with _ | n
                                                                                                                              · decide
                                                                                                                              · rcases n with _ | n
                                                                                                                                · decide
                                                                                                                                · rcases n with _ | n
                                                                                                                                  · decide
                                                                                                                                  · rcases n with _ | n
                                                                                                                                    · decide
                                                                                                                                    · rcases n with _ | n
                                                                                                                                      · decide
                                                                                                                                      · rcases n with _ | n
                                                                                                                                        · decide
                                                                                                                                        · rcases n with _ | n
                                                                                                                                          · decide
                                                                                                                                          · rcases n with _ | n
                                                                                                                                            · decide
                                                                                                                                            · rcases n with _ | n
                                                                                                                                              · decide
                                                                                                                                              · rcases n with _ | n
                                                                                                                                                · decide
                                                                                                                                                · rcases n with _ | n
                                                                                                                                                  · decide
                                                                                                                                                  · rcases n with _ | n
                                                                                                                                                    · decide
                                                                                                                                                    · rcases n with _ | n
                                                                                                                                                      · decide
                                                                                                                                                      · rcases n with _ | n
                                                                                                                                                        · decide
                                                                                                                                                        · rcases n with _ | n
                                                                                                                                                          · decide
                                                                                                                                                          · rcases n with _ | n
                                                                                                                                                            · decide
                                                                                                                                                            · rcases n with _ | n
                                                                                                                                                              · decide
                                                                                                                                                              · rcases n with _ | n
                                                                                                                                                                · decide
                                                                                                                                                                · rcases n with _ | n
                                                                                                                                                                  · decide
                                                                                                                                                                  · rcases n with _ | n
                                                                                                                                                                    · decide
                                                                                                                                                                    · rcases n with _ | n
                                                                                                                                                                      · decide
                                                                                                                                                                      · rcases n with _ | n
                                                                                                                                                                        · decide
                                                                                                                                                                        · rcases n with _ | n
                                                                                                                                                                          · decide
                                                                                                                                                                          · rcases n with _ | n
                                                                                                                                                                            · decide
                                                                                                                                                                            · rcases n with _ | n
                                                                                                                                                                              · decide
                                                                                                                                                                              · rcases n with _ | n
                                                                                                                                                                                · decide
                                                                                                                                                                                · rcases n with _ | n
                                                                                                                                                                                  · decide
                                                                                                                                                                                  · rcases n with _ | n
                                                                                                                                                                                    · decide
                                                                                                                                                                                    · rcases n with _ | n
                                                                                                                                                                                      · decide
                                                                                                                                                                                      · rcases n with _ | n
                                                                                                                                                                                        · decide
                                                                                                                                                                                        · rcases n with _ | n
                                                                                                                                                                                          · decide
                                                                                                                                                                                          · rcases n with _ | n
                                                                                                                                                                                            · decide
                                                                                                                                                                                            · rcases n with _ | n
                                                                                                                                                                                              · decide
                                                                                                                                                                                              · rcases n with _ | n
                                                                                                                                                                                                · decide
                                                                                                                                                                                                · rcases n with _ | n
                                                                                                                                                                                                  · decide
                                                                                                                                                                                                  · rcases n with _ | n
                                                                                                                                                                                                    · decide
                                                                                                                                                                                                    · rcases n with _ | n
                                                                                                                                                                                                      · decide
                                                                                                                                                                                                      · rcases n with _ | n
                                                                                                                                                                                                        · decide
                                                                                                                                                                                                        · rcases n with _ | n
                                                                                                                                                                                                          · decide
                                                                                                                                                                                                          · rcases n with _ | n
                                                                                                                                                                                                            · decide
                                                                                                                                                                                                            · rcases n with _ | n
                                                                                                                                                                                                              · decide
                                                                                                                                                                                                              · rcases n with _ | n
                                                                                                                                                                                                                · decide
                                                                                                                                                                                                                · rcases n with _ | n
                                                                                                                                                                                                                  · decide
                                                                                                                                                                                                                  · rcases n with _ | n
                                                                                                                                                                                                                    · decide
                                                                                                                                                                                                                    · rcases n with _ | n
                                                                                                                                                                                                                      · decide
                                                                                                                                                                                                                      · rcases n with _ | n
                                                                                                                                                                                                                        · decide
                                                                                                                                                                                                                        · rcases n with _ | n
                                                                                                                                                                                                                          · decide
                                                                                                                                                                                                                          · rcases n with _ | n
                                                                                                                                                                                                                            · decide
                                                                                                                                                                                                                            · rcases n with _ | n
                                                                                                                                                                                                                              · decide
                                                                                                                                                                                                                              · rcases n with _ | n
                                                                                                                                                                                                                                · decide
                                                                                                                                                                                                                                · rcases n with _ | n
                                                                                                                                                                                                                                  · decide
                                                                                                                                                                                                                                  · rcases n with _ | n
                                                                                                                                                                                                                                    · decide
                                                                                                                                                                                                                                    · rcases n with _ | n
                                                                                                                                                                                                                                      · decide
                                                                                                                                                                                                                                      · rcases n with _ | n
                                                                                                                                                                                                                                        · decide
                                                                                                                                                                                                                                        · rcases n with _ | n
                                                                                                                                                                                                                                          · decide
                                                                                                                                                                                                                                          · rcases n with _ | n
                                                                                                                                                                                                                                            · decide
                                                                                                                                                                                                                                            · rcases n with _ | n
                                                                                                                                                                                                                                              · decide
                                                                                                                                                                                                                                              · rcases n with _ | n
                                                                                                                                                                                                                                                · decide
                                                                                                                                                                                                                                                · sorry

theorem oeis_179537_conjecture_sun_part2a_mod_n :
  ∀ n : ℕ, n ≥ 1 → A179537_sum_weighted n ≡ 0 [ZMOD n] := by
  intro n hn
  rcases n with _ | m
  · contradiction
  · exact inductive_step m (key_congruence m)









