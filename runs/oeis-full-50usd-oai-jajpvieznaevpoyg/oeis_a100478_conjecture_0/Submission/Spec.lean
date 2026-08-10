import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

/--
Pentanacci $\pi$ function: $a(1)=a(2)=a(3)=a(4)=a(5)=1$;
for $n>5$, $a(n) = \pi(\sum_{j=1}^5 a(n-j))$ where $\pi = A000720$.
Note on indices: for $n \ge 0$, $a(n)$ corresponds to $A_{n+1}$ in the OEIS sequence.
-/
noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 1 -- Corresponds to A(1)
  | 1 => 1 -- Corresponds to A(2)
  | 2 => 1 -- Corresponds to A(3)
  | 3 => 1 -- Corresponds to A(4)
  | 4 => 1 -- Corresponds to A(5)
  | i + 5 => -- i+5 corresponds to OEIS index i+6 > 5
    -- The terms are a(i+4), a(i+3), a(i+2), a(i+1), a(i), which are the previous 5 terms.
    let sum_terms := a (i + 4) + a (i + 3) + a (i + 2) + a (i + 1) + a i
    π sum_terms

/--
A general sequence defined by the Pentanacci $\pi$ recurrence, starting with arbitrary initial values $v: \text{Fin 5} \to \mathbb{N}$.
The sequence $a'(v, n)$ is the n-th term (0-indexed).
-/
noncomputable def a_general (v : Fin 5 → ℕ) (n : ℕ) : ℕ :=
  match n with
  | 0 => v 0
  | 1 => v 1
  | 2 => v 2
  | 3 => v 3
  | 4 => v 4
  | i + 5 =>
    let sum_terms := a_general v (i + 4) + a_general v (i + 3) + a_general v (i + 2) + a_general v (i + 1) + a_general v i
    π sum_terms

/-- oeis_100478_conjecture_0: Starting with other values of a(1), a(2), a(3), a(4), a(5) what behaviors are possible? Does the sequence always stick at a single integer after some point, or can it go into a loop, or is there a third pattern? -/
lemma primeCounting_le_self (n : ℕ) : π' n ≤ n := by
  simpa [Nat.primeCounting'] using (Nat.count_le (p := Nat.Prime) (n := n))

lemma totient_30030 : Nat.totient 30030 = 5760 := by
  rw [show 30030 = 2 * (3 * (5 * (7 * (11 * 13)))) by norm_num]
  rw [Nat.totient_mul (by norm_num [Nat.coprime_iff_gcd_eq_one])]
  rw [Nat.totient_mul (by norm_num [Nat.coprime_iff_gcd_eq_one])]
  rw [Nat.totient_mul (by norm_num [Nat.coprime_iff_gcd_eq_one])]
  rw [Nat.totient_mul (by norm_num [Nat.coprime_iff_gcd_eq_one])]
  rw [Nat.totient_mul (by norm_num [Nat.coprime_iff_gcd_eq_one])]
  norm_num [Nat.totient_prime]

lemma primeCounting_five_mul_le (M : ℕ) (hM : 1000000 ≤ M) : π (5 * M) ≤ M := by
  have hdecomp : 30031 + (5 * M + 1 - 30031) = 5 * M + 1 := by omega
  have hmain := Nat.primeCounting'_add_le (a := 30030) (k := 30031)
    (by norm_num) (by norm_num) (5 * M + 1 - 30031)
  rw [hdecomp] at hmain
  change π' (5 * M + 1) ≤ M
  calc
    π' (5 * M + 1) ≤ π' 30031 + Nat.totient 30030 * ((5 * M + 1 - 30031) / 30030 + 1) := hmain
    _ ≤ 30031 + 5760 * ((5 * M + 1 - 30031) / 30030 + 1) := by
      rw [totient_30030]
      exact Nat.add_le_add_right (primeCounting_le_self 30031) _
    _ ≤ 30031 + 5760 * (M / 6006 + 1) := by
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul_left
      apply Nat.add_le_add_right
      have hnum : 5 * M + 1 - 30031 ≤ 5 * M := by omega
      calc
        (5 * M + 1 - 30031) / 30030 ≤ (5 * M) / 30030 := Nat.div_le_div_right hnum
        _ = M / 6006 := by
          rw [show 30030 = 5 * 6006 by norm_num]
          exact Nat.mul_div_mul_left M 6006 (by norm_num)
    _ ≤ M := by
      have hq : 166 ≤ M / 6006 := by
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 6006)]
        omega
      have hmul : 6006 * (M / 6006) ≤ M := Nat.mul_div_le M 6006
      omega

lemma a_general_bound (v : Fin 5 → ℕ) :
    let B := 1000000 + v 0 + v 1 + v 2 + v 3 + v 4
    ∀ n, a_general v n ≤ B := by
  intro B n
  have hB : 1000000 ≤ B := by dsimp [B]; omega
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => dsimp [B]; simp [a_general]; omega
    | 1 => dsimp [B]; simp [a_general]; omega
    | 2 => dsimp [B]; simp [a_general]; omega
    | 3 => dsimp [B]; simp [a_general]; omega
    | 4 => dsimp [B]; simp [a_general]
    | i + 5 =>
      have h0 : a_general v i ≤ B := ih i (by omega)
      have h1 : a_general v (i + 1) ≤ B := ih (i + 1) (by omega)
      have h2 : a_general v (i + 2) ≤ B := ih (i + 2) (by omega)
      have h3 : a_general v (i + 3) ≤ B := ih (i + 3) (by omega)
      have h4 : a_general v (i + 4) ≤ B := ih (i + 4) (by omega)
      have hsum : a_general v (i + 4) + a_general v (i + 3) + a_general v (i + 2) +
          a_general v (i + 1) + a_general v i ≤ 5 * B := by omega
      calc
        a_general v (i + 5) = π (a_general v (i + 4) + a_general v (i + 3) +
            a_general v (i + 2) + a_general v (i + 1) + a_general v i) := by simp [a_general]
        _ ≤ π (5 * B) := Nat.monotone_primeCounting hsum
        _ ≤ B := primeCounting_five_mul_le B hB

lemma a_general_eq_of_eq_window {v : Fin 5 → ℕ} {N P : ℕ}
    (hwin : ∀ i : ℕ, i < 5 → a_general v (N + P + i) = a_general v (N + i)) :
    ∀ t : ℕ, a_general v (N + P + t) = a_general v (N + t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht : t < 5
    · exact hwin t ht
    · obtain ⟨k, rfl⟩ : ∃ k, t = k + 5 := by
        use t - 5
        omega
      rw [show N + P + (k + 5) = (N + P + k) + 5 by omega]
      rw [show N + (k + 5) = (N + k) + 5 by omega]
      simp only [a_general]
      have e4 : a_general v (N + P + k + 4) = a_general v (N + k + 4) := by
        simpa only [Nat.add_assoc] using ih (k + 4) (by omega)
      have e3 : a_general v (N + P + k + 3) = a_general v (N + k + 3) := by
        simpa only [Nat.add_assoc] using ih (k + 3) (by omega)
      have e2 : a_general v (N + P + k + 2) = a_general v (N + k + 2) := by
        simpa only [Nat.add_assoc] using ih (k + 2) (by omega)
      have e1 : a_general v (N + P + k + 1) = a_general v (N + k + 1) := by
        simpa only [Nat.add_assoc] using ih (k + 1) (by omega)
      have e0 : a_general v (N + P + k) = a_general v (N + k) := by
        simpa only [Nat.add_assoc] using ih k (by omega)
      rw [e4, e3, e2, e1, e0]

theorem oeis_a100478_conjecture_0 :
  -- For any set of five positive starting values v
  ∀ (v : Fin 5 → ℕ), (∀ i, v i > 0) →
  -- The sequence is ultimately periodic.
  ∃ N P : ℕ, P > 0 ∧ (∀ n, n ≥ N → a_general v (n + P) = a_general v n) := by
  intro v _hpos
  let B := 1000000 + v 0 + v 1 + v 2 + v 3 + v 4
  have hbound : ∀ n, a_general v n ≤ B := by
    simpa [B] using (a_general_bound v)
  let window : ℕ → (Fin 5 → Fin (B + 1)) := fun n i =>
    ⟨a_general v (n + i), Nat.lt_succ_of_le (hbound (n + i))⟩
  obtain ⟨m, n, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite window
  wlog hmn : m < n generalizing m n with H
  · have hnm : n < m := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hmn) hne.symm
    obtain ⟨N, P, hP, hper⟩ := H n m hne.symm heq.symm hnm
    exact ⟨N, P, hP, hper⟩
  refine ⟨m, n - m, Nat.sub_pos_of_lt hmn, ?_⟩
  have hwin : ∀ i : ℕ, i < 5 → a_general v (m + (n - m) + i) = a_general v (m + i) := by
    intro i hi
    have hfin := congrFun heq ⟨i, hi⟩
    have hval := congrArg Fin.val hfin
    dsimp [window] at hval
    rw [show m + (n - m) + i = n + i by omega]
    exact hval.symm
  have hper0 := a_general_eq_of_eq_window (v := v) (N := m) (P := n - m) hwin
  intro q hq
  have hqeq : q = m + (q - m) := by omega
  calc
    a_general v (q + (n - m)) = a_general v (m + (n - m) + (q - m)) := by congr 1; omega
    _ = a_general v (m + (q - m)) := hper0 (q - m)
    _ = a_general v q := by congr 1; omega
