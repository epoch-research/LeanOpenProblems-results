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

noncomputable def state (v : Fin 5 → ℕ) (n : ℕ) (i : Fin 5) : ℕ := a_general v (n + i)

theorem tot_30030 : Nat.totient 30030 = 5760 := by
  have h2 : Nat.totient 2 = 1 := by decide
  have h3 : Nat.totient 3 = 2 := by decide
  have h5 : Nat.totient 5 = 4 := by decide
  have h7 : Nat.totient 7 = 6 := by decide
  have h11 : Nat.totient 11 = 10 := by decide
  have h13 : Nat.totient 13 = 12 := by decide
  have c23 : Nat.Coprime 2 3 := by decide
  have h6 : Nat.totient 6 = 2 := by
    rw [show 6 = 2 * 3 by rfl, Nat.totient_mul c23, h2, h3]
  have c65 : Nat.Coprime 6 5 := by decide
  have h30 : Nat.totient 30 = 8 := by
    rw [show 30 = 6 * 5 by rfl, Nat.totient_mul c65, h6, h5]
  have c307 : Nat.Coprime 30 7 := by decide
  have h210 : Nat.totient 210 = 48 := by
    rw [show 210 = 30 * 7 by rfl, Nat.totient_mul c307, h30, h7]
  have c21011 : Nat.Coprime 210 11 := by decide
  have h2310 : Nat.totient 2310 = 480 := by
    rw [show 2310 = 210 * 11 by rfl, Nat.totient_mul c21011, h210, h11]
  have c231013 : Nat.Coprime 2310 13 := by decide
  rw [show 30030 = 2310 * 13 by rfl, Nat.totient_mul c231013, h2310, h13]

theorem pi_bound (M : ℕ) (hM : 1000000 ≤ M) : π (5 * M) ≤ M := by
  have H0 : 30030 ≠ 0 := by decide
  have H1 : 30030 < 30031 := by decide
  have H2 : 5 * M + 1 = 30031 + (5 * M - 30030) := by omega
  rw [Nat.primeCounting, H2]
  have H3 := Nat.primeCounting'_add_le (a := 30030) (k := 30031) H0 H1 (5 * M - 30030)
  rw [tot_30030] at H3
  have H5 : π' 30031 ≤ 30031 := Nat.count_le _
  omega

theorem bounded_state (v : Fin 5 → ℕ) : ∃ B : ℕ, ∀ n i, state v n i ≤ B := by
  let vmax := max (v 0) (max (v 1) (max (v 2) (max (v 3) (v 4))))
  let B := max vmax 1000000
  use B
  have hB : 1000000 ≤ B := le_max_right _ _
  intro n
  induction n with
  | zero =>
    intro i
    have hv0 : v 0 ≤ B := by change v 0 ≤ max vmax 1000000; omega
    have hv1 : v 1 ≤ B := by change v 1 ≤ max vmax 1000000; omega
    have hv2 : v 2 ≤ B := by change v 2 ≤ max vmax 1000000; omega
    have hv3 : v 3 ≤ B := by change v 3 ≤ max vmax 1000000; omega
    have hv4 : v 4 ≤ B := by change v 4 ≤ max vmax 1000000; omega
    fin_cases i
    · exact hv0
    · exact hv1
    · exact hv2
    · exact hv3
    · exact hv4
  | succ n ih =>
    intro i
    fin_cases i
    · exact ih ⟨1, by decide⟩
    · exact ih ⟨2, by decide⟩
    · exact ih ⟨3, by decide⟩
    · exact ih ⟨4, by decide⟩
    · change a_general v (n + 5) ≤ B
      have stepN : a_general v (n + 5) = π (a_general v (n + 4) + a_general v (n + 3) + a_general v (n + 2) + a_general v (n + 1) + a_general v n) := rfl
      rw [stepN]
      have hs0 : a_general v n = state v n ⟨0, by decide⟩ := rfl
      have hs1 : a_general v (n + 1) = state v n ⟨1, by decide⟩ := rfl
      have hs2 : a_general v (n + 2) = state v n ⟨2, by decide⟩ := rfl
      have hs3 : a_general v (n + 3) = state v n ⟨3, by decide⟩ := rfl
      have hs4 : a_general v (n + 4) = state v n ⟨4, by decide⟩ := rfl
      rw [hs4, hs3, hs2, hs1, hs0]
      have sum_bound : state v n ⟨4, by decide⟩ + state v n ⟨3, by decide⟩ + state v n ⟨2, by decide⟩ + state v n ⟨1, by decide⟩ + state v n ⟨0, by decide⟩ ≤ 5 * B := by
        have i0 := ih ⟨0, by decide⟩
        have i1 := ih ⟨1, by decide⟩
        have i2 := ih ⟨2, by decide⟩
        have i3 := ih ⟨3, by decide⟩
        have i4 := ih ⟨4, by decide⟩
        omega
      have H := Nat.monotone_primeCounting sum_bound
      have H2 := pi_bound B hB
      exact H.trans H2

theorem pigeonhole (s : ℕ → Fin 5 → ℕ) (B : ℕ) (h : ∀ n i, s n i ≤ B) : ∃ i j, i < j ∧ s i = s j := by
  let f : ℕ → Fin 5 → Fin (B + 1) := fun n i => ⟨s n i, Nat.lt_succ_of_le (h n i)⟩
  have : ¬ Function.Injective f := not_injective_infinite_finite f
  unfold Function.Injective at this
  push_neg at this
  rcases this with ⟨x, y, heq, hne⟩
  have H : s x = s y := by
    ext i
    have : f x i = f y i := by rw [heq]
    exact congrArg Fin.val this
  rcases lt_trichotomy x y with hlt | heq2 | hgt
  · exact ⟨x, y, hlt, H⟩
  · contradiction
  · exact ⟨y, x, hgt, H.symm⟩

theorem state_eq_implies_next_eq (v : Fin 5 → ℕ) (N M : ℕ) (h : state v N = state v M) : state v (N + 1) = state v (M + 1) := by
  ext i
  unfold state
  have h0 : a_general v N = a_general v M := by
    have := congr_fun h ⟨0, by decide⟩
    exact this
  have h1 : a_general v (N + 1) = a_general v (M + 1) := congr_fun h ⟨1, by decide⟩
  have h2 : a_general v (N + 2) = a_general v (M + 2) := congr_fun h ⟨2, by decide⟩
  have h3 : a_general v (N + 3) = a_general v (M + 3) := congr_fun h ⟨3, by decide⟩
  have h4 : a_general v (N + 4) = a_general v (M + 4) := congr_fun h ⟨4, by decide⟩
  fin_cases i
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · change a_general v (N + 5) = a_general v (M + 5)
    have stepN : a_general v (N + 5) = π (a_general v (N + 4) + a_general v (N + 3) + a_general v (N + 2) + a_general v (N + 1) + a_general v N) := rfl
    have stepM : a_general v (M + 5) = π (a_general v (M + 4) + a_general v (M + 3) + a_general v (M + 2) + a_general v (M + 1) + a_general v M) := rfl
    rw [stepN, stepM, h4, h3, h2, h1, h0]

theorem state_eq_implies_add_eq (v : Fin 5 → ℕ) (N M : ℕ) (h : state v N = state v M) (k : ℕ) :
    state v (N + k) = state v (M + k) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    have ih2 : state v (N + k + 1) = state v (M + k + 1) := state_eq_implies_next_eq v (N + k) (M + k) ih
    rw [← Nat.add_assoc, ← Nat.add_assoc]
    exact ih2

theorem state_eq_implies_periodic (v : Fin 5 → ℕ) (N M : ℕ) (hLT : N < M) (hEq : state v N = state v M) :
    ∃ N' P : ℕ, P > 0 ∧ (∀ n, n ≥ N' → a_general v (n + P) = a_general v n) := by
  use N, M - N
  have hP : M - N > 0 := Nat.sub_pos_of_lt hLT
  refine ⟨hP, fun n hn => ?_⟩
  let k := n - N
  have hN_k : n = N + k := (Nat.add_sub_cancel' hn).symm
  rw [hN_k]
  have H := state_eq_implies_add_eq v N M hEq k
  have H0 := congr_fun H ⟨0, by decide⟩
  have hM_k : M + k = N + k + (M - N) := by omega
  rw [hM_k] at H0
  exact H0.symm

/-- oeis_100478_conjecture_0: Starting with other values of a(1), a(2), a(3), a(4), a(5) what behaviors are possible? Does the sequence always stick at a single integer after some point, or can it go into a loop, or is there a third pattern? -/
theorem oeis_a100478_conjecture_0 :
  -- For any set of five positive starting values v
  ∀ (v : Fin 5 → ℕ), (∀ i, v i > 0) →
  -- The sequence is ultimately periodic.
  ∃ N P : ℕ, P > 0 ∧ (∀ n, n ≥ N → a_general v (n + P) = a_general v n) := by
  intro v _
  have ⟨B, hB⟩ := bounded_state v
  have ⟨i, j, hLT, hEq⟩ := pigeonhole (state v) B hB
  exact state_eq_implies_periodic v i j hLT hEq

theorem oeis_a100478_conjecture_0.disproof : ¬ (type_of% @oeis_a100478_conjecture_0) := sorry
