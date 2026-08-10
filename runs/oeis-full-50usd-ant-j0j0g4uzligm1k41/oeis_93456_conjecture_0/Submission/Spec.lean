import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A093456: Product of all composite numbers between $n(n-1)/2+1$ and $n(n+1)/2$ (including boundaries),
where $n(n-1)/2 = \binom{n}{2}$ and $n(n+1)/2 = \binom{n+1}{2}$.
-/
def a (n : ℕ) : ℕ :=
  let L := n.choose 2 + 1
  let R := (n + 1).choose 2

  -- A number k is composite if k > 1 and is not prime.
  let is_composite (k : ℕ) : Prop := 1 < k ∧ ¬ k.Prime

  (Icc L R).filter is_composite |>.prod id

/--
Conjecture: There are finitely many numbers such that $a(n)$ is not $\equiv 0 \pmod{a(n-1)}$.
(Also mentioned in A093455.)

This is FALSE: the set is in fact infinite.  For every prime `p` (large enough), if `j` is the
index of the "triangular block" containing `2 * p` (i.e. `C(j,2) < 2p ≤ C(j+1,2)`), then `2p` is a
composite number in the block for `j`, so `p ∣ a j`; while no composite multiple of `p` lies in the
block for `j+1` (as `2p` is below it and `3p` is above it), so `p ∤ a (j+1)`.  Hence
`a j ∤ a (j+1)`, i.e. `n = j+1` is in the bad set, and these `n` are unbounded.
-/

private lemma a_eq (n : ℕ) :
    a n = (Finset.filter (fun k => 1 < k ∧ ¬ k.Prime)
      (Finset.Icc (n.choose 2 + 1) ((n + 1).choose 2))).prod id := rfl

/-- `(m+1).choose 2 = m.choose 2 + m`. -/
private lemma choose_two_succ (m : ℕ) : (m + 1).choose 2 = m.choose 2 + m := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]

/-- For `j ≥ 9`, `4 * j ≤ C(j,2)`. -/
private lemma four_mul_le_choose_two {j : ℕ} (hj : 9 ≤ j) : 4 * j ≤ j.choose 2 := by
  have h2 : 2 * j.choose 2 = j * (j - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self j).two_dvd
  have hge : 8 * j ≤ j * (j - 1) := by
    calc 8 * j = j * 8 := by ring
    _ ≤ j * (j - 1) := Nat.mul_le_mul (le_refl j) (by omega)
  omega

/-- The core step: for a prime `p ≥ 23` there is `n` in the bad set with `2 * p ≤ C(n,2)`. -/
private lemma bad_of_prime {p : ℕ} (hp : p.Prime) (hp23 : 23 ≤ p) :
    ∃ n, 1 < n ∧ ¬ (a (n - 1) ∣ a n) ∧ 2 * p ≤ n.choose 2 := by
  -- There is a block index `j` with `2 * p ≤ C(j+1, 2)`.
  have hex : ∃ j, 2 * p ≤ (j + 1).choose 2 := by
    refine ⟨2 * p, ?_⟩
    rw [choose_two_succ]; omega
  set j := Nat.find hex with hjdef
  have hjs : 2 * p ≤ (j + 1).choose 2 := Nat.find_spec hex
  -- Show `j ≥ 10`.
  have hj10 : 10 ≤ j := by
    by_contra h
    push_neg at h
    have : (j + 1).choose 2 ≤ (10).choose 2 := Nat.choose_le_choose 2 (by omega)
    simp only [show (10).choose 2 = 45 from rfl] at this
    omega
  -- Lower bound: `C(j,2) < 2 * p`.
  have hlow : j.choose 2 < 2 * p := by
    have hmin := Nat.find_min hex (m := j - 1) (by omega)
    rw [show j - 1 + 1 = j from by omega] at hmin
    omega
  -- Bound needed for the `j+1` block: `C(j+2, 2) < 3 * p`.
  have hcs1 := choose_two_succ j
  have hcs2 := choose_two_succ (j + 1)
  have h4j := four_mul_le_choose_two (show 9 ≤ j by omega)
  have h3 : (j + 1 + 1).choose 2 < 3 * p := by omega
  -- Claim A: `p ∣ a j`, because `2 * p` is a composite in the `j`-block.
  have hAmem : (2 * p) ∈ Finset.filter (fun k => 1 < k ∧ ¬ k.Prime)
      (Finset.Icc (j.choose 2 + 1) ((j + 1).choose 2)) := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hjs⟩, by omega, Nat.not_prime_mul (by norm_num) (by omega)⟩
  have hA : p ∣ a j := by
    rw [a_eq]
    have hd : (2 * p) ∣ (Finset.filter (fun k => 1 < k ∧ ¬ k.Prime)
        (Finset.Icc (j.choose 2 + 1) ((j + 1).choose 2))).prod id := by
      simpa using Finset.dvd_prod_of_mem id hAmem
    exact dvd_trans (dvd_mul_left p 2) hd
  -- Claim B: `p ∤ a (j+1)`.
  have hB : ¬ p ∣ a (j + 1) := by
    rw [a_eq]
    refine Prime.not_dvd_finset_prod hp.prime ?_
    intro c hc hpc
    rw [Finset.mem_filter, Finset.mem_Icc] at hc
    obtain ⟨⟨hcL, hcR⟩, _⟩ := hc
    simp only [id] at hpc
    obtain ⟨k, rfl⟩ := hpc
    have hklb : 3 ≤ k := by
      by_contra hk
      push_neg at hk
      have : p * k ≤ p * 2 := Nat.mul_le_mul (le_refl p) (by omega)
      omega
    have h3p : 3 * p ≤ p * k := by
      calc 3 * p = p * 3 := by ring
      _ ≤ p * k := Nat.mul_le_mul (le_refl p) hklb
    omega
  -- Assemble.
  refine ⟨j + 1, by omega, ?_, ?_⟩
  · rw [Nat.add_sub_cancel]
    intro hdvd
    exact hB (dvd_trans hA hdvd)
  · exact hjs

theorem oeis_93456_conjecture_0.disproof :
    ¬ Set.Finite {n : ℕ | n > 1 ∧ ¬ (a (n - 1) ∣ a n)} := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro N
  obtain ⟨p, hpn, hpp⟩ := Nat.exists_infinite_primes (max 23 ((N + 1).choose 2 + 1))
  have hp23 : 23 ≤ p := le_trans (le_max_left _ _) hpn
  have hplow : (N + 1).choose 2 + 1 ≤ p := le_trans (le_max_right _ _) hpn
  obtain ⟨n, hn1, hnd, hn2⟩ := bad_of_prime hpp hp23
  have hBC : (N + 1).choose 2 < n.choose 2 := by omega
  have hlt : N < n := by
    by_contra hle
    push_neg at hle
    have : n.choose 2 ≤ (N + 1).choose 2 := Nat.choose_le_choose 2 (by omega)
    omega
  exact ⟨n, ⟨hn1, hnd⟩, hlt⟩
