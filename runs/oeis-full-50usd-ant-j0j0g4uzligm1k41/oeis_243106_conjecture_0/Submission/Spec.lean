import FormalConjectures.Util.ProblemImports

open Finset

/--
A243106: The sequence
$$a(n) = \sum_{k=1}^n (-1)^{\operatorname{isprime}(k)} 10^k$$
where the sign is $-1$ if $k$ is prime, and $1$ if $k$ is not prime.
-/
def a (n : ℕ) : Int :=
  (Icc 1 n).sum fun k : ℕ =>
    (if Nat.Prime k then (-1 : Int) else 1) * (10 : Int) ^ k

/-- From `(N : ℤ) = r + b * q` with `r < b`, deduce `q ≥ 0` and `N = r + b * q.toNat`. -/
private lemma bridge (b N r : ℕ) (q : ℤ) (hb : 0 < b) (hr : r < b)
    (h : (N : ℤ) = (r : ℤ) + (b : ℤ) * q) : 0 ≤ q ∧ N = r + b * q.toNat := by
  have hqnn : 0 ≤ q := by
    by_contra hcon
    push_neg at hcon
    have hq1 : q ≤ -1 := by omega
    have h2 : (b : ℤ) * q ≤ -(b : ℤ) := by
      have := mul_le_mul_of_nonneg_left hq1 (by exact_mod_cast Nat.zero_le b : (0 : ℤ) ≤ b)
      simpa using this
    have hNnn : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
    have hrb : (r : ℤ) < (b : ℤ) := by exact_mod_cast hr
    linarith
  refine ⟨hqnn, ?_⟩
  have hQ : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hqnn
  have hcast : ((r + b * q.toNat : ℕ) : ℤ) = (N : ℤ) := by
    push_cast
    rw [hQ]
    linarith
  exact_mod_cast hcast.symm

/-- The key inductive lemma. -/
private lemma key (b : ℕ) (hb : 2 ≤ b) :
    ∀ (m : ℕ) (f : ℕ → ℤ) (_ : ∀ j, f j = -1 ∨ f j = 0 ∨ f j = 1)
      (c : ℤ) (_ : c = -1 ∨ c = 0) (N : ℕ),
      (N : ℤ) = c + ∑ j ∈ Finset.range m, f j * (b : ℤ) ^ j →
      ∀ d ∈ Nat.digits b N, d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1 := by
  intro m
  induction m with
  | zero =>
    intro f hf c hc N hN
    rw [Finset.sum_range_zero] at hN
    have hN0 : N = 0 := by rcases hc with rfl | rfl <;> omega
    subst hN0
    intro d hd
    simp at hd
  | succ m IH =>
    intro f hf c hc N hN
    -- peel off the lowest term
    have hsum : ∑ i ∈ Finset.range m, f (i + 1) * (b : ℤ) ^ (i + 1)
        = (b : ℤ) * ∑ i ∈ Finset.range m, f (i + 1) * (b : ℤ) ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [Finset.sum_range_succ', hsum, pow_zero, mul_one] at hN
    set S' := ∑ i ∈ Finset.range m, f (i + 1) * (b : ℤ) ^ i with hS'
    -- hN : (N : ℤ) = c + (b * S' + f 0)
    -- common tail
    have tail : ∀ (r : ℕ) (c' : ℤ), r < b →
        (r = 0 ∨ r = 1 ∨ r = b - 2 ∨ r = b - 1) → (c' = -1 ∨ c' = 0) →
        (N : ℤ) = (r : ℤ) + (b : ℤ) * (c' + S') →
        ∀ d ∈ Nat.digits b N, d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1 := by
      intro r c' hr hrset hc' heq
      obtain ⟨hqnn, hNnat⟩ := bridge b N r (c' + S') (by omega) hr heq
      have hN'eq : (((c' + S').toNat : ℕ) : ℤ) = c' + S' := Int.toNat_of_nonneg hqnn
      have hIH := IH (fun i => f (i + 1)) (fun j => hf (j + 1)) c' hc' (c' + S').toNat
        (by rw [hN'eq, hS'])
      intro d hd
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · rw [h0] at hd; simp at hd
      · have hnz : r ≠ 0 ∨ (c' + S').toNat ≠ 0 := by
          by_contra hcon
          push_neg at hcon
          obtain ⟨hr0, hy0⟩ := hcon
          rw [hr0, hy0] at hNnat
          simp at hNnat
          omega
        rw [hNnat, Nat.digits_add b (by omega) r (c' + S').toNat hr hnz] at hd
        rcases List.mem_cons.mp hd with h | h
        · subst h; exact hrset
        · exact hIH d h
    -- case analysis on c and f 0
    rcases hc with rfl | rfl <;> rcases hf 0 with hf0 | hf0 | hf0
    -- c = -1
    · -- f 0 = -1  ⇒ r = b-2, c' = -1
      refine tail (b - 2) (-1) (by omega) (by omega) (Or.inl rfl) ?_
      have hc2 : ((b - 2 : ℕ) : ℤ) = (b : ℤ) - 2 := by omega
      rw [hN, hf0, hc2]; ring
    · -- f 0 = 0 ⇒ r = b-1, c' = -1
      refine tail (b - 1) (-1) (by omega) (by omega) (Or.inl rfl) ?_
      have hc1 : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
      rw [hN, hf0, hc1]; ring
    · -- f 0 = 1 ⇒ r = 0, c' = 0
      refine tail 0 0 (by omega) (by omega) (Or.inr rfl) ?_
      rw [hN, hf0]; push_cast; ring
    -- c = 0
    · -- f 0 = -1 ⇒ r = b-1, c' = -1
      refine tail (b - 1) (-1) (by omega) (by omega) (Or.inl rfl) ?_
      have hc1 : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
      rw [hN, hf0, hc1]; ring
    · -- f 0 = 0 ⇒ r = 0, c' = 0
      refine tail 0 0 (by omega) (by omega) (Or.inr rfl) ?_
      rw [hN, hf0]; push_cast; ring
    · -- f 0 = 1 ⇒ r = 1, c' = 0
      refine tail 1 0 (by omega) (by omega) (Or.inr rfl) ?_
      rw [hN, hf0]; push_cast; ring

/--
Conjecture: For any natural number $n$ and base $b > 4$, the absolute value of any sum of the form
$\sum_{k=1}^n \sigma_k b^k$ where $\sigma_k \in \{-1, 1\}$ only contains digits
belonging to $\{0, 1, b-2, b-1\}$ when expressed in base $b$.
This is the formalization of the conjecture for general base $b$.
-/
theorem oeis_243106_conjecture_0 (b n : ℕ) (hb : b ≥ 5) :
  ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
    let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
    ∀ d ∈ (b.digits x.natAbs),
      d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1 :=
by
  intro σ hσ x
  have hx : x = ∑ k ∈ Finset.Icc 1 n, σ k * (b : ℤ) ^ k := rfl
  -- the coefficient function
  set g : ℕ → ℤ := fun j => if j ∈ Finset.Icc 1 n then σ j else 0 with hg_def
  have hsub : Finset.Icc 1 n ⊆ Finset.range (n + 1) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  have hgsum : ∑ j ∈ Finset.range (n + 1), g j * (b : ℤ) ^ j = x := by
    have step1 : ∑ j ∈ Finset.range (n + 1), g j * (b : ℤ) ^ j
        = ∑ j ∈ Finset.Icc 1 n, g j * (b : ℤ) ^ j := by
      refine (Finset.sum_subset hsub ?_).symm
      intro k _ hknot
      simp only [hg_def, if_neg hknot, zero_mul]
    rw [step1, hx]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [hg_def, if_pos hk]
  have hg : ∀ j, g j = -1 ∨ g j = 0 ∨ g j = 1 := by
    intro j
    simp only [hg_def]
    split
    · rename_i hj
      rcases hσ j hj with h | h
      · right; right; exact h
      · left; exact h
    · right; left; rfl
  by_cases hx0 : 0 ≤ x
  · intro d hd
    refine key b (by omega) (n + 1) g hg 0 (Or.inr rfl) x.natAbs ?_ d hd
    rw [Int.natAbs_of_nonneg hx0, zero_add, hgsum]
  · replace hx0 : x < 0 := not_le.mp hx0
    intro d hd
    refine key b (by omega) (n + 1) (fun j => - g j) ?_ 0 (Or.inr rfl) x.natAbs ?_ d hd
    · intro j
      rcases hg j with h | h | h <;> simp [h]
    · rw [Int.natCast_natAbs, abs_of_neg hx0, zero_add]
      have : ∑ j ∈ Finset.range (n + 1), (fun j => - g j) j * (b : ℤ) ^ j
          = - ∑ j ∈ Finset.range (n + 1), g j * (b : ℤ) ^ j := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [this, hgsum]
