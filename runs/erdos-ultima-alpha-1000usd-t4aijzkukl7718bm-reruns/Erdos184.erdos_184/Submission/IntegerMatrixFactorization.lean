import FormalConjecturesUtil

/-!
Integral factorization of a nonnegative integer matrix with equal row and
column sums. This is an auxiliary matching lemma, not a settlement of
Erdős 184. No assertion about the number of components of a permutation
factor, or about cycle decompositions of arbitrary graphs, is made here.
-/

open scoped BigOperators Classical
namespace Erdos184.IntegerMatrixFactorization

variable {V : Type*} [Fintype V]

/-- Hall's condition for the positive support of a regular integer matrix. -/
lemma support_hall (A : V → V → ℕ) (r : ℕ) (hr : 0 < r)
    (hrow : ∀ i, (∑ j, A i j) = r)
    (hcol : ∀ j, (∑ i, A i j) = r) (S : Finset V) :
    S.card ≤ (S.biUnion (fun i => Finset.univ.filter (fun j => A i j ≠ 0))).card := by
  classical
  let N := S.biUnion (fun i => Finset.univ.filter (fun j => A i j ≠ 0))
  have hrestrict (i : V) (hi : i ∈ S) : (∑ j ∈ N, A i j) = r := by
    rw [← hrow i]
    apply Finset.sum_subset (Finset.subset_univ N)
    intro j _ hj
    by_contra hn
    apply hj
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hn⟩⟩
  have hleft : (∑ i ∈ S, ∑ j ∈ N, A i j) = S.card * r := by
    simp only [Finset.sum_congr rfl (fun i hi => hrestrict i hi), Finset.sum_const,
      smul_eq_mul]
  have hright : (∑ i, ∑ j ∈ N, A i j) = N.card * r := by
    rw [Finset.sum_comm]
    simp [hcol]
  have hb : S.card * r ≤ N.card * r := by
    rw [← hleft, ← hright]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun _ _ _ => Nat.zero_le _)
  exact Nat.le_of_mul_le_mul_right hb hr

/-- A positive regular integer matrix has a supported permutation. -/
lemma exists_supported_permutation (A : V → V → ℕ) (r : ℕ) (hr : 0 < r)
    (hrow : ∀ i, (∑ j, A i j) = r)
    (hcol : ∀ j, (∑ i, A i j) = r) :
    ∃ σ : Equiv.Perm V, ∀ i, 0 < A i (σ i) := by
  classical
  obtain ⟨f, hf, hfs⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (fun i => Finset.univ.filter (fun j => A i j ≠ 0))).mp
      (fun S => support_hall A r hr hrow hcol S)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), ?_⟩
  intro i
  exact Nat.pos_of_ne_zero (Finset.mem_filter.mp (hfs i)).2

/-- Integer Birkhoff factorization: a matrix with row and column sums r
is a sum of exactly r permutation matrices. Repetition is permitted. -/
theorem exists_permutation_factorization (A : V → V → ℕ) (r : ℕ)
    (hrow : ∀ i, (∑ j, A i j) = r)
    (hcol : ∀ j, (∑ i, A i j) = r) :
    ∃ p : Fin r → Equiv.Perm V,
      ∀ i j, A i j = ∑ c, if p c i = j then 1 else 0 := by
  classical
  induction r generalizing A with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    intro i j
    have hb : A i j ≤ ∑ k, A i k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [hrow] at hb
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    omega
  | succ r ih =>
    obtain ⟨σ, hσ⟩ := exists_supported_permutation A (r+1) (by omega) hrow hcol
    let B : V → V → ℕ := fun i j => A i j - if σ i = j then 1 else 0
    have hab (i j : V) : A i j = B i j + if σ i = j then 1 else 0 := by
      dsimp [B]
      split_ifs with h
      · subst j
        have := hσ i
        omega
      · omega
    have brow (i : V) : (∑ j, B i j) = r := by
      have h := hrow i
      simp only [hab, Finset.sum_add_distrib] at h
      have hsum : (∑ j : V, if σ i = j then 1 else 0) = 1 := by
        simp [eq_comm]
      rw [hsum] at h
      omega
    have bcol (j : V) : (∑ i, B i j) = r := by
      have h := hcol j
      simp only [hab, Finset.sum_add_distrib] at h
      have hsum : (∑ i : V, if σ i = j then 1 else 0) = 1 := by
        simp [← Equiv.eq_symm_apply]
      rw [hsum] at h
      omega
    obtain ⟨p, hp⟩ := ih B brow bcol
    refine ⟨Fin.cases σ p, ?_⟩
    intro i j
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    rw [← hp, hab]
    omega

end Erdos184.IntegerMatrixFactorization
