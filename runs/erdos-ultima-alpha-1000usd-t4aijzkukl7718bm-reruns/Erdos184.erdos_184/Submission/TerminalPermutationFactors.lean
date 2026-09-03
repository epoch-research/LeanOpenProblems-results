import Submission.IntegerMatrixFactorization

/-!
Permutation factorization with a finite terminal set. If every off-diagonal
matrix entry away from the terminals increases a rank, all nontrivial cycles
in every supported permutation meet a terminal. This is an auxiliary finite
statement, not a decomposition theorem for arbitrary undirected graphs.
-/

open scoped BigOperators Classical
namespace Erdos184.TerminalPermutationFactors

variable {V : Type*} [Fintype V]

lemma supported_of_factorization (A : V → V → ℕ) (r : ℕ)
    (p : Fin r → Equiv.Perm V)
    (hp : ∀ i j, A i j = ∑ c, if p c i = j then 1 else 0)
    (c : Fin r) (i : V) : 0 < A i (p c i) := by
  classical
  rw [hp]
  have h := Finset.single_le_sum
    (f := fun d : Fin r => if p d i = p c i then 1 else 0)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  simp only [ite_true] at h
  omega

lemma no_fixed_point_of_zero_diagonal (A : V → V → ℕ) (r : ℕ)
    (p : Fin r → Equiv.Perm V)
    (hp : ∀ i j, A i j = ∑ c, if p c i = j then 1 else 0)
    (i : V) (hi : A i i = 0) (c : Fin r) : p c i ≠ i := by
  intro h
  have hh := supported_of_factorization A r p hp c i
  rw [h, hi] at hh
  omega

/-- A nontrivial permutation cycle cannot stay in the strictly
rank-increasing part of the support. -/
lemma cycle_hits_terminals (σ : Equiv.Perm V) (T : Finset V) (rank : V → ℕ)
    (hforward : ∀ i, i ∉ T → σ i ∉ T → σ i ≠ i → rank i < rank (σ i))
    (q : Equiv.Perm V) (hq : q ∈ σ.cycleFactorsFinset) :
    ∃ v ∈ q.support, v ∈ T := by
  classical
  obtain ⟨hcycle, heq⟩ := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hq
  obtain ⟨v, hv, hmax⟩ := q.support.exists_max_image rank hcycle.nonempty_support
  by_contra! hmiss
  have hσv : σ v ∈ q.support :=
    (Equiv.Perm.mem_cycleFactorsFinset_support hq v).mpr hv
  have hne : σ v ≠ v := by
    rw [← heq v hv]
    exact Equiv.Perm.mem_support.mp hv
  have hh := hforward v (hmiss v hv) (hmiss (σ v) hσv) hne
  have hb := hmax (σ v) hσv
  omega

/-- Distinct permutation cycles have disjoint supports, so choosing a
terminal in each gives an injection into the terminal set. -/
lemma cycle_count_le_terminals (σ : Equiv.Perm V) (T : Finset V) (rank : V → ℕ)
    (hforward : ∀ i, i ∉ T → σ i ∉ T → σ i ≠ i → rank i < rank (σ i)) :
    σ.cycleFactorsFinset.card ≤ T.card := by
  classical
  have hex := fun q (hq : q ∈ σ.cycleFactorsFinset) =>
    cycle_hits_terminals σ T rank hforward q hq
  choose v hv hT using hex
  let f : σ.cycleFactorsFinset → T := fun q => ⟨v q.val q.property, hT q.val q.property⟩
  have hf : Function.Injective f := by
    intro q z he
    apply Subtype.ext
    by_contra hne
    have hdis := (Equiv.Perm.cycleFactorsFinset_pairwise_disjoint σ)
      q.property z.property hne
    have hvq := hv q.val q.property
    have hvz := hv z.val z.property
    have hval : v q.val q.property = v z.val z.property := congrArg Subtype.val he
    exact Finset.disjoint_left.mp hdis.disjoint_support hvq (hval.symm ▸ hvz)
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hh

/-- Factorization into supported permutations whose nontrivial cycles all
meet the specified terminal set. Diagonal entries represent unused capacity. -/
theorem exists_terminal_factorization (A : V → V → ℕ) (r : ℕ)
    (hrow : ∀ i, (∑ j, A i j) = r)
    (hcol : ∀ j, (∑ i, A i j) = r)
    (T : Finset V) (rank : V → ℕ)
    (hforward : ∀ i j, i ∉ T → j ∉ T → i ≠ j → 0 < A i j → rank i < rank j) :
    ∃ p : Fin r → Equiv.Perm V,
      (∀ i j, A i j = ∑ c, if p c i = j then 1 else 0) ∧
      (∀ c q, q ∈ (p c).cycleFactorsFinset → ∃ v ∈ q.support, v ∈ T) ∧
      (∀ c, (p c).cycleFactorsFinset.card ≤ T.card) ∧
      (∀ i, A i i = 0 → ∀ c, p c i ≠ i) := by
  classical
  obtain ⟨p, hp⟩ := IntegerMatrixFactorization.exists_permutation_factorization A r hrow hcol
  have hf (c : Fin r) (i : V) (hi : i ∉ T) (hj : p c i ∉ T) (hne : p c i ≠ i) :
      rank i < rank (p c i) :=
    hforward i (p c i) hi hj hne.symm (supported_of_factorization A r p hp c i)
  exact ⟨p, hp, fun c => cycle_hits_terminals (p c) T rank (hf c),
    fun c => cycle_count_le_terminals (p c) T rank (hf c),
    fun i hi c => no_fixed_point_of_zero_diagonal A r p hp i hi c⟩

end Erdos184.TerminalPermutationFactors
