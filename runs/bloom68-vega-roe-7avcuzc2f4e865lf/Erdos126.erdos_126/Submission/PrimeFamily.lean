import Submission.PrimeCode
import Submission.OrbitFamily
import Submission.SignedFamily

/-!
# Signed families at direct prime-power residue levels

At level `k`, the values are the original natural numbers modulo `p ^ (k + 1)`.
The mixed negation-orbits are tagged by their levels, so equal supports at
several levels remain distinct nodes. Their supports form a laminar family,
and every node has at least two vertices. The signs are the existing
`Erdos126PrimeCode.primeColor p (a i)`; no valuation normalization is used in
constructing the residues or the nodes.
-/

namespace Erdos126PrimeFamily

open scoped BigOperators
open Finset

noncomputable section

variable {V : Type*}

/-- The direct residue at level `k`, without removing any prime powers. -/
def residue (a : V → ℕ) (p k : ℕ) (i : V) : ZMod (p ^ (k + 1)) :=
  (a i : ZMod (p ^ (k + 1)))

/-- Negation of direct residues is equivalent to divisibility of their sum. -/
theorem residue_eq_neg_iff_dvd (a : V → ℕ) (p k : ℕ) (i j : V) :
    residue a p k i = -residue a p k j ↔ p ^ (k + 1) ∣ a i + a j := by
  simpa only [residue, Nat.cast_add, add_eq_zero_iff_eq_neg] using
    (ZMod.natCast_eq_zero_iff (a i + a j) (p ^ (k + 1)))

/-- A direct residue is self-opposite exactly when the modulus divides twice it. -/
theorem residue_eq_self_neg_iff_dvd_twice (a : V → ℕ) (p k : ℕ) (i : V) :
    residue a p k i = -residue a p k i ↔ p ^ (k + 1) ∣ 2 * a i := by
  simpa only [two_mul] using residue_eq_neg_iff_dvd a p k i i

/-- Reduction from a higher direct-residue level to a lower one. -/
@[simp] theorem castHom_residue (a : V → ℕ) (p : ℕ) {k l : ℕ} (h : k ≤ l)
    (i : V) :
    ZMod.castHom (pow_dvd_pow p (Nat.add_le_add_right h 1))
        (ZMod (p ^ (k + 1))) (residue a p l i) = residue a p k i := by
  exact map_natCast _ (a i)

/-- At every level, the prime colors separate opposite, non-self-opposite
residues. The existing prime-color bound includes the prime two. -/
theorem color_separation (a : V → ℕ) (p : ℕ) (hp : p.Prime)
    (ha : ∀ i, a i ≠ 0) (k : ℕ) :
    ∀ i j, residue a p k i = -residue a p k j →
      residue a p k i ≠ -residue a p k i →
      Erdos126PrimeCode.primeColor p (a i) ≠ Erdos126PrimeCode.primeColor p (a j) := by
  intro i j hij hni hc
  have hsum : p ^ (k + 1) ∣ a i + a j :=
    (residue_eq_neg_iff_dvd a p k i j).mp hij
  have htwice : ¬ p ^ (k + 1) ∣ 2 * a i :=
    fun h => hni ((residue_eq_self_neg_iff_dvd_twice a p k i).mpr h)
  have hsum0 : a i + a j ≠ 0 := by
    have := ha i
    omega
  have htwice0 : 2 * a i ≠ 0 := mul_ne_zero (by decide) (ha i)
  have hle := Erdos126PrimeCode.factorization_sum_le_of_color_eq hp (ha i) (ha j) hc
  exact htwice ((hp.pow_dvd_iff_le_factorization htwice0).mpr
    (((hp.pow_dvd_iff_le_factorization hsum0).mp hsum).trans hle))

variable [Fintype V]

/-- Mixed negation-orbits, with the level retained as part of each node. -/
def nodes (a : V → ℕ) (p K : ℕ) : Finset (Σ _ : ℕ, Finset V) :=
  (range K).sigma (fun k => Erdos126Orbit.family (residue a p k))

/-- The local weighted co-membership kernel, with constant weight `log p`. -/
def kernel (a : V → ℕ) (p K : ℕ) : V → V → ℝ :=
  Erdos126Kernel.familyKernel (nodes a p K) (fun t => t.2) (fun _ => Real.log p)

@[simp] theorem mem_nodes (a : V → ℕ) (p K : ℕ) {t : Σ _ : ℕ, Finset V} :
    t ∈ nodes a p K ↔ t.1 < K ∧ t.2 ∈ Erdos126Orbit.family (residue a p t.1) := by
  simp only [nodes, Finset.mem_sigma, Finset.mem_range]

/-- Every node contains at least two vertices. -/
theorem nodes_card_two_le (a : V → ℕ) (p K : ℕ) :
    ∀ t ∈ nodes a p K, 2 ≤ t.2.card := by
  intro t ht
  exact Erdos126Orbit.card_two_le_of_mem_family (residue a p t.1)
    ((mem_nodes a p K).mp ht).2

/-- At a fixed level, supports are disjoint or equal. -/
theorem family_disjoint_or_eq (a : V → ℕ) (p k : ℕ) {U W : Finset V}
    (hU : U ∈ Erdos126Orbit.family (residue a p k))
    (hW : W ∈ Erdos126Orbit.family (residue a p k)) : Disjoint U W ∨ U = W :=
  Erdos126Orbit.family_disjoint_or_eq (residue a p k) hU hW

/-- When `k ≤ l`, a support at level `l` is disjoint from, or contained in,
a support at level `k`. -/
theorem family_disjoint_or_subset (a : V → ℕ) (p : ℕ) {k l : ℕ} (h : k ≤ l)
    {U W : Finset V}
    (hU : U ∈ Erdos126Orbit.family (residue a p l))
    (hW : W ∈ Erdos126Orbit.family (residue a p k)) : Disjoint U W ∨ U ⊆ W := by
  let f : ZMod (p ^ (l + 1)) →+ ZMod (p ^ (k + 1)) :=
    (ZMod.castHom (pow_dvd_pow p (Nat.add_le_add_right h 1))
      (ZMod (p ^ (k + 1)))).toAddMonoidHom
  have hf : (fun i => f (residue a p l i)) = residue a p k := by
    funext i
    exact castHom_residue a p h i
  apply Erdos126Orbit.family_map_disjoint_or_subset (residue a p l) f hU
  simpa only [hf] using hW

/-- The supports of the level-tagged nodes are laminar. Equal supports at
different levels are allowed. -/
theorem nodes_laminar (a : V → ℕ) (p K : ℕ) :
    ∀ t ∈ nodes a p K, ∀ u ∈ nodes a p K,
      Disjoint t.2 u.2 ∨ t.2 ⊆ u.2 ∨ u.2 ⊆ t.2 := by
  intro t ht u hu
  have htF := ((mem_nodes a p K).mp ht).2
  have huF := ((mem_nodes a p K).mp hu).2
  rcases le_total t.1 u.1 with h | h
  · rcases family_disjoint_or_subset a p h huF htF with hd | hs
    · exact Or.inl hd.symm
    · exact Or.inr (Or.inr hs)
  · rcases family_disjoint_or_subset a p h htF huF with hd | hs
    · exact Or.inl hd
    · exact Or.inr (Or.inl hs)

section Entries

open scoped Classical

/-- Expanding the level tags gives the finite sum of the level kernels. -/
theorem kernel_eq_sum (a : V → ℕ) (p K : ℕ) (i j : V) :
    kernel a p K i j =
      ∑ k ∈ range K, ∑ U ∈ Erdos126Orbit.family (residue a p k),
        if i ∈ U ∧ j ∈ U then Real.log p else 0 := by
  unfold kernel Erdos126Kernel.familyKernel nodes
  exact (Finset.sum_sigma' (range K)
    (fun k => Erdos126Orbit.family (residue a p k))
    (fun _ U => if i ∈ U ∧ j ∈ U then Real.log p else 0)).symm

/-- Equivalently, `log p` multiplies the number of supporting nodes. -/
theorem kernel_eq_log_mul_sum (a : V → ℕ) (p K : ℕ) (i j : V) :
    kernel a p K i j =
      Real.log p * ∑ k ∈ range K, ∑ U ∈ Erdos126Orbit.family (residue a p k),
        if i ∈ U ∧ j ∈ U then (1 : ℝ) else 0 := by
  rw [kernel_eq_sum]
  simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]

/-- Opposite-color entries recover exactly the opposite, non-self-opposite
residue pairs at the chosen levels. -/
theorem kernel_cross_eq (a : V → ℕ) (p K : ℕ) (hp : p.Prime)
    (ha : ∀ i, a i ≠ 0) (i j : V) :
    (if Erdos126PrimeCode.primeColor p (a i) = Erdos126PrimeCode.primeColor p (a j)
      then 0 else kernel a p K i j) =
      Real.log p * ∑ k ∈ range K,
        if residue a p k i = -residue a p k j ∧
          residue a p k i ≠ -residue a p k i then (1 : ℝ) else 0 := by
  calc
    _ = Real.log p * ∑ k ∈ range K,
        ∑ U ∈ Erdos126Orbit.family (residue a p k),
          if i ∈ U ∧ j ∈ U ∧
            Erdos126PrimeCode.primeColor p (a i) ≠ Erdos126PrimeCode.primeColor p (a j)
            then (1 : ℝ) else 0 := by
      by_cases hc : Erdos126PrimeCode.primeColor p (a i) =
          Erdos126PrimeCode.primeColor p (a j)
      · simp [hc]
      · simpa [hc] using kernel_eq_log_mul_sum a p K i j
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      exact Erdos126Orbit.sum_cross_entries (residue a p k)
        (fun i => Erdos126PrimeCode.primeColor p (a i))
        (color_separation a p hp ha k) i j

/-- Prime logarithms give nonnegative local weights. -/
theorem log_prime_nonneg (p : ℕ) (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) :=
  Real.log_nonneg (by exact_mod_cast hp.one_lt.le)

/-- Equal-color entries are bounded by equal, non-self-opposite residues at
the chosen levels. -/
theorem kernel_same_le (a : V → ℕ) (p K : ℕ) (hp : p.Prime)
    (ha : ∀ i, a i ≠ 0) (i j : V) :
    (if Erdos126PrimeCode.primeColor p (a i) = Erdos126PrimeCode.primeColor p (a j)
      then kernel a p K i j else 0) ≤
      Real.log p * ∑ k ∈ range K,
        if residue a p k i = residue a p k j ∧
          residue a p k i ≠ -residue a p k i then (1 : ℝ) else 0 := by
  calc
    _ = Real.log p * ∑ k ∈ range K,
        ∑ U ∈ Erdos126Orbit.family (residue a p k),
          if i ∈ U ∧ j ∈ U ∧
            Erdos126PrimeCode.primeColor p (a i) = Erdos126PrimeCode.primeColor p (a j)
            then (1 : ℝ) else 0 := by
      by_cases hc : Erdos126PrimeCode.primeColor p (a i) =
          Erdos126PrimeCode.primeColor p (a j)
      · simpa only [if_pos hc, hc, and_true] using kernel_eq_log_mul_sum a p K i j
      · simp [hc]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (log_prime_nonneg p hp)
      apply Finset.sum_le_sum
      intro k hk
      exact Erdos126Orbit.sum_same_entries_le (residue a p k)
        (fun i => Erdos126PrimeCode.primeColor p (a i))
        (color_separation a p hp ha k) i j

end Entries

/-- The local kernel has nonnegative entries. -/
theorem kernel_nonneg (a : V → ℕ) (p K : ℕ) (hp : p.Prime) (i j : V) :
    0 ≤ kernel a p K i j :=
  Erdos126Kernel.familyKernel_nonneg (nodes a p K) (fun t => t.2)
    (fun _ => Real.log p) (fun _ _ => log_prime_nonneg p hp) i j

/-- The local kernel is symmetric. -/
theorem kernel_symm (a : V → ℕ) (p K : ℕ) (i j : V) :
    kernel a p K i j = kernel a p K j i :=
  Erdos126Kernel.familyKernel_symm (nodes a p K) (fun t => t.2)
    (fun _ => Real.log p) i j

/-- Nonnegative node weights make the local family kernel positive semidefinite. -/
theorem kernel_psd (a : V → ℕ) (p K : ℕ) (hp : p.Prime) (z : V → ℝ) :
    0 ≤ Erdos126Kernel.qform (kernel a p K) z :=
  Erdos126Kernel.familyKernel_psd (nodes a p K) (fun t => t.2)
    (fun _ => Real.log p) (fun _ _ => log_prime_nonneg p hp) z

end

end Erdos126PrimeFamily
