import Submission.CyclicResidueSampling

/-! A finite correlation transfer from conditioning on divisibility to the full
cyclic average, averaged over coprime moduli. Natural endpoint changes under
multiplication are not removed by this result. -/

namespace Erdos371.FiniteInformation
open Finset

variable {A : Type*} [Fintype A]

/-- A pair in a block, separated by `q`, starting at a position in `[0,q)`. -/
def blockPairArray (H q : ℕ) [NeZero q] (hq : 2*q ≤ H) (C : A → A → ℝ)
    (a : Fin H → A) (j : ZMod q) : ℝ :=
  C (a ⟨j.val, lt_of_lt_of_le j.val_lt (by omega)⟩)
    (a ⟨j.val+q, by have hj := j.val_lt; omega⟩)

omit [Fintype A] in
lemma blockPairArray_abs_le (H q : ℕ) [NeZero q] (hq : 2*q ≤ H)
    (C : A → A → ℝ) (hC : ∀ a b, |C a b| ≤ 1) (a : Fin H → A) (j : ZMod q) :
    |blockPairArray H q hq C a j| ≤ 1 := hC _ _

omit [Fintype A] in
lemma blockPairArray_cyclicBlock (N H q : ℕ) [NeZero N] [NeZero q] (hq : 2*q ≤ H)
    (L : ZMod N → A) (C : A → A → ℝ) (x : ZMod N) (j : ZMod q) :
    blockPairArray H q hq C (labelBlock (Equiv.addRight (1 : ZMod N)) L H x) j =
      C (L (x+(j.val : ZMod N))) (L ((x+(j.val : ZMod N))+(q : ZMod N))) := by
  change C (L (((fun x : ZMod N => x+1)^[j.val]) x))
    (L (((fun x : ZMod N => x+1)^[j.val+q]) x)) = _
  simp only [add_right_iterate, nsmul_one, Nat.cast_add, add_assoc]

/-- The conditioned discrepancy for a single cyclic gap. -/
noncomputable def cyclicGapDiscrepancy (N q : ℕ) [NeZero N] (L : ZMod N → A)
    (C : A → A → ℝ) : ℝ :=
  q * mean (uniformLaw (ZMod N)) (fun x =>
    if cyclicResidue N q x = 0 then C (L x) (L (x+(q : ZMod N))) else 0) -
      mean (uniformLaw (ZMod N)) (fun x => C (L x) (L (x+(q : ZMod N))))

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable (q : ι → ℕ) [∀ i, NeZero (q i)]

/-- Exact information-theoretic correlation transfer on a cycle. The constant
is independent of the modulus sizes and the number of labels. -/
theorem cyclic_gap_average_sq_le_information
    (hcop : Pairwise (fun i j => Nat.Coprime (q i) (q j)))
    (N M H : ℕ) [NeZero N] [NeZero M] (hM : M ∣ N) (hd : (∏ i, q i) ∣ M)
    (hq : ∀ i, 2*q i ≤ H) (L : ZMod N → A) (C : A → A → ℝ)
    (hC : ∀ a b, |C a b| ≤ 1) :
    ((∑ i, cyclicGapDiscrepancy N (q i) L C) / Fintype.card ι) ^ 2 ≤
      8 * mutualInformation
        (blockJointLaw (uniformLaw (ZMod N)) (Equiv.addRight 1) L (cyclicResidue N M) H) /
          Fintype.card ι := by
  let P := blockJointLaw (uniformLaw (ZMod N)) (Equiv.addRight 1) L (cyclicResidue N M) H
  let F : (Fin H → A) → ∀ i, ZMod (q i) → ℝ := fun a i j => blockPairArray H (q i) (hq i) C a j
  have hh := residue_choice_sq_le_information q hcop M hd P
    (secondMarginal_cyclicBlock N M H hM L) F
    (fun a i j => blockPairArray_abs_le H (q i) (hq i) C hC a j)
  have hdiv (i : ι) : q i ∣ M := (dvd_prod_of_mem q (mem_univ i)).trans hd
  have hres (i : ι) (x : ZMod N) :
      cyclicResidue M (q i) (cyclicResidue N M x) = cyclicResidue N (q i) x :=
    congrFun (cyclicResidue_comp N M (q i) hM (hdiv i)) x
  have he : mean P (fun ay =>
      (∑ i, (F ay.1 i (-cyclicResidue M (q i) ay.2) -
        mean (uniformLaw (ZMod (q i))) (F ay.1 i))) / Fintype.card ι) =
          (∑ i, cyclicGapDiscrepancy N (q i) L C) / Fintype.card ι := by
    simp only [P, blockJointLaw, mean_mapLaw]
    rw [mean_div, mean_finset_sum]
    congr 1
    apply sum_congr rfl
    intro i _
    simp only [F, blockPairArray_cyclicBlock, hres]
    exact mean_cyclic_selection_discrepancy N (q i) ((hdiv i).trans hM)
      (fun x => C (L x) (L (x+(q i : ZMod N))))
  rw [he] at hh
  exact hh

#print axioms cyclic_gap_average_sq_le_information
end Erdos371.FiniteInformation
