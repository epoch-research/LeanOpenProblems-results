import Submission.GraphRowGeometryExplore

/-! Connecting the row estimates to the existing cyclic-thickening and
integer-block realization, with arbitrary block-dependent plane templates. -/
namespace Erdos66GraphBlockGeometry
open AdditiveCombinatorics Erdos66CyclicThickening Erdos66IntegerBlock
  Erdos66GraphRowGeometry Erdos66RowSparsePrefix
open scoped Classical
set_option maxHeartbeats 1500000

lemma cyclicEncode_nat_digits (b : ℕ) [NeZero b] (n : ℕ) :
    cyclicEncode b ((n : ZMod b),((n/b : ℕ) : ZMod b))=(n : ZMod (b^2)) := by
  have hm := mul_cast_eq b ((n/b)%b) (n/b) (ZMod.natCast_mod _ _)
  change (((n : ZMod b).val+b*(((n/b : ℕ) : ZMod b).val) : ℕ) : ZMod (b^2))=_
  simp only [ZMod.val_natCast,Nat.cast_add,Nat.cast_mul]
  rw [hm,← Nat.cast_mul,← Nat.cast_add,Nat.mod_add_div]

lemma cyclicDecode_nat (b : ℕ) [NeZero b] (n : ℕ) :
    (cyclicDigitEquiv b).symm (n : ZMod (b^2))=
      ((n : ZMod b),((n/b : ℕ) : ZMod b)) := by
  apply (Equiv.symm_apply_eq _).mpr
  exact (cyclicEncode_nat_digits b n).symm

lemma reduce_nat (p K : ℕ) [NeZero p] [NeZero K] (n : ℕ) :
    reduceDigit p K (n : ZMod (p*K))=(n : ZMod p) := map_natCast _ _

lemma thickenedSet_nat_mem (p K : ℕ) [NeZero p] [NeZero K]
    (B : Finset (ZMod p×ZMod p)) (n : ℕ) :
    (n : ZMod ((p*K)^2))∈thickenedSet p K B ↔
      ((n : ZMod p),((n/(p*K) : ℕ) : ZMod p))∈B := by
  simp only [thickenedSet,Finset.mem_filter,Finset.mem_univ,true_and,
    cyclicDecode_nat,reduce_nat]

lemma thickened_block_eq_rows (p K : ℕ) [NeZero p] [NeZero K]
    (B : ℕ → Finset (ZMod p×ZMod p)) :
    blockSet ((p*K)^2) (fun k ↦ thickenedSet p K (B k))=
      graphRowsSet p K (fun q ↦ B (q/(p*K))) := by
  ext n
  change (n : ZMod ((p*K)^2))∈thickenedSet p K (B (n/((p*K)^2))) ↔ _
  rw [thickenedSet_nat_mem]
  change _ ↔ ((n : ZMod p),((n/(p*K) : ℕ) : ZMod p))∈B (n/(p*K)/(p*K))
  rw [Nat.div_div_eq_div_mul,← pow_two]

/-- The row bound is unchanged by varying the plane template between
integer blocks. In particular, truncated and tapered families are allowed. -/
theorem thickened_block_rowSparse (p K : ℕ) [NeZero p] [NeZero K]
    (B : ℕ → Finset (ZMod p×ZMod p)) (H : ℕ)
    (hB : ∀ q s, rowCount (B q) s ≤ H) :
    RowSparse (blockSet ((p*K)^2) (fun k ↦ thickenedSet p K (B k))) (p*K) (K*H) := by
  rw [thickened_block_eq_rows]
  exact graphRows_sparse p K (fun q ↦ B (q/(p*K))) H (fun q s ↦ hB _ s)

/-- Uniform mixed-count control for the actual integer realization used in
the finite template construction, not just for an unrelated encoding. -/
theorem thickened_block_prefix_bound (p K : ℕ) [NeZero p] [NeZero K]
    (B : ℕ → Finset (ZMod p×ZMod p)) (H : ℕ)
    (hB : ∀ q s, rowCount (B q) s ≤ H)
    (A : Finset ℕ) (L n : ℕ) (hA : ∀ a∈A, a<L) (hL : L ≤ p*K)
    (hd : Disjoint (A : Set ℕ) (blockSet ((p*K)^2) (fun k ↦ thickenedSet p K (B k))))
    (hn : 2*L ≤ n) :
    let C := blockSet ((p*K)^2) (fun k ↦ thickenedSet p K (B k))
    sumRep C n ≤ sumRep ((A : Set ℕ)∪C) n ∧
      sumRep ((A : Set ℕ)∪C) n ≤ sumRep C n+4*K*H := by
  dsimp only
  have hh := union_short_prefix_bound A _ L (p*K) (K*H) n hA hd
    (Nat.mul_pos (NeZero.pos p) (NeZero.pos K)) hL (thickened_block_rowSparse p K B H hB) hn
  convert hh using 1 <;> ring

end Erdos66GraphBlockGeometry
