import Submission.FirstHitDisjointCost

/-! Exact Boolean coefficient costs for a core-supported common lower kernel.
This is an algebraic limitation of a coefficientwise unit-error estimate, not
an obstruction to stronger arithmetic remainder bounds or a Jacobsthal disproof. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- All nonzero monomials use only the indicated core coordinates. -/
def CoeffSupportedOn (a : Finset ι → ℝ) (A : Finset ι) : Prop :=
  ∀ T, a T ≠ 0 → T ⊆ A

omit [Fintype ι] [DecidableEq ι] in
lemma CoeffSupportedOn.zero_of_not_subset {a : Finset ι → ℝ} {A T : Finset ι}
    (ha : CoeffSupportedOn a A) (hT : ¬T ⊆ A) : a T = 0 := by
  by_contra hn
  exact hT (ha T hn)

lemma ordinaryCoefficient_supported (q : ι → ℝ) (c : Finset ι → ℝ)
    (A : Finset ι) (hc : CoeffSupportedOn c A) :
    CoeffSupportedOn (ordinaryCoefficient q c) A := by
  intro T hT
  by_contra hTA
  apply hT
  unfold ordinaryCoefficient
  have hz : (∑ Q : Finset ι, if T ⊆ Q then c Q else 0) = 0 := by
    apply sum_eq_zero
    intro Q hQ
    split_ifs with hTQ
    · exact hc.zero_of_not_subset (fun hQA => hTA (hTQ.trans hQA))
    · rfl
  rw [hz, mul_zero]

lemma booleanSquareCoefficient_supported (a : Finset ι → ℝ) (A : Finset ι)
    (ha : CoeffSupportedOn a A) : CoeffSupportedOn (booleanSquareCoefficient a) A := by
  intro T hT
  obtain ⟨Q, _, hQ⟩ := exists_ne_zero_of_sum_ne_zero hT
  obtain ⟨R, _, hR⟩ := exists_ne_zero_of_sum_ne_zero hQ
  by_cases he : Q ∪ R = T
  · rw [if_pos he] at hR
    obtain ⟨haQ, haR⟩ := mul_ne_zero_iff.mp hR
    rw [← he]
    exact union_subset (ha Q haQ) (ha R haR)
  · simp [he] at hR

omit [Fintype ι] in
lemma hitShift_nonzero_of_supported (b : Finset ι → ℝ) (A : Finset ι)
    (hb : CoeffSupportedOn b A) (i : ι) (T : Finset ι)
    (hT : hitShiftCoefficient i b T ≠ 0) : i ∈ T ∧ T.erase i ⊆ A := by
  by_cases hi : i ∈ T
  · exact ⟨hi, hb _ (by simpa [hitShiftCoefficient, hi] using hT)⟩
  · simp [hitShiftCoefficient, hi] at hT

/-- Different tail coordinates give disjoint monomial supports, without an
ordering assumption and even when every tail uses the same core polynomial. -/
lemma tail_hitShift_disjoint (b : Finset ι → ℝ) (A B : Finset ι)
    (hb : CoeffSupportedOn b A) (hAB : Disjoint A B)
    (i j : ι) (_hi : i ∈ B) (hj : j ∈ B) (hij : i ≠ j) (T : Finset ι) :
    hitShiftCoefficient i b T = 0 ∨ hitShiftCoefficient j b T = 0 := by
  by_contra hn
  push_neg at hn
  have hiT := hitShift_nonzero_of_supported b A hb i T hn.1
  have hjT := hitShift_nonzero_of_supported b A hb j T hn.2
  have hjA := hiT.2 (mem_erase.mpr ⟨hij.symm, hjT.1⟩)
  exact (disjoint_left.mp hAB) hjA hj

lemma core_tail_abs_identity (b c : Finset ι → ℝ) (A B : Finset ι)
    (hb : CoeffSupportedOn b A) (hc : CoeffSupportedOn c A)
    (hAB : Disjoint A B) (T : Finset ι) :
    |c T - ∑ i ∈ B, hitShiftCoefficient i b T| =
      |c T| + ∑ i ∈ B, |hitShiftCoefficient i b T| := by
  by_cases hex : ∃ i ∈ B, hitShiftCoefficient i b T ≠ 0
  · obtain ⟨i, hi, hiT⟩ := hex
    have hz (j : ι) (hj : j ∈ B) (hji : j ≠ i) :
        hitShiftCoefficient j b T = 0 :=
      (tail_hitShift_disjoint b A B hb hAB j i hj hi hji T).resolve_right hiT
    have hcT : c T = 0 := by
      apply hc.zero_of_not_subset
      intro hTA
      have hiA := hTA (hitShift_nonzero_of_supported b A hb i T hiT).1
      exact (disjoint_left.mp hAB) hiA hi
    rw [sum_eq_single i (fun j hj hji => hz j hj hji) (by simp [hi]),
      sum_eq_single i (fun j hj hji => by rw [hz j hj hji, abs_zero]) (by simp [hi]), hcT]
    simp
  · push_neg at hex
    have hz : (∑ i ∈ B, hitShiftCoefficient i b T) = 0 := sum_eq_zero hex
    have hza : (∑ i ∈ B, |hitShiftCoefficient i b T|) = 0 :=
      sum_eq_zero (fun i hi => by rw [hex i hi, abs_zero])
    rw [hz, hza, sub_zero, add_zero]

/-- The tail-cardinality factor is exact after Boolean merging. The core
contribution is allowed to have arbitrary signed coefficients. -/
theorem core_tail_merged_cost (b c : Finset ι → ℝ) (A B : Finset ι)
    (hb : CoeffSupportedOn b A) (hc : CoeffSupportedOn c A)
    (hAB : Disjoint A B) :
    (∑ T : Finset ι, |c T - ∑ i ∈ B, hitShiftCoefficient i b T|) =
      (∑ T : Finset ι, |c T|) + (B.card : ℝ) * ∑ T : Finset ι, |b T| := by
  simp_rw [core_tail_abs_identity b c A B hb hc hAB]
  rw [sum_add_distrib, sum_comm]
  congr 1
  calc
    (∑ i ∈ B, ∑ T : Finset ι, |hitShiftCoefficient i b T|) =
        ∑ _i ∈ B, ∑ T : Finset ι, |b T| := by
      apply sum_congr rfl
      intro i hi
      apply hitShift_cost
      intro T hiT
      apply hb.zero_of_not_subset
      intro hTA
      exact (disjoint_left.mp hAB) (hTA hiT) hi
    _ = _ := by simp

/-- The Boolean coefficient of multiplication by a hit, allowing that
coordinate to occur in the original polynomial. -/
noncomputable def booleanHitCoefficient (i : ι) (b : Finset ι → ℝ)
    (T : Finset ι) : ℝ :=
  if i ∈ T then b T + b (T.erase i) else 0

lemma booleanHit_expansion (i : ι) (b : Finset ι → ℝ) (ω : ι → Bool) :
    (∑ T : Finset ι, booleanHitCoefficient i b T * hitMonomial T ω) =
      hitMonomial {i} ω * (∑ T : Finset ι, b T * hitMonomial T ω) := by
  rw [sum_all_split i, sum_all_split i (fun T => b T * hitMonomial T ω), mul_sum]
  apply sum_congr rfl
  intro Q hQ
  have hiQ := not_mem_of_erase_powerset hQ
  simp only [booleanHitCoefficient, if_neg hiQ, mem_insert_self, if_true,
    erase_insert hiQ, zero_mul, zero_add]
  have hi : hitMonomial {i} ω * hitMonomial {i} ω = hitMonomial {i} ω := by
    rw [hitMonomial_mul, union_self]
  rw [show insert i Q = {i} ∪ Q by simp, ← hitMonomial_mul]
  linear_combination -(b ({i} ∪ Q) * hitMonomial Q ω) * hi

lemma booleanHit_supported (b : Finset ι → ℝ) (A : Finset ι)
    (hb : CoeffSupportedOn b A) (i : ι) (hi : i ∈ A) :
    CoeffSupportedOn (booleanHitCoefficient i b) A := by
  intro T hT
  by_contra hn
  apply hT
  unfold booleanHitCoefficient
  split_ifs with hiT
  · have he : ¬T.erase i ⊆ A := by
      intro h
      apply hn
      intro j hj
      by_cases hji : j = i
      · simpa [hji] using hi
      · exact h (mem_erase.mpr ⟨hji, hj⟩)
    rw [hb.zero_of_not_subset hn, hb.zero_of_not_subset he, add_zero]
  · rfl

noncomputable def booleanLowerCoefficient (A : Finset ι) (b : Finset ι → ℝ)
    (T : Finset ι) : ℝ :=
  b T - ∑ i ∈ A, booleanHitCoefficient i b T

lemma booleanLower_supported (b : Finset ι → ℝ) (A : Finset ι)
    (hb : CoeffSupportedOn b A) : CoeffSupportedOn (booleanLowerCoefficient A b) A := by
  intro T hT
  by_contra hn
  apply hT
  unfold booleanLowerCoefficient
  rw [hb.zero_of_not_subset hn]
  have hz : (∑ i ∈ A, booleanHitCoefficient i b T) = 0 := by
    exact sum_eq_zero (fun i hi => (booleanHit_supported b A hb i hi).zero_of_not_subset hn)
  rw [hz, sub_self]

lemma booleanLower_expansion (A : Finset ι) (b : Finset ι → ℝ) (ω : ι → Bool) :
    (∑ T : Finset ι, booleanLowerCoefficient A b T * hitMonomial T ω) =
      (1 - ∑ i ∈ A, hitMonomial {i} ω) * (∑ T : Finset ι, b T * hitMonomial T ω) := by
  simp only [booleanLowerCoefficient, sub_mul, sum_sub_distrib, sum_mul]
  rw [sum_comm]
  simp_rw [booleanHit_expansion]
  rw [← sum_mul]
  ring

lemma booleanHit_eq_shift_of_not_mem (b : Finset ι → ℝ) (A : Finset ι)
    (hb : CoeffSupportedOn b A) (i : ι) (hi : i ∉ A) (T : Finset ι) :
    booleanHitCoefficient i b T = hitShiftCoefficient i b T := by
  unfold booleanHitCoefficient hitShiftCoefficient
  split_ifs with hiT
  · have hz := hb.zero_of_not_subset (fun hTA => hi (hTA hiT))
    rw [hz, zero_add]
  · rfl

/-- The exact L1 cost of the full common lower polynomial is the core lower
cost plus one full Boolean-square cost for every coordinate outside the core. -/
theorem common_lower_boolean_cost (a : Finset ι → ℝ) (A : Finset ι)
    (ha : CoeffSupportedOn a A) :
    (∑ T : Finset ι, |booleanLowerCoefficient univ (booleanSquareCoefficient a) T|) =
      (∑ T : Finset ι, |booleanLowerCoefficient A (booleanSquareCoefficient a) T|) +
        ((univ \ A).card : ℝ) * booleanSquareCost a := by
  let b := booleanSquareCoefficient a
  have hb : CoeffSupportedOn b A := booleanSquareCoefficient_supported a A ha
  have hc := booleanLower_supported b A hb
  have he (T : Finset ι) : booleanLowerCoefficient univ b T =
      booleanLowerCoefficient A b T - ∑ i ∈ univ \ A, hitShiftCoefficient i b T := by
    unfold booleanLowerCoefficient
    have hs := sum_sdiff (subset_univ A) (f := fun i => booleanHitCoefficient i b T)
    have ht : (∑ i ∈ univ \ A, booleanHitCoefficient i b T) =
        ∑ i ∈ univ \ A, hitShiftCoefficient i b T := by
      apply sum_congr rfl
      intro i hi
      exact booleanHit_eq_shift_of_not_mem b A hb i (mem_sdiff.mp hi).2 T
    rw [ht] at hs
    linarith
  change (∑ T : Finset ι, |booleanLowerCoefficient univ b T|) = _
  simp_rw [he]
  exact core_tail_merged_cost b (booleanLowerCoefficient A b) A (univ \ A)
    hb hc disjoint_sdiff_self_right

/-- The tail contribution remains a lower bound even after all core
cancellations have been performed. This is a statement about coefficient
cost, not a lower bound for an actual interval discrepancy. -/
theorem tail_card_mul_booleanSquareCost_le (a : Finset ι → ℝ) (A : Finset ι)
    (ha : CoeffSupportedOn a A) :
    ((univ \ A).card : ℝ) * booleanSquareCost a ≤
      ∑ T : Finset ι, |booleanLowerCoefficient univ (booleanSquareCoefficient a) T| := by
  rw [common_lower_boolean_cost a A ha]
  exact le_add_of_nonneg_left (sum_nonneg (fun _ _ => abs_nonneg _))

/-- Exact expansion of the common Selberg lower kernel in the Boolean basis. -/
lemma common_lower_expansion (q : ι → ℝ) (c : Finset ι → ℝ) (ω : ι → Bool) :
    (∑ T : Finset ι,
      booleanLowerCoefficient univ (booleanSquareCoefficient (ordinaryCoefficient q c)) T *
        hitMonomial T ω) =
      (1 - ∑ i, hitCoordinate i ω) * linearKernel q c ω ^ 2 := by
  rw [booleanLower_expansion, ← booleanSquare_expansion, ← linearKernel_expansion]
  congr 2
  apply sum_congr rfl
  intro i hi
  simp only [hitMonomial, prod_singleton, hitCoordinate]

/-- A unit-error estimate with the fully merged Boolean cost. -/
theorem arbitrary_lowerKernel_boolean_error (q : ι → ℝ) (hq : ∀ i, q i ≠ 0)
    (c : Finset ι → ℝ) (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1) :
    |(∑ j ∈ range m, (1 - ∑ i, hitCoordinate i (ω j)) * linearKernel q c (ω j) ^ 2) -
      (m : ℝ) * kernelEnergy q c| ≤
      ∑ T : Finset ι,
        |booleanLowerCoefficient univ (booleanSquareCoefficient (ordinaryCoefficient q c)) T| := by
  have he := finite_polynomial_interval_error univ
    (booleanLowerCoefficient univ (booleanSquareCoefficient (ordinaryCoefficient q c)))
    id q m ω herr
  simp only [id_eq] at he
  simp_rw [common_lower_expansion] at he
  rwa [lowerKernel_average q hq c] at he

/-- For a core-supported orthogonal kernel, the exact cost splits into its
core part and one Boolean-square cost per tail coordinate. -/
theorem common_lower_error_core_tail (q : ι → ℝ) (hq : ∀ i, q i ≠ 0)
    (c : Finset ι → ℝ) (A : Finset ι) (hc : CoeffSupportedOn c A)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1) :
    |(∑ j ∈ range m, (1 - ∑ i, hitCoordinate i (ω j)) * linearKernel q c (ω j) ^ 2) -
      (m : ℝ) * kernelEnergy q c| ≤
      (∑ T : Finset ι,
        |booleanLowerCoefficient A (booleanSquareCoefficient (ordinaryCoefficient q c)) T|) +
        ((univ \ A).card : ℝ) * booleanSquareCost (ordinaryCoefficient q c) := by
  have he := arbitrary_lowerKernel_boolean_error q hq c m ω herr
  rwa [common_lower_boolean_cost _ A (ordinaryCoefficient_supported q c A hc)] at he

/-- A sufficient survivor criterion retaining the exact Boolean cost. The
main-term inequality remains an explicit hypothesis. -/
theorem survivor_of_kernelEnergy_boolean_cost (q : ι → ℝ) (hq : ∀ i, q i ≠ 0)
    (c : Finset ι → ℝ) (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (hmain : (∑ T : Finset ι,
      |booleanLowerCoefficient univ (booleanSquareCoefficient (ordinaryCoefficient q c)) T|) <
        (m : ℝ) * kernelEnergy q c) :
    ∃ j < m, ∀ i, ω j i = false := by
  by_contra hbad
  push_neg at hbad
  have hsum : (∑ j ∈ range m,
      (1 - ∑ i, hitCoordinate i (ω j)) * linearKernel q c (ω j) ^ 2) ≤ 0 := by
    apply sum_nonpos
    intro j hj
    apply lowerKernel_nonpos_of_nonempty
    intro he
    obtain ⟨i, hi⟩ := hbad j (mem_range.mp hj)
    exact hi (congrFun he i)
  have he := (abs_le.mp (arbitrary_lowerKernel_boolean_error q hq c m ω herr)).1
  linarith

/-- The empty monomial has no interval-count error, so it need not be
charged in the coefficientwise remainder budget. -/
noncomputable def nonemptyCoeffCost (a : Finset ι → ℝ) : ℝ :=
  ∑ T ∈ (univ : Finset (Finset ι)).erase ∅, |a T|

lemma nonemptyCoeffCost_eq (a : Finset ι → ℝ) :
    nonemptyCoeffCost a = (∑ T : Finset ι, |a T|) - |a ∅| := by
  unfold nonemptyCoeffCost
  have hh := sum_erase_add (s := (univ : Finset (Finset ι))) (fun T => |a T|) (mem_univ ∅)
  linarith

omit [Fintype ι] in
lemma booleanLowerCoefficient_empty (A : Finset ι) (b : Finset ι → ℝ) :
    booleanLowerCoefficient A b ∅ = b ∅ := by
  simp [booleanLowerCoefficient, booleanHitCoefficient]

/-- Even with the empty-monomial error deleted, merging leaves exactly the
same tail-cardinality factor. -/
theorem common_lower_nonempty_cost (a : Finset ι → ℝ) (A : Finset ι)
    (ha : CoeffSupportedOn a A) :
    nonemptyCoeffCost (booleanLowerCoefficient univ (booleanSquareCoefficient a)) =
      nonemptyCoeffCost (booleanLowerCoefficient A (booleanSquareCoefficient a)) +
        ((univ \ A).card : ℝ) * booleanSquareCost a := by
  rw [nonemptyCoeffCost_eq, nonemptyCoeffCost_eq, common_lower_boolean_cost a A ha,
    booleanLowerCoefficient_empty, booleanLowerCoefficient_empty]
  ring

theorem tail_card_mul_booleanSquareCost_le_nonempty (a : Finset ι → ℝ)
    (A : Finset ι) (ha : CoeffSupportedOn a A) :
    ((univ \ A).card : ℝ) * booleanSquareCost a ≤
      nonemptyCoeffCost (booleanLowerCoefficient univ (booleanSquareCoefficient a)) := by
  rw [common_lower_nonempty_cost a A ha]
  exact le_add_of_nonneg_left (sum_nonneg (fun _ _ => abs_nonneg _))

lemma boolean_polynomial_interval_error_nonempty (q : ι → ℝ)
    (a : Finset ι → ℝ) (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι, T.Nonempty →
      |(∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1) :
    |(∑ j ∈ range m, ∑ T : Finset ι, a T * hitMonomial T (ω j)) -
      (m : ℝ) * average q (fun v => ∑ T : Finset ι, a T * hitMonomial T v)| ≤
        nonemptyCoeffCost a := by
  let E (T : Finset ι) := a T *
    ((∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i)
  have he : (∑ j ∈ range m, ∑ T : Finset ι, a T * hitMonomial T (ω j)) -
      (m : ℝ) * average q (fun v => ∑ T : Finset ι, a T * hitMonomial T v) =
        ∑ T : Finset ι, E T := by
    rw [average_sum]
    simp_rw [average_mul_const, average_hitMonomial]
    rw [sum_comm, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro T hT
    rw [← mul_sum]
    dsimp only [E]
    ring
  have he0 : E ∅ = 0 := by simp [E, hitMonomial]
  have hes : (∑ T : Finset ι, E T) = ∑ T ∈ (univ : Finset (Finset ι)).erase ∅, E T := by
    have hh := sum_erase_add (s := (univ : Finset (Finset ι))) E (mem_univ ∅)
    rw [he0, add_zero] at hh
    exact hh.symm
  rw [he, hes]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro T hT
  have hne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr (mem_erase.mp hT).1
  dsimp only [E]
  rw [abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (herr T hne) (abs_nonneg (a T))

/-- Fully merged common-kernel remainder with no constant-coefficient charge. -/
theorem arbitrary_lowerKernel_nonempty_boolean_error (q : ι → ℝ)
    (hq : ∀ i, q i ≠ 0) (c : Finset ι → ℝ) (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι, T.Nonempty →
      |(∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1) :
    |(∑ j ∈ range m, (1 - ∑ i, hitCoordinate i (ω j)) * linearKernel q c (ω j) ^ 2) -
      (m : ℝ) * kernelEnergy q c| ≤
      nonemptyCoeffCost (booleanLowerCoefficient univ
        (booleanSquareCoefficient (ordinaryCoefficient q c))) := by
  have he := boolean_polynomial_interval_error_nonempty q
    (booleanLowerCoefficient univ (booleanSquareCoefficient (ordinaryCoefficient q c))) m ω herr
  simp_rw [common_lower_expansion] at he
  rwa [lowerKernel_average q hq c] at he

#print axioms common_lower_nonempty_cost
#print axioms tail_card_mul_booleanSquareCost_le_nonempty
#print axioms arbitrary_lowerKernel_nonempty_boolean_error
#print axioms core_tail_merged_cost
#print axioms common_lower_boolean_cost
#print axioms common_lower_expansion
#print axioms common_lower_error_core_tail
#print axioms survivor_of_kernelEnergy_boolean_cost
end Erdos970.FiniteSelberg
