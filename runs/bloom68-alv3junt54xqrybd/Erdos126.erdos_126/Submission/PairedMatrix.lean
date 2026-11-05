import Submission.PairedCore

/-!
Finite real-matrix estimates used in the paired-block polynomial bound.
In particular, the CND estimate is stated after multiplication by the
number of vertices, so no division or nonempty owner type is implicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos126Aux.Paired

variable {ι : Type*} [Fintype ι]

noncomputable def traceSum (K : ι → ι → ℝ) : ℝ := ∑ i, K i i
noncomputable def rowSum (K : ι → ι → ℝ) (i : ι) : ℝ := ∑ j, K i j
noncomputable def totalSum (K : ι → ι → ℝ) : ℝ := ∑ i, ∑ j, K i j
noncomputable def pairing (K : ι → ι → ℝ) (x y : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * y j * K i j

noncomputable def basis (i : ι) (j : ι) : ℝ := by
  classical
  exact if j = i then 1 else 0

lemma sum_basis (i : ι) : (∑ j, basis i j) = 1 := by
  classical
  simp [basis]

lemma qform_one (K : ι → ι → ℝ) : qform K (fun _ => 1) = totalSum K := by
  simp [qform, totalSum]

lemma pairing_symm (K : ι → ι → ℝ) (hK : ∀ i j, K i j = K j i)
    (x y : ι → ℝ) : pairing K x y = pairing K y x := by
  unfold pairing
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hK j i]
  ring

lemma pairing_add_left (K : ι → ι → ℝ) (x y z : ι → ℝ) :
    pairing K (fun i => x i + y i) z = pairing K x z + pairing K y z := by
  simp only [pairing, add_mul, Finset.sum_add_distrib]

lemma pairing_add_right (K : ι → ι → ℝ) (x y z : ι → ℝ) :
    pairing K x (fun i => y i + z i) = pairing K x y + pairing K x z := by
  simp only [pairing, mul_add, add_mul, Finset.sum_add_distrib]

lemma pairing_affine_left (K : ι → ι → ℝ) (x y z : ι → ℝ) (a c : ℝ) :
    pairing K (fun i => a * x i - c * y i) z =
      a * pairing K x z - c * pairing K y z := by
  unfold pairing
  simp_rw [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]

lemma pairing_affine_right (K : ι → ι → ℝ) (x y z : ι → ℝ) (a c : ℝ) :
    pairing K x (fun i => a * y i - c * z i) =
      a * pairing K x y - c * pairing K x z := by
  unfold pairing
  simp_rw [mul_sub, sub_mul]
  simp_rw [show ∀ i j, x i * (a * y j) * K i j = a * (x i * y j * K i j) by
    intros; ring]
  simp_rw [show ∀ i j, x i * (c * z j) * K i j = c * (x i * z j * K i j) by
    intros; ring]
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

lemma pairing_basis_left (K : ι → ι → ℝ) (i : ι) (x : ι → ℝ) :
    pairing K (basis i) x = ∑ j, x j * K i j := by
  classical
  simp [pairing, basis, ite_mul]

lemma pairing_basis_right (K : ι → ι → ℝ) (i : ι) (x : ι → ℝ) :
    pairing K x (basis i) = ∑ j, x j * K j i := by
  classical
  simp [pairing, basis, mul_ite, ite_mul]

lemma qform_basis (K : ι → ι → ℝ) (i : ι) : qform K (basis i) = K i i := by
  change pairing K (basis i) (basis i) = _
  rw [pairing_basis_left]
  classical
  simp [basis, ite_mul]

lemma qform_add_basis (K : ι → ι → ℝ) (i j : ι) :
    qform K (fun k => basis i k + basis j k) =
      K i i + K i j + (K j i + K j j) := by
  change pairing K (fun k => basis i k + basis j k)
    (fun k => basis i k + basis j k) = _
  rw [pairing_add_left, pairing_add_right, pairing_add_right]
  simp only [pairing_basis_left]
  classical
  simp [basis, ite_mul]

lemma qform_affine (K : ι → ι → ℝ) (hK : ∀ i j, K i j = K j i)
    (x : ι → ℝ) (a c : ℝ) :
    qform K (fun i => a * x i - c) =
      a ^ 2 * qform K x - 2 * a * c * pairing K x (fun _ => 1) +
        c ^ 2 * totalSum K := by
  change pairing K (fun i => a * x i - c) (fun i => a * x i - c) = _
  have he : (fun i => a * x i - c) = (fun i => a * x i - c * 1) := by
    funext i; ring
  rw [he, pairing_affine_left, pairing_affine_right, pairing_affine_right,
    pairing_symm K hK (fun _ => 1) x]
  change a * (a * qform K x - c * pairing K x (fun _ => 1)) -
    c * (a * pairing K x (fun _ => 1) - c * qform K (fun _ => 1)) = _
  rw [qform_one]
  ring

/-- Cardinality of a fiber, with classical decidability internal to the definition. -/
noncomputable def indegree (F : ι → ι) (j : ι) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => F i = j)).card

lemma indegree_eq_filter_card [DecidableEq ι] (F : ι → ι) (j : ι) :
    indegree F j = (Finset.univ.filter (fun i => F i = j)).card := by
  unfold indegree
  apply congrArg Finset.card
  ext i
  simp

/-- A nonnegative weight cannot acquire more than `d` copies under a map
whose fibers have cardinality at most `d`. -/
lemma sum_comp_le_of_indegree (F : ι → ι) (w : ι → ℝ) (d : ℕ)
    (hw : ∀ i, 0 ≤ w i)
    (hF : ∀ j, indegree F j ≤ d) :
    (∑ i, w (F i)) ≤ (d : ℝ) * ∑ j, w j := by
  classical
  calc
    (∑ i, w (F i)) = ∑ i, ∑ j, if F i = j then w j else 0 := by simp
    _ = ∑ j, ∑ i, if F i = j then w j else 0 := Finset.sum_comm
    _ = ∑ j, ((Finset.univ.filter (fun i => F i = j)).card : ℝ) * w j := by
      simp_rw [← Finset.sum_filter]
      simp
    _ ≤ ∑ j, (d : ℝ) * w j := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hF j) (hw j)
    _ = (d : ℝ) * ∑ j, w j := (Finset.mul_sum _ _ _).symm

/-- The elementary CND estimate for a directed mate of bounded indegree.
Only symmetry, zero diagonal, and conditional negative semidefiniteness
are needed; entrywise nonnegativity is not needed. -/
theorem cnd_mate_bound (K : ι → ι → ℝ)
    (hK : ∀ i j, K i j = K j i) (hdiag : ∀ i, K i i = 0)
    (hcnd : CND K) (hn : 0 < Fintype.card ι)
    (F : ι → ι) (d : ℕ)
    (hF : ∀ j, indegree F j ≤ d) :
    (Fintype.card ι : ℝ) * (∑ i, K i (F i)) ≤
      ((d : ℝ) + 1) * totalSum K := by
  classical
  let n : ℝ := Fintype.card ι
  let B : ℝ := totalSum K
  let β : ι → ℝ := fun i => n * rowSum K i - B / 2
  have hnpos : 0 < n := by dsimp [n]; exact_mod_cast hn
  have hβ : ∀ i, 0 ≤ β i := by
    intro i
    have hs : (∑ k, (n * basis i k - 1)) = 0 := by
      simp [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_basis, n]
    have h := hcnd _ hs
    rw [qform_affine K hK, qform_basis, hdiag, pairing_basis_left] at h
    simp only [mul_zero, zero_sub, one_mul, mul_one, one_pow] at h
    dsimp [β, B, rowSum]
    linarith
  have hentry : ∀ i j, n ^ 2 * K i j ≤ 2 * (β i + β j) := by
    intro i j
    have hs : (∑ k, (n * (basis i k + basis j k) - 2)) = 0 := by
      simp [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
        sum_basis, n]
      ring
    have h := hcnd _ hs
    rw [qform_affine K hK, qform_add_basis, hdiag, hdiag, hK j i,
      pairing_add_left, pairing_basis_left, pairing_basis_left] at h
    simp only [one_mul] at h
    dsimp [β, B, rowSum]
    nlinarith
  have hβsum : (∑ i, β i) = n * B / 2 := by
    simp [β, Finset.sum_sub_distrib, ← Finset.mul_sum, rowSum, B, totalSum, n]
    ring
  have hcomp := sum_comp_le_of_indegree F β d hβ hF
  have hsum : n ^ 2 * (∑ i, K i (F i)) ≤ ((d : ℝ) + 1) * n * B := by
    calc
      n ^ 2 * (∑ i, K i (F i)) ≤ ∑ i, 2 * (β i + β (F i)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => hentry i (F i)
      _ = 2 * ((∑ i, β i) + ∑ i, β (F i)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ 2 * ((∑ i, β i) + (d : ℝ) * ∑ i, β i) := by linarith
      _ = ((d : ℝ) + 1) * n * B := by rw [hβsum]; ring
  have : n * (n * (∑ i, K i (F i))) ≤ n * (((d : ℝ) + 1) * B) := by
    nlinarith [hsum]
  exact (mul_le_mul_iff_of_pos_left hnpos).mp this

lemma qform_one_lt_trace (K : ι → ι → ℝ) (hn : 2 ≤ Fintype.card ι)
    (hoff : ∀ i j, i ≠ j → K i j < 0) :
    qform K (fun _ => 1) < traceSum K := by
  classical
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card ι)
  have hrow : ∀ i, (∑ j, K i j) ≤ K i i := by
    intro i
    calc
      (∑ j, K i j) ≤ ∑ j, if j = i then K i i else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hji : j = i
        · simp [hji]
        · simp only [hji, if_false]
          exact (hoff i j (Ne.symm hji)).le
      _ = K i i := by simp
  have hstrict : (∑ k, K i k) < K i i := by
    calc
      (∑ k, K i k) < ∑ k, if k = i then K i i else 0 := by
        apply Finset.sum_lt_sum
        · intro k hk
          by_cases hki : k = i
          · simp [hki]
          · simp only [hki, if_false]
            exact (hoff i k (Ne.symm hki)).le
        · exact ⟨j, Finset.mem_univ _, by simpa [Ne.symm hij] using hoff i j hij⟩
      _ = K i i := by simp
  rw [qform_one]
  exact Finset.sum_lt_sum (fun i _ => hrow i) ⟨i, Finset.mem_univ _, hstrict⟩

/-- An entrywise-negative offdiagonal matrix has a uniform bound on the
quadratic form of vectors in the unit cube. -/
lemma qform_le_twice_trace_sub_total (K : ι → ι → ℝ)
    (hdiag : ∀ i, 0 ≤ K i i) (hoff : ∀ i j, i ≠ j → K i j ≤ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    qform K x ≤ 2 * traceSum K - totalSum K := by
  classical
  have hsq : ∀ i, (x i) ^ 2 ≤ 1 := by
    intro i
    have h := abs_le.mp (hx i)
    nlinarith
  have hprod : ∀ i j, -1 ≤ x i * x j := by
    intro i j
    nlinarith [hsq i, hsq j, sq_nonneg (x i + x j)]
  have he : ∀ i j, x i * x j * K i j ≤
      (if j = i then 2 * K i i else 0) - K i j := by
    intro i j
    by_cases hji : j = i
    · subst j
      simp only [if_true]
      nlinarith [mul_le_mul_of_nonneg_right (hsq i) (hdiag i)]
    · simp only [hji, if_false, zero_sub]
      have := mul_le_mul_of_nonpos_right (hprod i j) (hoff i j (Ne.symm hji))
      nlinarith
  calc
    qform K x ≤ ∑ i, ∑ j, ((if j = i then 2 * K i i else 0) - K i j) := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => he i j
    _ = 2 * traceSum K - totalSum K := by
      simp [Finset.sum_sub_distrib, traceSum, totalSum, Finset.mul_sum]

lemma qform_le_twice_trace (K : ι → ι → ℝ) (hpsd : PSD K)
    (hdiag : ∀ i, 0 ≤ K i i) (hoff : ∀ i j, i ≠ j → K i j ≤ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    qform K x ≤ 2 * traceSum K := by
  have h := qform_le_twice_trace_sub_total K hdiag hoff x hx
  have h0 := hpsd (fun _ => 1)
  rw [qform_one] at h0
  linarith

end Erdos126Aux.Paired
