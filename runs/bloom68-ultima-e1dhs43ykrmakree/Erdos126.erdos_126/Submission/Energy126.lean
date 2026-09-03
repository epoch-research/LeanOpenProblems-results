import FormalConjecturesUtil
import Submission.Model126
import Submission.LogKernel126

/-!
# Energy and diameter bounds for opposition trees

The local estimates use only laminarity and bichromatic nodes. The global
energy estimate combines the unsigned and signed Gram kernels with CND.
The diameter estimate uses a three-point CND test, not a Euclidean embedding.
-/

open scoped BigOperators

namespace E126

noncomputable section

variable {ι : Type*} [DecidableEq ι]

namespace LaminarFamily

/-- Inclusion of the common-node supports gives an inequality of kernels. -/
theorem kernel_le_of_common_nodes (W : LaminarFamily ι) (a b c d : ι)
    (h : ∀ B ∈ W.nodes, a ∈ B → b ∈ B → c ∈ B ∧ d ∈ B) :
    W.kernel a b ≤ W.kernel c d := by
  apply Finset.sum_le_sum
  intro B hB
  by_cases ha : a ∈ B
  · by_cases hb : b ∈ B
    · obtain ⟨hc, hd⟩ := h B hB ha hb
      simp [ind, ha, hb, hc, hd]
    · simpa [ind, hb] using
        mul_nonneg (mul_nonneg (W.weight_nonneg B hB) (ind_nonneg B c))
          (ind_nonneg B d)
  · simpa [ind, ha] using
      mul_nonneg (mul_nonneg (W.weight_nonneg B hB) (ind_nonneg B c))
        (ind_nonneg B d)

/-- A laminar common-ancestor kernel is an ultrametric similarity. -/
theorem kernel_min_le (W : LaminarFamily ι) (x i j : ι) :
    min (W.kernel x i) (W.kernel x j) ≤ W.kernel i j := by
  by_cases h : ∀ B ∈ W.nodes, x ∈ B → i ∈ B → j ∈ B
  · exact (min_le_left _ _).trans
      (W.kernel_le_of_common_nodes x i i j (fun B hB hx hi => ⟨hi, h B hB hx hi⟩))
  · push_neg at h
    obtain ⟨B, hB, hxB, hiB, hjB⟩ := h
    apply (min_le_right _ _).trans
    apply W.kernel_le_of_common_nodes x j i j
    intro C hC hxC hjC
    rcases W.laminar B hB C hC with hBC | hCB | hd
    · exact ⟨hBC hiB, hjC⟩
    · exact (hjB (hCB hjC)).elim
    · exact (Finset.disjoint_left.mp hd hxB hxC).elim

/-- A smallest node through a point is contained in all nodes through it. -/
theorem exists_smallest_node (W : LaminarFamily ι) (i : ι)
    (h : ∃ B ∈ W.nodes, i ∈ B) :
    ∃ B ∈ W.nodes, i ∈ B ∧ ∀ C ∈ W.nodes, i ∈ C → B ⊆ C := by
  let S := W.nodes.filter (fun B => i ∈ B)
  have hS : S.Nonempty := by
    obtain ⟨B, hB, hi⟩ := h
    exact ⟨B, Finset.mem_filter.mpr ⟨hB, hi⟩⟩
  obtain ⟨B, hB, hmin⟩ := S.exists_min_image Finset.card hS
  obtain ⟨hBW, hiB⟩ := Finset.mem_filter.mp hB
  refine ⟨B, hBW, hiB, ?_⟩
  intro C hC hiC
  rcases W.laminar B hBW C hC with hBC | hCB | hd
  · exact hBC
  · have hcard : B.card ≤ C.card := hmin C (Finset.mem_filter.mpr ⟨hC, hiC⟩)
    have heq : C = B := Finset.eq_of_subset_of_card_le hCB hcard
    rw [heq]
  · exact (Finset.disjoint_left.mp hd hiB hiC).elim

end LaminarFamily

namespace OppositionFamily

theorem agreement_nonneg (W : OppositionFamily ι) (i j : ι) :
    0 ≤ W.agreement i j := by
  unfold agreement
  split
  · exact W.unsigned_nonneg i j
  · exact le_rfl

/-- The common-neighbor bound, also valid with coincident indices. -/
theorem opposition_min_le_agreement (W : OppositionFamily ι) (x i j : ι) :
    min (W.opposition x i) (W.opposition x j) ≤ W.agreement i j := by
  by_cases hxi : W.sign x = W.sign i
  · calc
      _ ≤ W.opposition x i := min_le_left _ _
      _ = 0 := if_pos hxi
      _ ≤ _ := W.agreement_nonneg i j
  by_cases hxj : W.sign x = W.sign j
  · calc
      _ ≤ W.opposition x j := min_le_right _ _
      _ = 0 := if_pos hxj
      _ ≤ _ := W.agreement_nonneg i j
  have hij : W.sign i = W.sign j := by
    cases hx : W.sign x <;> cases hi : W.sign i <;> cases hj : W.sign j <;>
      simp_all
  simpa only [opposition, agreement, if_neg hxi, if_neg hxj, if_pos hij] using
    W.toLaminarFamily.kernel_min_le x i j

/-- Bichromaticity supplies an opposite vertex realizing the entire diagonal.
If no node contains `i`, both sides are zero and the witness can be `i`. -/
theorem exists_diagonal_witness (W : OppositionFamily ι) (i : ι) :
    ∃ j, W.unsigned i i = W.opposition i j := by
  by_cases h : ∃ B ∈ W.nodes, i ∈ B
  · obtain ⟨B, hB, hiB, hmin⟩ := W.toLaminarFamily.exists_smallest_node i h
    obtain ⟨j, hjB, hji⟩ := W.bichromatic B hB i hiB
    refine ⟨j, ?_⟩
    rw [opposition, if_neg (Ne.symm hji)]
    unfold unsigned LaminarFamily.kernel
    apply Finset.sum_congr rfl
    intro C hC
    by_cases hiC : i ∈ C
    · have hjC : j ∈ C := hmin C hC hiC hjB
      simp [ind, hiC, hjC]
    · simp [ind, hiC]
  · refine ⟨i, ?_⟩
    rw [opposition_diag]
    unfold unsigned LaminarFamily.kernel
    apply Finset.sum_eq_zero
    intro B hB
    have hiB : i ∉ B := fun hi => h ⟨B, hB, hi⟩
    simp [ind, hiB]

/-- In particular, any uniform opposition bound controls the unsigned diagonal. -/
theorem unsigned_diag_le (W : OppositionFamily ι) (L : ℝ)
    (hL : ∀ i j, W.opposition i j ≤ L) (i : ι) :
    W.unsigned i i ≤ L := by
  obtain ⟨j, hj⟩ := W.exists_diagonal_witness i
  rw [hj]
  exact hL i j

end OppositionFamily

variable [Fintype ι]

namespace LaminarFamily

/-- The unsigned kernel is a nonnegative sum of rank-one quadratic forms. -/
theorem kernel_quad_eq (W : LaminarFamily ι) (q : ι → ℝ) :
    quad W.kernel q = ∑ B ∈ W.nodes, W.weight B * (∑ i, q i * ind B i) ^ 2 := by
  simpa only [quad, kernel, mul_assoc] using
    LogKernel.weighted_feature_sum W.nodes W.weight ind q

theorem kernel_psd (W : LaminarFamily ι) (q : ι → ℝ) :
    0 ≤ quad W.kernel q := by
  rw [W.kernel_quad_eq]
  exact Finset.sum_nonneg (fun B hB => mul_nonneg (W.weight_nonneg B hB) (sq_nonneg _))

end LaminarFamily

namespace OppositionFamily

theorem unsigned_psd (W : OppositionFamily ι) (q : ι → ℝ) :
    0 ≤ quad W.unsigned q := W.toLaminarFamily.kernel_psd q

/-- Consistent signs preserve the Gram representation. -/
theorem signed_psd (W : OppositionFamily ι) (q : ι → ℝ) :
    0 ≤ quad W.signed q := by
  calc
    0 ≤ quad W.unsigned (fun i => q i * W.signVal i) := W.unsigned_psd _
    _ = quad W.signed q := by
      unfold quad signed
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

omit [Fintype ι] in
@[simp] theorem signed_diag (W : OppositionFamily ι) (i : ι) :
    W.signed i i = W.unsigned i i := by
  rw [signed, ← pow_two, signVal_sq, one_mul]

end OppositionFamily

omit [DecidableEq ι] in
/-- A PSD matrix with nonpositive off-diagonal entries is bounded by twice its
own diagonal. Symmetry is not needed for this quadratic-form statement. -/
theorem z_matrix_quad_le (K : ι → ι → ℝ)
    (hpsd : ∀ q, 0 ≤ quad K q) (hoff : ∀ i j, i ≠ j → K i j ≤ 0) (q : ι → ℝ) :
    quad K q ≤ 2 * ∑ i, q i ^ 2 * K i i := by
  classical
  have hterm (i j : ι) :
      q i * q j * K i j + |q i| * |q j| * K i j ≤
        if i = j then 2 * (q i ^ 2 * K i i) else 0 := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl, ← pow_two, ← pow_two, sq_abs]
      linarith
    · rw [if_neg hij]
      have hab : 0 ≤ q i * q j + |q i| * |q j| := by
        have h := neg_abs_le (q i * q j)
        rw [abs_mul] at h
        linarith
      simpa only [add_mul] using
        mul_nonpos_of_nonneg_of_nonpos hab (hoff i j hij)
  have hsum : quad K q + quad K (fun i => |q i|) ≤ 2 * ∑ i, q i ^ 2 * K i i := by
    calc
      _ = ∑ i, ∑ j, (q i * q j * K i j + |q i| * |q j| * K i j) := by
        simp only [quad, Finset.sum_add_distrib]
      _ ≤ ∑ i, ∑ j, if i = j then 2 * (q i ^ 2 * K i i) else 0 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
      _ = _ := by simp [Finset.mul_sum]
  have habs := hpsd (fun i => |q i|)
  linarith

omit [DecidableEq ι] in
/-- A three-point test of CND gives the squared-distance triangle bound directly.
The test vector is `e_a + e_b - 2 e_y`; coincident points are allowed. -/
theorem cnd_triangle (K : ι → ι → ℝ) (hCND : CND K)
    (hsym : ∀ i j, K i j = K j i) (hdiag : ∀ i, K i i = 0) (a b y : ι) :
    K a b ≤ 2 * K a y + 2 * K b y := by
  classical
  let q : ι → ℝ := fun i =>
    (if i = a then 1 else 0) + (if i = b then 1 else 0) -
      2 * (if i = y then 1 else 0)
  have htest (f : ι → ℝ) : ∑ i, q i * f i = f a + f b - 2 * f y := by
    simp [q, add_mul, sub_mul, ite_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
  have hq : ∑ i, q i = 0 := by
    have h := htest (fun _ => 1)
    norm_num at h
    exact h
  have heval : quad K q =
      (K a a + K a b - 2 * K a y) + (K b a + K b b - 2 * K b y) -
        2 * (K y a + K y b - 2 * K y y) := by
    calc
      _ = ∑ i, q i * (∑ j, q j * K i j) := by
        simp only [quad, Finset.mul_sum, mul_assoc]
      _ = (∑ j, q j * K a j) + (∑ j, q j * K b j) -
          2 * (∑ j, q j * K y j) := htest _
      _ = _ := by rw [htest, htest, htest]
  have hc := hCND q hq
  rw [heval, hdiag a, hdiag b, hdiag y, hsym b a, hsym y a, hsym y b] at hc
  linarith

variable {κ : Type*} [Fintype κ]

omit [DecidableEq ι] in
/-- Quadratic forms commute with finite sums of kernels. -/
theorem quad_sum (K : κ → ι → ι → ℝ) (q : ι → ℝ) :
    quad (fun i j => ∑ p, K p i j) q = ∑ p, quad (K p) q := by
  classical
  unfold quad
  simp_rw [Finset.mul_sum]
  calc
    (∑ i, ∑ j, ∑ p, q i * q j * K p i j) =
        ∑ i, ∑ p, ∑ j, q i * q j * K p i j := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem totalUnsigned_psd (W : κ → OppositionFamily ι) (q : ι → ℝ) :
    0 ≤ quad (totalUnsigned W) q := by
  unfold totalUnsigned
  rw [quad_sum]
  exact Finset.sum_nonneg (fun p _ => (W p).unsigned_psd q)

theorem totalSigned_psd (W : κ → OppositionFamily ι) (q : ι → ℝ) :
    0 ≤ quad (totalSigned W) q := by
  unfold totalSigned
  rw [quad_sum]
  exact Finset.sum_nonneg (fun p _ => (W p).signed_psd q)

omit [Fintype ι] in
theorem opposition_le_totalOpposition (W : κ → OppositionFamily ι) (p : κ) (i j : ι) :
    (W p).opposition i j ≤ totalOpposition W i j :=
  Finset.single_le_sum (fun k _ => (W k).opposition_nonneg i j) (Finset.mem_univ p)

omit [Fintype ι] in
theorem totalOpposition_nonneg (W : κ → OppositionFamily ι) (i j : ι) :
    0 ≤ totalOpposition W i j :=
  Finset.sum_nonneg (fun p _ => (W p).opposition_nonneg i j)

omit [Fintype ι] in
@[simp] theorem totalOpposition_diag (W : κ → OppositionFamily ι) (i : ι) :
    totalOpposition W i i = 0 := by
  simp [totalOpposition]

omit [Fintype ι] in
theorem totalOpposition_symm (W : κ → OppositionFamily ι) (i j : ι) :
    totalOpposition W i j = totalOpposition W j i := by
  unfold totalOpposition
  exact Finset.sum_congr rfl (fun p _ => (W p).opposition_symm i j)

omit [Fintype ι] in
theorem totalOpposition_eq (W : κ → OppositionFamily ι) (i j : ι) :
    totalOpposition W i j = (totalUnsigned W i j - totalSigned W i j) / 2 := by
  unfold totalOpposition totalUnsigned totalSigned
  simp_rw [OppositionFamily.opposition_eq]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]

theorem quad_totalOpposition (W : κ → OppositionFamily ι) (q : ι → ℝ) :
    quad (totalOpposition W) q =
      (quad (totalUnsigned W) q - quad (totalSigned W) q) / 2 := by
  unfold quad
  simp_rw [totalOpposition_eq, ← mul_div_assoc, ← Finset.sum_div, mul_sub,
    Finset.sum_sub_distrib]

omit [Fintype ι] in
@[simp] theorem totalSigned_diag (W : κ → OppositionFamily ι) (i : ι) :
    totalSigned W i i = totalUnsigned W i i := by
  simp [totalSigned, totalUnsigned]

omit [Fintype ι] in
theorem totalUnsigned_diag_le (W : κ → OppositionFamily ι) (L : ℝ)
    (hL : ∀ i j, totalOpposition W i j ≤ L) (i : ι) :
    totalUnsigned W i i ≤ (Fintype.card κ : ℝ) * L := by
  calc
    _ ≤ ∑ _p : κ, L := by
      apply Finset.sum_le_sum
      intro p hp
      exact (W p).unsigned_diag_le L
        (fun a b => (opposition_le_totalOpposition W p a b).trans (hL a b)) i
    _ = _ := by simp

theorem quad_unsigned_le_totalUnsigned (W : κ → OppositionFamily ι) (p : κ) (q : ι → ℝ) :
    quad (W p).unsigned q ≤ quad (totalUnsigned W) q := by
  unfold totalUnsigned
  rw [quad_sum]
  exact Finset.single_le_sum (fun k _ => (W k).unsigned_psd q) (Finset.mem_univ p)

/-- The energy estimate only needs the weak Z-matrix hypothesis. No positivity
hypothesis on `L` is required beyond its being a uniform opposition bound. -/
theorem unsigned_energy_bound_of_nonpos (W : κ → OppositionFamily ι)
    (hV : ∀ i j, i ≠ j → totalSigned W i j ≤ 0)
    (hCND : CND (totalOpposition W)) (L : ℝ)
    (hL : ∀ i j, totalOpposition W i j ≤ L) (p : κ) (q : ι → ℝ)
    (hq : ∑ i, q i = 0) :
    quad (W p).unsigned q ≤
      2 * (Fintype.card κ : ℝ) * L * (∑ i, q i ^ 2) := by
  have hUV : quad (totalUnsigned W) q ≤ quad (totalSigned W) q := by
    have hc := hCND q hq
    rw [quad_totalOpposition] at hc
    linarith
  calc
    _ ≤ quad (totalUnsigned W) q := quad_unsigned_le_totalUnsigned W p q
    _ ≤ quad (totalSigned W) q := hUV
    _ ≤ 2 * ∑ i, q i ^ 2 * totalSigned W i i :=
      z_matrix_quad_le (totalSigned W) (totalSigned_psd W) hV q
    _ ≤ 2 * ∑ i, q i ^ 2 * ((Fintype.card κ : ℝ) * L) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro i hi
      rw [totalSigned_diag]
      exact mul_le_mul_of_nonneg_left (totalUnsigned_diag_le W L hL i) (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The unsigned energy estimate under the strict off-diagonal LCM hypothesis. -/
theorem unsigned_energy_bound (W : κ → OppositionFamily ι)
    (hV : ∀ i j, i ≠ j → totalSigned W i j < 0)
    (hCND : CND (totalOpposition W)) (L : ℝ)
    (hL : ∀ i j, totalOpposition W i j ≤ L) (p : κ) (q : ι → ℝ)
    (hq : ∑ i, q i = 0) :
    quad (W p).unsigned q ≤
      2 * (Fintype.card κ : ℝ) * L * (∑ i, q i ^ 2) :=
  unsigned_energy_bound_of_nonpos W (fun i j hij => (hV i j hij).le) hCND L hL p q hq

omit [Fintype ι] in
/-- A negative total signed entry strictly dominates every individual agreement
entry by the total opposition entry. -/
theorem agreement_lt_totalOpposition (W : κ → OppositionFamily ι) (p : κ) (i j : ι)
    (hV : totalSigned W i j < 0) :
    (W p).agreement i j < totalOpposition W i j := by
  have hsum : (∑ k, (W k).agreement i j) < totalOpposition W i j := by
    unfold totalSigned at hV
    simp_rw [OppositionFamily.signed_eq, Finset.sum_sub_distrib] at hV
    exact sub_neg.mp hV
  exact (Finset.single_le_sum (fun k _ => (W k).agreement_nonneg i j)
    (Finset.mem_univ p)).trans_lt hsum

omit [Fintype ι] in
/-- For a fixed point and family, a set of opposition diameter at most `δ`
contains at most one point whose opposition to the fixed point exceeds `δ`. -/
theorem large_opposition_card_le_one (W : κ → OppositionFamily ι)
    (hV : ∀ i j, i ≠ j → totalSigned W i j < 0) (T : Finset ι) (δ : ℝ)
    (hT : ∀ i ∈ T, ∀ j ∈ T, totalOpposition W i j ≤ δ) (x : ι) (p : κ) :
    (T.filter (fun y => δ < (W p).opposition x y)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hiT, hi⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjT, hj⟩ := Finset.mem_filter.mp hj
  by_contra hij
  have hmin : δ < min ((W p).opposition x i) ((W p).opposition x j) := lt_min hi hj
  have hlocal := (W p).opposition_min_le_agreement x i j
  have hglobal := agreement_lt_totalOpposition W p i j (hV i j hij)
  have hbound := hT i hiT j hjT
  linarith

omit [Fintype ι] in
/-- Avoiding the at most `2 * card κ` exceptional points gives a point good
simultaneously for the two prescribed points in every family. -/
theorem exists_good_intermediate (W : κ → OppositionFamily ι)
    (hV : ∀ i j, i ≠ j → totalSigned W i j < 0) (T : Finset ι) (δ : ℝ)
    (hT : ∀ i ∈ T, ∀ j ∈ T, totalOpposition W i j ≤ δ)
    (hcard : 2 * Fintype.card κ < T.card) (a b : ι) :
    ∃ y ∈ T, (∀ p, (W p).opposition a y ≤ δ) ∧
      (∀ p, (W p).opposition b y ≤ δ) := by
  classical
  let bad (x : ι) : Finset ι :=
    Finset.univ.biUnion (fun p : κ => T.filter (fun y => δ < (W p).opposition x y))
  have hbad (x : ι) : (bad x).card ≤ Fintype.card κ := by
    calc
      _ ≤ ∑ p : κ, (T.filter (fun y => δ < (W p).opposition x y)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _p : κ, 1 := Finset.sum_le_sum
        (fun p _ => large_opposition_card_le_one W hV T δ hT x p)
      _ = _ := by simp
  have hbadab : (bad a ∪ bad b).card ≤ 2 * Fintype.card κ := by
    have hu := Finset.card_union_le (bad a) (bad b)
    have ha := hbad a
    have hb := hbad b
    omega
  obtain ⟨y, hyT, hybad⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (hbadab.trans_lt hcard)
  have hgood (x : ι) (hx : y ∉ bad x) (p : κ) : (W p).opposition x y ≤ δ := by
    by_contra h
    apply hx
    exact Finset.mem_biUnion.mpr
      ⟨p, Finset.mem_univ p, Finset.mem_filter.mpr ⟨hyT, lt_of_not_ge h⟩⟩
  refine ⟨y, hyT, hgood a ?_, hgood b ?_⟩
  · exact fun h => hybad (Finset.mem_union_left _ h)
  · exact fun h => hybad (Finset.mem_union_right _ h)

/-- A small diameter on more than `2 * card κ` points controls the global
opposition diameter. This proof uses only exceptional-point counting and the
three-point CND test. A separate nonnegativity assumption on `δ` is unnecessary. -/
theorem totalOpposition_diameter_bound (W : κ → OppositionFamily ι)
    (hV : ∀ i j, i ≠ j → totalSigned W i j < 0)
    (hCND : CND (totalOpposition W)) (T : Finset ι) (δ : ℝ)
    (hT : ∀ i ∈ T, ∀ j ∈ T, totalOpposition W i j ≤ δ)
    (hcard : 2 * Fintype.card κ < T.card) (a b : ι) :
    totalOpposition W a b ≤ 4 * (Fintype.card κ : ℝ) * δ := by
  obtain ⟨y, _hyT, hay, hby⟩ := exists_good_intermediate W hV T δ hT hcard a b
  have hsum (x : ι) (hx : ∀ p, (W p).opposition x y ≤ δ) :
      totalOpposition W x y ≤ (Fintype.card κ : ℝ) * δ := by
    calc
      _ ≤ ∑ _p : κ, δ := Finset.sum_le_sum (fun p _ => hx p)
      _ = _ := by simp
  have ha := hsum a hay
  have hb := hsum b hby
  have htri := cnd_triangle (totalOpposition W) hCND
    (totalOpposition_symm W) (totalOpposition_diag W) a b y
  linarith

/-- Version convenient for bounds obtained only on distinct pairs in `T`. -/
theorem totalOpposition_diameter_bound_of_offDiag (W : κ → OppositionFamily ι)
    (hV : ∀ i j, i ≠ j → totalSigned W i j < 0)
    (hCND : CND (totalOpposition W)) (T : Finset ι) (δ : ℝ) (hδ : 0 ≤ δ)
    (hT : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → totalOpposition W i j ≤ δ)
    (hcard : 2 * Fintype.card κ < T.card) (a b : ι) :
    totalOpposition W a b ≤ 4 * (Fintype.card κ : ℝ) * δ := by
  apply totalOpposition_diameter_bound W hV hCND T δ _ hcard a b
  intro i hi j hj
  by_cases hij : i = j
  · subst j
    simpa using hδ
  · exact hT i hi j hj hij

end
end E126
