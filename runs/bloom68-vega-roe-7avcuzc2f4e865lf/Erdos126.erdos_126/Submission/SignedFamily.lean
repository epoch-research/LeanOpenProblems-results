import FormalConjecturesUtil

/-!
# A signed laminar-family cardinal bound

Scalar quadratic forms, a two-copy Hall matching, and the two budgets for the
signed-family kernel occurring in the `n ≤ 3 r²` bound.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Erdos126Kernel

/-- The scalar quadratic form of a finite real kernel. -/
def qform {V : Type*} [Fintype V] (M : V → V → ℝ) (z : V → ℝ) : ℝ :=
  ∑ i, ∑ j, z i * z j * M i j

/-- Conditional negative semidefiniteness on vectors whose coordinates sum to zero. -/
def CND {V : Type*} [Fintype V] (M : V → V → ℝ) : Prop :=
  ∀ z : V → ℝ, (∑ i, z i) = 0 → qform M z ≤ 0

/-- The weighted co-membership kernel of a finite family of supports. -/
def familyKernel {V : Type*} [Fintype V] {J : Type*}
    (F : Finset J) (U : J → Finset V) (w : J → ℝ) (i j : V) : ℝ := by
  classical
  exact ∑ t ∈ F, if i ∈ U t ∧ j ∈ U t then w t else 0

/-- The contribution from pairs of opposite signs. -/
def crossKernel {V P : Type*} [Fintype P]
    (M : P → V → V → ℝ) (σ : P → V → Bool) (i j : V) : ℝ :=
  ∑ p, if σ p i = σ p j then 0 else M p i j

/-- The contribution from pairs of equal signs. -/
def sameKernel {V P : Type*} [Fintype P]
    (M : P → V → V → ℝ) (σ : P → V → Bool) (i j : V) : ℝ :=
  ∑ p, if σ p i = σ p j then M p i j else 0

set_option maxHeartbeats 0

section Matching

variable {V : Type*} [Fintype V]

/-- A laminar family of sets, each containing its index and at least two points,
has distinct representatives in two copies of the punctured sets. -/
theorem laminar_two_copy_matching (A : V → Finset V)
    (hself : ∀ i, i ∈ A i) (hsize : ∀ i, 2 ≤ (A i).card)
    (hlam : ∀ i j, Disjoint (A i) (A j) ∨ A i ⊆ A j ∨ A j ⊆ A i) :
    ∃ H : V → V × Bool, Function.Injective H ∧
      ∀ i, (H i).1 ≠ i ∧ (H i).1 ∈ A i := by
  classical
  have hne (i : V) : ((A i).erase i).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (hself i)]
    have := hsize i
    omega
  choose g hg using hne
  have hall (s : Finset V) :
      s.card ≤ (s.biUnion (fun i => (A i).erase i ×ˢ (univ : Finset Bool))).card := by
    let N := s.biUnion (fun i => (A i).erase i)
    let B := s \ N
    have hB (i : V) (hi : i ∈ B) : i ∈ s ∧ i ∉ N := mem_sdiff.mp hi
    have hdisj (i j : V) (hi : i ∈ B) (hj : j ∈ B) (hne : i ≠ j) :
        Disjoint (A i) (A j) := by
      rcases hlam i j with hd | hij | hji
      · exact hd
      · exfalso
        apply (hB i hi).2
        exact mem_biUnion.mpr ⟨j, (hB j hj).1, mem_erase.mpr ⟨hne, hij (hself i)⟩⟩
      · exfalso
        apply (hB j hj).2
        exact mem_biUnion.mpr ⟨i, (hB i hi).1, mem_erase.mpr ⟨hne.symm, hji (hself j)⟩⟩
    have hBN : B.card ≤ N.card := by
      apply Finset.card_le_card_of_injOn g
      · intro i hi
        exact mem_biUnion.mpr ⟨i, (hB i hi).1, hg i⟩
      · intro i hi j hj hij
        by_contra hne
        have hd := Finset.disjoint_left.mp (hdisj i j hi hj hne)
        exact hd (mem_of_mem_erase (hg i)) (hij ▸ mem_of_mem_erase (hg j))
    have hs : s.card ≤ 2 * N.card := by
      have hcard := Finset.card_sdiff_add_card_inter s N
      have hinter : (s ∩ N).card ≤ N.card := card_le_card inter_subset_right
      dsimp [B] at hBN
      omega
    have hprod : s.biUnion (fun i => (A i).erase i ×ˢ (univ : Finset Bool)) =
        N ×ˢ (univ : Finset Bool) := by
      ext x
      simp [N]
    rw [hprod, card_product]
    simpa [Nat.mul_comm] using hs
  obtain ⟨H, hH, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (fun i => (A i).erase i ×ˢ (univ : Finset Bool))).mp hall
  exact ⟨H, hH, fun i => mem_erase.mp (mem_product.mp (hmem i)).1⟩

/-- A smallest support through a point lies in every support through that point.
If no support contains the point, the whole vertex set is used. -/
theorem exists_minimal_support {J : Type*} (F : Finset J) (U : J → Finset V)
    (hn : 2 ≤ Fintype.card V)
    (hsize : ∀ t ∈ F, 2 ≤ (U t).card)
    (hlam : ∀ t ∈ F, ∀ u ∈ F,
      Disjoint (U t) (U u) ∨ U t ⊆ U u ∨ U u ⊆ U t) (i : V) :
    ∃ A : Finset V, i ∈ A ∧ 2 ≤ A.card ∧
      (A = univ ∨ ∃ t ∈ F, A = U t) ∧
      ∀ t ∈ F, i ∈ U t → A ⊆ U t := by
  classical
  let G := F.filter (fun t => i ∈ U t)
  by_cases hG : G.Nonempty
  · obtain ⟨t, ht, hmin⟩ := G.exists_min_image (fun t => (U t).card) hG
    have htF : t ∈ F := (mem_filter.mp ht).1
    have hit : i ∈ U t := (mem_filter.mp ht).2
    refine ⟨U t, hit, hsize t htF, Or.inr ⟨t, htF, rfl⟩, ?_⟩
    intro u hu hiu
    rcases hlam t htF u hu with hd | htu | hut
    · exact False.elim (Finset.disjoint_left.mp hd hit hiu)
    · exact htu
    · have hcard := hmin u (mem_filter.mpr ⟨hu, hiu⟩)
      exact le_of_eq (Finset.eq_of_subset_of_card_le hut hcard).symm
  · refine ⟨univ, mem_univ i, by simpa using hn, Or.inl rfl, ?_⟩
    intro t ht hit
    exact False.elim (hG ⟨t, mem_filter.mpr ⟨ht, hit⟩⟩)

/-- Laminar weighted kernels have a two-copy matching along which each diagonal
entry is preserved. No finiteness assumption on the label type is required. -/
theorem familyKernel_matching {J : Type*} (F : Finset J)
    (U : J → Finset V) (w : J → ℝ) (hn : 2 ≤ Fintype.card V)
    (hsize : ∀ t ∈ F, 2 ≤ (U t).card)
    (hlam : ∀ t ∈ F, ∀ u ∈ F,
      Disjoint (U t) (U u) ∨ U t ⊆ U u ∨ U u ⊆ U t) :
    ∃ H : V → V × Bool, Function.Injective H ∧
      ∀ i, (H i).1 ≠ i ∧
        familyKernel F U w i (H i).1 = familyKernel F U w i i := by
  classical
  choose A hself hcard horigin hsub using
    (exists_minimal_support F U hn hsize hlam)
  have hAlam (i j : V) : Disjoint (A i) (A j) ∨ A i ⊆ A j ∨ A j ⊆ A i := by
    rcases horigin i with hi | ⟨t, ht, hi⟩
    · exact Or.inr (Or.inr (hi ▸ subset_univ _))
    rcases horigin j with hj | ⟨u, hu, hj⟩
    · exact Or.inr (Or.inl (hj ▸ subset_univ _))
    rw [hi, hj]
    exact hlam t ht u hu
  obtain ⟨H, hH, hmem⟩ := laminar_two_copy_matching A hself hcard hAlam
  refine ⟨H, hH, fun i => ⟨(hmem i).1, ?_⟩⟩
  unfold familyKernel
  apply sum_congr rfl
  intro t ht
  by_cases hit : i ∈ U t
  · have hjt := hsub i t ht hit (hmem i).2
    simp [hit, hjt]
  · simp [hit]

end Matching

section Geometry

variable {V : Type*} [Fintype V]

/-- A coordinate unit vector, with no decidable-equality assumption in the API. -/
def unitVector (i k : V) : ℝ := by
  classical
  exact if k = i then 1 else 0

@[simp] theorem sum_unitVector (i : V) : (∑ k, unitVector i k) = 1 := by
  classical
  simp [unitVector]

@[simp] theorem sum_unitVector_mul (i : V) (f : V → ℝ) :
    (∑ k, unitVector i k * f k) = f i := by
  classical
  simp [unitVector, ite_mul]

@[simp] theorem qform_unitVector (C : V → V → ℝ) (i : V) :
    qform C (unitVector i) = C i i := by
  classical
  simp [qform, unitVector, ite_mul, mul_ite]

theorem qform_unitVector_add (C : V → V → ℝ) (i j : V) :
    qform C (fun k => unitVector i k + unitVector j k) =
      C i i + C i j + C j i + C j j := by
  classical
  simp [qform, unitVector, add_mul, mul_add, ite_mul, mul_ite, sum_add_distrib]
  ring

/-- Expanding an affine test vector using symmetry, entirely in scalar sums. -/
theorem qform_affine (C : V → V → ℝ) (hsymm : ∀ i j, C i j = C j i)
    (x : V → ℝ) (a b : ℝ) :
    qform C (fun i => a * x i - b) =
      a ^ 2 * qform C x - 2 * a * b * (∑ i, x i * ∑ j, C i j) +
        b ^ 2 * (∑ i, ∑ j, C i j) := by
  have hcol : (∑ i, ∑ j, x j * C i j) = ∑ i, x i * ∑ j, C i j := by
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [hsymm i j]
  unfold qform
  calc
    (∑ i, ∑ j, (a * x i - b) * (a * x j - b) * C i j) =
        ∑ i, ∑ j, (a ^ 2 * (x i * x j * C i j) -
          a * b * (x i * C i j) - a * b * (x j * C i j) + b ^ 2 * C i j) := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
      rw [hcol]
      ring

/-- The elementary CND geometry estimates from the one-point and two-point tests. -/
theorem cnd_geometry (C : V → V → ℝ) (hcnd : CND C)
    (hsymm : ∀ i j, C i j = C j i) (hdiag : ∀ i, C i i = 0) :
    ∃ h : V → ℝ, (∀ i, 0 ≤ h i) ∧
      (∀ i j, (Fintype.card V : ℝ) ^ 2 * C i j ≤ h i + h j) ∧
      (∑ i, h i) = (Fintype.card V : ℝ) * (∑ i, ∑ j, C i j) := by
  let n : ℝ := Fintype.card V
  let S := ∑ i, ∑ j, C i j
  let h := fun i => 2 * n * (∑ j, C i j) - S
  refine ⟨h, ?_, ?_, ?_⟩
  · intro i
    have hz : (∑ k, (n * unitVector i k - 1)) = 0 := by
      simp [sum_sub_distrib, ← mul_sum, n]
    have ht := hcnd _ hz
    rw [qform_affine C hsymm, qform_unitVector, hdiag, sum_unitVector_mul] at ht
    dsimp [h, S]
    nlinarith
  · intro i j
    have hz : (∑ k, (n * (unitVector i k + unitVector j k) - 2)) = 0 := by
      simp [sum_sub_distrib, ← mul_sum, sum_add_distrib, n]
      ring
    have ht := hcnd _ hz
    have hrow : (∑ k, (unitVector i k + unitVector j k) * (∑ l, C k l)) =
        (∑ l, C i l) + (∑ l, C j l) := by
      simp [add_mul, sum_add_distrib]
    rw [qform_affine C hsymm, qform_unitVector_add, hdiag, hdiag, hrow,
      hsymm j i] at ht
    change n ^ 2 * C i j ≤ (2 * n * (∑ k, C i k) - S) +
      (2 * n * (∑ k, C j k) - S)
    dsimp [S]
    nlinarith
  · dsimp [h]
    simp only [sum_sub_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
    dsimp [n, S]
    ring

/-- An injection into two copies charges each nonnegative weight at most twice. -/
theorem sum_fst_le_two_sum (h : V → ℝ) (h0 : ∀ i, 0 ≤ h i)
    (H : V → V × Bool) (hH : Function.Injective H) :
    (∑ i, h (H i).1) ≤ 2 * ∑ i, h i := by
  classical
  calc
    (∑ i, h (H i).1) = ∑ x ∈ univ.image H, h x.1 :=
      (sum_image (s := univ) (f := fun x : V × Bool => h x.1)
        (fun i _ j _ hij => hH hij)).symm
    _ ≤ ∑ x : V × Bool, h x.1 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ => h0 x.1)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [← mul_sum, ← two_mul]

/-- The second budget for a diagonal dominated along a two-copy matching. -/
theorem cnd_matching_budget (C : V → V → ℝ) (hcnd : CND C)
    (hsymm : ∀ i j, C i j = C j i) (hdiag : ∀ i, C i i = 0)
    (hn : 0 < Fintype.card V) (D : V → ℝ)
    (H : V → V × Bool) (hH : Function.Injective H)
    (hD : ∀ i, D i ≤ C i (H i).1) :
    (Fintype.card V : ℝ) * (∑ i, D i) ≤ 3 * (∑ i, ∑ j, C i j) := by
  obtain ⟨h, h0, hpairs, hsum⟩ := cnd_geometry C hcnd hsymm hdiag
  have hbound : (Fintype.card V : ℝ) ^ 2 * (∑ i, D i) ≤ 3 * ∑ i, h i := by
    calc
      _ = ∑ i, (Fintype.card V : ℝ) ^ 2 * D i := mul_sum _ _ _
      _ ≤ ∑ i, (h i + h (H i).1) := by
        apply sum_le_sum
        intro i _
        exact (mul_le_mul_of_nonneg_left (hD i) (sq_nonneg _)).trans (hpairs i (H i).1)
      _ = (∑ i, h i) + (∑ i, h (H i).1) := sum_add_distrib
      _ ≤ 3 * ∑ i, h i := by
        have := sum_fst_le_two_sum h h0 H hH
        linarith
  rw [hsum] at hbound
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  apply le_of_mul_le_mul_left (a := (Fintype.card V : ℝ)) _ hnR
  nlinarith [hbound]

end Geometry

section SignedKernels

variable {V : Type*} [Fintype V]

@[simp] theorem qform_one (M : V → V → ℝ) :
    qform M (fun _ => 1) = ∑ i, ∑ j, M i j := by
  simp [qform]

/-- Quadratic forms commute with a finite sum of kernels. -/
theorem qform_sum {J : Type*} (F : Finset J) (M : J → V → V → ℝ) (z : V → ℝ) :
    qform (fun i j => ∑ t ∈ F, M t i j) z = ∑ t ∈ F, qform (M t) z := by
  unfold qform
  simp only [mul_sum]
  calc
    (∑ i, ∑ j, ∑ t ∈ F, z i * z j * M t i j) =
        ∑ i, ∑ t ∈ F, ∑ j, z i * z j * M t i j := by
      apply sum_congr rfl
      intro i _
      exact sum_comm
    _ = _ := sum_comm

/-- A weighted family kernel is a sum of rank-one Gram kernels. -/
theorem qform_familyKernel {J : Type*} (F : Finset J) (U : J → Finset V)
    (w : J → ℝ) (z : V → ℝ) :
    qform (familyKernel F U w) z = ∑ t ∈ F, w t * (∑ i ∈ U t, z i) ^ 2 := by
  classical
  unfold familyKernel
  rw [qform_sum]
  apply sum_congr rfl
  intro t _
  calc
    qform (fun i j => if i ∈ U t ∧ j ∈ U t then w t else 0) z =
        ∑ i, ∑ j, (if i ∈ U t then z i else 0) *
          (if j ∈ U t then z j else 0) * w t := by
      unfold qform
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      by_cases hi : i ∈ U t <;> by_cases hj : j ∈ U t <;> simp [hi, hj]
    _ = w t * (∑ i ∈ U t, z i) ^ 2 := by
      simp only [← sum_mul, ← mul_sum, sum_ite_mem, univ_inter]
      ring

theorem familyKernel_nonneg {J : Type*} (F : Finset J) (U : J → Finset V)
    (w : J → ℝ) (hw : ∀ t ∈ F, 0 ≤ w t) (i j : V) :
    0 ≤ familyKernel F U w i j := by
  classical
  unfold familyKernel
  apply sum_nonneg
  intro t ht
  split_ifs
  · exact hw t ht
  · exact le_rfl

theorem familyKernel_symm {J : Type*} (F : Finset J) (U : J → Finset V)
    (w : J → ℝ) (i j : V) :
    familyKernel F U w i j = familyKernel F U w j i := by
  classical
  simp only [familyKernel, and_comm]

theorem familyKernel_psd {J : Type*} (F : Finset J) (U : J → Finset V)
    (w : J → ℝ) (hw : ∀ t ∈ F, 0 ≤ w t) (z : V → ℝ) :
    0 ≤ qform (familyKernel F U w) z := by
  rw [qform_familyKernel]
  exact sum_nonneg (fun t ht => mul_nonneg (hw t ht) (sq_nonneg _))

/-- The real sign associated with a Boolean. -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem boolSign_mul_self (b : Bool) : boolSign b * boolSign b = 1 := by
  cases b <;> norm_num [boolSign]

theorem boolSign_cases (b : Bool) : boolSign b = 1 ∨ boolSign b = -1 := by
  cases b <;> simp [boolSign]

theorem boolSign_mul (a b : Bool) :
    boolSign a * boolSign b = if a = b then 1 else -1 := by
  cases a <;> cases b <;> norm_num [boolSign]

/-- Twisting a kernel by signs is the same as twisting its test vector. -/
theorem qform_twist (M : V → V → ℝ) (s z : V → ℝ) :
    qform (fun i j => s i * s j * M i j) z = qform M (fun i => s i * z i) := by
  unfold qform
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

variable {P : Type*} [Fintype P]

/-- The sum of the signed Gram kernels. -/
def signedKernel (M : P → V → V → ℝ) (σ : P → V → Bool) (i j : V) : ℝ :=
  ∑ p, boolSign (σ p i) * boolSign (σ p j) * M p i j

section VertexIndependent

omit [Fintype V]

@[simp] theorem signedKernel_diag (M : P → V → V → ℝ) (σ : P → V → Bool) (i : V) :
    signedKernel M σ i i = ∑ p, M p i i := by
  simp [signedKernel]

theorem signedKernel_eq (M : P → V → V → ℝ) (σ : P → V → Bool) (i j : V) :
    signedKernel M σ i j = sameKernel M σ i j - crossKernel M σ i j := by
  unfold signedKernel sameKernel crossKernel
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  rw [boolSign_mul]
  by_cases h : σ p i = σ p j <;> simp [h]

theorem kernel_mass_split (M : P → V → V → ℝ) (σ : P → V → Bool) (i j : V) :
    (∑ p, M p i j) = 2 * crossKernel M σ i j + signedKernel M σ i j := by
  unfold crossKernel signedKernel
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  rw [boolSign_mul]
  by_cases h : σ p i = σ p j <;> simp [h]
  ring

theorem crossKernel_nonneg (M : P → V → V → ℝ) (σ : P → V → Bool)
    (hM : ∀ p i j, 0 ≤ M p i j) (i j : V) : 0 ≤ crossKernel M σ i j := by
  unfold crossKernel
  apply sum_nonneg
  intro p _
  split_ifs
  · exact le_rfl
  · exact hM p i j

theorem sameKernel_nonneg (M : P → V → V → ℝ) (σ : P → V → Bool)
    (hM : ∀ p i j, 0 ≤ M p i j) (i j : V) : 0 ≤ sameKernel M σ i j := by
  unfold sameKernel
  apply sum_nonneg
  intro p _
  split_ifs
  · exact hM p i j
  · exact le_rfl

@[simp] theorem crossKernel_diag (M : P → V → V → ℝ) (σ : P → V → Bool) (i : V) :
    crossKernel M σ i i = 0 := by
  simp [crossKernel]

theorem crossKernel_symm (M : P → V → V → ℝ) (σ : P → V → Bool)
    (hM : ∀ p i j, M p i j = M p j i) (i j : V) :
    crossKernel M σ i j = crossKernel M σ j i := by
  unfold crossKernel
  apply sum_congr rfl
  intro p _
  rw [hM p i j]
  by_cases h : σ p i = σ p j
  · simp only [h, if_true]
  · simp only [if_neg h, if_neg (Ne.symm h)]

/-- Every off-diagonal family entry is bounded by the cross kernel, using the
strict separation for pairs whose signs agree. -/
theorem kernel_le_cross_offdiag (M : P → V → V → ℝ) (σ : P → V → Bool)
    (hM : ∀ p i j, 0 ≤ M p i j)
    (hstrict : ∀ i j, i ≠ j → sameKernel M σ i j < crossKernel M σ i j)
    (p : P) (i j : V) (hij : i ≠ j) : M p i j ≤ crossKernel M σ i j := by
  by_cases h : σ p i = σ p j
  · have hs : M p i j ≤ sameKernel M σ i j := by
      have hs := single_le_sum (s := univ)
        (f := fun q => if σ q i = σ q j then M q i j else 0)
        (fun q _ => by dsimp only; split_ifs; exact hM q i j; exact le_rfl) (mem_univ p)
      simpa only [if_pos h] using hs
    exact hs.trans (hstrict i j hij).le
  · have hs := single_le_sum (s := univ)
      (f := fun q => if σ q i = σ q j then 0 else M q i j)
      (fun q _ => by dsimp only; split_ifs; exact le_rfl; exact hM q i j) (mem_univ p)
    simpa only [if_neg h] using hs

end VertexIndependent

/-- Strict separation and at least two vertices make the total cross mass positive. -/
theorem crossKernel_total_pos (M : P → V → V → ℝ) (σ : P → V → Bool)
    (hM : ∀ p i j, 0 ≤ M p i j) (hn : 2 ≤ Fintype.card V)
    (hstrict : ∀ i j, i ≠ j → sameKernel M σ i j < crossKernel M σ i j) :
    0 < ∑ i, ∑ j, crossKernel M σ i j := by
  obtain ⟨i, j, hij⟩ := Fintype.one_lt_card_iff.mp (show 1 < Fintype.card V by omega)
  have hpos : 0 < crossKernel M σ i j :=
    (sameKernel_nonneg M σ hM i j).trans_lt (hstrict i j hij)
  apply sum_pos' (fun k _ => sum_nonneg (fun l _ => crossKernel_nonneg M σ hM k l))
  exact ⟨i, mem_univ i, sum_pos' (fun l _ => crossKernel_nonneg M σ hM i l)
    ⟨j, mem_univ j, hpos⟩⟩

end SignedKernels

section Budgets

variable {V : Type*} [Fintype V]

/-- For a kernel with nonpositive off-diagonal entries, every sign vector costs
at most twice the trace, minus the all-ones quadratic form. -/
theorem qform_sign_bound (Q : V → V → ℝ)
    (hneg : ∀ i j, i ≠ j → Q i j ≤ 0) (s : V → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) :
    qform Q s + qform Q (fun _ => 1) ≤ 2 * ∑ i, Q i i := by
  classical
  calc
    _ = ∑ i, ∑ j, (s i * s j + 1) * Q i j := by
      simp only [qform, add_mul, one_mul, sum_add_distrib]
    _ ≤ ∑ i, ∑ j, if i = j then 2 * Q i i else 0 := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      by_cases hij : i = j
      · subst j
        rcases hs i with hi | hi <;> norm_num [hi]
      · rw [if_neg hij]
        have hn : 0 ≤ s i * s j + 1 := by
          rcases hs i with hi | hi <;> rcases hs j with hj | hj <;> norm_num [hi, hj]
        exact mul_nonpos_of_nonneg_of_nonpos hn (hneg i j hij)
    _ = _ := by simp [← mul_sum]

variable {P : Type*} [Fintype P]

/-- The signed-Gram budget `S ≤ r T`. -/
theorem signed_budget (M : P → V → V → ℝ) (σ : P → V → Bool)
    (hpsd : ∀ p z, 0 ≤ qform (M p) z)
    (hstrict : ∀ i j, i ≠ j → sameKernel M σ i j < crossKernel M σ i j) :
    (∑ i, ∑ j, crossKernel M σ i j) ≤
      (Fintype.card P : ℝ) * (∑ p, ∑ i, M p i i) := by
  let Qp := fun p i j => boolSign (σ p i) * boolSign (σ p j) * M p i j
  let Q := signedKernel M σ
  let T := ∑ p, ∑ i, M p i i
  let S := ∑ i, ∑ j, crossKernel M σ i j
  let mass := fun p => ∑ i, ∑ j, M p i j
  let r : ℝ := Fintype.card P
  have hQp (p : P) (z : V → ℝ) : 0 ≤ qform (Qp p) z := by
    dsimp [Qp]
    rw [qform_twist]
    exact hpsd p _
  have hQsum (z : V → ℝ) : qform Q z = ∑ p, qform (Qp p) z := by
    exact qform_sum univ Qp z
  have hQ (z : V → ℝ) : 0 ≤ qform Q z := by
    rw [hQsum]
    exact sum_nonneg (fun p _ => hQp p z)
  have htrace : (∑ i, Q i i) = T := by
    dsimp [Q, T]
    simp only [signedKernel_diag]
    exact sum_comm
  have hneg (i j : V) (hij : i ≠ j) : Q i j ≤ 0 := by
    dsimp [Q]
    rw [signedKernel_eq]
    linarith [hstrict i j hij]
  have hmass (p : P) : mass p ≤ 2 * T := by
    let sp := fun i => boolSign (σ p i)
    have heval : qform (Qp p) sp = mass p := by
      dsimp [Qp, sp]
      rw [qform_twist]
      simp only [boolSign_mul_self, qform_one]
      rfl
    have hle : qform (Qp p) sp ≤ qform Q sp := by
      rw [hQsum]
      exact single_le_sum (fun q _ => hQp q sp) (mem_univ p)
    have hb := qform_sign_bound Q hneg sp (fun i => boolSign_cases (σ p i))
    rw [htrace] at hb
    have hb0 := hQ (fun _ => 1)
    linarith
  have hmass_total : (∑ p, mass p) ≤ 2 * r * T := by
    calc
      _ ≤ ∑ _p : P, 2 * T := sum_le_sum (fun p _ => hmass p)
      _ = _ := by simp [r]; ring
  have hsplit : (∑ p, mass p) = 2 * S + qform Q (fun _ => 1) := by
    calc
      (∑ p, mass p) = ∑ i, ∑ j, ∑ p, M p i j := by
        dsimp [mass]
        rw [sum_comm]
        apply sum_congr rfl
        intro i _
        exact sum_comm
      _ = 2 * S + ∑ i, ∑ j, Q i j := by
        simp_rw [kernel_mass_split M σ]
        simp only [sum_add_distrib, ← mul_sum]
        rfl
      _ = _ := by rw [qform_one]
  have hb0 := hQ (fun _ => 1)
  change S ≤ r * T
  linarith

end Budgets

/-- **Signed laminar-family cardinal bound.**

The labels `J` need not form a finite type, and different labels may have equal
supports. For each `p`, the weights are nonnegative, every support has at least
two vertices, and the supports are laminar. Conditional negative definiteness
of the cross kernel and strict off-diagonal separation imply `|V| ≤ 3 |P|²`.
-/
theorem signed_family_card_bound
    {V P J : Type*} [Fintype V] [Fintype P]
    (F : P → Finset J) (U : P → J → Finset V) (w : P → J → ℝ)
    (σ : P → V → Bool)
    (hn : 2 ≤ Fintype.card V)
    (hw : ∀ p t, t ∈ F p → 0 ≤ w p t)
    (hsize : ∀ p t, t ∈ F p → 2 ≤ (U p t).card)
    (hlam : ∀ p t, t ∈ F p → ∀ u, u ∈ F p →
      Disjoint (U p t) (U p u) ∨ U p t ⊆ U p u ∨ U p u ⊆ U p t)
    (hcnd : CND (crossKernel (fun p => familyKernel (F p) (U p) (w p)) σ))
    (hstrict : ∀ i j, i ≠ j →
      sameKernel (fun p => familyKernel (F p) (U p) (w p)) σ i j <
        crossKernel (fun p => familyKernel (F p) (U p) (w p)) σ i j) :
    (Fintype.card V : ℝ) ≤ 3 * (Fintype.card P : ℝ) ^ 2 := by
  let M := fun p => familyKernel (F p) (U p) (w p)
  let C := crossKernel M σ
  let S := ∑ i, ∑ j, C i j
  let T := ∑ p, ∑ i, M p i i
  let n : ℝ := Fintype.card V
  let r : ℝ := Fintype.card P
  have hM0 (p : P) (i j : V) : 0 ≤ M p i j :=
    familyKernel_nonneg (F p) (U p) (w p) (hw p) i j
  have hMpsd (p : P) (z : V → ℝ) : 0 ≤ qform (M p) z :=
    familyKernel_psd (F p) (U p) (w p) (hw p) z
  have hMsymm (p : P) (i j : V) : M p i j = M p j i :=
    familyKernel_symm (F p) (U p) (w p) i j
  have hCsymm : ∀ i j, C i j = C j i := crossKernel_symm M σ hMsymm
  have hCdiag : ∀ i, C i i = 0 := crossKernel_diag M σ
  have hnpos : 0 < Fintype.card V := by omega
  have hnR : 0 < n := by
    dsimp [n]
    exact_mod_cast hnpos
  have hrR : 0 ≤ r := Nat.cast_nonneg _
  have hS : 0 < S := crossKernel_total_pos M σ hM0 hn hstrict
  have hfirst : S ≤ r * T := signed_budget M σ hMpsd hstrict
  have hsecondp (p : P) : n * (∑ i, M p i i) ≤ 3 * S := by
    obtain ⟨H, hH, hmatch⟩ :=
      familyKernel_matching (F p) (U p) (w p) hn (hsize p) (hlam p)
    apply cnd_matching_budget C hcnd hCsymm hCdiag hnpos (fun i => M p i i) H hH
    intro i
    calc
      M p i i = M p i (H i).1 := (hmatch i).2.symm
      _ ≤ C i (H i).1 :=
        kernel_le_cross_offdiag M σ hM0 hstrict p i (H i).1 (hmatch i).1.symm
  have hsecond : n * T ≤ 3 * r * S := by
    calc
      _ = ∑ p, n * (∑ i, M p i i) := mul_sum _ _ _
      _ ≤ ∑ _p : P, 3 * S := sum_le_sum (fun p _ => hsecondp p)
      _ = _ := by simp [r]; ring
  have hfinal : n * S ≤ (3 * r ^ 2) * S := by
    calc
      n * S ≤ n * (r * T) := mul_le_mul_of_nonneg_left hfirst hnR.le
      _ = r * (n * T) := by ring
      _ ≤ r * (3 * r * S) := mul_le_mul_of_nonneg_left hsecond hrR
      _ = (3 * r ^ 2) * S := by ring
  exact le_of_mul_le_mul_right hfinal hS

end Erdos126Kernel
