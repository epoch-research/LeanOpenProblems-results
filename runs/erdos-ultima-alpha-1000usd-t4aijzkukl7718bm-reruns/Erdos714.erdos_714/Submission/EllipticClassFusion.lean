import FormalConjecturesUtil

/-!
A union of four elliptic trace--determinant classes in GL(2) already has a K44.
This is an obstruction to a construction family, not a resolution of Erdős 714.
-/

noncomputable section
open Finset SimpleGraph Classical
set_option maxHeartbeats 2000000

namespace Erdos714EllipticFusion

variable {F : Type*} [Field F] [Fintype F]

/-- A nonzero determinant and a characteristic polynomial with no field root. -/
def Elliptic (c : F × F) : Prop :=
  c.1 ≠ 0 ∧ ∀ x : F, x^2-c.2*x+c.1 ≠ 0

def Parameter (S : Finset (F × F)) := Σ c : S, {x : F // x ≠ 0 ∧ x ≠ c.val.2}

instance (S : Finset (F × F)) : Fintype (Parameter S) := by
  unfold Parameter
  infer_instance

abbrev Ratio := {k : F // k ≠ 0 ∧ k ≠ 1}

instance : Fintype (Ratio (F := F)) := by unfold Ratio; infer_instance

lemma card_excluding (t : F) :
    Fintype.card F - 2 ≤ Fintype.card {x : F // x ≠ 0 ∧ x ≠ t} := by
  rw [Fintype.card_subtype]
  have hs : univ.filter (fun x : F => x ≠ 0 ∧ x ≠ t) = univ \ {0,t} := by
    ext x
    simp
  rw [hs, card_sdiff_of_subset (subset_univ _), card_univ]
  have ht : ({0,t} : Finset F).card ≤ 2 := by
    simpa using card_insert_le (0 : F) {t}
  omega

lemma ratio_card : Fintype.card (Ratio (F := F)) = Fintype.card F - 2 := by
  change Fintype.card {k : F // k ≠ 0 ∧ k ≠ 1} = _
  rw [Fintype.card_subtype]
  have hs : univ.filter (fun k : F => k ≠ 0 ∧ k ≠ 1) = univ \ {0,1} := by
    ext k
    simp
  rw [hs, card_sdiff_of_subset (subset_univ _), card_univ, card_pair zero_ne_one]

lemma parameter_card (S : Finset (F × F)) :
    S.card * (Fintype.card F - 2) ≤ Fintype.card (Parameter S) := by
  change _ ≤ Fintype.card (Σ c : S, {x : F // x ≠ 0 ∧ x ≠ c.val.2})
  rw [Fintype.card_sigma]
  calc
    _ = ∑ _ : S, (Fintype.card F - 2) := by simp
    _ ≤ _ := sum_le_sum (fun c _ => card_excluding c.val.2)

def ratioMap (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (p : Parameter S) : Ratio (F := F) := by
  let d := p.1.val.1
  let t := p.1.val.2
  let x := p.2.val
  have hd : d ≠ 0 := (hS p.1.val p.1.property).1
  have hx : x ≠ 0 := p.2.property.1
  have hy : t - x ≠ 0 := sub_ne_zero.mpr p.2.property.2.symm
  refine ⟨x * (t-x) / d, div_ne_zero (mul_ne_zero hx hy) hd, ?_⟩
  intro hk
  have he : x * (t-x) = d := (div_eq_one_iff_eq hd).mp hk
  apply (hS p.1.val p.1.property).2 x
  change x^2-t*x+d = 0
  linear_combination -he

/-- Some nontrivial ratio has at least as many parameters as there are accepted classes. -/
theorem large_fiber (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (hq : 2 < Fintype.card F) :
    ∃ k : Ratio (F := F), S.card ≤ Fintype.card {p : Parameter S // ratioMap S hS p = k} := by
  haveI : Nonempty (Ratio (F := F)) := Fintype.card_pos_iff.mp (by rw [ratio_card]; omega)
  have hc : Fintype.card (Ratio (F := F)) * S.card ≤ Fintype.card (Parameter S) := by
    rw [ratio_card, mul_comm]
    exact parameter_card S
  obtain ⟨k,hk⟩ := Fintype.exists_le_card_fiber_of_mul_le_card (ratioMap S hS) hc
  exact ⟨k, by simpa only [Fintype.card_subtype] using hk⟩


/-- The genuine trace and determinant of an invertible matrix. -/
def invariants (g : Matrix.GeneralLinearGroup (Fin 2) F) : F × F :=
  ((g : Matrix (Fin 2) (Fin 2) F).det, (g : Matrix (Fin 2) (Fin 2) F).trace)

/-- The two-part Cayley relation on actual GL(2), with no inverse-closure assumption. -/
def graph (S : Finset (F × F)) :
    SimpleGraph (Matrix.GeneralLinearGroup (Fin 2) F ⊕ Matrix.GeneralLinearGroup (Fin 2) F) where
  Adj u v := match u,v with
    | .inl g, .inr h => invariants (g⁻¹*h) ∈ S
    | .inr h, .inl g => invariants (g⁻¹*h) ∈ S
    | _, _ => False
  symm := by intro u v; cases u <;> cases v <;> simp_all
  loopless := by intro u; cases u <;> simp

omit [Fintype F] in
/-- Both the matrix and its inverse are supplied explicitly. -/
def diagonalRow (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    Matrix.GeneralLinearGroup (Fin 2) F where
  val := !![x⁻¹,0;0,y⁻¹]
  inv := !![x,0;0,y]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hx, hy]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hx, hy]

omit [Fintype F] in
lemma column_det (k b : F) (hb : b ≠ 0) :
    Matrix.det !![(1 : F),b;(1-k⁻¹)/b,1] = k⁻¹ := by
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, one_mul]
  field_simp
  ring

/-- A split-torus orbit with one column for every nonzero field element. -/
def column (k : Ratio (F := F)) (b : Fˣ) : Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1,(b : F);(1-(k : F)⁻¹)/(b : F),1]
    (by rw [column_det _ _ b.ne_zero]; exact inv_ne_zero k.property.1)

omit [Fintype F] in
lemma relative_invariants (x y : F) (hx : x ≠ 0) (hy : y ≠ 0)
    (k : Ratio (F := F)) (b : Fˣ) :
    invariants ((diagonalRow x y hx hy)⁻¹ * column k b) =
      (x*y/(k : F), x+y) := by
  have hb : (b : F) ≠ 0 := b.ne_zero
  apply Prod.ext
  · change Matrix.det (!![x,0;0,y] * !![1,(b : F);(1-(k : F)⁻¹)/(b : F),1]) = _
    rw [Matrix.det_mul, column_det _ _ hb]
    simp [Matrix.det_fin_two, div_eq_mul_inv]
  · change Matrix.trace (!![x,0;0,y] * !![1,(b : F);(1-(k : F)⁻¹)/(b : F),1]) = _
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]

def fiberRow (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (k : Ratio (F := F)) (p : {p : Parameter S // ratioMap S hS p = k}) :
    Matrix.GeneralLinearGroup (Fin 2) F :=
  diagonalRow p.val.2.val (p.val.1.val.2-p.val.2.val) p.val.2.property.1
    (sub_ne_zero.mpr p.val.2.property.2.symm)

omit [Fintype F] in
lemma fiber_invariants (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (k : Ratio (F := F)) (p : {p : Parameter S // ratioMap S hS p = k}) (b : Fˣ) :
    invariants ((fiberRow S hS k p)⁻¹ * column k b) = p.val.1.val := by
  rw [fiberRow, relative_invariants]
  have he := congrArg Subtype.val p.property
  change p.val.2.val*(p.val.1.val.2-p.val.2.val)/p.val.1.val.1 = (k : F) at he
  have hd := (hS p.val.1.val p.val.1.property).1
  have he' := (div_eq_iff hd).mp he
  apply Prod.ext
  · apply (div_eq_iff k.property.1).mpr
    simpa only [mul_comm] using he'
  · simp

omit [Fintype F] in
lemma fiberRow_injective (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (k : Ratio (F := F)) : Function.Injective (fiberRow S hS k) := by
  intro p q hpq
  have hc : p.val.1.val = q.val.1.val := by
    rw [← fiber_invariants S hS k p 1, ← fiber_invariants S hS k q 1, hpq]
  have hx : p.val.2.val = q.val.2.val := by
    have hh := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) F => g 0 0) hpq
    change p.val.2.val⁻¹ = q.val.2.val⁻¹ at hh
    exact inv_injective hh
  rcases p with ⟨⟨c,x⟩,hp⟩
  rcases q with ⟨⟨d,y⟩,hq⟩
  change c.val = d.val at hc
  have hcd : c = d := Subtype.ext hc
  subst d
  change x.val = y.val at hx
  have hxy : x = y := Subtype.ext hx
  subst y
  rfl

omit [Fintype F] in
lemma column_injective (k : Ratio (F := F)) : Function.Injective (column k) := by
  intro a b hab
  apply Units.ext
  exact congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) F => g 0 1) hab

/-- The entire fiber-by-torus rectangle consists of genuine Cayley edges. -/
def fiberCopy (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c) (k : Ratio (F := F)) :
    Copy (completeBipartiteGraph {p : Parameter S // ratioMap S hS p = k} Fˣ) (graph S) := by
  let L := (⟨fiberRow S hS k, fiberRow_injective S hS k⟩ : _ ↪ _)
  let R := (⟨column k, column_injective k⟩ : _ ↪ _)
  have he (p : {p : Parameter S // ratioMap S hS p = k}) (b : Fˣ) :
      invariants ((L p)⁻¹ * R b) ∈ S := by
    change invariants ((fiberRow S hS k p)⁻¹ * column k b) ∈ S
    rw [fiber_invariants]
    exact p.val.1.property
  refine ⟨⟨L.sumMap R, ?_⟩, (L.sumMap R).injective⟩
  intro u v huv
  cases u with
  | inl p =>
    cases v with
    | inl q => simp at huv
    | inr b => exact he p b
  | inr b =>
    cases v with
    | inr c => simp at huv
    | inl p => exact he p b


/-- Accepting `r` distinct elliptic classes forces K(r,r) once the field has `r+1` elements. -/
theorem not_free (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (r : ℕ) (hr : 2 ≤ r) (hsize : r ≤ S.card) (hq : r+1 ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free (graph S) := by
  obtain ⟨k,hk⟩ := large_fiber S hS (by omega)
  let A := {p : Parameter S // ratioMap S hS p = k}
  let L : Fin r ↪ A := (Fin.castLEEmb (hsize.trans hk)).trans
    (Fintype.equivFin A).symm.toEmbedding
  have hunit : r ≤ Fintype.card Fˣ := by rw [Fintype.card_units]; omega
  let R : Fin r ↪ Fˣ := (Fin.castLEEmb hunit).trans
    (Fintype.equivFin Fˣ).symm.toEmbedding
  let c : Copy (completeBipartiteGraph (Fin r) (Fin r)) (completeBipartiteGraph A Fˣ) :=
    ⟨⟨L.sumMap R, by
      intro u v huv
      cases u <;> cases v <;> simp_all⟩, (L.sumMap R).injective⟩
  intro hf
  exact hf ⟨(fiberCopy S hS k).comp c⟩

/-- In particular, a K44-free elliptic class fusion contains at most three classes. -/
theorem class_bound (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (hq : 5 ≤ Fintype.card F)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph S)) :
    S.card ≤ 3 := by
  by_contra h
  exact not_free S hS 4 (by decide) (by omega) hq hf


omit [Fintype F] in
/-- A root-free characteristic polynomial excludes triangular matrices. -/
lemma offDiagonal_ne_zero (g : Matrix.GeneralLinearGroup (Fin 2) F)
    (hg : Elliptic (invariants g)) : g 0 1 ≠ 0 := by
  intro hz
  apply hg.2 (g 0 0)
  dsimp [invariants]
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.det_fin_two]
  rw [hz]
  ring

omit [Fintype F] in
lemma classMatrix_det (d t a : F) (b : Fˣ) :
    Matrix.det !![a,(b : F);(a*(t-a)-d)/(b : F),t-a] = d := by
  have hb : (b : F) ≠ 0 := b.ne_zero
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

omit [Fintype F] in
/-- All matrices in one elliptic class, parameterized by one field element and one unit. -/
def classMatrix (c : F × F) (hc : c.1 ≠ 0) (a : F) (b : Fˣ) :
    Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a,(b : F);(a*(c.2-a)-c.1)/(b : F),c.2-a]
    (by rw [classMatrix_det]; exact hc)

omit [Fintype F] in
lemma classMatrix_invariants (c : F × F) (hc : c.1 ≠ 0) (a : F) (b : Fˣ) :
    invariants (classMatrix c hc a b) = c := by
  apply Prod.ext
  · exact classMatrix_det _ _ _ _
  · change Matrix.trace !![a,(b : F);(a*(c.2-a)-c.1)/(b : F),c.2-a] = c.2
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

omit [Fintype F] in
lemma classMatrix_reconstruct (g : Matrix.GeneralLinearGroup (Fin 2) F)
    (hg : Elliptic (invariants g)) :
    classMatrix (invariants g) hg.1 (g 0 0) (Units.mk0 (g 0 1) (offDiagonal_ne_zero g hg)) = g := by
  have hb : g 0 1 ≠ 0 := offDiagonal_ne_zero g hg
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · change (g 0 0 * ((g : Matrix (Fin 2) (Fin 2) F).trace - g 0 0) -
      (g : Matrix (Fin 2) (Fin 2) F).det) / g 0 1 = g 1 0
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.det_fin_two]
    field_simp
    ring
  · change (g : Matrix (Fin 2) (Fin 2) F).trace - g 0 0 = g 1 1
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- Actual connection matrices, not a set of class labels or multiplicities. -/
def Connection (S : Finset (F × F)) :=
  {g : Matrix.GeneralLinearGroup (Fin 2) F // invariants g ∈ S}

instance (S : Finset (F × F)) : Fintype (Connection S) := by unfold Connection; infer_instance

def connectionEquiv (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c) :
    Connection S ≃ S × (F × Fˣ) where
  toFun g := (⟨invariants g.val,g.property⟩,
    (g.val 0 0, Units.mk0 (g.val 0 1) (offDiagonal_ne_zero g.val (hS _ g.property))))
  invFun p := ⟨classMatrix p.1.val (hS _ p.1.property).1 p.2.1 p.2.2,
    by rw [classMatrix_invariants]; exact p.1.property⟩
  left_inv g := Subtype.ext (classMatrix_reconstruct g.val (hS _ g.property))
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (classMatrix_invariants p.1.val (hS _ p.1.property).1 p.2.1 p.2.2)
    · apply Prod.ext
      · rfl
      · apply Units.ext
        rfl

/-- Each accepted elliptic pair contributes exactly `q(q-1)` connection matrices. -/
theorem connection_card (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c) :
    Fintype.card (Connection S) = S.card * Fintype.card F * (Fintype.card F - 1) := by
  rw [Fintype.card_congr (connectionEquiv S hS), Fintype.card_prod, Fintype.card_prod,
    Fintype.card_coe, Fintype.card_units]
  ring


/-- Multiplication parametrizes the neighbors on the left. -/
def leftNeighborEquiv (S : Finset (F × F)) (g : Matrix.GeneralLinearGroup (Fin 2) F) :
    Connection S ≃ (graph S).neighborSet (.inl g) :=
  Equiv.ofBijective
    (fun s => ⟨Sum.inr (g*s.val), by
      change invariants (g⁻¹*(g*s.val)) ∈ S
      simpa only [inv_mul_cancel_left] using s.property⟩) (by
      constructor
      · intro s t h
        apply Subtype.ext
        exact mul_left_cancel (Sum.inr.inj (congrArg Subtype.val h))
      · rintro ⟨v,hv⟩
        cases v with
        | inl h => exact False.elim hv
        | inr h =>
          refine ⟨⟨g⁻¹*h,hv⟩, Subtype.ext ?_⟩
          simp)

/-- The same holds on the right even when the connection set is not inverse-closed. -/
def rightNeighborEquiv (S : Finset (F × F)) (g : Matrix.GeneralLinearGroup (Fin 2) F) :
    Connection S ≃ (graph S).neighborSet (.inr g) :=
  Equiv.ofBijective
    (fun s => ⟨Sum.inl (g*s.val⁻¹), by
      change invariants ((g*s.val⁻¹)⁻¹*g) ∈ S
      simpa [mul_assoc] using s.property⟩) (by
      constructor
      · intro s t h
        apply Subtype.ext
        exact inv_injective (mul_left_cancel (Sum.inl.inj (congrArg Subtype.val h)))
      · rintro ⟨v,hv⟩
        cases v with
        | inr h => exact False.elim hv
        | inl h =>
          refine ⟨⟨h⁻¹*g,hv⟩, Subtype.ext ?_⟩
          simp)

lemma degree_inl (S : Finset (F × F)) (g : Matrix.GeneralLinearGroup (Fin 2) F) :
    (graph S).degree (.inl g) = Fintype.card (Connection S) := by
  rw [← card_neighborSet_eq_degree]
  exact Fintype.card_congr (leftNeighborEquiv S g).symm

lemma degree_inr (S : Finset (F × F)) (g : Matrix.GeneralLinearGroup (Fin 2) F) :
    (graph S).degree (.inr g) = Fintype.card (Connection S) := by
  rw [← card_neighborSet_eq_degree]
  exact Fintype.card_congr (rightNeighborEquiv S g).symm

/-- The count is of actual undirected edges, without class or matrix multiplicities. -/
theorem edge_count (S : Finset (F × F)) :
    (graph S).edgeFinset.card =
      Fintype.card (Matrix.GeneralLinearGroup (Fin 2) F) * Fintype.card (Connection S) := by
  have hh := (graph S).sum_degrees_eq_twice_card_edges
  simp only [Fintype.sum_sum_type, degree_inl, degree_inr, sum_const,
    card_univ, smul_eq_mul] at hh
  omega

lemma matrix_card_bound :
    Fintype.card (Matrix.GeneralLinearGroup (Fin 2) F) ≤ Fintype.card F ^ 4 := by
  have hh := Fintype.card_le_of_injective
    (fun g : Matrix.GeneralLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F))
    Units.val_injective
  have he : Fintype.card (Matrix (Fin 2) (Fin 2) F) = Fintype.card F ^ 4 := by
    change Fintype.card (Fin 2 → Fin 2 → F) = _
    simp [← pow_mul]
  exact hh.trans_eq he

/-- Every free elliptic class fusion has only O(q^6), rather than Omega(q^7), edges. -/
theorem free_edge_bound (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (hq : 5 ≤ Fintype.card F)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph S)) :
    (graph S).edgeFinset.card ≤ 3 * Fintype.card F ^ 6 := by
  rw [edge_count, connection_card S hS]
  calc
    _ ≤ Fintype.card F ^ 4 * (3 * Fintype.card F * Fintype.card F) := by
      gcongr
      · exact matrix_card_bound
      · exact class_bound S hS hq hf
      · omega
    _ = _ := by ring

/-- An elliptic class-fusion family cannot attain the critical scale for unbounded fields. -/
theorem critical_size_bound (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (hq : 5 ≤ Fintype.card F)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph S))
    (C : ℕ) (he : Fintype.card F ^ 7 ≤ C * (graph S).edgeFinset.card) :
    Fintype.card F ≤ 3*C := by
  have hb := free_edge_bound S hS hq hf
  have hh : Fintype.card F ^ 6 * Fintype.card F ≤ Fintype.card F ^ 6 * (3*C) := by
    calc
      _ = Fintype.card F ^ 7 := by ring
      _ ≤ C * (graph S).edgeFinset.card := he
      _ ≤ C * (3 * Fintype.card F ^ 6) := Nat.mul_le_mul_left C hb
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (pow_pos (by omega) 6)


omit [Fintype F] in
def upperRow (t : F) : Matrix.GeneralLinearGroup (Fin 2) F where
  val := !![1,t;0,1]
  inv := !![1,-t;0,1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [Fintype F] in
def splitColumn (x y : F) (hxy : x*y ≠ 0) (b : F) : Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![x,b;0,y]
    (by simpa [Matrix.det_fin_two] using hxy)

omit [Fintype F] in
lemma split_relative_invariants (x y : F) (hxy : x*y ≠ 0) (a b : F) :
    invariants ((upperRow a)⁻¹ * splitColumn x y hxy b) = (x*y,x+y) := by
  apply Prod.ext
  · change Matrix.det (!![1,-a;0,1] * !![x,b;0,y]) = x*y
    rw [Matrix.det_mul]
    simp [Matrix.det_fin_two]
  · change Matrix.trace (!![1,-a;0,1] * !![x,b;0,y]) = x+y
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]

/-- A single split trace--determinant pair gives a full q-by-q grid. -/
def splitCopy (S : Finset (F × F)) (c : F × F) (hc : c ∈ S) (hd : c.1 ≠ 0)
    (x : F) (hx : x^2-c.2*x+c.1 = 0) :
    Copy (completeBipartiteGraph F F) (graph S) := by
  have hp : x*(c.2-x) = c.1 := by linear_combination -hx
  have hn : x*(c.2-x) ≠ 0 := by rwa [hp]
  let L : F ↪ Matrix.GeneralLinearGroup (Fin 2) F := ⟨upperRow, by
    intro a b h
    exact congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) F => g 0 1) h⟩
  let R : F ↪ Matrix.GeneralLinearGroup (Fin 2) F := ⟨splitColumn x (c.2-x) hn, by
    intro a b h
    exact congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) F => g 0 1) h⟩
  have he (a b : F) : invariants ((L a)⁻¹*R b) ∈ S := by
    change invariants ((upperRow a)⁻¹*splitColumn x (c.2-x) hn b) ∈ S
    rw [split_relative_invariants, hp]
    simpa using hc
  refine ⟨⟨L.sumMap R, ?_⟩, (L.sumMap R).injective⟩
  intro u v huv
  cases u with
  | inl a =>
    cases v with
    | inl b => simp at huv
    | inr b => exact he a b
  | inr b =>
    cases v with
    | inr a => simp at huv
    | inl a => exact he a b

/-- Every genuine accepted pair in a free fusion must be elliptic, in every characteristic. -/
theorem free_pairs_elliptic (S : Finset (F × F)) (hd : ∀ c ∈ S, c.1 ≠ 0)
    (r : ℕ) (hq : r ≤ Fintype.card F)
    (hf : (completeBipartiteGraph (Fin r) (Fin r)).Free (graph S)) :
    ∀ c ∈ S, Elliptic c := by
  intro c hc
  refine ⟨hd c hc, ?_⟩
  intro x hx
  let e : Fin r ↪ F := (Fin.castLEEmb hq).trans (Fintype.equivFin F).symm.toEmbedding
  let d : Copy (completeBipartiteGraph (Fin r) (Fin r)) (completeBipartiteGraph F F) :=
    ⟨⟨e.sumMap e, by
      intro u v huv
      cases u <;> cases v <;> simp_all⟩, (e.sumMap e).injective⟩
  exact hf ⟨(splitCopy S c hc (hd c hc) x hx).comp d⟩

/-- No trace--determinant fusion on GL(2), split or elliptic, attains the fourth-case scale. -/
theorem fusion_edge_bound (S : Finset (F × F)) (hd : ∀ c ∈ S, c.1 ≠ 0)
    (hq : 5 ≤ Fintype.card F)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph S)) :
    (graph S).edgeFinset.card ≤ 3 * Fintype.card F ^ 6 :=
  free_edge_bound S (free_pairs_elliptic S hd 4 (by omega) hf) hq hf

/-- Integer asymptotic obstruction, with no ellipticity assumption on the accepted pairs. -/
theorem fusion_critical_size_bound (S : Finset (F × F)) (hd : ∀ c ∈ S, c.1 ≠ 0)
    (hq : 5 ≤ Fintype.card F)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph S))
    (C : ℕ) (he : Fintype.card F ^ 7 ≤ C * (graph S).edgeFinset.card) :
    Fintype.card F ≤ 3*C :=
  critical_size_bound S (free_pairs_elliptic S hd 4 (by omega) hf) hq hf C he

end Erdos714EllipticFusion

#print axioms Erdos714EllipticFusion.large_fiber

#print axioms Erdos714EllipticFusion.relative_invariants
#print axioms Erdos714EllipticFusion.fiberCopy
#print axioms Erdos714EllipticFusion.not_free
#print axioms Erdos714EllipticFusion.class_bound

#print axioms Erdos714EllipticFusion.connection_card

#print axioms Erdos714EllipticFusion.edge_count
#print axioms Erdos714EllipticFusion.free_edge_bound
#print axioms Erdos714EllipticFusion.critical_size_bound

#print axioms Erdos714EllipticFusion.splitCopy
#print axioms Erdos714EllipticFusion.fusion_edge_bound
#print axioms Erdos714EllipticFusion.fusion_critical_size_bound
