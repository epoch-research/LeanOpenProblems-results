import FormalConjectures.Util.ProblemImports

open scoped EuclideanGeometry
open MeasureTheory MeasureTheory.Measure Metric Set AffineSubspace intervalIntegral
open scoped BigOperators

/-
A379732: Decimal expansion of $207/208$.
The $n$-th term of the sequence (for $n \ge 0$) is the $(n+1)$-th digit of $207/208`
after the decimal point.
-/
def a (n : ℕ) : ℕ :=
  let p := 207
  let q := 208
  let power_of_10 := 10 ^ (n + 1)
  let I := (p * power_of_10) / q
  I % 10

/-
# Densest packing of regular truncated tetrahedra

The regular truncated tetrahedron `T` is the convex hull of twelve explicit vertices.
Its packing density is the limsup, as `R → ∞`, of the greatest fraction of a Euclidean
ball of radius `R` that can be filled by finitely many non-overlapping isometric copies of `T`.
-/

/-- A point of `ℝ³`. -/
noncomputable def pt (x y z : ℝ) : ℝ³ := WithLp.toLp 2 ![x, y, z]

lemma pt_apply (x y z : ℝ) (i : Fin 3) : pt x y z i = ![x, y, z] i := rfl

lemma pt_smul (c x y z : ℝ) : c • pt x y z = pt (c * x) (c * y) (c * z) := by
  ext i; fin_cases i <;> simp [pt]

lemma pt_neg (x y z : ℝ) : -pt x y z = pt (-x) (-y) (-z) := by
  ext i; fin_cases i <;> simp [pt]

lemma pt_add (x₁ y₁ z₁ x₂ y₂ z₂ : ℝ) :
    pt x₁ y₁ z₁ + pt x₂ y₂ z₂ = pt (x₁ + x₂) (y₁ + y₂) (z₁ + z₂) := by
  ext i; fin_cases i <;> simp [pt]

lemma pt_sub (x₁ y₁ z₁ x₂ y₂ z₂ : ℝ) :
    pt x₁ y₁ z₁ - pt x₂ y₂ z₂ = pt (x₁ - x₂) (y₁ - y₂) (z₁ - z₂) := by
  ext i; fin_cases i <;> simp [pt]

lemma pt_zero : pt 0 0 0 = 0 := by
  ext i; fin_cases i <;> simp [pt]

/-- The twelve vertices of the regular truncated tetrahedron. -/
noncomputable def TTVertex : Fin 12 → ℝ³
  | 0 => pt 3 1 1
  | 1 => pt 3 (-1) (-1)
  | 2 => pt 1 3 1
  | 3 => pt (-1) 3 (-1)
  | 4 => pt 1 1 3
  | 5 => pt (-1) (-1) 3
  | 6 => pt 1 (-1) (-3)
  | 7 => pt (-1) 1 (-3)
  | 8 => pt 1 (-3) (-1)
  | 9 => pt (-1) (-3) 1
  | 10 => pt (-3) 1 (-1)
  | 11 => pt (-3) (-1) 1

/-- The regular truncated tetrahedron. -/
noncomputable def truncatedTetrahedron : Set ℝ³ :=
  convexHull ℝ (Set.range TTVertex)

/-- A finite collection of isometries is a packing of `K` inside a container `C`
if every image of `K` lies in `C` and the interiors of distinct images are disjoint. -/
def IsFinitePacking (K : Set ℝ³) (fs : Finset (ℝ³ ≃ᵢ ℝ³)) (C : Set ℝ³) : Prop :=
  (∀ f ∈ fs, (f : ℝ³ ≃ᵢ ℝ³) '' K ⊆ C) ∧
    (∀ f ∈ fs, ∀ g ∈ fs, f ≠ g →
      interior ((f : ℝ³ ≃ᵢ ℝ³) '' K) ∩ interior ((g : ℝ³ ≃ᵢ ℝ³) '' K) = ∅)

/-- Densities of finite packings of `K` into the closed ball of radius `R`. -/
noncomputable def densitiesInBall (K : Set ℝ³) (R : ℝ) : Set ℝ :=
  { d | ∃ fs : Finset (ℝ³ ≃ᵢ ℝ³),
      IsFinitePacking K fs (closedBall (0 : ℝ³) R) ∧
      d = (fs.card : ℝ) * (volume K).toReal /
        (volume (closedBall (0 : ℝ³) R)).toReal }

/-- Best packing density of `K` inside the closed ball of radius `R`. -/
noncomputable def packingDensityInBall (K : Set ℝ³) (R : ℝ) : ℝ :=
  sSup (densitiesInBall K R)

/--
The maximum packing density of congruent regular truncated tetrahedra: the limsup of
the best finite packing densities in balls of integer radius.
-/
noncomputable def max_packing_density_truncated_tetrahedra : ℝ :=
  Filter.atTop.limsup (fun n : ℕ => packingDensityInBall truncatedTetrahedron (n : ℝ))

/-- The four vertices of the large regular tetrahedron from which `T` is obtained by truncation. -/
noncomputable def largeTetVertex : Fin 4 → ℝ³
  | 0 => pt 3 3 3
  | 1 => pt 3 (-3) (-3)
  | 2 => pt (-3) 3 (-3)
  | 3 => pt (-3) (-3) 3

/-- The large regular tetrahedron. -/
noncomputable def largeTet : Set ℝ³ := convexHull ℝ (Set.range largeTetVertex)

/-- Coordinate matrix of three vectors. -/
noncomputable def coordMatrix (a b c : ℝ³) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a 0, b 0, c 0; a 1, b 1, c 1; a 2, b 2, c 2]

lemma coordMatrix_of_pt (x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ : ℝ) :
    coordMatrix (pt x₁ y₁ z₁) (pt x₂ y₂ z₂) (pt x₃ y₃ z₃) =
      !![x₁, x₂, x₃; y₁, y₂, y₃; z₁, z₂, z₃] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coordMatrix, pt]

lemma largeTet_edge1 : largeTetVertex 1 - largeTetVertex 0 = pt 0 (-6) (-6) := by
  simp only [largeTetVertex]; rw [pt_sub]; congr 1 <;> norm_num

lemma largeTet_edge2 : largeTetVertex 2 - largeTetVertex 0 = pt (-6) 0 (-6) := by
  simp only [largeTetVertex]; rw [pt_sub]; congr 1 <;> norm_num

lemma largeTet_edge3 : largeTetVertex 3 - largeTetVertex 0 = pt (-6) (-6) 0 := by
  simp only [largeTetVertex]; rw [pt_sub]; congr 1 <;> norm_num

lemma det_largeTet_edges :
    Matrix.det (coordMatrix (largeTetVertex 1 - largeTetVertex 0)
      (largeTetVertex 2 - largeTetVertex 0) (largeTetVertex 3 - largeTetVertex 0)) = -432 := by
  rw [largeTet_edge1, largeTet_edge2, largeTet_edge3, coordMatrix_of_pt, Matrix.det_fin_three]
  simp; norm_num

lemma integral_one_sub_sq :
    ∫ x in (0 : ℝ)..1, (1 - x) ^ 2 = (1 / 3 : ℝ) := by
  rw [integral_comp_sub_left (f := fun u : ℝ => u ^ 2) (d := 1)]
  simp only [sub_zero, one_div, sub_self]
  rw [integral_pow (n := 2)]
  norm_num

lemma integral_inner_simplex (c : ℝ) :
    ∫ y in (0 : ℝ)..c, (c - y) = c ^ 2 / 2 := by
  have h := intervalIntegral.integral_sub
    (μ := volume) (a := (0 : ℝ)) (b := c)
    (f := fun _ : ℝ => c) (g := fun y : ℝ => y)
    (hf := intervalIntegral.intervalIntegrable_const) (hg := intervalIntegrable_id)
  have hc : ∫ y in (0 : ℝ)..c, c = c * (c - 0) := by
    simp [intervalIntegral.integral_const]
  have hy : ∫ y in (0 : ℝ)..c, y = c ^ 2 / 2 := by
    have hp := integral_pow (a := (0 : ℝ)) (b := c) (n := 1)
    simp only [pow_one, Nat.cast_one] at hp
    convert hp using 1
    ring
  calc
    ∫ y in (0 : ℝ)..c, (c - y) = (∫ y in (0 : ℝ)..c, c) - ∫ y in (0 : ℝ)..c, y := h
    _ = c * c - c ^ 2 / 2 := by rw [hc, hy]; ring
    _ = c ^ 2 / 2 := by ring


lemma integral_half_one_sub_sq :
    ∫ x in (0 : ℝ)..1, (1 - x) ^ 2 / 2 = (1 / 6 : ℝ) := by
  have h := integral_one_sub_sq
  have hmul :
      ∫ x in (0 : ℝ)..1, (2 : ℝ)⁻¹ * (1 - x) ^ 2 =
        (2 : ℝ)⁻¹ * ∫ x in (0 : ℝ)..1, (1 - x) ^ 2 :=
    intervalIntegral.integral_const_mul _ _
  have hfun :
      (fun x : ℝ => (1 - x) ^ 2 / 2) = fun x => (2 : ℝ)⁻¹ * (1 - x) ^ 2 := by
    funext x; ring
  rw [hfun, hmul, h]
  norm_num

/-- Iterated integral for the volume of the standard 3-simplex. -/
lemma simplex_iterated_integral :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1 - x), (1 - x - y) = (1 / 6 : ℝ) := by
  have inner : ∀ x : ℝ, ∫ y in (0 : ℝ)..(1 - x), (1 - x - y) = (1 - x) ^ 2 / 2 :=
    fun x => integral_inner_simplex (1 - x)
  simp_rw [inner]
  exact integral_half_one_sub_sq


lemma integral_ordered_yz (x : ℝ) :
    ∫ y in (0 : ℝ)..x, y = x ^ 2 / 2 := by
  have hp := integral_pow (a := (0 : ℝ)) (b := x) (n := 1)
  simp only [pow_one, Nat.cast_one] at hp
  convert hp using 1
  ring

lemma integral_ordered_simplex_2d :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x, y = (1 / 6 : ℝ) := by
  simp_rw [integral_ordered_yz]
  have h := integral_pow (a := (0 : ℝ)) (b := 1) (n := 2)
  have hfun : (fun x : ℝ => x ^ 2 / 2) = fun x => (2 : ℝ)⁻¹ * x ^ 2 := by
    funext x; ring
  rw [hfun, intervalIntegral.integral_const_mul, h]
  norm_num


/- Linear forms of type (111). -/
noncomputable def form111 (εx εy εz : ℝ) (p : ℝ³) : ℝ :=
  εx * p 0 + εy * p 1 + εz * p 2

lemma form111_pt (εx εy εz x y z : ℝ) :
    form111 εx εy εz (pt x y z) = εx * x + εy * y + εz * z := by
  simp [form111, pt]

lemma form111_add (εx εy εz : ℝ) (p q : ℝ³) :
    form111 εx εy εz (p + q) = form111 εx εy εz p + form111 εx εy εz q := by
  simp [form111, PiLp.add_apply]; ring

lemma form111_smul (εx εy εz c : ℝ) (p : ℝ³) :
    form111 εx εy εz (c • p) = c * form111 εx εy εz p := by
  simp [form111, PiLp.smul_apply]; ring

lemma form111_sub (εx εy εz : ℝ) (p q : ℝ³) :
    form111 εx εy εz (p - q) = form111 εx εy εz p - form111 εx εy εz q := by
  simp [form111, PiLp.sub_apply]; ring

/-- Signs for the four even-parity (111)-forms. -/
def evenSign : Fin 4 → ℝ × ℝ × ℝ
  | 0 => (1, 1, 1)
  | 1 => (1, -1, -1)
  | 2 => (-1, 1, -1)
  | 3 => (-1, -1, 1)

/-- The four even-sign (111)-forms. -/
noncomputable def evenForm (i : Fin 4) (p : ℝ³) : ℝ :=
  form111 (evenSign i).1 (evenSign i).2.1 (evenSign i).2.2 p

lemma evenForm_add (i : Fin 4) (p q : ℝ³) :
    evenForm i (p + q) = evenForm i p + evenForm i q :=
  form111_add _ _ _ _ _

lemma evenForm_smul (i : Fin 4) (c : ℝ) (p : ℝ³) :
    evenForm i (c • p) = c * evenForm i p :=
  form111_smul _ _ _ _ _

lemma evenForm_sub (i : Fin 4) (p q : ℝ³) :
    evenForm i (p - q) = evenForm i p - evenForm i q :=
  form111_sub _ _ _ _ _

/-- The large tetrahedron as an intersection of four half-spaces. -/
def largeTetHS : Set ℝ³ :=
  {p | ∀ i : Fin 4, -3 ≤ evenForm i p}

/-- The truncated tetrahedron as an intersection of eight half-spaces. -/
def truncatedTetrahedronHS : Set ℝ³ :=
  {p | ∀ i : Fin 4, -3 ≤ evenForm i p ∧ evenForm i p ≤ 5}

lemma evenForm_pt (i : Fin 4) (x y z : ℝ) :
    evenForm i (pt x y z) =
      (evenSign i).1 * x + (evenSign i).2.1 * y + (evenSign i).2.2 * z :=
  form111_pt _ _ _ _ _ _

lemma largeTetVertex_mem_HS (i : Fin 4) : largeTetVertex i ∈ largeTetHS := by
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [largeTetVertex, evenForm_pt, evenSign] <;> norm_num

lemma convex_largeTetHS : Convex ℝ largeTetHS := by
  refine convex_iff_forall_pos.mpr ?_
  intro x hx y hy a b ha hb hab i
  have hx' := hx i
  have hy' := hy i
  rw [evenForm_add, evenForm_smul, evenForm_smul]
  nlinarith

lemma largeTet_subset_HS : largeTet ⊆ largeTetHS := by
  intro p hp
  have hconv : Convex ℝ largeTetHS := convex_largeTetHS
  have hpts : range largeTetVertex ⊆ largeTetHS := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    exact largeTetVertex_mem_HS i
  exact convexHull_min hpts hconv hp

/- Evaluate evenForm on all twelve truncated-tetrahedron vertices. -/
lemma TTVertex_form (i : Fin 12) (j : Fin 4) :
    -3 ≤ evenForm j (TTVertex i) ∧ evenForm j (TTVertex i) ≤ 5 := by
  fin_cases i <;> fin_cases j <;>
    simp only [TTVertex, evenForm_pt, evenSign] <;> norm_num

lemma TTVertex_mem_HS (i : Fin 12) : TTVertex i ∈ truncatedTetrahedronHS := by
  intro j
  exact TTVertex_form i j

lemma convex_truncatedTetrahedronHS : Convex ℝ truncatedTetrahedronHS := by
  refine convex_iff_forall_pos.mpr ?_
  intro x hx y hy a b ha hb hab i
  have hx' := hx i
  have hy' := hy i
  rw [evenForm_add, evenForm_smul, evenForm_smul]
  constructor <;> nlinarith

lemma truncatedTetrahedron_subset_HS :
    truncatedTetrahedron ⊆ truncatedTetrahedronHS := by
  intro p hp
  have hpts : range TTVertex ⊆ truncatedTetrahedronHS := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    exact TTVertex_mem_HS i
  exact convexHull_min hpts convex_truncatedTetrahedronHS hp


/-- Barycentric coordinate of a point w.r.t. the large tetrahedron, index `i`. -/
noncomputable def bary (i : Fin 4) (p : ℝ³) : ℝ :=
  (evenForm i p + 3) / 12

lemma bary_nonneg_of_mem_HS {p : ℝ³} (hp : p ∈ largeTetHS) (i : Fin 4) : 0 ≤ bary i p := by
  have := hp i
  simp only [bary]
  linarith

lemma sum_evenForm (p : ℝ³) :
    evenForm 0 p + evenForm 1 p + evenForm 2 p + evenForm 3 p = 0 := by
  simp only [evenForm, evenSign, form111]
  ring

lemma sum_bary (p : ℝ³) : bary 0 p + bary 1 p + bary 2 p + bary 3 p = 1 := by
  simp only [bary]
  have h := sum_evenForm p
  linarith

lemma largeTetVertex_eq_pt :
    largeTetVertex 0 = pt 3 3 3 ∧ largeTetVertex 1 = pt 3 (-3) (-3) ∧
    largeTetVertex 2 = pt (-3) 3 (-3) ∧ largeTetVertex 3 = pt (-3) (-3) 3 :=
  ⟨rfl, rfl, rfl, rfl⟩

lemma bary_reconstruction (p : ℝ³) :
    bary 0 p • largeTetVertex 0 + bary 1 p • largeTetVertex 1 +
      bary 2 p • largeTetVertex 2 + bary 3 p • largeTetVertex 3 = p := by
  rw [largeTetVertex_eq_pt.1, largeTetVertex_eq_pt.2.1,
      largeTetVertex_eq_pt.2.2.1, largeTetVertex_eq_pt.2.2.2]
  rw [pt_smul, pt_smul, pt_smul, pt_smul, pt_add, pt_add, pt_add]
  have hx : 3 * bary 0 p + 3 * bary 1 p + -3 * bary 2 p + -3 * bary 3 p = p 0 := by
    simp only [bary, evenForm, evenSign, form111]; ring
  have hy : 3 * bary 0 p + -3 * bary 1 p + 3 * bary 2 p + -3 * bary 3 p = p 1 := by
    simp only [bary, evenForm, evenSign, form111]; ring
  have hz : 3 * bary 0 p + -3 * bary 1 p + -3 * bary 2 p + 3 * bary 3 p = p 2 := by
    simp only [bary, evenForm, evenSign, form111]; ring
  ext i
  fin_cases i
  · simp [pt]; linarith
  · simp [pt]; linarith
  · simp [pt]; linarith

lemma mem_largeTet_of_mem_HS {p : ℝ³} (hp : p ∈ largeTetHS) : p ∈ largeTet := by
  refine mem_convexHull_of_exists_fintype (bary · p) largeTetVertex
    (fun i => bary_nonneg_of_mem_HS hp i) ?_ (fun i => mem_range_self i) ?_
  · simp [Fin.sum_univ_four, sum_bary]
  · simp [Fin.sum_univ_four, bary_reconstruction]

lemma largeTet_eq_HS : largeTet = largeTetHS :=
  subset_antisymm largeTet_subset_HS fun _ hp => mem_largeTet_of_mem_HS hp


lemma bary_le_two_thirds_of_mem_HS {p : ℝ³} (hp : p ∈ truncatedTetrahedronHS) (i : Fin 4) :
    bary i p ≤ 2 / 3 := by
  have := (hp i).2
  simp only [bary]
  linarith

lemma mem_truncatedHS_iff {p : ℝ³} :
    p ∈ truncatedTetrahedronHS ↔ (∀ i, 0 ≤ bary i p ∧ bary i p ≤ 2 / 3) := by
  constructor
  · intro hp i
    exact ⟨bary_nonneg_of_mem_HS (fun j => (hp j).1) i, bary_le_two_thirds_of_mem_HS hp i⟩
  · intro hp i
    have h0 := (hp i).1
    have h1 := (hp i).2
    constructor <;> (simp only [bary] at h0 h1; linarith)

lemma evenForm_largeTetVertex (i j : Fin 4) :
    evenForm i (largeTetVertex j) = if i = j then (9 : ℝ) else (-3 : ℝ) := by
  fin_cases i <;> fin_cases j <;>
    simp only [largeTetVertex, evenForm_pt, evenSign, ↓reduceIte] <;> norm_num

lemma evenForm_vertex_sub (i j k : Fin 4) :
    evenForm k (largeTetVertex i - largeTetVertex j) =
      (if k = i then (12 : ℝ) else 0) - if k = j then 12 else 0 := by
  rw [evenForm_sub, evenForm_largeTetVertex, evenForm_largeTetVertex]
  split_ifs <;> norm_num

lemma bary_vertex_sub (i j k : Fin 4) (p : ℝ³) (ε : ℝ) :
    bary k (p + ε • (largeTetVertex i - largeTetVertex j)) =
      bary k p + ε * ((if k = i then 1 else 0) - if k = j then 1 else 0) := by
  simp only [bary, evenForm_add, evenForm_smul, evenForm_vertex_sub]
  ring_nf
  split_ifs <;> ring

lemma form111_continuous (εx εy εz : ℝ) : Continuous (form111 εx εy εz) := by
  unfold form111
  fun_prop

lemma evenForm_continuous (i : Fin 4) : Continuous (evenForm i) :=
  form111_continuous _ _ _

lemma truncatedTetrahedronHS_closed : IsClosed truncatedTetrahedronHS := by
  have : truncatedTetrahedronHS =
      ⋂ i : Fin 4, {p | -3 ≤ evenForm i p} ∩ {p | evenForm i p ≤ 5} := by
    ext p; simp [truncatedTetrahedronHS]
  rw [this]
  refine isClosed_iInter fun i => IsClosed.inter ?_ ?_
  · exact isClosed_le continuous_const (evenForm_continuous i)
  · exact isClosed_le (evenForm_continuous i) continuous_const

lemma truncatedTetrahedronHS_subset_largeTet : truncatedTetrahedronHS ⊆ largeTet := by
  intro p hp
  rw [largeTet_eq_HS]
  exact fun i => (hp i).1

lemma truncatedTetrahedronHS_compact : IsCompact truncatedTetrahedronHS :=
  (Finite.isCompact_convexHull (finite_range largeTetVertex)).of_isClosed_subset
    truncatedTetrahedronHS_closed truncatedTetrahedronHS_subset_largeTet

lemma pt_combo_eq (x₁ y₁ z₁ x₂ y₂ z₂ : ℝ) :
    (2 / 3 : ℝ) • pt x₁ y₁ z₁ + (1 / 3 : ℝ) • pt x₂ y₂ z₂ =
      pt ((2 * x₁ + x₂) / 3) ((2 * y₁ + y₂) / 3) ((2 * z₁ + z₂) / 3) := by
  rw [pt_smul, pt_smul, pt_add]; congr 1 <;> ring

lemma edgePoint_mem_range_TTVertex (i j : Fin 4) (hij : i ≠ j) :
    (2 / 3 : ℝ) • largeTetVertex i + (1 / 3 : ℝ) • largeTetVertex j ∈ range TTVertex := by
  fin_cases i <;> fin_cases j <;> try (exact (hij rfl).elim)
  · use 0; simp only [TTVertex, largeTetVertex]; rw [pt_combo_eq]; congr 1 <;> norm_num
  · use 2; simp only [TTVertex, largeTetVertex]; rw [pt_combo_eq]; congr 1 <;> norm_num
  · use 4; simp only [TTVertex, largeTetVertex]; rw [pt_combo_eq]; congr 1 <;> norm_num
  · use 1; simp only [TTVertex, largeTetVertex]; rw [pt_combo_eq]; congr 1 <;> norm_num
  · use 6; simp only [TTVertex, largeTetVertex]; rw [pt_combo_eq]; congr 1 <;> norm_num
  · use 8; simp only [TTVertex, largeTetVertex]; rw [pt_combo_eq]; congr 1 <;> norm_num
  · use 3; simp only [TTVertex, largeTetVertex]; rw [pt_combo_eq]; congr 1 <;> norm_num
  · use 7; simp only [TTVertex, largeTetVertex]; rw [pt_combo_eq]; congr 1 <;> norm_num
  · use 10; simp only [TTVertex, largeTetVertex]; rw [pt_combo_eq]; congr 1 <;> norm_num
  · use 5; simp only [TTVertex, largeTetVertex]; rw [pt_combo_eq]; congr 1 <;> norm_num
  · use 9; simp only [TTVertex, largeTetVertex]; rw [pt_combo_eq]; congr 1 <;> norm_num
  · use 11; simp only [TTVertex, largeTetVertex]; rw [pt_combo_eq]; congr 1 <;> norm_num

lemma bary_eq_two_thirds_one_third {p : ℝ³} {i j : Fin 4} (hij : i ≠ j)
    (hi : bary i p = 2 / 3) (hj : bary j p = 1 / 3)
    (hk : ∀ k, k ≠ i → k ≠ j → bary k p = 0) :
    p = (2 / 3 : ℝ) • largeTetVertex i + (1 / 3 : ℝ) • largeTetVertex j := by
  rw [← bary_reconstruction p]
  fin_cases i <;> fin_cases j <;> try (exact (hij rfl).elim)
  all_goals
    dsimp at hi hj hk
    have hA := hk 0; have hB := hk 1; have hC := hk 2; have hD := hk 3
    try (specialize hA (by decide) (by decide))
    try (specialize hB (by decide) (by decide))
    try (specialize hC (by decide) (by decide))
    try (specialize hD (by decide) (by decide))
    rw [hi, hj]
    simp [hA, hB, hC, hD, zero_smul]
    try ac_rfl


lemma largeTetVertex_injective : Function.Injective largeTetVertex := by
  intro a b h
  fin_cases a <;> fin_cases b <;> try rfl
  all_goals
    have hx := congrArg (fun p : ℝ³ => p 0) h
    have hy := congrArg (fun p : ℝ³ => p 1) h
    simp [largeTetVertex, pt] at hx hy
    linarith


lemma evenForm_zero (i : Fin 4) : evenForm i 0 = 0 := by
  simp [evenForm, form111]

lemma bary_zero (i : Fin 4) : bary i 0 = 1 / 4 := by
  simp [bary, evenForm_zero]; norm_num

lemma origin_mem_HS : (0 : ℝ³) ∈ truncatedTetrahedronHS := by
  intro i
  constructor <;> simp [evenForm_zero]

lemma origin_mem_largeTet : (0 : ℝ³) ∈ largeTet :=
  mem_largeTet_of_mem_HS fun i => by simp [evenForm_zero]

lemma coord_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ³) (k : Fin 3) :
    (∑ i ∈ s, f i) k = ∑ i ∈ s, f i k := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

lemma sum_TTVertex : ∑ i : Fin 12, TTVertex i = 0 := by
  ext k
  rw [coord_sum]
  fin_cases k
  · simp [TTVertex, pt, Fin.sum_univ_succ]
  · simp [TTVertex, pt, Fin.sum_univ_succ]
  · simp [TTVertex, pt, Fin.sum_univ_succ]

lemma origin_mem_T : (0 : ℝ³) ∈ truncatedTetrahedron := by
  refine mem_convexHull_of_exists_fintype (fun _ : Fin 12 => (1 / 12 : ℝ)) TTVertex
    (fun _ => by norm_num) ?_ (fun i => mem_range_self i) ?_
  · simp [Finset.sum_const, Finset.card_univ]
  · rw [← Finset.smul_sum, sum_TTVertex, smul_zero]




lemma pt_ne_zero_of {x y z : ℝ} {i : Fin 3} (hi : ![x, y, z] i ≠ 0) :
    pt x y z ≠ 0 := by
  intro h
  have := congrArg (fun p : ℝ³ => p i) h
  simp [pt] at this
  exact hi this

lemma evenForm_all_zero {v : ℝ³} (h : ∀ i : Fin 4, evenForm i v = 0) : v = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [evenForm, evenSign, form111] at h0 h1 h2 h3
  have hx : v 0 = 0 := by linarith
  have hy : v 1 = 0 := by linarith
  have hz : v 2 = 0 := by linarith
  ext i
  fin_cases i
  · simpa using hx
  · simpa using hy
  · simpa using hz

lemma bary_add_smul (i : Fin 4) (p v : ℝ³) (ε : ℝ) :
    bary i (p + ε • v) = bary i p + ε * evenForm i v / 12 := by
  simp only [bary, evenForm_add, evenForm_smul]
  ring

lemma exists_ker_two (i j : Fin 4) (hij : i ≠ j) :
    ∃ v : ℝ³, v ≠ 0 ∧ evenForm i v = 0 ∧ evenForm j v = 0 := by
  fin_cases i <;> fin_cases j <;> try (exact (hij rfl).elim)
  · refine ⟨pt 0 1 (-1), pt_ne_zero_of (i := 1) (by norm_num), ?_, ?_⟩
    · simp [evenForm_pt, evenSign]
    · simp [evenForm_pt, evenSign]
  · refine ⟨pt 1 0 (-1), pt_ne_zero_of (i := 0) (by norm_num), ?_, ?_⟩
    · simp [evenForm_pt, evenSign]
    · simp [evenForm_pt, evenSign]
  · refine ⟨pt 1 (-1) 0, pt_ne_zero_of (i := 0) (by norm_num), ?_, ?_⟩
    · simp [evenForm_pt, evenSign]
    · simp [evenForm_pt, evenSign]
  · refine ⟨pt 0 1 (-1), pt_ne_zero_of (i := 1) (by norm_num), ?_, ?_⟩
    · simp [evenForm_pt, evenSign]
    · simp [evenForm_pt, evenSign]
  · refine ⟨pt 1 1 0, pt_ne_zero_of (i := 0) (by norm_num), ?_, ?_⟩
    · simp [evenForm_pt, evenSign]
    · simp [evenForm_pt, evenSign]
  · refine ⟨pt 1 0 1, pt_ne_zero_of (i := 0) (by norm_num), ?_, ?_⟩
    · simp [evenForm_pt, evenSign]
    · simp [evenForm_pt, evenSign]
  · refine ⟨pt 1 0 (-1), pt_ne_zero_of (i := 0) (by norm_num), ?_, ?_⟩
    · simp [evenForm_pt, evenSign]
    · simp [evenForm_pt, evenSign]
  · refine ⟨pt 1 1 0, pt_ne_zero_of (i := 0) (by norm_num), ?_, ?_⟩
    · simp [evenForm_pt, evenSign]
    · simp [evenForm_pt, evenSign]
  · refine ⟨pt 0 1 1, pt_ne_zero_of (i := 1) (by norm_num), ?_, ?_⟩
    · simp [evenForm_pt, evenSign]
    · simp [evenForm_pt, evenSign]
  · refine ⟨pt 1 (-1) 0, pt_ne_zero_of (i := 0) (by norm_num), ?_, ?_⟩
    · simp [evenForm_pt, evenSign]
    · simp [evenForm_pt, evenSign]
  · refine ⟨pt 1 0 1, pt_ne_zero_of (i := 0) (by norm_num), ?_, ?_⟩
    · simp [evenForm_pt, evenSign]
    · simp [evenForm_pt, evenSign]
  · refine ⟨pt 0 1 1, pt_ne_zero_of (i := 1) (by norm_num), ?_, ?_⟩
    · simp [evenForm_pt, evenSign]
    · simp [evenForm_pt, evenSign]

lemma slack_nonneg {p : ℝ³} (hp : p ∈ truncatedTetrahedronHS) (i : Fin 4) :
    0 ≤ min (bary i p) (2 / 3 - bary i p) := by
  have hi := mem_truncatedHS_iff.mp hp i
  apply le_min
  · exact hi.1
  · linarith [hi.2]

lemma slack_pos_of_not_tight {p : ℝ³} (hp : p ∈ truncatedTetrahedronHS) {i : Fin 4}
    (h0 : bary i p ≠ 0) (h1 : bary i p ≠ 2 / 3) :
    0 < min (bary i p) (2 / 3 - bary i p) := by
  have hi := mem_truncatedHS_iff.mp hp i
  apply lt_min
  · exact lt_of_le_of_ne hi.1 h0.symm
  · exact lt_of_le_of_ne (by linarith [hi.2]) (by intro h; apply h1; linarith)

/-- Vertex-type barycentric coordinates: a permutation of `(2/3, 1/3, 0, 0)`. -/
def IsVertexBary (p : ℝ³) : Prop :=
  ∃ i j : Fin 4, i ≠ j ∧ bary i p = 2 / 3 ∧ bary j p = 1 / 3 ∧
    (∀ k, k ≠ i → k ≠ j → bary k p = 0)

lemma isTight_of_mem {p : ℝ³} {i : Fin 4}
    (hi : i ∈ Finset.univ.filter (fun k => bary k p = 0 ∨ bary k p = 2 / 3)) :
    bary i p = 0 ∨ bary i p = 2 / 3 :=
  (Finset.mem_filter.mp hi).2

lemma exists_fourth (a b c : Fin 4) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ d : Fin 4, d ≠ a ∧ d ≠ b ∧ d ≠ c ∧
      ({a, b, c, d} : Finset (Fin 4)) = Finset.univ := by
  have hcard : ({a, b, c} : Finset (Fin 4)).card = 3 := by
    simp [Finset.card_insert_of_notMem, hab, hac, hbc]
  have hcompl : ({a, b, c} : Finset (Fin 4))ᶜ.card = 1 := by
    rw [Finset.card_compl, hcard]
    decide
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hcompl
  have hd_not : d ∉ ({a, b, c} : Finset (Fin 4)) := by
    have : d ∈ ({a, b, c} : Finset (Fin 4))ᶜ := by simp [hd]
    exact Finset.mem_compl.mp this
  have hne : d ≠ a ∧ d ≠ b ∧ d ≠ c := by
    simp [Finset.mem_insert, Finset.mem_singleton] at hd_not
    exact hd_not
  refine ⟨d, hne.1, hne.2.1, hne.2.2, ?_⟩
  apply Finset.eq_univ_of_card
  have hd' : d ∉ (∅ : Finset (Fin 4)) := Finset.notMem_empty d
  have hc' : c ∉ ({d} : Finset (Fin 4)) := by
    exact mt Finset.mem_singleton.mp hne.2.2.symm
  have hb' : b ∉ ({c, d} : Finset (Fin 4)) := by
    intro hbmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbmem
    rcases hbmem with h | h
    · exact hbc h
    · exact hne.2.1 h.symm
  have ha' : a ∉ ({b, c, d} : Finset (Fin 4)) := by
    intro hamem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hamem
    rcases hamem with h | h | h
    · exact hab h
    · exact hac h
    · exact hne.1 h.symm
  change Finset.card ({a, b, c, d} : Finset (Fin 4)) = Fintype.card (Fin 4)
  rw [Finset.card_insert_of_notMem ha', Finset.card_insert_of_notMem hb',
      Finset.card_insert_of_notMem hc', Finset.card_singleton]
  decide

lemma sum_bary_of_univ {p : ℝ³} {a b c d : Fin 4}
    (huniv : ({a, b, c, d} : Finset (Fin 4)) = Finset.univ)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    bary a p + bary b p + bary c p + bary d p = 1 := by
  have hsum : ∑ i ∈ Finset.univ, bary i p = 1 := by
    simpa [Fin.sum_univ_four] using sum_bary p
  rw [← huniv] at hsum
  have ha' : a ∉ ({b, c, d} : Finset (Fin 4)) := by
    simp [Finset.mem_insert, Finset.mem_singleton, hab, hac, had]
  have hb' : b ∉ ({c, d} : Finset (Fin 4)) := by
    simp [Finset.mem_insert, Finset.mem_singleton, hbc, hbd]
  have hc' : c ∉ ({d} : Finset (Fin 4)) := by
    simp [Finset.mem_singleton, hcd]
  rw [Finset.sum_insert ha', Finset.sum_insert hb', Finset.sum_insert hc',
      Finset.sum_singleton] at hsum
  linarith

/-- Three tight barycentric coordinates force vertex type (or exit from `T_HS`). -/
lemma isVertexBary_of_three_tight {p : ℝ³} (hp : p ∈ truncatedTetrahedronHS)
    {a b c : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : bary a p = 0 ∨ bary a p = 2 / 3)
    (hb : bary b p = 0 ∨ bary b p = 2 / 3)
    (hc : bary c p = 0 ∨ bary c p = 2 / 3) :
    IsVertexBary p := by
  obtain ⟨d, hda, hdb, hdc, huniv⟩ := exists_fourth a b c hab hac hbc
  have had : a ≠ d := hda.symm
  have hbd : b ≠ d := hdb.symm
  have hcd : c ≠ d := hdc.symm
  have hsum' := sum_bary_of_univ (p := p) huniv hab hac had hbc hbd hcd
  have hp' := mem_truncatedHS_iff.mp hp
  have mem_ab : ∀ k, k ≠ a → k ≠ b → k ≠ c → k ≠ d → False := by
    intro k hka hkb hkc hkd
    have hk : k ∈ Finset.univ := Finset.mem_univ k
    rw [← huniv] at hk
    simp [Finset.mem_insert, Finset.mem_singleton, hka, hkb, hkc, hkd] at hk
  rcases ha with ha0 | ha23 <;> rcases hb with hb0 | hb23 <;> rcases hc with hc0 | hc23
  · have : bary d p = 1 := by linarith
    linarith [(hp' d).2]
  · refine ⟨c, d, hdc.symm, hc23, (by linarith), ?_⟩
    intro k hkc hkd
    have : k = a ∨ k = b := by
      have hk : k ∈ Finset.univ := Finset.mem_univ k
      rw [← huniv] at hk
      simpa [Finset.mem_insert, Finset.mem_singleton, hkc, hkd] using hk
    rcases this with rfl | rfl <;> exact ‹_›
  · refine ⟨b, d, hdb.symm, hb23, (by linarith), ?_⟩
    intro k hkb hkd
    have : k = a ∨ k = c := by
      have hk : k ∈ Finset.univ := Finset.mem_univ k
      rw [← huniv] at hk
      simpa [Finset.mem_insert, Finset.mem_singleton, hkb, hkd] using hk
    rcases this with rfl | rfl <;> exact ‹_›
  · have : bary d p = -1 / 3 := by linarith
    linarith [(hp' d).1]
  · refine ⟨a, d, hda.symm, ha23, (by linarith), ?_⟩
    intro k hka hkd
    have : k = b ∨ k = c := by
      have hk : k ∈ Finset.univ := Finset.mem_univ k
      rw [← huniv] at hk
      simpa [Finset.mem_insert, Finset.mem_singleton, hka, hkd] using hk
    rcases this with rfl | rfl <;> exact ‹_›
  · have : bary d p = -1 / 3 := by linarith
    linarith [(hp' d).1]
  · have : bary d p = -1 / 3 := by linarith
    linarith [(hp' d).1]
  · have : bary d p = -1 := by linarith
    linarith [(hp' d).1]

lemma exists_covering_pair {p : ℝ³} (hnot : ¬ IsVertexBary p)
    (hp : p ∈ truncatedTetrahedronHS) :
    ∃ i j : Fin 4, i ≠ j ∧
      ∀ k, bary k p = 0 ∨ bary k p = 2 / 3 → k = i ∨ k = j := by
  let t := Finset.univ.filter (fun k : Fin 4 => bary k p = 0 ∨ bary k p = 2 / 3)
  have hle : t.card ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ t.card := Nat.succ_le_of_lt (lt_of_not_ge h)
    obtain ⟨u, hu_sub, hu_card⟩ := (Finset.le_card_iff_exists_subset_card).1 h3
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := (Finset.card_eq_three).1 hu_card
    have ha : bary a p = 0 ∨ bary a p = 2 / 3 := isTight_of_mem (hu_sub (by simp))
    have hb : bary b p = 0 ∨ bary b p = 2 / 3 := isTight_of_mem (hu_sub (by simp))
    have hc : bary c p = 0 ∨ bary c p = 2 / 3 := isTight_of_mem (hu_sub (by simp))
    exact hnot (isVertexBary_of_three_tight hp hab hac hbc ha hb hc)
  interval_cases hcard : t.card
  · refine ⟨0, 1, by decide, ?_⟩
    intro k hk
    have hk' : k ∈ t := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
    have : t = ∅ := Finset.card_eq_zero.mp hcard
    rw [this] at hk'
    exact (Finset.notMem_empty k hk').elim
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
    refine ⟨i, i + 1, ?_, ?_⟩
    · intro h
      have := congrArg Fin.val h
      have hi4 := i.isLt
      simp [Fin.val_add] at this
      omega
    · intro k hk
      have hk' : k ∈ t := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
      rw [hi] at hk'
      exact Or.inl (Finset.mem_singleton.mp hk')
  · obtain ⟨i, j, hij, ht_eq⟩ := (Finset.card_eq_two).1 hcard
    refine ⟨i, j, hij, ?_⟩
    intro k hk
    have hk' : k ∈ t := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
    rw [ht_eq] at hk'
    simpa using hk'

/-- If `v` is killed by every tight form at `p`, a short segment through `p` stays in `T_HS`. -/
lemma exists_openSegment_of_ker {p v : ℝ³} (hp : p ∈ truncatedTetrahedronHS) (hv : v ≠ 0)
    (hker : ∀ i, bary i p = 0 ∨ bary i p = 2 / 3 → evenForm i v = 0) :
    ∃ x y : ℝ³, x ≠ y ∧ x ∈ truncatedTetrahedronHS ∧ y ∈ truncatedTetrahedronHS ∧
      p ∈ openSegment ℝ x y := by
  let δ : Fin 4 → ℝ := fun i => min (bary i p) (2 / 3 - bary i p)
  let b : Fin 4 → ℝ := fun i =>
    if evenForm i v = 0 then (1 : ℝ) else 12 * δ i / |evenForm i v|
  have hbpos : ∀ i, 0 < b i := by
    intro i
    by_cases hf : evenForm i v = 0
    · simp [b, hf]
    · have hnotTight : ¬ (bary i p = 0 ∨ bary i p = 2 / 3) := fun ht => hf (hker i ht)
      have hδ : 0 < δ i :=
        slack_pos_of_not_tight hp (fun h => hnotTight (Or.inl h)) (fun h => hnotTight (Or.inr h))
      have habs : 0 < |evenForm i v| := abs_pos.mpr hf
      simp only [b, hf, ite_false]
      positivity
  let ε := Finset.univ.inf' Finset.univ_nonempty b
  have εpos : 0 < ε := by
    rw [Finset.lt_inf'_iff]
    intro i _; exact hbpos i
  have hmem : ∀ t : ℝ, |t| ≤ ε → p + t • v ∈ truncatedTetrahedronHS := by
    intro t ht
    rw [mem_truncatedHS_iff]
    intro i
    have hεi : ε ≤ b i := Finset.inf'_le _ (Finset.mem_univ i)
    rw [bary_add_smul]
    by_cases hf : evenForm i v = 0
    · simpa [hf] using (mem_truncatedHS_iff.mp hp i)
    · have habs0 : |evenForm i v| ≠ 0 := abs_ne_zero.mpr hf
      have hbval : b i = 12 * δ i / |evenForm i v| := by simp [b, hf]
      have hbound : |t * evenForm i v / 12| ≤ δ i := by
        have h1 : |t * evenForm i v / 12| = |t| * |evenForm i v| / 12 := by
          simp [abs_mul, abs_div]
        have h2 : |t| * |evenForm i v| / 12 ≤ ε * |evenForm i v| / 12 := by
          gcongr
        have h3 : ε * |evenForm i v| / 12 ≤ b i * |evenForm i v| / 12 := by
          gcongr
        have h4 : b i * |evenForm i v| / 12 = δ i := by
          rw [hbval]
          field_simp [habs0]
        linarith
      have hi := mem_truncatedHS_iff.mp hp i
      constructor
      · nlinarith [neg_le_abs (t * evenForm i v / 12), min_le_left (bary i p) (2 / 3 - bary i p)]
      · nlinarith [le_abs_self (t * evenForm i v / 12), min_le_right (bary i p) (2 / 3 - bary i p)]
  refine ⟨p + ε • v, p + (-ε) • v, ?_,
      hmem ε (by simp [abs_of_pos εpos]),
      hmem (-ε) (by simp [abs_of_pos εpos]), ?_⟩
  · intro heq
    have hcoord : ∀ i : Fin 3, ε * v i = (-ε) * v i := by
      intro i
      have := congrArg (fun q : ℝ³ => q i) (add_left_cancel heq)
      simpa [PiLp.smul_apply] using this
    apply hv
    ext i
    have : (2 * ε) * v i = 0 := by linarith [hcoord i]
    have h2ε : (2 : ℝ) * ε ≠ 0 := by positivity
    have : v i = 0 := (mul_eq_zero.mp this).resolve_left h2ε
    simpa using this
  · refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    ext i
    simp [PiLp.add_apply, PiLp.smul_apply]
    ring

lemma exists_openSegment_mem_HS {p : ℝ³} (hp : p ∈ truncatedTetrahedronHS)
    (hnot : ¬ IsVertexBary p) :
    ∃ x y : ℝ³, x ≠ y ∧ x ∈ truncatedTetrahedronHS ∧ y ∈ truncatedTetrahedronHS ∧
      p ∈ openSegment ℝ x y := by
  obtain ⟨i, j, hij, hcov⟩ := exists_covering_pair hnot hp
  obtain ⟨v, hv, hvi, hvj⟩ := exists_ker_two i j hij
  refine exists_openSegment_of_ker hp hv ?_
  intro k hk
  rcases hcov k hk with rfl | rfl
  · exact hvi
  · exact hvj

lemma isVertexBary_mem_range_TTVertex {p : ℝ³} (h : IsVertexBary p) :
    p ∈ range TTVertex := by
  rcases h with ⟨i, j, hij, hi, hj, hk⟩
  have := bary_eq_two_thirds_one_third hij hi hj hk
  rw [this]
  exact edgePoint_mem_range_TTVertex i j hij

lemma extremePoints_HS_subset_TTVertex :
    extremePoints ℝ truncatedTetrahedronHS ⊆ range TTVertex := by
  intro p hp
  have hpT : p ∈ truncatedTetrahedronHS := extremePoints_subset hp
  by_cases hv : IsVertexBary p
  · exact isVertexBary_mem_range_TTVertex hv
  · obtain ⟨x, y, hxy, hx, hy, hseg⟩ := exists_openSegment_mem_HS hpT hv
    have hex := (mem_extremePoints.mp hp).2 x hx y hy hseg
    exact False.elim (hxy (hex.1.trans hex.2.symm))

lemma truncatedTetrahedronHS_eq :
    truncatedTetrahedronHS = truncatedTetrahedron := by
  refine subset_antisymm ?_ truncatedTetrahedron_subset_HS
  have hKM :=
    closure_convexHull_extremePoints truncatedTetrahedronHS_compact convex_truncatedTetrahedronHS
  have hcl : truncatedTetrahedronHS ⊆ closure (convexHull ℝ (range TTVertex)) := by
    intro p hp
    have hp' : p ∈ closure (convexHull ℝ (extremePoints ℝ truncatedTetrahedronHS)) := by
      rwa [hKM]
    exact closure_mono (convexHull_mono extremePoints_HS_subset_TTVertex) hp'
  have hclosed : IsClosed (convexHull ℝ (range TTVertex)) :=
    (Finite.isCompact_convexHull (finite_range TTVertex)).isClosed
  rwa [hclosed.closure_eq] at hcl


/- Volume of the standard 3-simplex, the large tetrahedron, and T. -/

def stdSimp3 : Set ℝ³ :=
  {p | 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ 0 ≤ p 2 ∧ p 0 + p 1 + p 2 ≤ 1}

def unitCube3 : Set ℝ³ :=
  {p | ∀ i : Fin 3, p i ∈ Icc (0 : ℝ) 1}

def coordLM (i : Fin 3) : ℝ³ →ₗ[ℝ] ℝ where
  toFun := fun p => p i
  map_add' := fun _ _ => by simp [PiLp.add_apply]
  map_smul' := fun _ _ => by simp [PiLp.smul_apply]

lemma volume_coord_eq_hyperplane (i j : Fin 3) (hij : i ≠ j) :
    volume {p : ℝ³ | p i = p j} = 0 := by
  have hker : {p : ℝ³ | p i = p j} = (coordLM i - coordLM j).ker := by
    ext p; simp [coordLM, sub_eq_zero, LinearMap.mem_ker]
  rw [hker]
  refine Measure.addHaar_submodule volume (coordLM i - coordLM j).ker ?_
  intro htop
  have hzero : coordLM i - coordLM j = 0 := LinearMap.ker_eq_top.mp htop
  let e : ℝ³ := WithLp.toLp 2 (Pi.single i (1 : ℝ))
  have hi : e i = 1 := by simp [e]
  have hj : e j = 0 := by
    simp [e, Pi.single_eq_of_ne hij.symm]
  have hval : (coordLM i - coordLM j) e = 1 := by
    simp [coordLM, hi, hj]
  simp [hzero] at hval

lemma volume_unitCube3 : volume unitCube3 = 1 := by
  have hpre : unitCube3 = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹' Icc 0 1 := by
    ext p
    constructor
    · intro hp
      simp only [mem_preimage, mem_Icc, Pi.le_def]
      exact ⟨fun i => (hp i).1, fun i => (hp i).2⟩
    · intro hp
      intro i
      simp only [mem_preimage, mem_Icc, Pi.le_def] at hp
      exact ⟨hp.1 i, hp.2 i⟩
  rw [hpre]
  have hp : MeasurePreserving (@WithLp.ofLp 2 (Fin 3 → ℝ)) :=
    PiLp.volume_preserving_ofLp (ι := Fin 3)
  have hI : volume (Icc (0 : Fin 3 → ℝ) 1) = 1 := by
    rw [Real.volume_Icc_pi]
    simp
  have hs : NullMeasurableSet (Icc (0 : Fin 3 → ℝ) 1) volume :=
    measurableSet_Icc.nullMeasurableSet
  rw [hp.measure_preimage hs, hI]

noncomputable def unipotentU : ℝ³ →ₗ[ℝ] ℝ³ where
  toFun p := pt (p 0 + p 1 + p 2) (p 1 + p 2) (p 2)
  map_add' p q := by
    ext i; fin_cases i <;> simp [pt, PiLp.add_apply] <;> ring
  map_smul' c p := by
    ext i; fin_cases i <;> simp [pt, PiLp.smul_apply] <;> ring

lemma unipotentU_apply (p : ℝ³) :
    unipotentU p = pt (p 0 + p 1 + p 2) (p 1 + p 2) (p 2) :=
  rfl

lemma det_unipotentU : LinearMap.det unipotentU = 1 := by
  have hmat :
      LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin 3)) (PiLp.basisFun 2 ℝ (Fin 3)) unipotentU =
        !![1, 1, 1; 0, 1, 1; 0, 0, 1] := by
    ext i j
    simp only [LinearMap.toMatrix_apply, PiLp.basisFun_repr, PiLp.basisFun_apply, unipotentU_apply]
    fin_cases i <;> fin_cases j <;> simp [pt, Pi.single]
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 3)), hmat, Matrix.det_fin_three]
  simp

lemma unipotentU_image_stdSimp :
    unipotentU '' stdSimp3 = {p : ℝ³ | 0 ≤ p 2 ∧ p 2 ≤ p 1 ∧ p 1 ≤ p 0 ∧ p 0 ≤ 1} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [unipotentU_apply]
    rcases hq with ⟨h0, h1, h2, hs⟩
    simp [pt]
    constructor
    · linarith
    · constructor
      · linarith
      · constructor
        · linarith
        · linarith
  · intro hp
    refine ⟨pt (p 0 - p 1) (p 1 - p 2) (p 2), ?_, ?_⟩
    · simp [stdSimp3, pt]
      rcases hp with ⟨hp2, hp21, hp10, hp0⟩
      constructor
      · linarith
      · constructor
        · linarith
        · constructor
          · linarith
          · linarith
    · rw [unipotentU_apply]
      simp [pt]
      ext i
      fin_cases i <;> simp [pt] <;> ring



def stdSimp2 (c : ℝ) : Set (Fin 2 → ℝ) :=
  {y | 0 ≤ y 0 ∧ 0 ≤ y 1 ∧ y 0 + y 1 ≤ c}

lemma isClosed_stdSimp2 (c : ℝ) : IsClosed (stdSimp2 c) := by
  have : stdSimp2 c =
      {y : Fin 2 → ℝ | 0 ≤ y 0} ∩ {y | 0 ≤ y 1} ∩ {y | y 0 + y 1 ≤ c} := by
    ext; simp [stdSimp2]; constructor <;> intro h <;> tauto
  rw [this]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · exact isClosed_le continuous_const (continuous_apply 0)
  · exact isClosed_le continuous_const (continuous_apply 1)
  · exact isClosed_le ((continuous_apply 0).add (continuous_apply 1)) continuous_const

lemma image_stdSimp2 (c : ℝ) :
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) 0 '' stdSimp2 c =
      {p : ℝ × (Fin 1 → ℝ) | 0 ≤ p.1 ∧ 0 ≤ p.2 0 ∧ p.1 + p.2 0 ≤ c} := by
  set e1 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) 0
  ext p
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp [stdSimp2, e1, Fin.insertNthEquiv] at hy ⊢
    simpa [Fin.removeNth] using hy
  · intro hp
    refine ⟨e1.symm p, ?_, e1.apply_symm_apply p⟩
    simp [stdSimp2, e1, Fin.insertNthEquiv] at hp ⊢
    simpa [Fin.insertNth] using hp

lemma volume_eq_image_stdSimp2 (c : ℝ) :
    volume (stdSimp2 c) =
      volume {p : ℝ × (Fin 1 → ℝ) | 0 ≤ p.1 ∧ 0 ≤ p.2 0 ∧ p.1 + p.2 0 ≤ c} := by
  rw [← image_stdSimp2]
  set e1 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) 0
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin 2 => ℝ) 0).symm
  have hcl : NullMeasurableSet (stdSimp2 c) volume :=
    (isClosed_stdSimp2 c).nullMeasurableSet
  have h := hp.measure_preimage hcl
  rw [← MeasurableEquiv.image_eq_preimage_symm] at h
  exact h.symm

lemma image_s_to_sR (c : ℝ) :
    ⇑(MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.funUnique (Fin 1) ℝ)) ''
        {p : ℝ × (Fin 1 → ℝ) | 0 ≤ p.1 ∧ 0 ≤ p.2 0 ∧ p.1 + p.2 0 ≤ c} =
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ c} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simp [MeasurableEquiv.prodCongr, MeasurableEquiv.funUnique] at hq ⊢
    exact hq
  · intro hp
    refine ⟨(p.1, fun _ => p.2), ?_, ?_⟩
    · simpa using hp
    · simp [MeasurableEquiv.prodCongr, MeasurableEquiv.funUnique]

lemma isClosed_sR (c : ℝ) : IsClosed {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ c} := by
  have : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ c} =
      {p : ℝ × ℝ | 0 ≤ p.1} ∩ {p | 0 ≤ p.2} ∩ {p | p.1 + p.2 ≤ c} := by
    ext; simp; constructor <;> intro h <;> tauto
  rw [this]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · exact isClosed_le continuous_const continuous_fst
  · exact isClosed_le continuous_const continuous_snd
  · exact isClosed_le (continuous_fst.add continuous_snd) continuous_const

lemma isClosed_s (c : ℝ) :
    IsClosed {p : ℝ × (Fin 1 → ℝ) | 0 ≤ p.1 ∧ 0 ≤ p.2 0 ∧ p.1 + p.2 0 ≤ c} := by
  have : {p : ℝ × (Fin 1 → ℝ) | 0 ≤ p.1 ∧ 0 ≤ p.2 0 ∧ p.1 + p.2 0 ≤ c} =
      {p | 0 ≤ p.1} ∩ {p | 0 ≤ p.2 0} ∩ {p | p.1 + p.2 0 ≤ c} := by
    ext; simp; constructor <;> intro h <;> tauto
  rw [this]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · exact isClosed_le continuous_const continuous_fst
  · exact isClosed_le continuous_const ((continuous_apply 0).comp continuous_snd)
  · exact isClosed_le (continuous_fst.add ((continuous_apply 0).comp continuous_snd))
      continuous_const

lemma volume_s_eq_sR (c : ℝ) :
    volume {p : ℝ × (Fin 1 → ℝ) | 0 ≤ p.1 ∧ 0 ≤ p.2 0 ∧ p.1 + p.2 0 ≤ c} =
      volume {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ c} := by
  rw [← image_s_to_sR]
  set e := MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.funUnique (Fin 1) ℝ)
  have hpU : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ) :=
    measurePreserving_piUnique (fun _ : Fin 1 => volume)
  have hid : MeasurePreserving (MeasurableEquiv.refl ℝ) := MeasurePreserving.id _
  have hpm : MeasurePreserving e
      ((volume : Measure ℝ).prod (volume : Measure (Fin 1 → ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    hid.prod hpU
  have hvol1 : (volume : Measure (ℝ × (Fin 1 → ℝ))) =
      (volume : Measure ℝ).prod volume := volume_eq_prod (α := ℝ) (β := Fin 1 → ℝ)
  have hvol2 : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume :=
    volume_eq_prod (α := ℝ) (β := ℝ)
  have h := hpm.symm.measure_preimage (isClosed_s c).nullMeasurableSet
  rw [hvol1, hvol2]
  rw [← MeasurableEquiv.image_eq_preimage_symm] at h
  exact h.symm

lemma volume_sR (c : ℝ) (hc : 0 < c) :
    volume {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ c} =
      ENNReal.ofReal (c ^ 2 / 2) := by
  have hsR : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ c} :=
    (isClosed_sR c).measurableSet
  have hprod : (volume : Measure (ℝ × ℝ)) = volume.prod volume :=
    volume_eq_prod (α := ℝ) (β := ℝ)
  rw [hprod, Measure.prod_apply hsR]
  have hslice : ∀ x : ℝ,
      volume (Prod.mk x ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ c}) =
        if 0 ≤ x ∧ x ≤ c then ENNReal.ofReal (c - x) else 0 := by
    intro x
    by_cases hx : 0 ≤ x ∧ x ≤ c
    · have hI : Prod.mk x ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ c} =
          Icc 0 (c - x) := by
        ext y
        change (0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ c) ↔ 0 ≤ y ∧ y ≤ c - x
        constructor
        · intro h
          exact ⟨h.2.1, by linarith [h.2.2]⟩
        · intro h
          exact ⟨hx.1, h.1, by linarith [h.2]⟩
      rw [hI, Real.volume_Icc, sub_zero, if_pos hx]
    · have : Prod.mk x ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ c} = ∅ := by
        ext y
        simp only [mem_preimage, mem_setOf_eq, mem_empty_iff_false, iff_false]
        intro h
        exact hx ⟨h.1, by linarith [h.2.2]⟩
      rw [this, measure_empty, if_neg hx]
  simp_rw [hslice]
  have : (∫⁻ x, (if 0 ≤ x ∧ x ≤ c then ENNReal.ofReal (c - x) else 0)) =
      ∫⁻ x in Icc 0 c, ENNReal.ofReal (c - x) := by
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ Icc (0 : ℝ) c
    · have hx' : 0 ≤ x ∧ x ≤ c := mem_Icc.mp hx
      simp [hx, hx']
    · have : ¬ (0 ≤ x ∧ x ≤ c) := by
        simpa [mem_Icc] using hx
      simp [hx, this]
  rw [this]
  have hnn : 0 ≤ᵐ[volume.restrict (Icc 0 c)] fun x : ℝ => c - x :=
    ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => sub_nonneg.mpr hx.2)
  have hint : IntegrableOn (fun x : ℝ => c - x) (Icc 0 c) :=
    (continuous_const.sub continuous_id).continuousOn.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  have : ∫ x in Icc 0 c, (c - x) = c ^ 2 / 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hc.le]
    simpa using integral_inner_simplex c
  rw [this]

lemma volume_stdSimp2 (c : ℝ) :
    volume (stdSimp2 c) = ENNReal.ofReal (if 0 ≤ c then c ^ 2 / 2 else 0) := by
  by_cases hc : c ≤ 0
  · have hsub : stdSimp2 c ⊆ ({0} : Set (Fin 2 → ℝ)) := by
      intro y hy
      simp only [stdSimp2, mem_setOf_eq] at hy
      have hy0 : y 0 = 0 := le_antisymm (by linarith [hy.2.1, hy.2.2]) hy.1
      have hy1 : y 1 = 0 := le_antisymm (by linarith [hy.1, hy.2.2]) hy.2.1
      ext i; fin_cases i <;> simp [hy0, hy1]
    have hvol : volume (stdSimp2 c) = 0 :=
      measure_mono_null hsub (measure_singleton _)
    simp [hvol]
    split_ifs with h0
    · have : c = 0 := le_antisymm hc h0
      simp [this]
    · rfl
  · push_neg at hc
    rw [volume_eq_image_stdSimp2, volume_s_eq_sR, volume_sR c hc]
    simp [hc.le]

def stdSimp3pi : Set (Fin 3 → ℝ) :=
  {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 ∧ x 0 + x 1 + x 2 ≤ 1}

lemma isClosed_stdSimp3pi : IsClosed stdSimp3pi := by
  have : stdSimp3pi =
      {x : Fin 3 → ℝ | 0 ≤ x 0} ∩ {x | 0 ≤ x 1} ∩ {x | 0 ≤ x 2} ∩
        {x | x 0 + x 1 + x 2 ≤ 1} := by
    ext; simp [stdSimp3pi]; constructor <;> intro h <;> tauto
  rw [this]
  refine IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_
  · exact isClosed_le continuous_const (continuous_apply 0)
  · exact isClosed_le continuous_const (continuous_apply 1)
  · exact isClosed_le continuous_const (continuous_apply 2)
  · exact isClosed_le ((continuous_apply 0).add (continuous_apply 1) |>.add (continuous_apply 2))
      continuous_const

lemma image_stdSimp3pi :
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0 '' stdSimp3pi =
      {p : ℝ × (Fin 2 → ℝ) | 0 ≤ p.1 ∧ p.2 ∈ stdSimp2 (1 - p.1)} := by
  set e0 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx0 : 0 ≤ x 0 := hx.1
    have hx1 : 0 ≤ x 1 := hx.2.1
    have hx2 : 0 ≤ x 2 := hx.2.2.1
    have hxs : x 0 + x 1 + x 2 ≤ 1 := hx.2.2.2
    have hfst : (e0 x).1 = x 0 := by
      simp [e0, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv]
    have h0 : (e0 x).2 0 = x 1 := by
      simp [e0, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.tail]
    have h1 : (e0 x).2 1 = x 2 := by
      simp [e0, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.tail]
    refine ⟨by rwa [hfst], ?_⟩
    change 0 ≤ (e0 x).2 0 ∧ 0 ≤ (e0 x).2 1 ∧ (e0 x).2 0 + (e0 x).2 1 ≤ 1 - (e0 x).1
    rw [h0, h1, hfst]
    exact ⟨hx1, hx2, by linarith⟩
  · intro hp
    refine ⟨e0.symm p, ?_, e0.apply_symm_apply p⟩
    have h0 : (e0.symm p) 0 = p.1 := by
      simp [e0, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    have h1 : (e0.symm p) 1 = p.2 0 := by
      simp [e0, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    have h2 : (e0.symm p) 2 = p.2 1 := by
      have hEq : e0.symm p = Fin.insertNth 0 p.1 p.2 := by
        simp [e0, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
      rw [hEq]
      rfl
    rcases hp with ⟨hp0, a, b, c⟩
    refine ⟨by rwa [h0], by rwa [h1], by rwa [h2], ?_⟩
    rw [h0, h1, h2]
    linarith

lemma volume_eq_image_stdSimp3pi :
    volume stdSimp3pi =
      volume {p : ℝ × (Fin 2 → ℝ) | 0 ≤ p.1 ∧ p.2 ∈ stdSimp2 (1 - p.1)} := by
  rw [← image_stdSimp3pi]
  set e0 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
  have h := hp.measure_preimage isClosed_stdSimp3pi.nullMeasurableSet
  rw [← MeasurableEquiv.image_eq_preimage_symm] at h
  exact h.symm

lemma isClosed_stdSimp3prod :
    IsClosed {p : ℝ × (Fin 2 → ℝ) | 0 ≤ p.1 ∧ p.2 ∈ stdSimp2 (1 - p.1)} := by
  have : {p : ℝ × (Fin 2 → ℝ) | 0 ≤ p.1 ∧ p.2 ∈ stdSimp2 (1 - p.1)} =
      {p | 0 ≤ p.1} ∩ {p | 0 ≤ p.2 0} ∩ {p | 0 ≤ p.2 1} ∩
        {p | p.1 + p.2 0 + p.2 1 ≤ 1} := by
    ext p
    simp only [mem_inter_iff, mem_setOf_eq, stdSimp2]
    constructor
    · intro h
      refine ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, ?_⟩
      linarith [h.2.2.2]
    · intro h
      refine ⟨h.1.1.1, h.1.1.2, h.1.2, ?_⟩
      linarith [h.2]
  rw [this]
  refine IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_
  · exact isClosed_le continuous_const continuous_fst
  · exact isClosed_le continuous_const ((continuous_apply 0).comp continuous_snd)
  · exact isClosed_le continuous_const ((continuous_apply 1).comp continuous_snd)
  · have hsum : Continuous fun p : ℝ × (Fin 2 → ℝ) => p.1 + p.2 0 + p.2 1 := by
      fun_prop
    exact isClosed_le hsum continuous_const

lemma volume_stdSimp3pi : volume stdSimp3pi = ENNReal.ofReal (1 / 6) := by
  rw [volume_eq_image_stdSimp3pi]
  have hs : MeasurableSet {p : ℝ × (Fin 2 → ℝ) | 0 ≤ p.1 ∧ p.2 ∈ stdSimp2 (1 - p.1)} :=
    isClosed_stdSimp3prod.measurableSet
  have hprod : (volume : Measure (ℝ × (Fin 2 → ℝ))) = volume.prod volume :=
    volume_eq_prod (α := ℝ) (β := Fin 2 → ℝ)
  rw [hprod, Measure.prod_apply hs]
  have hslice : ∀ t : ℝ,
      volume (Prod.mk t ⁻¹' {p : ℝ × (Fin 2 → ℝ) | 0 ≤ p.1 ∧ p.2 ∈ stdSimp2 (1 - p.1)}) =
        if 0 ≤ t ∧ t ≤ 1 then volume (stdSimp2 (1 - t)) else 0 := by
    intro t
    by_cases ht : 0 ≤ t ∧ t ≤ 1
    · have : Prod.mk t ⁻¹' {p : ℝ × (Fin 2 → ℝ) | 0 ≤ p.1 ∧ p.2 ∈ stdSimp2 (1 - p.1)} =
          stdSimp2 (1 - t) := by
        ext y
        change (0 ≤ t ∧ y ∈ stdSimp2 (1 - t)) ↔ y ∈ stdSimp2 (1 - t)
        constructor
        · intro h; exact h.2
        · intro h; exact ⟨ht.1, h⟩
      rw [this, if_pos ht]
    · have : Prod.mk t ⁻¹' {p : ℝ × (Fin 2 → ℝ) | 0 ≤ p.1 ∧ p.2 ∈ stdSimp2 (1 - p.1)} = ∅ := by
        ext y
        simp only [mem_preimage, mem_setOf_eq, mem_empty_iff_false, iff_false]
        intro h
        exact ht ⟨h.1, by
          have hy := h.2
          simp [stdSimp2] at hy
          linarith [hy.1, hy.2.1, hy.2.2]⟩
      rw [this, measure_empty, if_neg ht]
  simp_rw [hslice]
  have : (∫⁻ t, (if 0 ≤ t ∧ t ≤ 1 then volume (stdSimp2 (1 - t)) else 0)) =
      ∫⁻ t in Icc (0 : ℝ) 1, volume (stdSimp2 (1 - t)) := by
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · have ht' : 0 ≤ t ∧ t ≤ 1 := mem_Icc.mp ht
      simp [ht, ht']
    · have : ¬ (0 ≤ t ∧ t ≤ 1) := by simpa [mem_Icc] using ht
      simp [ht, this]
  rw [this]
  have hval : ∀ t ∈ Icc (0 : ℝ) 1,
      volume (stdSimp2 (1 - t)) = ENNReal.ofReal ((1 - t) ^ 2 / 2) := by
    intro t ht
    rw [volume_stdSimp2]
    have : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    simp [this]
  have heq : (∫⁻ t in Icc (0 : ℝ) 1, volume (stdSimp2 (1 - t))) =
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal ((1 - t) ^ 2 / 2) := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    exact hval t ht
  rw [heq]
  have hnn : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)] fun t : ℝ => (1 - t) ^ 2 / 2 :=
    ae_restrict_of_forall_mem measurableSet_Icc (fun _ _ => by positivity)
  have hint : IntegrableOn (fun t : ℝ => (1 - t) ^ 2 / 2) (Icc 0 1) := by
    have hcont : Continuous (fun t : ℝ => (1 - t) ^ 2 / 2) := by fun_prop
    exact hcont.continuousOn.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  have : ∫ t in Icc (0 : ℝ) 1, (1 - t) ^ 2 / 2 = (1 / 6 : ℝ) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hfun : (fun t : ℝ => (1 - t) ^ 2 / 2) = fun t => (2 : ℝ)⁻¹ * (1 - t) ^ 2 := by
      funext t; ring
    rw [hfun, intervalIntegral.integral_const_mul]
    have hcomp := integral_comp_sub_left (f := fun u : ℝ => u ^ 2) (a := (0 : ℝ)) (b := 1) (d := 1)
    simp only [_root_.sub_self, sub_zero] at hcomp
    have hp := integral_pow (a := (0 : ℝ)) (b := 1) (n := 2)
    rw [hcomp, hp]
    norm_num
  rw [this]

lemma volume_stdSimp3 : volume stdSimp3 = ENNReal.ofReal (1 / 6) := by
  have hpre : stdSimp3 = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹' stdSimp3pi := by
    ext p; simp [stdSimp3, stdSimp3pi]
  rw [hpre]
  have hp : MeasurePreserving (@WithLp.ofLp 2 (Fin 3 → ℝ)) :=
    PiLp.volume_preserving_ofLp (ι := Fin 3)
  have := hp.measure_preimage isClosed_stdSimp3pi.nullMeasurableSet
  rw [this, volume_stdSimp3pi]

noncomputable def linOfCols (u v w : ℝ³) : ℝ³ →ₗ[ℝ] ℝ³ where
  toFun p := p 0 • u + p 1 • v + p 2 • w
  map_add' p q := by
    simp [add_smul, PiLp.add_apply]
    abel
  map_smul' c p := by
    simp [smul_smul, smul_add, PiLp.smul_apply]

lemma det_linOfCols (u v w : ℝ³) :
    LinearMap.det (linOfCols u v w) = Matrix.det (coordMatrix u v w) := by
  have hmat :
      LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin 3)) (PiLp.basisFun 2 ℝ (Fin 3))
        (linOfCols u v w) = coordMatrix u v w := by
    ext i j
    simp only [LinearMap.toMatrix_apply, PiLp.basisFun_repr, PiLp.basisFun_apply]
    fin_cases j <;> fin_cases i <;> simp [coordMatrix, linOfCols, Pi.single]
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 3)), hmat]

lemma volume_vadd (o : ℝ³) (s : Set ℝ³) :
    volume ((fun q : ℝ³ => o + q) '' s) = volume s := by
  have : (fun q : ℝ³ => o + q) '' s = (fun q : ℝ³ => -o + q) ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      simp [hq]
    · intro hx
      refine ⟨-o + x, hx, ?_⟩
      simp
  rw [this, measure_preimage_add]

lemma volume_affine_simplex (o u v w : ℝ³) :
    volume ((fun p : ℝ³ => o + linOfCols u v w p) '' stdSimp3) =
      ENNReal.ofReal (|Matrix.det (coordMatrix u v w)| / 6) := by
  have htrans : (fun p : ℝ³ => o + linOfCols u v w p) '' stdSimp3 =
      (fun q => o + q) '' (linOfCols u v w '' stdSimp3) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨linOfCols u v w p, ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
  rw [htrans, volume_vadd, Measure.addHaar_image_linearMap, det_linOfCols, volume_stdSimp3]
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring


/-- The affine parametrization of the large tetrahedron. -/
noncomputable def largeTetParam (p : ℝ³) : ℝ³ :=
  largeTetVertex 0 + linOfCols
    (largeTetVertex 1 - largeTetVertex 0)
    (largeTetVertex 2 - largeTetVertex 0)
    (largeTetVertex 3 - largeTetVertex 0) p

lemma largeTetParam_eq (p : ℝ³) :
    largeTetParam p =
      (1 - p 0 - p 1 - p 2) • largeTetVertex 0 +
        p 0 • largeTetVertex 1 + p 1 • largeTetVertex 2 + p 2 • largeTetVertex 3 := by
  simp only [largeTetParam, linOfCols, LinearMap.coe_mk, AddHom.coe_mk]
  simp [smul_sub, sub_smul, add_smul]
  abel

lemma largeTetParam_image :
    largeTetParam '' stdSimp3 = largeTet := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [largeTetParam_eq]
    refine mem_convexHull_of_exists_fintype
      (fun i : Fin 4 => if i = 0 then 1 - p 0 - p 1 - p 2
        else if i = 1 then p 0 else if i = 2 then p 1 else p 2)
      largeTetVertex ?_ ?_ (fun i => mem_range_self i) ?_
    · intro i
      fin_cases i <;> simp [stdSimp3] at hp ⊢ <;> linarith
    · simp [Fin.sum_univ_four]; ring
    · simp [Fin.sum_univ_four]
  · intro hx
    have hx' : x ∈ largeTetHS := by
      rw [← largeTet_eq_HS]; exact hx
    refine ⟨pt (bary 1 x) (bary 2 x) (bary 3 x), ?_, ?_⟩
    · simp [stdSimp3, pt]
      exact ⟨bary_nonneg_of_mem_HS hx' 1, bary_nonneg_of_mem_HS hx' 2,
        bary_nonneg_of_mem_HS hx' 3, by
          have hsum := sum_bary x
          have h0 := bary_nonneg_of_mem_HS hx' 0
          linarith⟩
    · rw [largeTetParam_eq]
      simp [pt]
      have hrec := bary_reconstruction x
      have hsum := sum_bary x
      have hb0 : 1 - bary 1 x - bary 2 x - bary 3 x = bary 0 x := by linarith
      rw [hb0, hrec]

lemma volume_largeTet : volume largeTet = ENNReal.ofReal 72 := by
  rw [← largeTetParam_image]
  have : largeTetParam = fun p => largeTetVertex 0 +
      linOfCols (largeTetVertex 1 - largeTetVertex 0)
        (largeTetVertex 2 - largeTetVertex 0)
        (largeTetVertex 3 - largeTetVertex 0) p := rfl
  rw [this, volume_affine_simplex, det_largeTet_edges]
  norm_num


/-- The small corner tetrahedron at vertex `i` of the large tetrahedron. -/
def smallTet (i : Fin 4) : Set ℝ³ :=
  {p | p ∈ largeTet ∧ (2 / 3 : ℝ) ≤ bary i p}

lemma smallTet_eq_HS (i : Fin 4) :
    smallTet i = {p | p ∈ largeTetHS ∧ (2 / 3 : ℝ) ≤ bary i p} := by
  simp [smallTet, largeTet_eq_HS]

lemma bary_affine (i : Fin 4) (x y : ℝ³) (a b : ℝ) (hab : a + b = 1) :
    bary i (a • x + b • y) = a * bary i x + b * bary i y := by
  simp only [bary, evenForm_add, evenForm_smul]
  calc
    (a * evenForm i x + b * evenForm i y + 3) / 12
      = (a * (evenForm i x + 3) + b * (evenForm i y + 3)) / 12 := by
          have : a * 3 + b * 3 = 3 := by rw [← add_mul, hab, one_mul]
          linarith
    _ = a * ((evenForm i x + 3) / 12) + b * ((evenForm i y + 3) / 12) := by
          field_simp

lemma convex_smallTet (i : Fin 4) : Convex ℝ (smallTet i) := by
  rw [smallTet_eq_HS]
  refine convex_iff_forall_pos.mpr ?_
  intro x hx y hy a b ha hb hab
  have hxL := hx.1
  have hyL := hy.1
  have hL : a • x + b • y ∈ largeTetHS :=
    convex_largeTetHS hxL hyL ha.le hb.le hab
  refine ⟨hL, ?_⟩
  rw [bary_affine i x y a b hab]
  nlinarith [hx.2, hy.2]

lemma smallTet_subset_largeTet (i : Fin 4) : smallTet i ⊆ largeTet :=
  fun _ hp => hp.1

/-- Affine parametrization of the small tet at vertex 0. -/
noncomputable def smallTet0Param (p : ℝ³) : ℝ³ :=
  largeTetVertex 0 + linOfCols
    ((1 / 3 : ℝ) • (largeTetVertex 1 - largeTetVertex 0))
    ((1 / 3 : ℝ) • (largeTetVertex 2 - largeTetVertex 0))
    ((1 / 3 : ℝ) • (largeTetVertex 3 - largeTetVertex 0)) p

lemma det_smallTet0 :
    Matrix.det (coordMatrix
      ((1 / 3 : ℝ) • (largeTetVertex 1 - largeTetVertex 0))
      ((1 / 3 : ℝ) • (largeTetVertex 2 - largeTetVertex 0))
      ((1 / 3 : ℝ) • (largeTetVertex 3 - largeTetVertex 0))) = -16 := by
  have hsmul : ∀ (c : ℝ) (u v w : ℝ³),
      coordMatrix (c • u) (c • v) (c • w) = c • coordMatrix u v w := by
    intro c u v w
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coordMatrix, PiLp.smul_apply]
  rw [hsmul, Matrix.det_smul, det_largeTet_edges]
  norm_num

lemma volume_smallTet0_param :
    volume (smallTet0Param '' stdSimp3) = ENNReal.ofReal (8 / 3) := by
  have : smallTet0Param = fun p => largeTetVertex 0 +
      linOfCols
        ((1 / 3 : ℝ) • (largeTetVertex 1 - largeTetVertex 0))
        ((1 / 3 : ℝ) • (largeTetVertex 2 - largeTetVertex 0))
        ((1 / 3 : ℝ) • (largeTetVertex 3 - largeTetVertex 0)) p := rfl
  rw [this, volume_affine_simplex, det_smallTet0]
  norm_num


lemma smallTet0Param_eq (p : ℝ³) :
    smallTet0Param p =
      largeTetVertex 0 +
        (p 0 / 3) • (largeTetVertex 1 - largeTetVertex 0) +
        (p 1 / 3) • (largeTetVertex 2 - largeTetVertex 0) +
        (p 2 / 3) • (largeTetVertex 3 - largeTetVertex 0) := by
  simp only [smallTet0Param, linOfCols, LinearMap.coe_mk, AddHom.coe_mk]
  have h0 : p 0 • (1 / 3 : ℝ) • (largeTetVertex 1 - largeTetVertex 0) =
      (p 0 / 3) • (largeTetVertex 1 - largeTetVertex 0) := by
    rw [smul_smul]; congr 1; ring
  have h1 : p 1 • (1 / 3 : ℝ) • (largeTetVertex 2 - largeTetVertex 0) =
      (p 1 / 3) • (largeTetVertex 2 - largeTetVertex 0) := by
    rw [smul_smul]; congr 1; ring
  have h2 : p 2 • (1 / 3 : ℝ) • (largeTetVertex 3 - largeTetVertex 0) =
      (p 2 / 3) • (largeTetVertex 3 - largeTetVertex 0) := by
    rw [smul_smul]; congr 1; ring
  rw [h0, h1, h2]
  abel

lemma bary_largeTetVertex (k i : Fin 4) :
    bary k (largeTetVertex i) = if k = i then (1 : ℝ) else 0 := by
  simp only [bary, evenForm_largeTetVertex]
  split_ifs <;> norm_num

lemma bary_smallTet0Param (k : Fin 4) (p : ℝ³) :
    bary k (smallTet0Param p) =
      bary k (largeTetVertex 0) +
        (p 0 / 3) * ((if k = 1 then (1 : ℝ) else 0) - if k = 0 then 1 else 0) +
        (p 1 / 3) * ((if k = 2 then (1 : ℝ) else 0) - if k = 0 then 1 else 0) +
        (p 2 / 3) * ((if k = 3 then (1 : ℝ) else 0) - if k = 0 then 1 else 0) := by
  rw [smallTet0Param_eq]
  -- Reassociate to `(((v0 + a) + b) + c)` so `bary_vertex_sub` applies.
  have hassoc :
      largeTetVertex 0 +
          (p 0 / 3) • (largeTetVertex 1 - largeTetVertex 0) +
          (p 1 / 3) • (largeTetVertex 2 - largeTetVertex 0) +
          (p 2 / 3) • (largeTetVertex 3 - largeTetVertex 0) =
        ((largeTetVertex 0 + (p 0 / 3) • (largeTetVertex 1 - largeTetVertex 0)) +
          (p 1 / 3) • (largeTetVertex 2 - largeTetVertex 0)) +
          (p 2 / 3) • (largeTetVertex 3 - largeTetVertex 0) := by
    abel
  rw [hassoc, bary_vertex_sub 3 0 k, bary_vertex_sub 2 0 k, bary_vertex_sub 1 0 k]

lemma bary0_smallTet0Param (p : ℝ³) :
    bary 0 (smallTet0Param p) = 1 - (p 0 + p 1 + p 2) / 3 := by
  rw [bary_smallTet0Param, bary_largeTetVertex]
  simp [ite_true, ite_false]
  ring

lemma bary1_smallTet0Param (p : ℝ³) :
    bary 1 (smallTet0Param p) = p 0 / 3 := by
  rw [bary_smallTet0Param, bary_largeTetVertex]
  simp [ite_true, ite_false]

lemma bary2_smallTet0Param (p : ℝ³) :
    bary 2 (smallTet0Param p) = p 1 / 3 := by
  rw [bary_smallTet0Param, bary_largeTetVertex]
  simp [ite_true, ite_false]

lemma bary3_smallTet0Param (p : ℝ³) :
    bary 3 (smallTet0Param p) = p 2 / 3 := by
  rw [bary_smallTet0Param, bary_largeTetVertex]
  simp [ite_true, ite_false]

lemma reconstruction_from_vertex0 (x : ℝ³) :
    x = largeTetVertex 0 +
      bary 1 x • (largeTetVertex 1 - largeTetVertex 0) +
      bary 2 x • (largeTetVertex 2 - largeTetVertex 0) +
      bary 3 x • (largeTetVertex 3 - largeTetVertex 0) := by
  have hrec := bary_reconstruction x
  have hsum := sum_bary x
  have hb0 : bary 0 x = 1 - bary 1 x - bary 2 x - bary 3 x := by linarith
  have hexp :
      bary 0 x • largeTetVertex 0 + bary 1 x • largeTetVertex 1 +
          bary 2 x • largeTetVertex 2 + bary 3 x • largeTetVertex 3 =
        largeTetVertex 0 +
          bary 1 x • (largeTetVertex 1 - largeTetVertex 0) +
          bary 2 x • (largeTetVertex 2 - largeTetVertex 0) +
          bary 3 x • (largeTetVertex 3 - largeTetVertex 0) := by
    rw [hb0]
    have hsmul :
        (1 - bary 1 x - bary 2 x - bary 3 x) • largeTetVertex 0 =
          largeTetVertex 0 - bary 1 x • largeTetVertex 0 - bary 2 x • largeTetVertex 0 -
            bary 3 x • largeTetVertex 0 := by
      rw [show 1 - bary 1 x - bary 2 x - bary 3 x =
            1 - (bary 1 x + bary 2 x + bary 3 x) by ring]
      rw [sub_smul, one_smul, add_smul, add_smul]
      abel
    rw [hsmul]
    simp only [smul_sub]
    abel
  rw [← hexp, hrec]

lemma smallTet0Param_image : smallTet0Param '' stdSimp3 = smallTet 0 := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp0 : 0 ≤ p 0 := hp.1
    have hp1 : 0 ≤ p 1 := hp.2.1
    have hp2 : 0 ≤ p 2 := hp.2.2.1
    have hps : p 0 + p 1 + p 2 ≤ 1 := hp.2.2.2
    have hxL : smallTet0Param p ∈ largeTet := by
      rw [largeTet_eq_HS]
      intro j
      have h0 : 0 ≤ bary 0 (smallTet0Param p) := by
        rw [bary0_smallTet0Param]; linarith
      have h1 : 0 ≤ bary 1 (smallTet0Param p) := by
        rw [bary1_smallTet0Param]; linarith
      have h2 : 0 ≤ bary 2 (smallTet0Param p) := by
        rw [bary2_smallTet0Param]; linarith
      have h3 : 0 ≤ bary 3 (smallTet0Param p) := by
        rw [bary3_smallTet0Param]; linarith
      have : 0 ≤ bary j (smallTet0Param p) := by
        fin_cases j <;> assumption
      simp only [bary] at this
      linarith
    refine ⟨hxL, ?_⟩
    rw [bary0_smallTet0Param]
    linarith
  · intro hx
    have hxL : x ∈ largeTetHS := by
      rw [← largeTet_eq_HS]; exact hx.1
    have hb0 : (2 / 3 : ℝ) ≤ bary 0 x := hx.2
    refine ⟨pt (3 * bary 1 x) (3 * bary 2 x) (3 * bary 3 x), ?_, ?_⟩
    · simp [stdSimp3, pt]
      have h1 := bary_nonneg_of_mem_HS hxL 1
      have h2 := bary_nonneg_of_mem_HS hxL 2
      have h3 := bary_nonneg_of_mem_HS hxL 3
      have hsum := sum_bary x
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · set q := pt (3 * bary 1 x) (3 * bary 2 x) (3 * bary 3 x)
      rw [smallTet0Param_eq]
      have hp0 : q 0 = 3 * bary 1 x := by simp [q, pt]
      have hp1 : q 1 = 3 * bary 2 x := by simp [q, pt]
      have hp2 : q 2 = 3 * bary 3 x := by simp [q, pt]
      rw [hp0, hp1, hp2]
      have hdiv1 : (3 * bary 1 x) / 3 = bary 1 x := by ring
      have hdiv2 : (3 * bary 2 x) / 3 = bary 2 x := by ring
      have hdiv3 : (3 * bary 3 x) / 3 = bary 3 x := by ring
      rw [hdiv1, hdiv2, hdiv3, ← reconstruction_from_vertex0 x]

lemma volume_smallTet0 : volume (smallTet 0) = ENNReal.ofReal (8 / 3) := by
  rw [← smallTet0Param_image, volume_smallTet0_param]


/-! ### Volumes of the remaining corner tetrahedra via coordinate sign flips -/

/-- Linear map `(x,y,z) ↦ (εx x, εy y, εz z)`. -/
noncomputable def coordScale (εx εy εz : ℝ) : ℝ³ →ₗ[ℝ] ℝ³ where
  toFun p := pt (εx * p 0) (εy * p 1) (εz * p 2)
  map_add' p q := by
    ext i; fin_cases i <;> (simp [pt, PiLp.add_apply]; ring)
  map_smul' c p := by
    ext i; fin_cases i <;> (simp [pt, PiLp.smul_apply]; ring)

lemma coordScale_apply (εx εy εz : ℝ) (p : ℝ³) :
    coordScale εx εy εz p = pt (εx * p 0) (εy * p 1) (εz * p 2) :=
  rfl

lemma det_coordScale (εx εy εz : ℝ) :
    LinearMap.det (coordScale εx εy εz) = εx * εy * εz := by
  have hmat :
      LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin 3)) (PiLp.basisFun 2 ℝ (Fin 3))
        (coordScale εx εy εz) = !![εx, 0, 0; 0, εy, 0; 0, 0, εz] := by
    ext i j
    simp only [LinearMap.toMatrix_apply, PiLp.basisFun_repr, PiLp.basisFun_apply,
      coordScale_apply]
    fin_cases i <;> fin_cases j <;> simp [pt, Pi.single]
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 3)), hmat, Matrix.det_fin_three]
  simp

lemma volume_coordScale_image (εx εy εz : ℝ) (s : Set ℝ³) :
    volume (coordScale εx εy εz '' s) =
      ENNReal.ofReal |εx * εy * εz| * volume s := by
  rw [Measure.addHaar_image_linearMap, det_coordScale]

lemma evenForm_coordScale_yz_0 (p : ℝ³) :
    evenForm 0 (coordScale 1 (-1) (-1) p) = evenForm 1 p := by
  simp [evenForm, evenSign, form111, coordScale_apply, pt]

lemma evenForm_coordScale_yz_1 (p : ℝ³) :
    evenForm 1 (coordScale 1 (-1) (-1) p) = evenForm 0 p := by
  simp [evenForm, evenSign, form111, coordScale_apply, pt]

lemma evenForm_coordScale_yz_2 (p : ℝ³) :
    evenForm 2 (coordScale 1 (-1) (-1) p) = evenForm 3 p := by
  simp [evenForm, evenSign, form111, coordScale_apply, pt]

lemma evenForm_coordScale_yz_3 (p : ℝ³) :
    evenForm 3 (coordScale 1 (-1) (-1) p) = evenForm 2 p := by
  simp [evenForm, evenSign, form111, coordScale_apply, pt]

lemma evenForm_coordScale_xz_0 (p : ℝ³) :
    evenForm 0 (coordScale (-1) 1 (-1) p) = evenForm 2 p := by
  simp [evenForm, evenSign, form111, coordScale_apply, pt]

lemma evenForm_coordScale_xz_1 (p : ℝ³) :
    evenForm 1 (coordScale (-1) 1 (-1) p) = evenForm 3 p := by
  simp [evenForm, evenSign, form111, coordScale_apply, pt]

lemma evenForm_coordScale_xz_2 (p : ℝ³) :
    evenForm 2 (coordScale (-1) 1 (-1) p) = evenForm 0 p := by
  simp [evenForm, evenSign, form111, coordScale_apply, pt]

lemma evenForm_coordScale_xz_3 (p : ℝ³) :
    evenForm 3 (coordScale (-1) 1 (-1) p) = evenForm 1 p := by
  simp [evenForm, evenSign, form111, coordScale_apply, pt]

lemma evenForm_coordScale_xy_0 (p : ℝ³) :
    evenForm 0 (coordScale (-1) (-1) 1 p) = evenForm 3 p := by
  simp [evenForm, evenSign, form111, coordScale_apply, pt]

lemma evenForm_coordScale_xy_1 (p : ℝ³) :
    evenForm 1 (coordScale (-1) (-1) 1 p) = evenForm 2 p := by
  simp [evenForm, evenSign, form111, coordScale_apply, pt]

lemma evenForm_coordScale_xy_2 (p : ℝ³) :
    evenForm 2 (coordScale (-1) (-1) 1 p) = evenForm 1 p := by
  simp [evenForm, evenSign, form111, coordScale_apply, pt]

lemma evenForm_coordScale_xy_3 (p : ℝ³) :
    evenForm 3 (coordScale (-1) (-1) 1 p) = evenForm 0 p := by
  simp [evenForm, evenSign, form111, coordScale_apply, pt]

lemma bary_coordScale_yz_0 (p : ℝ³) :
    bary 0 (coordScale 1 (-1) (-1) p) = bary 1 p := by
  simp only [bary, evenForm_coordScale_yz_0]

lemma bary_coordScale_yz_1 (p : ℝ³) :
    bary 1 (coordScale 1 (-1) (-1) p) = bary 0 p := by
  simp only [bary, evenForm_coordScale_yz_1]

lemma bary_coordScale_xz_0 (p : ℝ³) :
    bary 0 (coordScale (-1) 1 (-1) p) = bary 2 p := by
  simp only [bary, evenForm_coordScale_xz_0]

lemma bary_coordScale_xz_2 (p : ℝ³) :
    bary 2 (coordScale (-1) 1 (-1) p) = bary 0 p := by
  simp only [bary, evenForm_coordScale_xz_2]

lemma bary_coordScale_xy_0 (p : ℝ³) :
    bary 0 (coordScale (-1) (-1) 1 p) = bary 3 p := by
  simp only [bary, evenForm_coordScale_xy_0]

lemma bary_coordScale_xy_3 (p : ℝ³) :
    bary 3 (coordScale (-1) (-1) 1 p) = bary 0 p := by
  simp only [bary, evenForm_coordScale_xy_3]

lemma coordScale_yz_mem_largeTet {p : ℝ³} (hp : p ∈ largeTet) :
    coordScale 1 (-1) (-1) p ∈ largeTet := by
  rw [largeTet_eq_HS] at hp ⊢
  intro i
  have hp0 := hp 0; have hp1 := hp 1; have hp2 := hp 2; have hp3 := hp 3
  match i with
  | 0 => rw [evenForm_coordScale_yz_0]; exact hp1
  | 1 => rw [evenForm_coordScale_yz_1]; exact hp0
  | 2 => rw [evenForm_coordScale_yz_2]; exact hp3
  | 3 => rw [evenForm_coordScale_yz_3]; exact hp2

lemma coordScale_xz_mem_largeTet {p : ℝ³} (hp : p ∈ largeTet) :
    coordScale (-1) 1 (-1) p ∈ largeTet := by
  rw [largeTet_eq_HS] at hp ⊢
  intro i
  have hp0 := hp 0; have hp1 := hp 1; have hp2 := hp 2; have hp3 := hp 3
  match i with
  | 0 => rw [evenForm_coordScale_xz_0]; exact hp2
  | 1 => rw [evenForm_coordScale_xz_1]; exact hp3
  | 2 => rw [evenForm_coordScale_xz_2]; exact hp0
  | 3 => rw [evenForm_coordScale_xz_3]; exact hp1

lemma coordScale_xy_mem_largeTet {p : ℝ³} (hp : p ∈ largeTet) :
    coordScale (-1) (-1) 1 p ∈ largeTet := by
  rw [largeTet_eq_HS] at hp ⊢
  intro i
  have hp0 := hp 0; have hp1 := hp 1; have hp2 := hp 2; have hp3 := hp 3
  match i with
  | 0 => rw [evenForm_coordScale_xy_0]; exact hp3
  | 1 => rw [evenForm_coordScale_xy_1]; exact hp2
  | 2 => rw [evenForm_coordScale_xy_2]; exact hp1
  | 3 => rw [evenForm_coordScale_xy_3]; exact hp0

lemma coordScale_involutive_yz (p : ℝ³) :
    coordScale 1 (-1) (-1) (coordScale 1 (-1) (-1) p) = p := by
  ext i; fin_cases i <;> simp [coordScale_apply, pt]

lemma coordScale_involutive_xz (p : ℝ³) :
    coordScale (-1) 1 (-1) (coordScale (-1) 1 (-1) p) = p := by
  ext i; fin_cases i <;> simp [coordScale_apply, pt]

lemma coordScale_involutive_xy (p : ℝ³) :
    coordScale (-1) (-1) 1 (coordScale (-1) (-1) 1 p) = p := by
  ext i; fin_cases i <;> simp [coordScale_apply, pt]

lemma coordScale_yz_image_smallTet0 :
    coordScale 1 (-1) (-1) '' smallTet 0 = smallTet 1 := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨coordScale_yz_mem_largeTet hp.1, ?_⟩
    rw [bary_coordScale_yz_1]
    exact hp.2
  · intro hq
    refine ⟨coordScale 1 (-1) (-1) q, ⟨coordScale_yz_mem_largeTet hq.1, ?_⟩,
      coordScale_involutive_yz q⟩
    rw [bary_coordScale_yz_0]
    exact hq.2

lemma coordScale_xz_image_smallTet0 :
    coordScale (-1) 1 (-1) '' smallTet 0 = smallTet 2 := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨coordScale_xz_mem_largeTet hp.1, ?_⟩
    rw [bary_coordScale_xz_2]
    exact hp.2
  · intro hq
    refine ⟨coordScale (-1) 1 (-1) q, ⟨coordScale_xz_mem_largeTet hq.1, ?_⟩,
      coordScale_involutive_xz q⟩
    rw [bary_coordScale_xz_0]
    exact hq.2

lemma coordScale_xy_image_smallTet0 :
    coordScale (-1) (-1) 1 '' smallTet 0 = smallTet 3 := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨coordScale_xy_mem_largeTet hp.1, ?_⟩
    rw [bary_coordScale_xy_3]
    exact hp.2
  · intro hq
    refine ⟨coordScale (-1) (-1) 1 q, ⟨coordScale_xy_mem_largeTet hq.1, ?_⟩,
      coordScale_involutive_xy q⟩
    rw [bary_coordScale_xy_0]
    exact hq.2

lemma volume_smallTet (i : Fin 4) : volume (smallTet i) = ENNReal.ofReal (8 / 3) := by
  match i with
  | 0 => exact volume_smallTet0
  | 1 =>
      rw [← coordScale_yz_image_smallTet0, volume_coordScale_image, volume_smallTet0]
      norm_num
  | 2 =>
      rw [← coordScale_xz_image_smallTet0, volume_coordScale_image, volume_smallTet0]
      norm_num
  | 3 =>
      rw [← coordScale_xy_image_smallTet0, volume_coordScale_image, volume_smallTet0]
      norm_num

/-! ### Partition of the large tetrahedron and volume of `T` -/

lemma smallTet_pairwise_disjoint {i j : Fin 4} (hij : i ≠ j) :
    smallTet i ∩ smallTet j = ∅ := by
  ext p
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
  intro ⟨hi, hj⟩
  have hxL : p ∈ largeTetHS := by
    rw [← largeTet_eq_HS]; exact hi.1
  have hsum := sum_bary p
  have h0 := bary_nonneg_of_mem_HS hxL 0
  have h1 := bary_nonneg_of_mem_HS hxL 1
  have h2 := bary_nonneg_of_mem_HS hxL 2
  have h3 := bary_nonneg_of_mem_HS hxL 3
  have hi' : (2 / 3 : ℝ) ≤ bary i p := hi.2
  have hj' : (2 / 3 : ℝ) ≤ bary j p := hj.2
  match i, j with
  | 0, 0 => exact (hij rfl).elim
  | 0, 1 => linarith [h0, h1, h2, h3, hsum, hi', hj']
  | 0, 2 => linarith [h0, h1, h2, h3, hsum, hi', hj']
  | 0, 3 => linarith [h0, h1, h2, h3, hsum, hi', hj']
  | 1, 0 => linarith [h0, h1, h2, h3, hsum, hi', hj']
  | 1, 1 => exact (hij rfl).elim
  | 1, 2 => linarith [h0, h1, h2, h3, hsum, hi', hj']
  | 1, 3 => linarith [h0, h1, h2, h3, hsum, hi', hj']
  | 2, 0 => linarith [h0, h1, h2, h3, hsum, hi', hj']
  | 2, 1 => linarith [h0, h1, h2, h3, hsum, hi', hj']
  | 2, 2 => exact (hij rfl).elim
  | 2, 3 => linarith [h0, h1, h2, h3, hsum, hi', hj']
  | 3, 0 => linarith [h0, h1, h2, h3, hsum, hi', hj']
  | 3, 1 => linarith [h0, h1, h2, h3, hsum, hi', hj']
  | 3, 2 => linarith [h0, h1, h2, h3, hsum, hi', hj']
  | 3, 3 => exact (hij rfl).elim

lemma T_eq_bary :
    truncatedTetrahedron = {p | p ∈ largeTet ∧ ∀ i : Fin 4, bary i p ≤ 2 / 3} := by
  rw [← truncatedTetrahedronHS_eq]
  ext p
  constructor
  · intro hp
    exact ⟨truncatedTetrahedronHS_subset_largeTet hp,
      fun i => bary_le_two_thirds_of_mem_HS hp i⟩
  · intro ⟨hL, hb⟩
    rw [mem_truncatedHS_iff]
    intro i
    exact ⟨bary_nonneg_of_mem_HS (by rwa [largeTet_eq_HS] at hL) i, hb i⟩

lemma largeTet_eq_T_union_small :
    largeTet = truncatedTetrahedron ∪ ⋃ i : Fin 4, smallTet i := by
  ext p
  constructor
  · intro hp
    by_cases h : ∀ i : Fin 4, bary i p ≤ 2 / 3
    · left
      rw [T_eq_bary]
      exact ⟨hp, h⟩
    · right
      simp only [mem_iUnion]
      push_neg at h
      obtain ⟨i, hi⟩ := h
      exact ⟨i, hp, le_of_lt hi⟩
  · intro hp
    rcases hp with hp | hp
    · have : p ∈ truncatedTetrahedronHS := by
        rwa [truncatedTetrahedronHS_eq]
      exact truncatedTetrahedronHS_subset_largeTet this
    · simp only [mem_iUnion] at hp
      obtain ⟨i, hi⟩ := hp
      exact hi.1

noncomputable def evenFormLM (i : Fin 4) : ℝ³ →ₗ[ℝ] ℝ where
  toFun := evenForm i
  map_add' := evenForm_add i
  map_smul' c p := evenForm_smul i c p

lemma evenFormLM_ne_zero (i : Fin 4) : evenFormLM i ≠ 0 := by
  intro h
  have : evenForm i (largeTetVertex i) = 0 := by
    simpa [evenFormLM] using LinearMap.congr_fun h (largeTetVertex i)
  rw [evenForm_largeTetVertex, if_pos rfl] at this
  norm_num at this

lemma volume_evenForm_eq (i : Fin 4) (c : ℝ) :
    volume {p : ℝ³ | evenForm i p = c} = 0 := by
  let p0 : ℝ³ := (c / 9) • largeTetVertex i
  have hp0 : evenForm i p0 = c := by
    rw [evenForm_smul, evenForm_largeTetVertex, if_pos rfl]
    ring
  have himg :
      {p : ℝ³ | evenForm i p = c} = (fun q : ℝ³ => p0 + q) '' {q | evenForm i q = 0} := by
    ext p
    constructor
    · intro h
      refine ⟨p - p0, ?_, by abel⟩
      simp only [mem_setOf_eq] at h ⊢
      rw [evenForm_sub, h, hp0]
      ring
    · rintro ⟨q, hq, rfl⟩
      simp only [mem_setOf_eq] at hq ⊢
      rw [evenForm_add, hq, hp0]
      ring
  rw [himg, volume_vadd]
  have hker : {q : ℝ³ | evenForm i q = 0} = (evenFormLM i).ker := by
    ext; simp [evenFormLM, LinearMap.mem_ker]
  rw [hker]
  refine Measure.addHaar_submodule volume (evenFormLM i).ker ?_
  intro htop
  exact evenFormLM_ne_zero i (LinearMap.ker_eq_top.mp htop)

lemma volume_bary_eq (i : Fin 4) (c : ℝ) :
    volume {p : ℝ³ | bary i p = c} = 0 := by
  have : {p : ℝ³ | bary i p = c} = {p | evenForm i p = 12 * c - 3} := by
    ext p
    simp only [mem_setOf_eq, bary]
    constructor <;> intro h <;> linarith
  rw [this]
  exact volume_evenForm_eq i _

lemma volume_T_inter_smallTet (i : Fin 4) :
    volume (truncatedTetrahedron ∩ smallTet i) = 0 := by
  refine measure_mono_null (t := {p : ℝ³ | bary i p = 2 / 3}) ?_ (volume_bary_eq i (2 / 3))
  intro p hp
  have hpT : p ∈ truncatedTetrahedronHS := by
    rw [truncatedTetrahedronHS_eq]; exact hp.1
  have hle := bary_le_two_thirds_of_mem_HS hpT i
  have hge := hp.2.2
  simp only [mem_setOf_eq]
  linarith

lemma isClosed_smallTet (i : Fin 4) : IsClosed (smallTet i) := by
  have : smallTet i = largeTet ∩ {p | (2 / 3 : ℝ) ≤ bary i p} := rfl
  rw [this]
  refine IsClosed.inter ?_ ?_
  · exact (Finite.isCompact_convexHull (finite_range largeTetVertex)).isClosed
  · have hb : Continuous (bary i) :=
      ((evenForm_continuous i).add continuous_const).div_const 12
    exact isClosed_le continuous_const hb

lemma volume_union_smallTet :
    volume (⋃ i : Fin 4, smallTet i) = ENNReal.ofReal (32 / 3) := by
  rw [measure_iUnion]
  · rw [tsum_fintype]
    have : (∑ i : Fin 4, volume (smallTet i)) = ∑ _i : Fin 4, ENNReal.ofReal (8 / 3) := by
      refine Finset.sum_congr rfl ?_
      intro i _; exact volume_smallTet i
    rw [this, Finset.sum_const, Finset.card_univ]
    simp only [Fintype.card_fin]
    rw [nsmul_eq_mul]
    have h4 : ((4 : ℕ) : ENNReal) = ENNReal.ofReal 4 :=
      (ENNReal.ofReal_natCast 4).symm
    rw [h4, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  · intro i j hij
    exact disjoint_iff_inter_eq_empty.mpr (smallTet_pairwise_disjoint hij)
  · exact fun i => (isClosed_smallTet i).measurableSet

lemma volume_T_inter_union_small :
    volume (truncatedTetrahedron ∩ ⋃ i : Fin 4, smallTet i) = 0 := by
  have : truncatedTetrahedron ∩ ⋃ i : Fin 4, smallTet i =
      ⋃ i : Fin 4, truncatedTetrahedron ∩ smallTet i := by
    ext p
    simp [mem_iUnion, mem_inter_iff]
  rw [this]
  exact measure_iUnion_null fun i => volume_T_inter_smallTet i

lemma volume_truncatedTetrahedron :
    volume truncatedTetrahedron = ENNReal.ofReal (184 / 3) := by
  have ht : MeasurableSet (⋃ i : Fin 4, smallTet i) :=
    MeasurableSet.iUnion fun i => (isClosed_smallTet i).measurableSet
  have hsplit := measure_union_add_inter (μ := volume)
    (s := truncatedTetrahedron) ht
  rw [← largeTet_eq_T_union_small, volume_largeTet, volume_T_inter_union_small,
      add_zero, volume_union_smallTet] at hsplit
  have hfin : ENNReal.ofReal (32 / 3) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsub : volume truncatedTetrahedron =
      ENNReal.ofReal 72 - ENNReal.ofReal (32 / 3) := by
    have := congrArg (fun x : ENNReal => x - ENNReal.ofReal (32 / 3)) hsplit.symm
    simpa [ENNReal.add_sub_cancel_right hfin] using this
  rw [hsub, ← ENNReal.ofReal_sub 72 (by norm_num : (0 : ℝ) ≤ 32 / 3)]
  norm_num


/-! ### The Jiao–Torquato dimer and lattice -/

/-- Partner offset: the point reflection of `T` through `(-1,-1,-1)` is `dimerOffset - T`. -/
noncomputable def dimerOffset : ℝ³ := pt (-2) (-2) (-2)

lemma evenForm_dimerOffset :
    evenForm 0 dimerOffset = -6 ∧ evenForm 1 dimerOffset = 2 ∧
    evenForm 2 dimerOffset = 2 ∧ evenForm 3 dimerOffset = 2 := by
  simp [dimerOffset, evenForm_pt, evenSign]; norm_num

lemma evenForm_sub_offset (i : Fin 4) (p : ℝ³) :
    evenForm i (dimerOffset - p) = evenForm i dimerOffset - evenForm i p :=
  evenForm_sub i _ _

/-- The convex dimer `T ∪ (dimerOffset - T)`. -/
def dimerHS : Set ℝ³ :=
  {p | -11 ≤ evenForm 0 p ∧ evenForm 0 p ≤ 5 ∧
        -3 ≤ evenForm 1 p ∧ evenForm 1 p ≤ 5 ∧
        -3 ≤ evenForm 2 p ∧ evenForm 2 p ≤ 5 ∧
        -3 ≤ evenForm 3 p ∧ evenForm 3 p ≤ 5}

lemma mem_T_of_mem_dimer_and_e0 (p : ℝ³) (hp : p ∈ dimerHS) (h : -3 ≤ evenForm 0 p) :
    p ∈ truncatedTetrahedron := by
  rw [← truncatedTetrahedronHS_eq]
  intro i
  match i with
  | 0 => exact ⟨h, hp.2.1⟩
  | 1 => exact ⟨hp.2.2.1, hp.2.2.2.1⟩
  | 2 => exact ⟨hp.2.2.2.2.1, hp.2.2.2.2.2.1⟩
  | 3 => exact ⟨hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2⟩

lemma mem_partner_of_mem_dimer_and_e0 (p : ℝ³) (hp : p ∈ dimerHS)
    (h : evenForm 0 p ≤ -3) :
    dimerOffset - p ∈ truncatedTetrahedron := by
  rw [← truncatedTetrahedronHS_eq]
  intro i
  have he := evenForm_sub_offset i p
  have hd := evenForm_dimerOffset
  match i with
  | 0 =>
      rw [he, hd.1]
      constructor <;> linarith [hp.1, h]
  | 1 =>
      rw [he, hd.2.1]
      constructor <;> linarith [hp.2.2.1, hp.2.2.2.1]
  | 2 =>
      rw [he, hd.2.2.1]
      constructor <;> linarith [hp.2.2.2.2.1, hp.2.2.2.2.2.1]
  | 3 =>
      rw [he, hd.2.2.2]
      constructor <;> linarith [hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2]

lemma T_subset_dimerHS : truncatedTetrahedron ⊆ dimerHS := by
  intro p hp
  rw [← truncatedTetrahedronHS_eq] at hp
  have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
  refine ⟨?_, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2⟩
  linarith [h0.1]

lemma partner_subset_dimerHS :
    (fun p : ℝ³ => dimerOffset - p) '' truncatedTetrahedron ⊆ dimerHS := by
  intro q hq
  rcases hq with ⟨p, hp, rfl⟩
  rw [← truncatedTetrahedronHS_eq] at hp
  have h0 := hp 0; have h1 := hp 1; have h2 := hp 2; have h3 := hp 3
  have he0 := evenForm_sub_offset 0 p
  have he1 := evenForm_sub_offset 1 p
  have he2 := evenForm_sub_offset 2 p
  have he3 := evenForm_sub_offset 3 p
  have hd := evenForm_dimerOffset
  simp only [dimerHS, mem_setOf_eq]
  rw [he0, he1, he2, he3, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

lemma dimerHS_eq_union :
    dimerHS = truncatedTetrahedron ∪ (fun p : ℝ³ => dimerOffset - p) '' truncatedTetrahedron := by
  ext p
  constructor
  · intro hp
    by_cases h : -3 ≤ evenForm 0 p
    · exact Or.inl (mem_T_of_mem_dimer_and_e0 p hp h)
    · have : evenForm 0 p ≤ -3 := le_of_lt (lt_of_not_ge h)
      refine Or.inr ⟨dimerOffset - p, mem_partner_of_mem_dimer_and_e0 p hp this, ?_⟩
      abel
  · intro hp
    rcases hp with hp | hp
    · exact T_subset_dimerHS hp
    · exact partner_subset_dimerHS hp

/-- The three generators of the Jiao–Torquato lattice. -/
noncomputable def jtGen : Fin 3 → ℝ³
  | 0 => pt (-4) (-8 / 3) (4 / 3)
  | 1 => pt (-4 / 3) 4 (8 / 3)
  | 2 => pt (-8 / 3) (4 / 3) (-4)

lemma evenForm_jtGen0_0 : evenForm 0 (jtGen 0) = -16 / 3 := by
  simp [jtGen, evenForm_pt, evenSign]; norm_num
lemma evenForm_jtGen0_1 : evenForm 1 (jtGen 0) = -8 / 3 := by
  simp [jtGen, evenForm_pt, evenSign]; norm_num
lemma evenForm_jtGen0_2 : evenForm 2 (jtGen 0) = 0 := by
  simp [jtGen, evenForm_pt, evenSign]; norm_num
lemma evenForm_jtGen0_3 : evenForm 3 (jtGen 0) = 8 := by
  simp [jtGen, evenForm_pt, evenSign]; norm_num

lemma evenForm_jtGen1_0 : evenForm 0 (jtGen 1) = 16 / 3 := by
  simp [jtGen, evenForm_pt, evenSign]; norm_num
lemma evenForm_jtGen1_1 : evenForm 1 (jtGen 1) = -8 := by
  simp [jtGen, evenForm_pt, evenSign]; norm_num
lemma evenForm_jtGen1_2 : evenForm 2 (jtGen 1) = 8 / 3 := by
  simp [jtGen, evenForm_pt, evenSign]; norm_num
lemma evenForm_jtGen1_3 : evenForm 3 (jtGen 1) = 0 := by
  simp [jtGen, evenForm_pt, evenSign]; norm_num

lemma evenForm_jtGen2_0 : evenForm 0 (jtGen 2) = -16 / 3 := by
  simp [jtGen, evenForm_pt, evenSign]; norm_num
lemma evenForm_jtGen2_1 : evenForm 1 (jtGen 2) = 0 := by
  simp [jtGen, evenForm_pt, evenSign]; norm_num
lemma evenForm_jtGen2_2 : evenForm 2 (jtGen 2) = 8 := by
  simp [jtGen, evenForm_pt, evenSign]; norm_num
lemma evenForm_jtGen2_3 : evenForm 3 (jtGen 2) = -8 / 3 := by
  simp [jtGen, evenForm_pt, evenSign]; norm_num

/-- A general lattice vector `a • v₁ + b • v₂ + c • v₃`. -/
noncomputable def jtLatticeVec (a b c : ℤ) : ℝ³ :=
  (a : ℝ) • jtGen 0 + (b : ℝ) • jtGen 1 + (c : ℝ) • jtGen 2

lemma evenForm0_jtLatticeVec (a b c : ℤ) :
    evenForm 0 (jtLatticeVec a b c) = (16 / 3 : ℝ) * (-a + b - c) := by
  simp only [jtLatticeVec, evenForm_add, evenForm_smul]
  rw [evenForm_jtGen0_0, evenForm_jtGen1_0, evenForm_jtGen2_0]
  push_cast
  ring

lemma evenForm1_jtLatticeVec (a b c : ℤ) :
    evenForm 1 (jtLatticeVec a b c) = (-8 : ℝ) * ((a : ℝ) / 3 + b) := by
  simp only [jtLatticeVec, evenForm_add, evenForm_smul]
  rw [evenForm_jtGen0_1, evenForm_jtGen1_1, evenForm_jtGen2_1]
  push_cast
  ring

lemma evenForm2_jtLatticeVec (a b c : ℤ) :
    evenForm 2 (jtLatticeVec a b c) = (8 : ℝ) * ((b : ℝ) / 3 + c) := by
  simp only [jtLatticeVec, evenForm_add, evenForm_smul]
  rw [evenForm_jtGen0_2, evenForm_jtGen1_2, evenForm_jtGen2_2]
  push_cast
  ring

lemma evenForm3_jtLatticeVec (a b c : ℤ) :
    evenForm 3 (jtLatticeVec a b c) = (8 : ℝ) * ((a : ℝ) - c / 3) := by
  simp only [jtLatticeVec, evenForm_add, evenForm_smul]
  rw [evenForm_jtGen0_3, evenForm_jtGen1_3, evenForm_jtGen2_3]
  push_cast
  ring

lemma abs_add_three_le (x y z : ℤ) : |x + y + z| ≤ |x| + |y| + |z| :=
  (abs_add_three x y z)

/-- Arithmetic criterion: a nonzero integer triple forces a wide even-form. -/
lemma jt_int_criterion (a b c : ℤ) (hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    3 ≤ |a + 3 * b| ∨ 3 ≤ |b + 3 * c| ∨ 3 ≤ |3 * a - c| ∨ 3 ≤ |b - a - c| := by
  by_contra H
  simp only [not_or] at H
  have hab : |a + 3 * b| ≤ 2 := Int.le_sub_one_of_lt (lt_of_not_ge H.1)
  have hbc : |b + 3 * c| ≤ 2 := Int.le_sub_one_of_lt (lt_of_not_ge H.2.1)
  have hac : |3 * a - c| ≤ 2 := Int.le_sub_one_of_lt (lt_of_not_ge H.2.2.1)
  have hsum : |b - a - c| ≤ 2 := Int.le_sub_one_of_lt (lt_of_not_ge H.2.2.2)
  -- Identity: 26 b = 9(a+3b) - 3(3a-c) - (b+3c)
  have hid : (26 : ℤ) * b =
      9 * (a + 3 * b) - 3 * (3 * a - c) - (b + 3 * c) := by ring
  have h26 : |(26 : ℤ) * b| ≤ 26 := by
    rw [hid]
    have h1 : |9 * (a + 3 * b)| ≤ 18 := by
      have := mul_le_mul_of_nonneg_left hab (by norm_num : (0 : ℤ) ≤ 9)
      simpa [abs_mul] using this
    have h2 : |3 * (3 * a - c)| ≤ 6 := by
      have := mul_le_mul_of_nonneg_left hac (by norm_num : (0 : ℤ) ≤ 3)
      simpa [abs_mul] using this
    have : |9 * (a + 3 * b) - 3 * (3 * a - c) - (b + 3 * c)| ≤
        |9 * (a + 3 * b)| + |3 * (3 * a - c)| + |b + 3 * c| := by
      calc |9 * (a + 3 * b) - 3 * (3 * a - c) - (b + 3 * c)|
          = |9 * (a + 3 * b) + (-(3 * (3 * a - c))) + (-(b + 3 * c))| := by
              ring
        _ ≤ |9 * (a + 3 * b)| + |-(3 * (3 * a - c))| + |-(b + 3 * c)| :=
              abs_add_three_le _ _ _
        _ = |9 * (a + 3 * b)| + |3 * (3 * a - c)| + |b + 3 * c| := by
              rw [abs_neg, abs_neg]
    linarith
  have hb : |b| ≤ 1 := by
    have : |(26 : ℤ) * b| = 26 * |b| := by simp [abs_mul]
    rw [this] at h26
    nlinarith
  have hcbound : |c| ≤ 1 := by
    have : |3 * c| ≤ |b + 3 * c| + |b| := by
      have h := abs_add_three_le (b + 3 * c) (-b) 0
      have : b + 3 * c + -b + 0 = 3 * c := by ring
      simpa [this, abs_neg] using h
    have : |3 * c| = 3 * |c| := by simp [abs_mul]
    nlinarith
  have ha : |a| ≤ 1 := by
    have : |3 * a| ≤ |3 * a - c| + |c| := by
      have h := abs_add_three_le (3 * a - c) c 0
      have : 3 * a - c + c + 0 = 3 * a := by ring
      simpa [this] using h
    have : |3 * a| = 3 * |a| := by simp [abs_mul]
    nlinarith
  have habs : a ∈ Finset.Icc (-1 : ℤ) 1 ∧ b ∈ Finset.Icc (-1 : ℤ) 1 ∧
      c ∈ Finset.Icc (-1 : ℤ) 1 := by
    refine ⟨Finset.mem_Icc.mpr ⟨neg_le_of_abs_le ha, le_of_abs_le ha⟩,
            Finset.mem_Icc.mpr ⟨neg_le_of_abs_le hb, le_of_abs_le hb⟩,
            Finset.mem_Icc.mpr ⟨neg_le_of_abs_le hcbound, le_of_abs_le hcbound⟩⟩
  have hexh :
      ∀ a ∈ Finset.Icc (-1 : ℤ) 1, ∀ b ∈ Finset.Icc (-1 : ℤ) 1,
        ∀ c ∈ Finset.Icc (-1 : ℤ) 1,
          a = 0 ∧ b = 0 ∧ c = 0 ∨
            3 ≤ |a + 3 * b| ∨ 3 ≤ |b + 3 * c| ∨ 3 ≤ |3 * a - c| ∨ 3 ≤ |b - a - c| := by
    decide
  have := hexh a habs.1 b habs.2.1 c habs.2.2
  rcases this with h | h | h | h | h
  · exact hne h
  · linarith
  · linarith
  · linarith
  · linarith




/-- Gradient vector of `evenForm i` (three coordinates `±1`). -/
noncomputable def evenGrad (i : Fin 4) : ℝ³ :=
  pt (evenSign i).1 (evenSign i).2.1 (evenSign i).2.2

lemma evenForm_evenGrad (i : Fin 4) : evenForm i (evenGrad i) = 3 := by
  match i with
  | 0 => simp [evenGrad, evenForm_pt, evenSign]; norm_num
  | 1 => simp [evenGrad, evenForm_pt, evenSign]; norm_num
  | 2 => simp [evenGrad, evenForm_pt, evenSign]; norm_num
  | 3 => simp [evenGrad, evenForm_pt, evenSign]; norm_num

lemma evenForm_neg_evenGrad (i : Fin 4) : evenForm i (-evenGrad i) = -3 := by
  have : -evenGrad i = (-1 : ℝ) • evenGrad i := by simp
  rw [this, evenForm_smul, evenForm_evenGrad]; ring

lemma exists_small_step_in_open {p : ℝ³} {U : Set ℝ³} (hU : IsOpen U) (hp : p ∈ U)
    (v : ℝ³) : ∃ t : ℝ, 0 < t ∧ p + t • v ∈ U := by
  rw [Metric.isOpen_iff] at hU
  obtain ⟨ε, εpos, hε⟩ := hU p hp
  by_cases hv : v = 0
  · refine ⟨1, one_pos, hε ?_⟩
    simpa [hv, Metric.mem_ball] using εpos
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let t := ε / (2 * ‖v‖)
    have htpos : 0 < t := div_pos εpos (mul_pos two_pos hvpos)
    refine ⟨t, htpos, hε ?_⟩
    have hnorm : ‖t • v‖ = t * ‖v‖ := by
      rw [norm_smul, Real.norm_of_nonneg htpos.le]
    have hval : t * ‖v‖ = ε / 2 := by
      simp [t]; field_simp
    simp [Metric.mem_ball, dist_eq_norm, hnorm, hval]
    linarith

lemma evenForm_shift (i : Fin 4) (p : ℝ³) (t : ℝ) (v : ℝ³) :
    evenForm i (p + t • v) = evenForm i p + t * evenForm i v := by
  rw [evenForm_add, evenForm_smul]


lemma interior_dimer_not_on_e0_lo {p : ℝ³} (hp : p ∈ interior dimerHS) :
    evenForm 0 p ≠ -11 := by
  intro heq
  rw [mem_interior] at hp
  rcases hp with ⟨U, hUsub, hUopen, hpU⟩
  obtain ⟨t, htpos, htU⟩ := exists_small_step_in_open hUopen hpU (-evenGrad 0)
  have htD : p + t • (-evenGrad 0) ∈ dimerHS := hUsub htU
  have hval : evenForm 0 (p + t • (-evenGrad 0)) = -11 - 3 * t := by
    rw [evenForm_shift, heq, evenForm_neg_evenGrad]; ring
  have : -11 ≤ evenForm 0 (p + t • (-evenGrad 0)) := htD.1
  rw [hval] at this
  nlinarith

lemma interior_dimer_not_on_e0_hi {p : ℝ³} (hp : p ∈ interior dimerHS) :
    evenForm 0 p ≠ 5 := by
  intro heq
  rw [mem_interior] at hp
  rcases hp with ⟨U, hUsub, hUopen, hpU⟩
  obtain ⟨t, htpos, htU⟩ := exists_small_step_in_open hUopen hpU (evenGrad 0)
  have htD : p + t • evenGrad 0 ∈ dimerHS := hUsub htU
  have hval : evenForm 0 (p + t • evenGrad 0) = 5 + 3 * t := by
    rw [evenForm_shift, heq, evenForm_evenGrad]; ring
  have : evenForm 0 (p + t • evenGrad 0) ≤ 5 := htD.2.1
  rw [hval] at this
  nlinarith

lemma interior_dimer_not_on_ei_lo {p : ℝ³} (hp : p ∈ interior dimerHS) (i : Fin 4)
    (hi : i ≠ 0) : evenForm i p ≠ -3 := by
  intro heq
  rw [mem_interior] at hp
  rcases hp with ⟨U, hUsub, hUopen, hpU⟩
  obtain ⟨t, htpos, htU⟩ := exists_small_step_in_open hUopen hpU (-evenGrad i)
  have htD : p + t • (-evenGrad i) ∈ dimerHS := hUsub htU
  have hval : evenForm i (p + t • (-evenGrad i)) = -3 - 3 * t := by
    rw [evenForm_shift, heq, evenForm_neg_evenGrad]; ring
  have hlo : -3 ≤ evenForm i (p + t • (-evenGrad i)) := by
    match i with
    | 0 => exact (hi rfl).elim
    | 1 => exact htD.2.2.1
    | 2 => exact htD.2.2.2.2.1
    | 3 => exact htD.2.2.2.2.2.2.1
  rw [hval] at hlo
  nlinarith

lemma interior_dimer_not_on_ei_hi {p : ℝ³} (hp : p ∈ interior dimerHS) (i : Fin 4)
    (hi : i ≠ 0) : evenForm i p ≠ 5 := by
  intro heq
  rw [mem_interior] at hp
  rcases hp with ⟨U, hUsub, hUopen, hpU⟩
  obtain ⟨t, htpos, htU⟩ := exists_small_step_in_open hUopen hpU (evenGrad i)
  have htD : p + t • evenGrad i ∈ dimerHS := hUsub htU
  have hval : evenForm i (p + t • evenGrad i) = 5 + 3 * t := by
    rw [evenForm_shift, heq, evenForm_evenGrad]; ring
  have hhi : evenForm i (p + t • evenGrad i) ≤ 5 := by
    match i with
    | 0 => exact (hi rfl).elim
    | 1 => exact htD.2.2.2.1
    | 2 => exact htD.2.2.2.2.2.1
    | 3 => exact htD.2.2.2.2.2.2.2
  rw [hval] at hhi
  nlinarith

lemma interior_dimerHS_strict {p : ℝ³} (hp : p ∈ interior dimerHS) :
    -11 < evenForm 0 p ∧ evenForm 0 p < 5 ∧
    -3 < evenForm 1 p ∧ evenForm 1 p < 5 ∧
    -3 < evenForm 2 p ∧ evenForm 2 p < 5 ∧
    -3 < evenForm 3 p ∧ evenForm 3 p < 5 := by
  have hpD : p ∈ dimerHS := interior_subset hp
  refine ⟨lt_of_le_of_ne hpD.1 (interior_dimer_not_on_e0_lo hp).symm,
          lt_of_le_of_ne hpD.2.1 (interior_dimer_not_on_e0_hi hp),
          lt_of_le_of_ne hpD.2.2.1 (interior_dimer_not_on_ei_lo hp 1 (by decide)).symm,
          lt_of_le_of_ne hpD.2.2.2.1 (interior_dimer_not_on_ei_hi hp 1 (by decide)),
          lt_of_le_of_ne hpD.2.2.2.2.1 (interior_dimer_not_on_ei_lo hp 2 (by decide)).symm,
          lt_of_le_of_ne hpD.2.2.2.2.2.1 (interior_dimer_not_on_ei_hi hp 2 (by decide)),
          lt_of_le_of_ne hpD.2.2.2.2.2.2.1 (interior_dimer_not_on_ei_lo hp 3 (by decide)).symm,
          lt_of_le_of_ne hpD.2.2.2.2.2.2.2 (interior_dimer_not_on_ei_hi hp 3 (by decide))⟩

lemma jtLatticeVec_evenForm_wide {a b c : ℤ} (hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    16 ≤ |evenForm 0 (jtLatticeVec a b c)| ∨
    8 ≤ |evenForm 1 (jtLatticeVec a b c)| ∨
    8 ≤ |evenForm 2 (jtLatticeVec a b c)| ∨
    8 ≤ |evenForm 3 (jtLatticeVec a b c)| := by
  have hcrit := jt_int_criterion a b c hne
  rw [evenForm0_jtLatticeVec, evenForm1_jtLatticeVec, evenForm2_jtLatticeVec,
      evenForm3_jtLatticeVec]
  -- hcrit cases: |a+3b|≥3, |b+3c|≥3, |3a-c|≥3, |b-a-c|≥3
  -- correspond to wide evenForm 1, 2, 3, 0 respectively.
  rcases hcrit with h | h | h | h
  · -- |a+3b| ≥ 3 ⇒ |evenForm 1| ≥ 8
    right; left
    have habs : |(-8 : ℝ) * ((a : ℝ) / 3 + ↑b)| = 8 * |((a : ℝ) / 3 + ↑b)| := by
      rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    rw [habs]
    have : (1 : ℝ) ≤ |((a : ℝ) / 3 + ↑b)| := by
      have : |(a : ℝ) / 3 + ↑b| = |(a + 3 * b : ℝ)| / 3 := by
        have : (a : ℝ) / 3 + ↑b = (↑a + 3 * ↑b) / 3 := by ring
        rw [this, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      rw [this]
      have : (3 : ℝ) ≤ |(a + 3 * b : ℝ)| := by norm_cast
      linarith
    nlinarith
  · -- |b+3c| ≥ 3 ⇒ |evenForm 2| ≥ 8
    right; right; left
    have habs : |(8 : ℝ) * ((b : ℝ) / 3 + ↑c)| = 8 * |((b : ℝ) / 3 + ↑c)| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    rw [habs]
    have : (1 : ℝ) ≤ |((b : ℝ) / 3 + ↑c)| := by
      have : |(b : ℝ) / 3 + ↑c| = |(b + 3 * c : ℝ)| / 3 := by
        have : (b : ℝ) / 3 + ↑c = (↑b + 3 * ↑c) / 3 := by ring
        rw [this, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      rw [this]
      have : (3 : ℝ) ≤ |(b + 3 * c : ℝ)| := by norm_cast
      linarith
    nlinarith
  · -- |3a-c| ≥ 3 ⇒ |evenForm 3| ≥ 8
    right; right; right
    have habs : |(8 : ℝ) * ((a : ℝ) - ↑c / 3)| = 8 * |((a : ℝ) - ↑c / 3)| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    rw [habs]
    have : (1 : ℝ) ≤ |((a : ℝ) - ↑c / 3)| := by
      have : |(a : ℝ) - ↑c / 3| = |(3 * a - c : ℝ)| / 3 := by
        have : (a : ℝ) - ↑c / 3 = (3 * ↑a - ↑c) / 3 := by ring
        rw [this, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      rw [this]
      have : (3 : ℝ) ≤ |(3 * a - c : ℝ)| := by norm_cast
      linarith
    nlinarith
  · -- |b-a-c| ≥ 3 ⇒ |evenForm 0| ≥ 16
    left
    have habs : |(16 / 3 : ℝ) * (-(a : ℝ) + ↑b - ↑c)| =
        (16 / 3) * |(-(a : ℝ) + ↑b - ↑c)| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16 / 3)]
    rw [habs]
    have : (3 : ℝ) ≤ |(-(a : ℝ) + ↑b - ↑c)| := by
      have : |(-(a : ℝ) + ↑b - ↑c)| = |(b - a - c : ℝ)| := by
        congr 1; push_cast; ring
      rw [this]; norm_cast
    nlinarith

/-- Two distinct lattice translates of the dimer have disjoint interiors. -/
lemma dimer_lattice_interiors_disjoint {a b c : ℤ}
    (hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    interior dimerHS ∩ (fun p : ℝ³ => p + jtLatticeVec a b c) '' interior dimerHS = ∅ := by
  ext p
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
  intro ⟨hp, hq⟩
  rcases hq with ⟨q, hq, hpq⟩
  have hp' := interior_dimerHS_strict hp
  have hq' := interior_dimerHS_strict hq
  have hlam := jtLatticeVec_evenForm_wide hne
  -- p = q + λ so evenForm i p = evenForm i q + evenForm i λ
  have heq (i : Fin 4) : evenForm i p = evenForm i q + evenForm i (jtLatticeVec a b c) := by
    have : p = q + jtLatticeVec a b c := hpq.symm
    rw [this, evenForm_add]
  have hdiff (i : Fin 4) : evenForm i (jtLatticeVec a b c) = evenForm i p - evenForm i q := by
    linarith [heq i]
  rcases hlam with h | h | h | h
  · have : |evenForm 0 p - evenForm 0 q| < 16 := by
      have hp0 : -11 < evenForm 0 p ∧ evenForm 0 p < 5 := ⟨hp'.1, hp'.2.1⟩
      have hq0 : -11 < evenForm 0 q ∧ evenForm 0 q < 5 := ⟨hq'.1, hq'.2.1⟩
      have : -16 < evenForm 0 p - evenForm 0 q ∧ evenForm 0 p - evenForm 0 q < 16 := by
        constructor <;> linarith
      exact abs_lt.mpr this
    rw [← hdiff 0] at this
    linarith
  · have : |evenForm 1 p - evenForm 1 q| < 8 := by
      have : -8 < evenForm 1 p - evenForm 1 q ∧ evenForm 1 p - evenForm 1 q < 8 := by
        constructor <;> linarith [hp'.2.2.1, hp'.2.2.2.1, hq'.2.2.1, hq'.2.2.2.1]
      exact abs_lt.mpr this
    rw [← hdiff 1] at this
    linarith
  · have : |evenForm 2 p - evenForm 2 q| < 8 := by
      have : -8 < evenForm 2 p - evenForm 2 q ∧ evenForm 2 p - evenForm 2 q < 8 := by
        constructor <;> linarith [hp'.2.2.2.2.1, hp'.2.2.2.2.2.1, hq'.2.2.2.2.1, hq'.2.2.2.2.2.1]
      exact abs_lt.mpr this
    rw [← hdiff 2] at this
    linarith
  · have : |evenForm 3 p - evenForm 3 q| < 8 := by
      have : -8 < evenForm 3 p - evenForm 3 q ∧ evenForm 3 p - evenForm 3 q < 8 := by
        constructor <;> linarith [hp'.2.2.2.2.2.2.1, hp'.2.2.2.2.2.2.2,
          hq'.2.2.2.2.2.2.1, hq'.2.2.2.2.2.2.2]
      exact abs_lt.mpr this
    rw [← hdiff 3] at this
    linarith


lemma interior_subset_interior_of_subset {s t : Set ℝ³} (h : s ⊆ t) :
    interior s ⊆ interior t :=
  interior_mono h

lemma T_subset_dimer : truncatedTetrahedron ⊆ dimerHS :=
  T_subset_dimerHS

lemma partner_image_subset_dimer :
    (fun p : ℝ³ => dimerOffset - p) '' truncatedTetrahedron ⊆ dimerHS :=
  partner_subset_dimerHS

/-- Point reflection through `(-1,-1,-1)`, sending `T` to the dimer partner. -/
noncomputable def partnerIsom : ℝ³ ≃ᵢ ℝ³ :=
  (AffineIsometryEquiv.pointReflection ℝ (pt (-1) (-1) (-1))).toIsometryEquiv

lemma partnerIsom_apply (p : ℝ³) : partnerIsom p = dimerOffset - p := by
  ext i
  simp only [partnerIsom, AffineIsometryEquiv.coe_toIsometryEquiv,
    AffineIsometryEquiv.pointReflection_apply, vsub_eq_sub, vadd_eq_add]
  have : (pt (-1) (-1) (-1) - p + pt (-1) (-1) (-1)) i =
      2 * pt (-1) (-1) (-1) i - p i := by
    simp [PiLp.add_apply, PiLp.sub_apply]; ring
  rw [this]
  simp [dimerOffset, pt]
  fin_cases i <;> simp [pt, PiLp.sub_apply]

lemma partnerIsom_image :
    partnerIsom '' truncatedTetrahedron =
      (fun p : ℝ³ => dimerOffset - p) '' truncatedTetrahedron := by
  ext; simp [partnerIsom_apply]

/-- Translation by a Jiao–Torquato lattice vector. -/
noncomputable def jtTranslate (a b c : ℤ) : ℝ³ ≃ᵢ ℝ³ :=
  (AffineIsometryEquiv.constVAdd ℝ ℝ³ (jtLatticeVec a b c)).toIsometryEquiv

lemma jtTranslate_apply (a b c : ℤ) (p : ℝ³) :
    jtTranslate a b c p = p + jtLatticeVec a b c := by
  simp [jtTranslate, AffineIsometryEquiv.coe_toIsometryEquiv,
    AffineIsometryEquiv.constVAdd, vadd_eq_add]
  abel

/-- Partner copy at lattice site `(a,b,c)`. -/
noncomputable def jtPartnerIsom (a b c : ℤ) : ℝ³ ≃ᵢ ℝ³ :=
  partnerIsom.trans (jtTranslate a b c)

lemma jtPartnerIsom_apply (a b c : ℤ) (p : ℝ³) :
    jtPartnerIsom a b c p = partnerIsom p + jtLatticeVec a b c := by
  simp [jtPartnerIsom, IsometryEquiv.trans_apply, jtTranslate_apply]

lemma interior_image_isometry (f : ℝ³ ≃ᵢ ℝ³) (s : Set ℝ³) :
    interior (f '' s) = f '' interior s :=
  (f.toHomeomorph.image_interior s).symm

lemma interior_T_subset_interior_dimer :
    interior truncatedTetrahedron ⊆ interior dimerHS :=
  interior_mono T_subset_dimerHS

lemma interior_partner_subset_interior_dimer :
    interior (partnerIsom '' truncatedTetrahedron) ⊆ interior dimerHS := by
  rw [partnerIsom_image]
  exact interior_mono partner_subset_dimerHS

/-- `T` and its partner meet only on the plane `evenForm 0 = -3`, hence have
disjoint interiors. -/
lemma T_partner_interiors_disjoint :
    interior truncatedTetrahedron ∩ interior (partnerIsom '' truncatedTetrahedron) = ∅ := by
  ext p
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
  intro ⟨hpT, hpP⟩
  have hpPset : p ∈ partnerIsom '' truncatedTetrahedron := interior_subset hpP
  rw [partnerIsom_image] at hpPset
  rcases hpPset with ⟨q, hq, rfl⟩
  have hqT : q ∈ truncatedTetrahedronHS := by
    rwa [truncatedTetrahedronHS_eq]
  have he0q : -3 ≤ evenForm 0 q := (hqT 0).1
  have hle : evenForm 0 (dimerOffset - q) ≤ -3 := by
    rw [evenForm_sub_offset, evenForm_dimerOffset.1]
    linarith
  rw [mem_interior] at hpT
  rcases hpT with ⟨U, hUsub, hUopen, hpU⟩
  obtain ⟨t, htpos, htU⟩ := exists_small_step_in_open hUopen hpU (-evenGrad 0)
  have htT : dimerOffset - q + t • (-evenGrad 0) ∈ truncatedTetrahedron := hUsub htU
  have htHS : dimerOffset - q + t • (-evenGrad 0) ∈ truncatedTetrahedronHS := by
    rwa [truncatedTetrahedronHS_eq]
  have hval : evenForm 0 (dimerOffset - q + t • (-evenGrad 0)) =
      evenForm 0 (dimerOffset - q) - 3 * t := by
    rw [evenForm_shift, evenForm_neg_evenGrad]; ring
  have hlo := (htHS 0).1
  rw [hval] at hlo
  linarith [hle, htpos]


lemma jtTranslate_image_add (a b c : ℤ) (s : Set ℝ³) :
    jtTranslate a b c '' s = (fun p : ℝ³ => p + jtLatticeVec a b c) '' s := by
  ext; simp [jtTranslate_apply]

lemma interior_translate (v : ℝ³) (s : Set ℝ³) :
    interior ((fun p : ℝ³ => p + v) '' s) = (fun p : ℝ³ => p + v) '' interior s := by
  have h : (fun p : ℝ³ => p + v) = fun p => v + p := funext fun p => add_comm _ _
  rw [h, ← Homeomorph.coe_addLeft, (Homeomorph.addLeft v).image_interior]

lemma jtLatticeVec_sub (a b c a' b' c' : ℤ) :
    jtLatticeVec a b c - jtLatticeVec a' b' c' =
      jtLatticeVec (a - a') (b - b') (c - c') := by
  simp only [jtLatticeVec]
  have ha : ((a - a' : ℤ) : ℝ) = (a : ℝ) - (a' : ℝ) := by push_cast; rfl
  have hb : ((b - b' : ℤ) : ℝ) = (b : ℝ) - (b' : ℝ) := by push_cast; rfl
  have hc : ((c - c' : ℤ) : ℝ) = (c : ℝ) - (c' : ℝ) := by push_cast; rfl
  rw [ha, hb, hc, sub_smul, sub_smul, sub_smul]
  abel

lemma T_translate_interiors_disjoint {a b c a' b' c' : ℤ}
    (hne : ¬ (a = a' ∧ b = b' ∧ c = c')) :
    interior (jtTranslate a b c '' truncatedTetrahedron) ∩
      interior (jtTranslate a' b' c' '' truncatedTetrahedron) = ∅ := by
  have hne' : ¬ (a' - a = 0 ∧ b' - b = 0 ∧ c' - c = 0) := by
    intro h
    apply hne
    rcases h with ⟨ha, hb, hc⟩
    exact ⟨(eq_of_sub_eq_zero ha).symm, (eq_of_sub_eq_zero hb).symm,
      (eq_of_sub_eq_zero hc).symm⟩
  have hdim := dimer_lattice_interiors_disjoint (a := a' - a) (b := b' - b) (c := c' - c) hne'
  have h1 : interior (jtTranslate a b c '' truncatedTetrahedron) ⊆
      (fun p : ℝ³ => p + jtLatticeVec a b c) '' interior dimerHS := by
    rw [jtTranslate_image_add, interior_translate]
    intro x hx
    rcases hx with ⟨p, hp, rfl⟩
    exact ⟨p, interior_T_subset_interior_dimer hp, rfl⟩
  have h2 : interior (jtTranslate a' b' c' '' truncatedTetrahedron) ⊆
      (fun p : ℝ³ => p + jtLatticeVec a' b' c') '' interior dimerHS := by
    rw [jtTranslate_image_add, interior_translate]
    intro x hx
    rcases hx with ⟨p, hp, rfl⟩
    exact ⟨p, interior_T_subset_interior_dimer hp, rfl⟩
  ext x
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
  intro ⟨hx1, hx2⟩
  have hx1' := h1 hx1
  have hx2' := h2 hx2
  rcases hx1' with ⟨p, hp, hpx⟩
  rcases hx2' with ⟨q, hq, hqx⟩
  -- x = p + lat = q + lat' so p = q + (lat' - lat)
  have hpq : p = q + jtLatticeVec (a' - a) (b' - b) (c' - c) := by
    have hxeq : p + jtLatticeVec a b c = q + jtLatticeVec a' b' c' :=
      hpx.trans hqx.symm
    calc p = p + jtLatticeVec a b c - jtLatticeVec a b c := by abel
      _ = q + jtLatticeVec a' b' c' - jtLatticeVec a b c := by rw [hxeq]
      _ = q + (jtLatticeVec a' b' c' - jtLatticeVec a b c) := by abel
      _ = q + jtLatticeVec (a' - a) (b' - b) (c' - c) := by
            rw [jtLatticeVec_sub]
  have : p ∈ interior dimerHS ∩
      (fun z : ℝ³ => z + jtLatticeVec (a' - a) (b' - b) (c' - c)) '' interior dimerHS :=
    ⟨hp, q, hq, hpq.symm⟩
  exact (hdim ▸ this).elim


lemma det_jtGen :
    Matrix.det (coordMatrix (jtGen 0) (jtGen 1) (jtGen 2)) = 3328 / 27 := by
  have h0 : jtGen 0 = pt (-4) (-8 / 3) (4 / 3) := rfl
  have h1 : jtGen 1 = pt (-4 / 3) 4 (8 / 3) := rfl
  have h2 : jtGen 2 = pt (-8 / 3) (4 / 3) (-4) := rfl
  rw [h0, h1, h2, coordMatrix_of_pt, Matrix.det_fin_three]
  simp [Matrix.cons_val']
  norm_num

lemma abs_det_jtGen :
    |Matrix.det (coordMatrix (jtGen 0) (jtGen 1) (jtGen 2))| = 3328 / 27 := by
  rw [det_jtGen]; norm_num

lemma TTVertex_norm_sq (i : Fin 12) : ‖TTVertex i‖ ^ 2 ≤ 11 := by
  have hnorm : ∀ (x y z : ℝ), ‖pt x y z‖ ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by
    intro x y z
    simp [pt, PiLp.norm_sq_eq_of_L2]
    simp [Fin.sum_univ_three]
  match i with
  | 0 => rw [TTVertex, hnorm]; norm_num
  | 1 => rw [TTVertex, hnorm]; norm_num
  | 2 => rw [TTVertex, hnorm]; norm_num
  | 3 => rw [TTVertex, hnorm]; norm_num
  | 4 => rw [TTVertex, hnorm]; norm_num
  | 5 => rw [TTVertex, hnorm]; norm_num
  | 6 => rw [TTVertex, hnorm]; norm_num
  | 7 => rw [TTVertex, hnorm]; norm_num
  | 8 => rw [TTVertex, hnorm]; norm_num
  | 9 => rw [TTVertex, hnorm]; norm_num
  | 10 => rw [TTVertex, hnorm]; norm_num
  | 11 => rw [TTVertex, hnorm]; norm_num

lemma TTVertex_mem_ball (i : Fin 12) :
    TTVertex i ∈ closedBall (0 : ℝ³) (Real.sqrt 11) := by
  rw [mem_closedBall, dist_zero_right]
  have hsq := TTVertex_norm_sq i
  have hnn : 0 ≤ ‖TTVertex i‖ := norm_nonneg _
  have h11 : 0 ≤ (11 : ℝ) := by norm_num
  exact (Real.le_sqrt hnn h11).mpr (by linarith)

lemma T_subset_ball : truncatedTetrahedron ⊆ closedBall (0 : ℝ³) (Real.sqrt 11) := by
  intro p hp
  have hconv : Convex ℝ (closedBall (0 : ℝ³) (Real.sqrt 11)) := convex_closedBall _ _
  have hpts : range TTVertex ⊆ closedBall (0 : ℝ³) (Real.sqrt 11) := by
    intro x hx; rcases hx with ⟨i, rfl⟩; exact TTVertex_mem_ball i
  exact convexHull_min hpts hconv hp

lemma volume_T_toReal : (volume truncatedTetrahedron).toReal = 184 / 3 := by
  rw [volume_truncatedTetrahedron, ENNReal.toReal_ofReal]
  norm_num

lemma two_vol_T_div_det : (2 : ℝ) * (184 / 3) / (3328 / 27) = 207 / 208 := by
  field_simp; ring

lemma pt_norm_sq (x y z : ℝ) : ‖pt x y z‖ ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by
  simp [pt, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]

lemma partnerVertex_norm_sq (i : Fin 12) :
    ‖dimerOffset - TTVertex i‖ ^ 2 ≤ 43 := by
  have hpt : ∀ x y z : ℝ, ‖pt (-2 - x) (-2 - y) (-2 - z)‖ ^ 2 =
      (-2 - x) ^ 2 + (-2 - y) ^ 2 + (-2 - z) ^ 2 := fun x y z => pt_norm_sq _ _ _
  have heq : ∀ x y z : ℝ, dimerOffset - pt x y z = pt (-2 - x) (-2 - y) (-2 - z) := by
    intro x y z; rw [dimerOffset, pt_sub]
  match i with
  | 0 => rw [TTVertex, heq, hpt]; norm_num
  | 1 => rw [TTVertex, heq, hpt]; norm_num
  | 2 => rw [TTVertex, heq, hpt]; norm_num
  | 3 => rw [TTVertex, heq, hpt]; norm_num
  | 4 => rw [TTVertex, heq, hpt]; norm_num
  | 5 => rw [TTVertex, heq, hpt]; norm_num
  | 6 => rw [TTVertex, heq, hpt]; norm_num
  | 7 => rw [TTVertex, heq, hpt]; norm_num
  | 8 => rw [TTVertex, heq, hpt]; norm_num
  | 9 => rw [TTVertex, heq, hpt]; norm_num
  | 10 => rw [TTVertex, heq, hpt]; norm_num
  | 11 => rw [TTVertex, heq, hpt]; norm_num

lemma partnerVertex_mem_ball (i : Fin 12) :
    dimerOffset - TTVertex i ∈ closedBall (0 : ℝ³) (Real.sqrt 43) := by
  rw [mem_closedBall, dist_zero_right]
  have hsq := partnerVertex_norm_sq i
  exact (Real.le_sqrt (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 43)).mpr (by linarith)

lemma partner_subset_ball :
    partnerIsom '' truncatedTetrahedron ⊆ closedBall (0 : ℝ³) (Real.sqrt 43) := by
  rw [partnerIsom_image]
  intro p hp
  rcases hp with ⟨q, hq, rfl⟩
  have hpts : range TTVertex ⊆ closedBall dimerOffset (Real.sqrt 43) := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    rw [mem_closedBall, dist_eq_norm_sub]
    have := partnerVertex_mem_ball i
    simpa [mem_closedBall, dist_zero_right, norm_sub_rev] using this
  have hqball : q ∈ closedBall dimerOffset (Real.sqrt 43) :=
    convexHull_min hpts (convex_closedBall _ _) hq
  rw [mem_closedBall, dist_eq_norm_sub] at hqball
  rw [mem_closedBall, dist_zero_right, norm_sub_rev]
  exact hqball

lemma sqrt11_le_seven : Real.sqrt 11 ≤ 7 := by
  have : Real.sqrt 11 ≤ Real.sqrt 49 :=
    Real.sqrt_le_sqrt (by norm_num : (11 : ℝ) ≤ 49)
  have : Real.sqrt 49 = 7 := by
    rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
  linarith

lemma sqrt43_le_seven : Real.sqrt 43 ≤ 7 := by
  have : Real.sqrt 43 ≤ Real.sqrt 49 :=
    Real.sqrt_le_sqrt (by norm_num : (43 : ℝ) ≤ 49)
  have : Real.sqrt 49 = 7 := by
    rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
  linarith

lemma T_subset_ball7 : truncatedTetrahedron ⊆ closedBall (0 : ℝ³) 7 :=
  T_subset_ball.trans (closedBall_subset_closedBall sqrt11_le_seven)

lemma partner_subset_ball7 :
    partnerIsom '' truncatedTetrahedron ⊆ closedBall (0 : ℝ³) 7 :=
  partner_subset_ball.trans (closedBall_subset_closedBall sqrt43_le_seven)

lemma jtGen_norm_sq (i : Fin 3) : ‖jtGen i‖ ^ 2 = 224 / 9 := by
  match i with
  | 0 =>
    have : jtGen 0 = pt (-4) (-8 / 3) (4 / 3) := rfl
    rw [this, pt_norm_sq]; norm_num
  | 1 =>
    have : jtGen 1 = pt (-4 / 3) 4 (8 / 3) := rfl
    rw [this, pt_norm_sq]; norm_num
  | 2 =>
    have : jtGen 2 = pt (-8 / 3) (4 / 3) (-4) := rfl
    rw [this, pt_norm_sq]; norm_num

lemma jtGen_norm_le_five (i : Fin 3) : ‖jtGen i‖ ≤ 5 := by
  have hsq : ‖jtGen i‖ ^ 2 ≤ (5 : ℝ) ^ 2 := by
    rw [jtGen_norm_sq]; norm_num
  exact (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 5)).1 hsq

lemma jtLatticeVec_norm_le (a b c : ℤ) :
    ‖jtLatticeVec a b c‖ ≤ 5 * (|a| + |b| + |c| : ℝ) := by
  simp only [jtLatticeVec]
  calc ‖(a : ℝ) • jtGen 0 + (b : ℝ) • jtGen 1 + (c : ℝ) • jtGen 2‖
      ≤ ‖(a : ℝ) • jtGen 0 + (b : ℝ) • jtGen 1‖ + ‖(c : ℝ) • jtGen 2‖ :=
        norm_add_le _ _
    _ ≤ ‖(a : ℝ) • jtGen 0‖ + ‖(b : ℝ) • jtGen 1‖ + ‖(c : ℝ) • jtGen 2‖ := by
        gcongr; exact norm_add_le _ _
    _ = |a| * ‖jtGen 0‖ + |b| * ‖jtGen 1‖ + |c| * ‖jtGen 2‖ := by
        simp [norm_smul, Int.cast_abs]
    _ ≤ |a| * 5 + |b| * 5 + |c| * 5 := by
        gcongr <;> exact jtGen_norm_le_five _
    _ = 5 * (|a| + |b| + |c|) := by ring

lemma closedBall_vadd (v : ℝ³) (r : ℝ) :
    (fun p : ℝ³ => p + v) '' closedBall (0 : ℝ³) r = closedBall v r := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [mem_closedBall, dist_eq_norm_sub, add_sub_cancel_right]
    simpa [mem_closedBall, dist_zero_right] using hq
  · intro hp
    refine ⟨p - v, ?_, by abel⟩
    rw [mem_closedBall, dist_zero_right]
    rw [mem_closedBall, dist_eq_norm_sub] at hp
    exact hp

lemma T_translate_subset_ball (a b c : ℤ) {R : ℝ}
    (hR : ‖jtLatticeVec a b c‖ + 7 ≤ R) :
    jtTranslate a b c '' truncatedTetrahedron ⊆ closedBall (0 : ℝ³) R := by
  rw [jtTranslate_image_add]
  intro p hp
  rcases hp with ⟨q, hq, rfl⟩
  have hq7 : q ∈ closedBall (0 : ℝ³) 7 := T_subset_ball7 hq
  rw [mem_closedBall, dist_zero_right] at hq7 ⊢
  calc ‖q + jtLatticeVec a b c‖
      ≤ ‖q‖ + ‖jtLatticeVec a b c‖ := norm_add_le _ _
    _ ≤ 7 + ‖jtLatticeVec a b c‖ := by gcongr
    _ ≤ R := by linarith

lemma partner_translate_subset_ball (a b c : ℤ) {R : ℝ}
    (hR : ‖jtLatticeVec a b c‖ + 7 ≤ R) :
    jtPartnerIsom a b c '' truncatedTetrahedron ⊆ closedBall (0 : ℝ³) R := by
  intro p hp
  rw [mem_image] at hp
  rcases hp with ⟨q, hq, rfl⟩
  rw [jtPartnerIsom_apply]
  have hq7 : partnerIsom q ∈ closedBall (0 : ℝ³) 7 := partner_subset_ball7 ⟨q, hq, rfl⟩
  rw [mem_closedBall, dist_zero_right] at hq7 ⊢
  calc ‖partnerIsom q + jtLatticeVec a b c‖
      ≤ ‖partnerIsom q‖ + ‖jtLatticeVec a b c‖ := norm_add_le _ _
    _ ≤ 7 + ‖jtLatticeVec a b c‖ := by gcongr
    _ ≤ R := by linarith

lemma jtPartnerIsom_image (a b c : ℤ) :
    jtPartnerIsom a b c '' truncatedTetrahedron =
      (fun p : ℝ³ => p + jtLatticeVec a b c) ''
        (partnerIsom '' truncatedTetrahedron) := by
  ext z
  constructor
  · intro hz
    rcases (mem_image _ _ _).1 hz with ⟨q, hq, rfl⟩
    rw [jtPartnerIsom_apply]
    exact ⟨partnerIsom q, ⟨q, hq, rfl⟩, rfl⟩
  · intro hz
    rcases (mem_image _ _ _).1 hz with ⟨p, hp, rfl⟩
    rcases (mem_image _ _ _).1 hp with ⟨q, hq, rfl⟩
    refine (mem_image _ _ _).2 ⟨q, hq, ?_⟩
    rw [jtPartnerIsom_apply]

/-- Partner copies at distinct lattice sites have disjoint interiors. -/
lemma partner_translate_interiors_disjoint {a b c a' b' c' : ℤ}
    (hne : ¬ (a = a' ∧ b = b' ∧ c = c')) :
    interior (jtPartnerIsom a b c '' truncatedTetrahedron) ∩
      interior (jtPartnerIsom a' b' c' '' truncatedTetrahedron) = ∅ := by
  have hne' : ¬ (a' - a = 0 ∧ b' - b = 0 ∧ c' - c = 0) := by
    intro h
    apply hne
    rcases h with ⟨ha, hb, hc⟩
    exact ⟨(eq_of_sub_eq_zero ha).symm, (eq_of_sub_eq_zero hb).symm,
      (eq_of_sub_eq_zero hc).symm⟩
  have hdim := dimer_lattice_interiors_disjoint (a := a' - a) (b := b' - b) (c := c' - c) hne'
  have h1 : interior (jtPartnerIsom a b c '' truncatedTetrahedron) ⊆
      (fun p : ℝ³ => p + jtLatticeVec a b c) '' interior dimerHS := by
    intro x hx
    rw [jtPartnerIsom_image, interior_translate] at hx
    rcases hx with ⟨p, hp, rfl⟩
    exact ⟨p, interior_partner_subset_interior_dimer hp, rfl⟩
  have h2 : interior (jtPartnerIsom a' b' c' '' truncatedTetrahedron) ⊆
      (fun p : ℝ³ => p + jtLatticeVec a' b' c') '' interior dimerHS := by
    intro x hx
    rw [jtPartnerIsom_image, interior_translate] at hx
    rcases hx with ⟨p, hp, rfl⟩
    exact ⟨p, interior_partner_subset_interior_dimer hp, rfl⟩
  ext x
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
  intro ⟨hx1, hx2⟩
  rcases h1 hx1 with ⟨p, hp, hpx⟩
  rcases h2 hx2 with ⟨q, hq, hqx⟩
  have hpq : p = q + jtLatticeVec (a' - a) (b' - b) (c' - c) := by
    have hxeq : p + jtLatticeVec a b c = q + jtLatticeVec a' b' c' :=
      hpx.trans hqx.symm
    calc p = p + jtLatticeVec a b c - jtLatticeVec a b c := by abel
      _ = q + jtLatticeVec a' b' c' - jtLatticeVec a b c := by rw [hxeq]
      _ = q + (jtLatticeVec a' b' c' - jtLatticeVec a b c) := by abel
      _ = q + jtLatticeVec (a' - a) (b' - b) (c' - c) := by rw [jtLatticeVec_sub]
  have : p ∈ interior dimerHS ∩
      (fun z : ℝ³ => z + jtLatticeVec (a' - a) (b' - b) (c' - c)) '' interior dimerHS :=
    ⟨hp, q, hq, hpq.symm⟩
  exact (hdim ▸ this).elim

/-- `T` at one site and the partner at another (possibly the same) have disjoint interiors. -/
lemma T_partner_translate_interiors_disjoint (a b c a' b' c' : ℤ) :
    interior (jtTranslate a b c '' truncatedTetrahedron) ∩
      interior (jtPartnerIsom a' b' c' '' truncatedTetrahedron) = ∅ := by
  by_cases heq : a = a' ∧ b = b' ∧ c = c'
  · -- same site: translate the dimer-internal disjointness
    rcases heq with ⟨rfl, rfl, rfl⟩
    have h0 := T_partner_interiors_disjoint
    rw [jtTranslate_image_add, jtPartnerIsom_image, interior_translate, interior_translate]
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
    rintro ⟨hxT, hxP⟩
    rcases hxT with ⟨p, hp, rfl⟩
    rcases hxP with ⟨q, hq, hqp⟩
    have hpq : p = q := by
      have := congrArg (fun z : ℝ³ => z - jtLatticeVec a b c) hqp
      simpa using this.symm
    subst hpq
    have : p ∈ interior truncatedTetrahedron ∩
        interior (partnerIsom '' truncatedTetrahedron) := ⟨hp, hq⟩
    exact (h0 ▸ this).elim
  · -- different sites: both live in disjoint dimer interiors
    have hne' : ¬ (a' - a = 0 ∧ b' - b = 0 ∧ c' - c = 0) := by
      intro h
      apply heq
      rcases h with ⟨ha, hb, hc⟩
      exact ⟨(eq_of_sub_eq_zero ha).symm, (eq_of_sub_eq_zero hb).symm,
        (eq_of_sub_eq_zero hc).symm⟩
    have hdim := dimer_lattice_interiors_disjoint (a := a' - a) (b := b' - b) (c := c' - c) hne'
    have h1 : interior (jtTranslate a b c '' truncatedTetrahedron) ⊆
        (fun p : ℝ³ => p + jtLatticeVec a b c) '' interior dimerHS := by
      rw [jtTranslate_image_add, interior_translate]
      intro x hx
      rcases hx with ⟨p, hp, rfl⟩
      exact ⟨p, interior_T_subset_interior_dimer hp, rfl⟩
    have h2 : interior (jtPartnerIsom a' b' c' '' truncatedTetrahedron) ⊆
        (fun p : ℝ³ => p + jtLatticeVec a' b' c') '' interior dimerHS := by
      intro x hx
      rw [jtPartnerIsom_image, interior_translate] at hx
      rcases hx with ⟨p, hp, rfl⟩
      exact ⟨p, interior_partner_subset_interior_dimer hp, rfl⟩
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
    intro ⟨hx1, hx2⟩
    rcases h1 hx1 with ⟨p, hp, hpx⟩
    rcases h2 hx2 with ⟨q, hq, hqx⟩
    have hpq : p = q + jtLatticeVec (a' - a) (b' - b) (c' - c) := by
      have hxeq : p + jtLatticeVec a b c = q + jtLatticeVec a' b' c' :=
        hpx.trans hqx.symm
      calc p = p + jtLatticeVec a b c - jtLatticeVec a b c := by abel
        _ = q + jtLatticeVec a' b' c' - jtLatticeVec a b c := by rw [hxeq]
        _ = q + (jtLatticeVec a' b' c' - jtLatticeVec a b c) := by abel
        _ = q + jtLatticeVec (a' - a) (b' - b) (c' - c) := by rw [jtLatticeVec_sub]
    have : p ∈ interior dimerHS ∩
        (fun z : ℝ³ => z + jtLatticeVec (a' - a) (b' - b) (c' - c)) '' interior dimerHS :=
      ⟨hp, q, hq, hpq.symm⟩
    exact (hdim ▸ this).elim

/-! ### Linear map of the Jiao–Torquato lattice and inverse bounds -/

noncomputable def jtMap : ℝ³ →ₗ[ℝ] ℝ³ where
  toFun x := x 0 • jtGen 0 + x 1 • jtGen 1 + x 2 • jtGen 2
  map_add' := fun x y => by
    simp only [PiLp.add_apply, add_smul]
    abel
  map_smul' := fun r x => by
    simp only [PiLp.smul_apply, RingHom.id_apply, smul_eq_mul, mul_smul, smul_add]

lemma jtMap_apply (x : ℝ³) :
    jtMap x = x 0 • jtGen 0 + x 1 • jtGen 1 + x 2 • jtGen 2 := rfl

lemma jtMap_coord (x : ℝ³) (i : Fin 3) :
    jtMap x i = x 0 * jtGen 0 i + x 1 * jtGen 1 i + x 2 * jtGen 2 i := by
  simp [jtMap, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

lemma jtLatticeVec_eq_map (a b c : ℤ) :
    jtLatticeVec a b c = jtMap (pt (a : ℝ) (b : ℝ) (c : ℝ)) := by
  simp [jtLatticeVec, jtMap_apply, pt]

lemma jtGen0_coord : jtGen 0 0 = -4 ∧ jtGen 0 1 = -8 / 3 ∧ jtGen 0 2 = 4 / 3 := by
  simp [jtGen, pt]

lemma jtGen1_coord : jtGen 1 0 = -4 / 3 ∧ jtGen 1 1 = 4 ∧ jtGen 1 2 = 8 / 3 := by
  simp [jtGen, pt]

lemma jtGen2_coord : jtGen 2 0 = -8 / 3 ∧ jtGen 2 1 = 4 / 3 ∧ jtGen 2 2 = -4 := by
  simp [jtGen, pt]

/-- Inverse linear combination with the explicit adjugate / determinant. -/
noncomputable def jtInvVec (y : ℝ³) : ℝ³ :=
  pt ((-33 * y 0 - 21 * y 1 + 15 * y 2) / 208)
     ((-15 * y 0 + 33 * y 1 + 21 * y 2) / 208)
     ((-21 * y 0 + 15 * y 1 - 33 * y 2) / 208)

lemma jtInvVec_apply_zero (y : ℝ³) :
    jtInvVec y 0 = (-33 * y 0 - 21 * y 1 + 15 * y 2) / 208 := by
  simp [jtInvVec, pt]

lemma jtInvVec_apply_one (y : ℝ³) :
    jtInvVec y 1 = (-15 * y 0 + 33 * y 1 + 21 * y 2) / 208 := by
  simp [jtInvVec, pt]

lemma jtInvVec_apply_two (y : ℝ³) :
    jtInvVec y 2 = (-21 * y 0 + 15 * y 1 - 33 * y 2) / 208 := by
  simp [jtInvVec, pt]

lemma abs_coord_le_norm (y : ℝ³) (i : Fin 3) : |y i| ≤ ‖y‖ := by
  have hsq : |y i| ^ 2 ≤ ‖y‖ ^ 2 := by
    have : (y i) ^ 2 ≤ ∑ j : Fin 3, (y j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)
    have hnorm : ‖y‖ ^ 2 = ∑ j : Fin 3, (y j) ^ 2 := by
      simpa [sq_abs] using (PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) y)
    rw [hnorm, sq_abs]; exact this
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).1 hsq

lemma jtMap_jtInvVec (y : ℝ³) : jtMap (jtInvVec y) = y := by
  ext i
  rw [jtMap_coord, jtInvVec_apply_zero, jtInvVec_apply_one, jtInvVec_apply_two]
  have h0 := jtGen0_coord
  have h1 := jtGen1_coord
  have h2 := jtGen2_coord
  match i with
  | 0 => rw [h0.1, h1.1, h2.1]; field_simp; ring
  | 1 => rw [h0.2.1, h1.2.1, h2.2.1]; field_simp; ring
  | 2 => rw [h0.2.2, h1.2.2, h2.2.2]; field_simp; ring

lemma jtInvVec_jtMap (x : ℝ³) : jtInvVec (jtMap x) = x := by
  ext i
  have hc0 := jtMap_coord x 0
  have hc1 := jtMap_coord x 1
  have hc2 := jtMap_coord x 2
  have g0 := jtGen0_coord
  have g1 := jtGen1_coord
  have g2 := jtGen2_coord
  match i with
  | 0 =>
    rw [jtInvVec_apply_zero, hc0, hc1, hc2, g0.1, g0.2.1, g0.2.2,
      g1.1, g1.2.1, g1.2.2, g2.1, g2.2.1, g2.2.2]
    field_simp; ring
  | 1 =>
    rw [jtInvVec_apply_one, hc0, hc1, hc2, g0.1, g0.2.1, g0.2.2,
      g1.1, g1.2.1, g1.2.2, g2.1, g2.2.1, g2.2.2]
    field_simp; ring
  | 2 =>
    rw [jtInvVec_apply_two, hc0, hc1, hc2, g0.1, g0.2.1, g0.2.2,
      g1.1, g1.2.1, g1.2.2, g2.1, g2.2.1, g2.2.2]
    field_simp; ring

lemma lincomb_div_le_norm (y : ℝ³) (a b c : ℝ) (hsum : |a| + |b| + |c| ≤ 69) :
    |a * y 0 + b * y 1 + c * y 2| / 208 ≤ ‖y‖ := by
  have hy0 := abs_coord_le_norm y 0
  have hy1 := abs_coord_le_norm y 1
  have hy2 := abs_coord_le_norm y 2
  have h1 : |a * y 0 + b * y 1 + c * y 2| ≤ |a| * |y 0| + |b| * |y 1| + |c| * |y 2| := by
    calc |a * y 0 + b * y 1 + c * y 2|
        ≤ |a * y 0| + |b * y 1| + |c * y 2| := abs_add_three _ _ _
      _ = |a| * |y 0| + |b| * |y 1| + |c| * |y 2| := by simp [abs_mul]
  have ha : |a| * |y 0| ≤ |a| * ‖y‖ := mul_le_mul_of_nonneg_left hy0 (abs_nonneg _)
  have hb : |b| * |y 1| ≤ |b| * ‖y‖ := mul_le_mul_of_nonneg_left hy1 (abs_nonneg _)
  have hc : |c| * |y 2| ≤ |c| * ‖y‖ := mul_le_mul_of_nonneg_left hy2 (abs_nonneg _)
  have h2 : |a| * |y 0| + |b| * |y 1| + |c| * |y 2| ≤ (|a| + |b| + |c|) * ‖y‖ := by linarith
  have hynn : 0 ≤ ‖y‖ := norm_nonneg _
  have h3 : (|a| + |b| + |c|) * ‖y‖ / 208 ≤ 69 * ‖y‖ / 208 := by
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 208)
    exact mul_le_mul_of_nonneg_right hsum hynn
  have h4 : 69 * ‖y‖ / 208 ≤ ‖y‖ := by
    calc 69 * ‖y‖ / 208 = (69 / 208) * ‖y‖ := by ring
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (by norm_num) hynn
      _ = ‖y‖ := one_mul _
  linarith

lemma jtInvVec_coord_le_norm (y : ℝ³) (i : Fin 3) : |jtInvVec y i| ≤ ‖y‖ := by
  have hden : (0 : ℝ) < 208 := by norm_num
  match i with
  | 0 =>
    rw [jtInvVec_apply_zero, abs_div, abs_of_pos hden]
    have heq : -33 * y 0 - 21 * y 1 + 15 * y 2 =
        (-33) * y 0 + (-21) * y 1 + 15 * y 2 := by ring
    rw [heq]
    exact lincomb_div_le_norm y (-33) (-21) 15 (by norm_num)
  | 1 =>
    rw [jtInvVec_apply_one, abs_div, abs_of_pos hden]
    exact lincomb_div_le_norm y (-15) 33 21 (by norm_num)
  | 2 =>
    rw [jtInvVec_apply_two, abs_div, abs_of_pos hden]
    have heq : -21 * y 0 + 15 * y 1 - 33 * y 2 =
        (-21) * y 0 + 15 * y 1 + (-33) * y 2 := by ring
    rw [heq]
    exact lincomb_div_le_norm y (-21) 15 (-33) (by norm_num)

lemma pt_coord (a b c : ℝ) : (pt a b c 0 = a ∧ pt a b c 1 = b ∧ pt a b c 2 = c) := by
  simp [pt]

lemma lattice_coords_le_norm (a b c : ℤ) :
    |(a : ℝ)| ≤ ‖jtLatticeVec a b c‖ ∧
    |(b : ℝ)| ≤ ‖jtLatticeVec a b c‖ ∧
    |(c : ℝ)| ≤ ‖jtLatticeVec a b c‖ := by
  have hinv : jtInvVec (jtLatticeVec a b c) = pt (a : ℝ) (b : ℝ) (c : ℝ) := by
    rw [jtLatticeVec_eq_map, jtInvVec_jtMap]
  have h0 := jtInvVec_coord_le_norm (jtLatticeVec a b c) 0
  have h1 := jtInvVec_coord_le_norm (jtLatticeVec a b c) 1
  have h2 := jtInvVec_coord_le_norm (jtLatticeVec a b c) 2
  have hp := pt_coord (a : ℝ) (b : ℝ) (c : ℝ)
  constructor
  · rw [hinv, hp.1] at h0; exact h0
  constructor
  · rw [hinv, hp.2.1] at h1; exact h1
  · rw [hinv, hp.2.2] at h2; exact h2

lemma jtMap_norm_le (x : ℝ³) :
    ‖jtMap x‖ ≤ 5 * (|x 0| + |x 1| + |x 2|) := by
  simp only [jtMap_apply]
  have h01 : ‖x 0 • jtGen 0 + x 1 • jtGen 1‖ ≤ ‖x 0 • jtGen 0‖ + ‖x 1 • jtGen 1‖ :=
    norm_add_le _ _
  have h012 : ‖x 0 • jtGen 0 + x 1 • jtGen 1 + x 2 • jtGen 2‖ ≤
      ‖x 0 • jtGen 0 + x 1 • jtGen 1‖ + ‖x 2 • jtGen 2‖ := norm_add_le _ _
  have : ‖x 0 • jtGen 0 + x 1 • jtGen 1 + x 2 • jtGen 2‖ ≤
      ‖x 0 • jtGen 0‖ + ‖x 1 • jtGen 1‖ + ‖x 2 • jtGen 2‖ := by linarith
  calc ‖x 0 • jtGen 0 + x 1 • jtGen 1 + x 2 • jtGen 2‖
      ≤ ‖x 0 • jtGen 0‖ + ‖x 1 • jtGen 1‖ + ‖x 2 • jtGen 2‖ := this
    _ = |x 0| * ‖jtGen 0‖ + |x 1| * ‖jtGen 1‖ + |x 2| * ‖jtGen 2‖ := by
        simp [norm_smul]
    _ ≤ |x 0| * 5 + |x 1| * 5 + |x 2| * 5 := by
        gcongr <;> exact jtGen_norm_le_five _
    _ = 5 * (|x 0| + |x 1| + |x 2|) := by ring

lemma jtMap_frac_norm_le (x : ℝ³) (hx0 : |x 0| ≤ 1) (hx1 : |x 1| ≤ 1) (hx2 : |x 2| ≤ 1) :
    ‖jtMap x‖ ≤ 15 := by
  have := jtMap_norm_le x
  linarith

/-- The closed unit cube `[0,1]³` in `ℝ³`. -/
def unitCube3' : Set ℝ³ := {x | ∀ i : Fin 3, 0 ≤ x i ∧ x i ≤ 1}

lemma continuous_coord (i : Fin 3) : Continuous (fun x : ℝ³ => x i) :=
  LipschitzWith.continuous (K := 1) <| LipschitzWith.of_dist_le_mul fun x y => by
    simpa [dist_eq_norm, Real.dist_eq] using abs_coord_le_norm (x - y) i

lemma isClosed_unitCube3' : IsClosed unitCube3' := by
  have : unitCube3' = ⋂ i : Fin 3, (fun x : ℝ³ => x i) ⁻¹' Icc (0 : ℝ) 1 := by
    ext x
    simp [unitCube3', mem_iInter, mem_Icc]
  rw [this]
  exact isClosed_iInter fun i => isClosed_Icc.preimage (continuous_coord i)

lemma volume_unitCube3' : volume unitCube3' = 1 := by
  have hmp := PiLp.volume_preserving_toLp (ι := Fin 3)
  have hpre :
      (@WithLp.toLp 2 (Fin 3 → ℝ)) ⁻¹' unitCube3' = Icc (0 : Fin 3 → ℝ) 1 := by
    ext y
    simp only [unitCube3', mem_preimage, mem_setOf_eq, mem_Icc]
    constructor
    · intro h
      exact ⟨fun i => (h i).1, fun i => (h i).2⟩
    · intro h i
      exact ⟨h.1 i, h.2 i⟩
  have : volume unitCube3' = volume (Icc (0 : Fin 3 → ℝ) 1) := by
    rw [← hmp.map_eq, Measure.map_apply hmp.measurable isClosed_unitCube3'.measurableSet, hpre]
  rw [this, Real.volume_Icc_pi]
  simp

lemma basisFun_repr_coord (x : ℝ³) (i : Fin 3) :
    ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.repr x) i = x i :=
  rfl

lemma single_coord (j i : Fin 3) :
    (EuclideanSpace.single j (1 : ℝ) : ℝ³) i = if i = j then (1 : ℝ) else 0 :=
  EuclideanSpace.single_apply j 1 i

lemma jtMap_single (j : Fin 3) :
    jtMap (EuclideanSpace.single j 1) = jtGen j := by
  simp only [jtMap_apply]
  have h : ∀ i : Fin 3, (EuclideanSpace.single j (1 : ℝ) : ℝ³) i = if i = j then 1 else 0 :=
    single_coord j
  rw [h 0, h 1, h 2]
  match j with
  | 0 => simp
  | 1 => simp
  | 2 => simp

lemma toMatrix_jtMap :
    LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis jtMap =
    coordMatrix (jtGen 0) (jtGen 1) (jtGen 2) := by
  ext i j
  rw [LinearMap.toMatrix_apply, basisFun_repr_coord]
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  rw [jtMap_single]
  fin_cases i <;> fin_cases j <;> simp [coordMatrix]

lemma det_jtMap : LinearMap.det jtMap = 3328 / 27 := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis, toMatrix_jtMap,
    det_jtGen]

lemma abs_det_jtMap : |LinearMap.det jtMap| = 3328 / 27 := by
  rw [det_jtMap]; norm_num

/-- The ellipsoid of lattice coordinates mapping into the Euclidean ball of radius `ρ`. -/
def jtEllipsoid (ρ : ℝ) : Set ℝ³ := {x | ‖jtMap x‖ ≤ ρ}

lemma mem_jtEllipsoid {ρ : ℝ} {x : ℝ³} : x ∈ jtEllipsoid ρ ↔ ‖jtMap x‖ ≤ ρ := Iff.rfl

lemma jtMap_image_ellipsoid (ρ : ℝ) :
    jtMap '' jtEllipsoid ρ = closedBall (0 : ℝ³) ρ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    exact hx
  · intro hy
    refine ⟨jtInvVec y, ?_, jtMap_jtInvVec y⟩
    rw [mem_jtEllipsoid, jtMap_jtInvVec]
    simpa [mem_closedBall, dist_zero_right] using hy

lemma volume_jtEllipsoid (ρ : ℝ) :
    volume (jtEllipsoid ρ) * ENNReal.ofReal (3328 / 27) =
      volume (closedBall (0 : ℝ³) ρ) := by
  have himg := Measure.addHaar_image_linearMap (μ := volume) jtMap (jtEllipsoid ρ)
  rw [jtMap_image_ellipsoid, abs_det_jtMap] at himg
  rw [himg]
  ring

lemma volume_jtEllipsoid_toReal (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (volume (jtEllipsoid ρ)).toReal =
      (volume (closedBall (0 : ℝ³) ρ)).toReal / (3328 / 27) := by
  have h := congrArg ENNReal.toReal (volume_jtEllipsoid ρ)
  have hdet : (ENNReal.ofReal (3328 / 27)).toReal = 3328 / 27 :=
    ENNReal.toReal_ofReal (by norm_num)
  rw [ENNReal.toReal_mul, hdet] at h
  have hpos : (3328 / 27 : ℝ) ≠ 0 := by norm_num
  field_simp [hpos] at h ⊢
  linarith

/-- Integer lattice sites whose Jiao–Torquato vector lies in the closed ball of radius `r`. -/
noncomputable def jtIntSites (r : ℝ) : Finset (ℤ × ℤ × ℤ) :=
  let M := Int.ceil r
  ((Finset.Icc (-M) M) ×ˢ (Finset.Icc (-M) M) ×ˢ (Finset.Icc (-M) M)).filter
    (fun p => ‖jtLatticeVec p.1 p.2.1 p.2.2‖ ≤ r)

lemma mem_jtIntSites {r : ℝ} {a b c : ℤ} :
    (a, b, c) ∈ jtIntSites r ↔
      a ∈ Finset.Icc (-Int.ceil r) (Int.ceil r) ∧
      b ∈ Finset.Icc (-Int.ceil r) (Int.ceil r) ∧
      c ∈ Finset.Icc (-Int.ceil r) (Int.ceil r) ∧
      ‖jtLatticeVec a b c‖ ≤ r := by
  simp [jtIntSites, Finset.mem_filter, Finset.mem_product]
  tauto

lemma int_abs_le_ceil {z : ℤ} {r : ℝ} (h : |(z : ℝ)| ≤ r) :
    z ∈ Finset.Icc (-Int.ceil r) (Int.ceil r) := by
  rw [Finset.mem_Icc]
  have habs := abs_le.mp h
  have hup : z ≤ Int.ceil r := by
    have : (z : ℝ) ≤ (Int.ceil r : ℝ) := habs.2.trans (Int.le_ceil r)
    exact Int.cast_le.mp this
  have hlo : -Int.ceil r ≤ z := by
    have hz : -(z : ℝ) ≤ r := by linarith [habs.1]
    have hle : -(z : ℝ) ≤ (Int.ceil r : ℝ) := hz.trans (Int.le_ceil r)
    have : ((-z : ℤ) : ℝ) ≤ (Int.ceil r : ℝ) := by
      rwa [Int.cast_neg]
    exact neg_le.mp (Int.cast_le.mp this)
  exact ⟨hlo, hup⟩

lemma lattice_mem_sites {r : ℝ} {a b c : ℤ} (h : ‖jtLatticeVec a b c‖ ≤ r) :
    (a, b, c) ∈ jtIntSites r := by
  rw [mem_jtIntSites]
  have hc := lattice_coords_le_norm a b c
  exact ⟨int_abs_le_ceil (hc.1.trans h), int_abs_le_ceil (hc.2.1.trans h),
    int_abs_le_ceil (hc.2.2.trans h), h⟩

noncomputable def coordCube (a b c : ℤ) : Set ℝ³ :=
  (fun x : ℝ³ => pt (a : ℝ) (b : ℝ) (c : ℝ) + x) '' unitCube3'

lemma volume_coordCube (a b c : ℤ) : volume (coordCube a b c) = 1 := by
  simp only [coordCube]
  rw [volume_vadd, volume_unitCube3']

lemma frac_nonneg (y : ℝ) : 0 ≤ y - Int.floor y :=
  sub_nonneg.mpr (Int.floor_le y)

lemma frac_le_one (y : ℝ) : y - Int.floor y ≤ 1 := by
  have : y < (Int.floor y : ℝ) + 1 := Int.lt_floor_add_one y
  linarith

lemma decompose_floor (x : ℝ³) :
    x = pt (↑(Int.floor (x 0))) (↑(Int.floor (x 1))) (↑(Int.floor (x 2))) +
      pt (x 0 - ↑(Int.floor (x 0))) (x 1 - ↑(Int.floor (x 1))) (x 2 - ↑(Int.floor (x 2))) := by
  ext i
  match i with
  | 0 => simp [pt, PiLp.add_apply]
  | 1 => simp [pt, PiLp.add_apply]
  | 2 => simp [pt, PiLp.add_apply]

lemma frac_mem_unitCube (x : ℝ³) :
    pt (x 0 - ↑(Int.floor (x 0))) (x 1 - ↑(Int.floor (x 1))) (x 2 - ↑(Int.floor (x 2)))
      ∈ unitCube3' := by
  intro i
  match i with
  | 0 =>
    constructor
    · simpa [pt] using frac_nonneg (x 0)
    · simpa [pt] using frac_le_one (x 0)
  | 1 =>
    constructor
    · simpa [pt] using frac_nonneg (x 1)
    · simpa [pt] using frac_le_one (x 1)
  | 2 =>
    constructor
    · simpa [pt] using frac_nonneg (x 2)
    · simpa [pt] using frac_le_one (x 2)

lemma mem_coordCube_of_floor (x : ℝ³) :
    x ∈ coordCube (Int.floor (x 0)) (Int.floor (x 1)) (Int.floor (x 2)) := by
  refine ⟨_, frac_mem_unitCube x, ?_⟩
  exact (decompose_floor x).symm

lemma abs_frac_le_one (x : ℝ³) (i : Fin 3) :
    |pt (x 0 - ↑(Int.floor (x 0))) (x 1 - ↑(Int.floor (x 1)))
      (x 2 - ↑(Int.floor (x 2))) i| ≤ 1 := by
  have h := frac_mem_unitCube x i
  have hnn : 0 ≤ pt (x 0 - ↑(Int.floor (x 0))) (x 1 - ↑(Int.floor (x 1)))
      (x 2 - ↑(Int.floor (x 2))) i := h.1
  rw [abs_of_nonneg hnn]
  exact h.2

lemma ellipsoid_subset_cubes {ρ r : ℝ} (h : ρ + 15 ≤ r) :
    jtEllipsoid ρ ⊆ ⋃ p ∈ jtIntSites r, coordCube p.1 p.2.1 p.2.2 := by
  intro x hx
  set a := Int.floor (x 0)
  set b := Int.floor (x 1)
  set c := Int.floor (x 2)
  have hxcube : x ∈ coordCube a b c := mem_coordCube_of_floor x
  set frac := pt (x 0 - (a : ℝ)) (x 1 - (b : ℝ)) (x 2 - (c : ℝ))
  have hfn : ‖jtMap frac‖ ≤ 15 := by
    apply jtMap_frac_norm_le
    · simpa [frac] using abs_frac_le_one x 0
    · simpa [frac] using abs_frac_le_one x 1
    · simpa [frac] using abs_frac_le_one x 2
  have hxdec : x = pt (a : ℝ) (b : ℝ) (c : ℝ) + frac := decompose_floor x
  have hsum : jtMap x = jtMap (pt (a : ℝ) (b : ℝ) (c : ℝ)) + jtMap frac := by
    rw [hxdec, LinearMap.map_add]
  have hlam : ‖jtLatticeVec a b c‖ ≤ r := by
    rw [jtLatticeVec_eq_map]
    have hxρ : ‖jtMap x‖ ≤ ρ := hx
    calc ‖jtMap (pt (a : ℝ) (b : ℝ) (c : ℝ))‖
        = ‖jtMap x - jtMap frac‖ := by rw [hsum, add_sub_cancel_right]
      _ ≤ ‖jtMap x‖ + ‖jtMap frac‖ := norm_sub_le _ _
      _ ≤ ρ + 15 := add_le_add hxρ hfn
      _ ≤ r := h
  exact mem_biUnion (lattice_mem_sites hlam) hxcube

lemma card_sites_ge_vol {ρ r : ℝ} (hρ : 0 ≤ ρ) (h : ρ + 15 ≤ r) :
    (volume (jtEllipsoid ρ)).toReal ≤ (jtIntSites r).card := by
  have hsub := ellipsoid_subset_cubes h
  have hle : volume (jtEllipsoid ρ) ≤
      volume (⋃ p ∈ jtIntSites r, coordCube p.1 p.2.1 p.2.2) :=
    measure_mono hsub
  have hunion : volume (⋃ p ∈ jtIntSites r, coordCube p.1 p.2.1 p.2.2) ≤
      ∑ p ∈ jtIntSites r, volume (coordCube p.1 p.2.1 p.2.2) :=
    measure_biUnion_finset_le _ _
  have hsum : ∑ p ∈ jtIntSites r, volume (coordCube p.1 p.2.1 p.2.2) =
      ∑ p ∈ jtIntSites r, (1 : ENNReal) := by
    refine Finset.sum_congr rfl ?_
    intro p _; rw [volume_coordCube]
  have hcard : ∑ p ∈ jtIntSites r, (1 : ENNReal) = (jtIntSites r).card := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hvol : volume (jtEllipsoid ρ) ≤ (jtIntSites r).card := by
    calc volume (jtEllipsoid ρ)
        ≤ volume (⋃ p ∈ jtIntSites r, coordCube p.1 p.2.1 p.2.2) := hle
      _ ≤ ∑ p ∈ jtIntSites r, volume (coordCube p.1 p.2.1 p.2.2) := hunion
      _ = (jtIntSites r).card := by rw [hsum, hcard]
  have : (volume (jtEllipsoid ρ)).toReal ≤ ((jtIntSites r).card : ENNReal).toReal :=
    ENNReal.toReal_mono (by simp) hvol
  simpa using this

/-! ### Finite Jiao–Torquato packings -/

noncomputable def jtSiteIsom (a b c : ℤ) (ε : Bool) : ℝ³ ≃ᵢ ℝ³ :=
  cond ε (jtPartnerIsom a b c) (jtTranslate a b c)

lemma jtLatticeVec_injective {a b c a' b' c' : ℤ}
    (h : jtLatticeVec a b c = jtLatticeVec a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h' : jtMap (pt (a : ℝ) (b : ℝ) (c : ℝ)) = jtMap (pt (a' : ℝ) (b' : ℝ) (c' : ℝ)) := by
    simpa [jtLatticeVec_eq_map] using h
  have heq : pt (a : ℝ) (b : ℝ) (c : ℝ) = pt (a' : ℝ) (b' : ℝ) (c' : ℝ) := by
    calc pt (a : ℝ) (b : ℝ) (c : ℝ)
        = jtInvVec (jtMap (pt (a : ℝ) (b : ℝ) (c : ℝ))) := (jtInvVec_jtMap _).symm
      _ = jtInvVec (jtMap (pt (a' : ℝ) (b' : ℝ) (c' : ℝ))) := by rw [h']
      _ = pt (a' : ℝ) (b' : ℝ) (c' : ℝ) := jtInvVec_jtMap _
  have hp := pt_coord (a : ℝ) (b : ℝ) (c : ℝ)
  have hp' := pt_coord (a' : ℝ) (b' : ℝ) (c' : ℝ)
  have h0 : (a : ℝ) = a' := by
    have := congrArg (fun p : ℝ³ => p 0) heq
    simpa [hp.1, hp'.1] using this
  have h1 : (b : ℝ) = b' := by
    have := congrArg (fun p : ℝ³ => p 1) heq
    simpa [hp.2.1, hp'.2.1] using this
  have h2 : (c : ℝ) = c' := by
    have := congrArg (fun p : ℝ³ => p 2) heq
    simpa [hp.2.2, hp'.2.2] using this
  exact ⟨Int.cast_injective h0, Int.cast_injective h1, Int.cast_injective h2⟩

lemma jtTranslate_injective {a b c a' b' c' : ℤ}
    (h : jtTranslate a b c = jtTranslate a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h0 := congrArg (fun f : ℝ³ ≃ᵢ ℝ³ => f 0) h
  simp only [jtTranslate_apply, zero_add] at h0
  exact jtLatticeVec_injective h0

lemma jtPartnerIsom_injective {a b c a' b' c' : ℤ}
    (h : jtPartnerIsom a b c = jtPartnerIsom a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h0 : partnerIsom 0 + jtLatticeVec a b c = partnerIsom 0 + jtLatticeVec a' b' c' := by
    have := congrArg (fun f : ℝ³ ≃ᵢ ℝ³ => f 0) h
    simpa [jtPartnerIsom_apply] using this
  exact jtLatticeVec_injective (add_left_cancel h0)

lemma jtTranslate_diff (a b c : ℤ) (p : ℝ³) :
    jtTranslate a b c p - jtTranslate a b c 0 = p := by
  simp [jtTranslate_apply]

lemma jtPartner_diff (a b c : ℤ) (p : ℝ³) :
    jtPartnerIsom a b c p - jtPartnerIsom a b c 0 = partnerIsom p - partnerIsom 0 := by
  simp [jtPartnerIsom_apply]

lemma partnerIsom_sub_zero (p : ℝ³) : partnerIsom p - partnerIsom 0 = -p := by
  simp [partnerIsom_apply]

lemma jtTranslate_ne_partner (a b c a' b' c' : ℤ) :
    jtTranslate a b c ≠ jtPartnerIsom a' b' c' := by
  intro h
  have he := congrArg (fun f : ℝ³ ≃ᵢ ℝ³ => f (pt 1 0 0) - f 0) h
  have : pt 1 0 0 = -pt 1 0 0 := by
    calc pt 1 0 0 = jtTranslate a b c (pt 1 0 0) - jtTranslate a b c 0 :=
          (jtTranslate_diff a b c _).symm
      _ = jtPartnerIsom a' b' c' (pt 1 0 0) - jtPartnerIsom a' b' c' 0 := he
      _ = partnerIsom (pt 1 0 0) - partnerIsom 0 := jtPartner_diff _ _ _ _
      _ = -pt 1 0 0 := partnerIsom_sub_zero _
  have h0 := congrArg (fun p : ℝ³ => p 0) this
  simp [pt] at h0
  linarith

lemma jtSiteIsom_injective {a b c a' b' c' : ℤ} {ε ε' : Bool}
    (h : jtSiteIsom a b c ε = jtSiteIsom a' b' c' ε') :
    a = a' ∧ b = b' ∧ c = c' ∧ ε = ε' := by
  cases ε <;> cases ε'
  · have := jtTranslate_injective (by simpa [jtSiteIsom] using h)
    exact ⟨this.1, this.2.1, this.2.2, rfl⟩
  · exact (jtTranslate_ne_partner a b c a' b' c' (by simpa [jtSiteIsom] using h)).elim
  · exact (jtTranslate_ne_partner a' b' c' a b c (by simpa [jtSiteIsom] using h.symm)).elim
  · have := jtPartnerIsom_injective (by simpa [jtSiteIsom] using h)
    exact ⟨this.1, this.2.1, this.2.2, rfl⟩

noncomputable def jtSiteEmbedding : (ℤ × ℤ × ℤ) × Bool ↪ (ℝ³ ≃ᵢ ℝ³) where
  toFun q := jtSiteIsom q.1.1 q.1.2.1 q.1.2.2 q.2
  inj' := by
    intro q q' h
    have := jtSiteIsom_injective h
    ext <;> simp [this]

noncomputable def jtPacking (R : ℝ) : Finset (ℝ³ ≃ᵢ ℝ³) :=
  ((jtIntSites (R - 7)) ×ˢ (Finset.univ : Finset Bool)).map jtSiteEmbedding

lemma jtPacking_card (R : ℝ) :
    (jtPacking R).card = 2 * (jtIntSites (R - 7)).card := by
  rw [jtPacking, Finset.card_map, Finset.card_product, Finset.card_univ, Fintype.card_bool,
    mul_comm]

lemma jtSiteIsom_image_subset {a b c : ℤ} {ε : Bool} {R : ℝ}
    (h : ‖jtLatticeVec a b c‖ + 7 ≤ R) :
    jtSiteIsom a b c ε '' truncatedTetrahedron ⊆ closedBall (0 : ℝ³) R := by
  cases ε
  · simpa [jtSiteIsom] using T_translate_subset_ball a b c h
  · simpa [jtSiteIsom] using partner_translate_subset_ball a b c h

lemma jtSiteIsom_interiors {a b c a' b' c' : ℤ} {ε ε' : Bool}
    (hne : ¬ (a = a' ∧ b = b' ∧ c = c' ∧ ε = ε')) :
    interior (jtSiteIsom a b c ε '' truncatedTetrahedron) ∩
      interior (jtSiteIsom a' b' c' ε' '' truncatedTetrahedron) = ∅ := by
  cases ε <;> cases ε'
  · have hne' : ¬ (a = a' ∧ b = b' ∧ c = c') := by
      intro h; exact hne ⟨h.1, h.2.1, h.2.2, rfl⟩
    simpa [jtSiteIsom] using T_translate_interiors_disjoint hne'
  · simpa [jtSiteIsom] using T_partner_translate_interiors_disjoint a b c a' b' c'
  · have := T_partner_translate_interiors_disjoint a' b' c' a b c
    rw [inter_comm] at this
    simpa [jtSiteIsom] using this
  · have hne' : ¬ (a = a' ∧ b = b' ∧ c = c') := by
      intro h; exact hne ⟨h.1, h.2.1, h.2.2, rfl⟩
    simpa [jtSiteIsom] using partner_translate_interiors_disjoint hne'

lemma isFinitePacking_jt (R : ℝ) :
    IsFinitePacking truncatedTetrahedron (jtPacking R) (closedBall (0 : ℝ³) R) := by
  constructor
  · intro f hf
    have hf' : f ∈ ((jtIntSites (R - 7)) ×ˢ (Finset.univ : Finset Bool)).map
        jtSiteEmbedding := by
      simpa [jtPacking] using hf
    rcases Finset.mem_map.mp hf' with ⟨q, hq, rfl⟩
    have hqsite : q.1 ∈ jtIntSites (R - 7) := (Finset.mem_product.mp hq).1
    have hnorm : ‖jtLatticeVec q.1.1 q.1.2.1 q.1.2.2‖ ≤ R - 7 :=
      (mem_jtIntSites.mp hqsite).2.2.2
    have : ‖jtLatticeVec q.1.1 q.1.2.1 q.1.2.2‖ + 7 ≤ R := by linarith
    exact jtSiteIsom_image_subset this
  · intro f hf g hg hfg
    have hf' : f ∈ ((jtIntSites (R - 7)) ×ˢ (Finset.univ : Finset Bool)).map
        jtSiteEmbedding := by
      simpa [jtPacking] using hf
    have hg' : g ∈ ((jtIntSites (R - 7)) ×ˢ (Finset.univ : Finset Bool)).map
        jtSiteEmbedding := by
      simpa [jtPacking] using hg
    rcases Finset.mem_map.mp hf' with ⟨q, hq, rfl⟩
    rcases Finset.mem_map.mp hg' with ⟨q', hq', rfl⟩
    apply jtSiteIsom_interiors
    intro heq
    apply hfg
    have : q = q' := by
      ext <;> simp [heq]
    subst this
    rfl

lemma volume_closedBall_formula (R : ℝ) :
    volume (closedBall (0 : ℝ³) R) =
      (ENNReal.ofReal R) ^ 3 *
        ENNReal.ofReal (Real.sqrt Real.pi ^ 3 / Real.Gamma ((3 : ℝ) / 2 + 1)) := by
  simpa [Fintype.card_fin] using EuclideanSpace.volume_closedBall (Fin 3) (0 : ℝ³) R

lemma volume_closedBall_toReal (R : ℝ) (hR : 0 ≤ R) :
    (volume (closedBall (0 : ℝ³) R)).toReal =
      R ^ 3 * (volume (closedBall (0 : ℝ³) 1)).toReal := by
  rw [volume_closedBall_formula R, volume_closedBall_formula 1]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1)]
  ring

lemma volume_closedBall_ne_top (R : ℝ) :
    volume (closedBall (0 : ℝ³) R) ≠ ⊤ := by
  rw [volume_closedBall_formula]
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top

lemma volume_closedBall_toReal_of_nonpos {R : ℝ} (hR : R ≤ 0) :
    (volume (closedBall (0 : ℝ³) R)).toReal = 0 := by
  rw [volume_closedBall_formula]
  have : ENNReal.ofReal R = 0 := ENNReal.ofReal_eq_zero.mpr hR
  simp [this]

lemma volume_closedBall_pos : 0 < (volume (closedBall (0 : ℝ³) (1 : ℝ))).toReal := by
  have h : 0 < volume (closedBall (0 : ℝ³) (1 : ℝ)) :=
    measure_closedBall_pos volume (0 : ℝ³) (by norm_num : (0 : ℝ) < 1)
  exact ENNReal.toReal_pos h.ne' (volume_closedBall_ne_top 1)

lemma convex_T : Convex ℝ truncatedTetrahedron :=
  convex_convexHull _ _

lemma isClosed_T : IsClosed truncatedTetrahedron :=
  (Finite.isCompact_convexHull (finite_range TTVertex)).isClosed

lemma volume_frontier_T : volume (frontier truncatedTetrahedron) = 0 :=
  convex_T.addHaar_frontier volume

lemma volume_interior_T :
    volume (interior truncatedTetrahedron) = volume truncatedTetrahedron := by
  have hsplit : (truncatedTetrahedron : Set ℝ³) =
      interior truncatedTetrahedron ∪ frontier truncatedTetrahedron := by
    calc truncatedTetrahedron
        = closure truncatedTetrahedron := isClosed_T.closure_eq.symm
      _ = interior truncatedTetrahedron ∪ frontier truncatedTetrahedron :=
        closure_eq_interior_union_frontier _
  have hfr : MeasurableSet (frontier truncatedTetrahedron) :=
    isClosed_frontier.measurableSet
  have hU := measure_union (μ := volume)
      (disjoint_interior_frontier (s := truncatedTetrahedron)) hfr
  rw [← hsplit, volume_frontier_T, add_zero] at hU
  exact hU.symm

lemma abs_det_linearIsometry (L : ℝ³ ≃ₗᵢ[ℝ] ℝ³) :
    |LinearMap.det (L.toLinearEquiv : ℝ³ →ₗ[ℝ] ℝ³)| = 1 := by
  have himg : (L.toLinearEquiv : ℝ³ →ₗ[ℝ] ℝ³) '' closedBall (0 : ℝ³) 1 =
      closedBall (0 : ℝ³) 1 := by
    ext x
    simp only [mem_image, mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [L.norm_map] using hy
    · intro hx
      refine ⟨L.symm x, ?_, L.apply_symm_apply x⟩
      simpa [L.symm.norm_map] using hx
  have hvol := Measure.addHaar_image_linearMap (μ := volume)
      (L.toLinearEquiv : ℝ³ →ₗ[ℝ] ℝ³) (closedBall (0 : ℝ³) 1)
  rw [himg] at hvol
  have hrt := congrArg ENNReal.toReal hvol
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)] at hrt
  have hpos := volume_closedBall_pos
  have hmul : |LinearMap.det (L.toLinearEquiv : ℝ³ →ₗ[ℝ] ℝ³)| *
      (volume (closedBall (0 : ℝ³) 1)).toReal =
      (volume (closedBall (0 : ℝ³) 1)).toReal := hrt.symm
  exact (mul_eq_right₀ hpos.ne').mp hmul

lemma isometry_volume (f : ℝ³ ≃ᵢ ℝ³) (s : Set ℝ³) :
    volume (f '' s) = volume s := by
  let L := f.toRealLinearIsometryEquiv
  have himg : f '' s = (fun x : ℝ³ => f 0 + x) '' ((L.toLinearEquiv : ℝ³ →ₗ[ℝ] ℝ³) '' s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨f x - f 0, ⟨x, hx, ?_⟩, ?_⟩
      · simp [L, IsometryEquiv.toRealLinearIsometryEquiv_apply]
      · simp [L, IsometryEquiv.toRealLinearIsometryEquiv_apply]; try abel
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      simp [L, IsometryEquiv.toRealLinearIsometryEquiv_apply]; try abel
  rw [himg, volume_vadd]
  have hlin := Measure.addHaar_image_linearMap (μ := volume)
      (L.toLinearEquiv : ℝ³ →ₗ[ℝ] ℝ³) s
  have hdet := abs_det_linearIsometry L
  rw [hlin, hdet, ENNReal.ofReal_one, one_mul]

lemma volume_T_ne_top : volume truncatedTetrahedron ≠ ⊤ := by
  rw [volume_truncatedTetrahedron]
  exact ENNReal.ofReal_ne_top

lemma interiors_pack_le_ball {R : ℝ} {fs : Finset (ℝ³ ≃ᵢ ℝ³)}
    (hsub : ∀ f ∈ fs, (f : ℝ³ ≃ᵢ ℝ³) '' truncatedTetrahedron ⊆ closedBall (0 : ℝ³) R)
    (hdisj : ∀ f ∈ fs, ∀ g ∈ fs, f ≠ g →
      interior ((f : ℝ³ ≃ᵢ ℝ³) '' truncatedTetrahedron) ∩
        interior ((g : ℝ³ ≃ᵢ ℝ³) '' truncatedTetrahedron) = ∅) :
    (fs.card : ENNReal) * volume (interior truncatedTetrahedron) ≤
      volume (closedBall (0 : ℝ³) R) := by
  have hU :
      volume (⋃ f ∈ fs, interior (f '' truncatedTetrahedron)) ≤
        volume (closedBall (0 : ℝ³) R) := by
    apply measure_mono
    intro x hx
    rcases mem_iUnion.mp hx with ⟨f, hf⟩
    rcases mem_iUnion.mp hf with ⟨hfmem, hxint⟩
    exact hsub f hfmem (interior_subset hxint)
  have hsum :
      volume (⋃ f ∈ fs, interior (f '' truncatedTetrahedron)) =
        ∑ f ∈ fs, volume (interior (f '' truncatedTetrahedron)) := by
    refine measure_biUnion_finset ?_ ?_
    · intro f hf g hg hfg
      exact disjoint_iff_inter_eq_empty.mpr (hdisj f hf g hg hfg)
    · intro f hf
      exact measurableSet_interior
  have himg : ∀ f : ℝ³ ≃ᵢ ℝ³,
      volume (interior (f '' truncatedTetrahedron)) =
        volume (interior truncatedTetrahedron) := by
    intro f
    rw [interior_image_isometry, isometry_volume]
  have hconst : ∑ f ∈ fs, volume (interior (f '' truncatedTetrahedron)) =
      fs.card * volume (interior truncatedTetrahedron) := by
    rw [Finset.sum_congr rfl (fun f _ => himg f), Finset.sum_const, nsmul_eq_mul]
  rw [hsum, hconst] at hU
  exact hU

lemma density_le_one (R : ℝ) {d : ℝ} (hd : d ∈ densitiesInBall truncatedTetrahedron R) :
    d ≤ 1 := by
  rcases hd with ⟨fs, ⟨hsub, hdisj⟩, rfl⟩
  by_cases hRpos : 0 < R
  · have hden : 0 < (volume (closedBall (0 : ℝ³) R)).toReal := by
      rw [volume_closedBall_toReal R hRpos.le]
      exact mul_pos (pow_pos hRpos 3) volume_closedBall_pos
    have hinteriors := interiors_pack_le_ball hsub hdisj
    rw [volume_interior_T] at hinteriors
    have hreal : (fs.card : ℝ) * (volume truncatedTetrahedron).toReal ≤
        (volume (closedBall (0 : ℝ³) R)).toReal := by
      have := ENNReal.toReal_mono (volume_closedBall_ne_top R) hinteriors
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at this
      exact this
    rwa [div_le_one hden]
  · have hR : R ≤ 0 := le_of_not_gt hRpos
    rw [volume_closedBall_toReal_of_nonpos hR]
    simp

lemma bddAbove_densities (R : ℝ) : BddAbove (densitiesInBall truncatedTetrahedron R) :=
  ⟨1, fun _ hd => density_le_one R hd⟩

lemma packingDensity_le_one (R : ℝ) :
    packingDensityInBall truncatedTetrahedron R ≤ 1 := by
  refine csSup_le ?_ (fun _ hd => density_le_one R hd)
  exact ⟨0, ⟨∅, ⟨by intro f hf; exact (Finset.notMem_empty f hf).elim,
    by intro f hf; exact (Finset.notMem_empty f hf).elim⟩, by simp⟩⟩

lemma packingDensity_nonneg (R : ℝ) :
    0 ≤ packingDensityInBall truncatedTetrahedron R := by
  refine le_csSup (bddAbove_densities R) ?_
  exact ⟨∅, ⟨by intro f hf; exact (Finset.notMem_empty f hf).elim,
    by intro f hf; exact (Finset.notMem_empty f hf).elim⟩, by simp⟩

lemma packing_density_ge {R : ℝ} (hR : 22 ≤ R) :
    (207 / 208) * ((R - 22) / R) ^ 3 ≤ packingDensityInBall truncatedTetrahedron R := by
  have hR0 : 0 ≤ R := by linarith
  have hρ : 0 ≤ R - 22 := by linarith
  have hrel : (R - 22) + 15 ≤ R - 7 := by linarith
  have hpack := isFinitePacking_jt R
  let d := (jtPacking R).card * (volume truncatedTetrahedron).toReal /
      (volume (closedBall (0 : ℝ³) R)).toReal
  have hd : d ∈ densitiesInBall truncatedTetrahedron R := ⟨jtPacking R, hpack, rfl⟩
  have hle : d ≤ packingDensityInBall truncatedTetrahedron R :=
    le_csSup (bddAbove_densities R) hd
  have hcard : (jtPacking R).card = 2 * (jtIntSites (R - 7)).card := jtPacking_card R
  have hcast : ((jtPacking R).card : ℝ) = 2 * ((jtIntSites (R - 7)).card : ℝ) := by
    rw [hcard, Nat.cast_mul, Nat.cast_ofNat]
  have hcount : (volume (jtEllipsoid (R - 22))).toReal ≤ (jtIntSites (R - 7)).card :=
    card_sites_ge_vol hρ hrel
  have hvT : (volume truncatedTetrahedron).toReal = 184 / 3 := volume_T_toReal
  have hvE : (volume (jtEllipsoid (R - 22))).toReal =
      (volume (closedBall (0 : ℝ³) (R - 22))).toReal / (3328 / 27) :=
    volume_jtEllipsoid_toReal (R - 22) hρ
  have hvB := volume_closedBall_toReal R hR0
  have hvBρ := volume_closedBall_toReal (R - 22) hρ
  have hRpos : 0 < R := by linarith
  have hdenpos : 0 < (volume (closedBall (0 : ℝ³) R)).toReal := by
    rw [hvB]; exact mul_pos (pow_pos hRpos 3) volume_closedBall_pos
  have hratio : (volume (closedBall (0 : ℝ³) (R - 22))).toReal /
      (volume (closedBall (0 : ℝ³) R)).toReal = ((R - 22) / R) ^ 3 := by
    rw [hvBρ, hvB]
    have hunit : (volume (closedBall (0 : ℝ³) 1)).toReal ≠ 0 := volume_closedBall_pos.ne'
    field_simp [hunit, hRpos.ne']
    try ring
  have d_eq : d = (2 * ((jtIntSites (R - 7)).card : ℝ)) * (184 / 3) /
      (volume (closedBall (0 : ℝ³) R)).toReal := by
    simp only [d, hcast, hvT]
  have hge : 2 * (volume (jtEllipsoid (R - 22))).toReal * (184 / 3) /
        (volume (closedBall (0 : ℝ³) R)).toReal ≤
      (2 * ((jtIntSites (R - 7)).card : ℝ)) * (184 / 3) /
        (volume (closedBall (0 : ℝ³) R)).toReal := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hdenpos)
    nlinarith [hcount, show (0 : ℝ) ≤ 184 / 3 by norm_num]
  have hrew : 2 * (volume (jtEllipsoid (R - 22))).toReal * (184 / 3) /
        (volume (closedBall (0 : ℝ³) R)).toReal =
      (207 / 208) * ((R - 22) / R) ^ 3 := by
    have htmp : 2 * (volume (jtEllipsoid (R - 22))).toReal * (184 / 3) /
          (volume (closedBall (0 : ℝ³) R)).toReal =
        (2 * (184 / 3) / (3328 / 27)) *
          ((volume (closedBall (0 : ℝ³) (R - 22))).toReal /
            (volume (closedBall (0 : ℝ³) R)).toReal) := by
      rw [hvE]
      field_simp
      try ring
    rw [htmp, two_vol_T_div_det, hratio]
  have htarget : (207 / 208) * ((R - 22) / R) ^ 3 ≤ d := by
    rw [d_eq, ← hrew]
    exact hge
  exact htarget.trans hle

lemma tendsto_packing_ratio :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ) - 22) / n) Filter.atTop (nhds 1) := by
  have h0 : Filter.Tendsto (fun n : ℕ => (22 : ℝ) / n) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 22
  have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - 22 / n) Filter.atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub h0
  have h1' : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - 22 / n) Filter.atTop (nhds 1) := by
    simpa using h1
  have heq : (fun n : ℕ => ((n : ℝ) - 22) / n) =ᶠ[Filter.atTop]
      (fun n : ℕ => (1 : ℝ) - 22 / n) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
    field_simp [hn0]
  exact Filter.Tendsto.congr' heq.symm h1'

lemma packing_density_liminf_ge :
    (207 / 208 : ℝ) ≤
      Filter.atTop.liminf (fun n : ℕ => packingDensityInBall truncatedTetrahedron (n : ℝ)) := by
  have hbd : Filter.atTop.IsBoundedUnder (· ≥ ·)
      (fun n : ℕ => packingDensityInBall truncatedTetrahedron (n : ℝ)) :=
    Filter.isBoundedUnder_of_eventually_ge (a := (0 : ℝ))
      (Filter.Eventually.of_forall fun n => packingDensity_nonneg n)
  have hcb : Filter.atTop.IsCoboundedUnder (· ≥ ·)
      (fun n : ℕ => packingDensityInBall truncatedTetrahedron (n : ℝ)) :=
    Filter.IsCoboundedUnder.of_frequently_le (a := (1 : ℝ))
      (Filter.Frequently.of_forall fun n => packingDensity_le_one (n : ℝ))
  refine (Filter.le_liminf_iff' hcb hbd).mpr ?_
  intro y hy
  have htend : Filter.Tendsto
      (fun n : ℕ => (207 / 208 : ℝ) * (((n : ℝ) - 22) / n) ^ 3)
      Filter.atTop (nhds ((207 / 208) * (1 : ℝ) ^ 3)) :=
    (tendsto_packing_ratio.pow 3).const_mul _
  have hlim : Filter.Tendsto
      (fun n : ℕ => (207 / 208 : ℝ) * (((n : ℝ) - 22) / n) ^ 3)
      Filter.atTop (nhds (207 / 208)) := by
    convert htend using 2
    ring
  have hnhds : ∀ᶠ z in nhds (207 / 208 : ℝ), y ≤ z :=
    eventually_ge_nhds hy
  have hev := hlim.eventually hnhds
  filter_upwards [hev, Filter.eventually_ge_atTop 22] with n hn hN
  have hge := packing_density_ge (R := (n : ℝ)) (by exact_mod_cast hN)
  exact hn.trans hge

lemma packing_density_limsup_ge :
    (207 / 208 : ℝ) ≤ max_packing_density_truncated_tetrahedra := by
  have hbd : Filter.atTop.IsBoundedUnder (· ≤ ·)
      (fun n : ℕ => packingDensityInBall truncatedTetrahedron (n : ℝ)) :=
    Filter.isBoundedUnder_of_eventually_le (a := (1 : ℝ))
      (Filter.Eventually.of_forall fun n => packingDensity_le_one n)
  have hbd' : Filter.atTop.IsBoundedUnder (· ≥ ·)
      (fun n : ℕ => packingDensityInBall truncatedTetrahedron (n : ℝ)) :=
    Filter.isBoundedUnder_of_eventually_ge (a := (0 : ℝ))
      (Filter.Eventually.of_forall fun n => packingDensity_nonneg n)
  exact packing_density_liminf_ge.trans (Filter.liminf_le_limsup hbd hbd')

lemma packing_density_limsup_le_one :
    max_packing_density_truncated_tetrahedra ≤ 1 := by
  have hbd : Filter.atTop.IsBoundedUnder (· ≤ ·)
      (fun n : ℕ => packingDensityInBall truncatedTetrahedron (n : ℝ)) :=
    Filter.isBoundedUnder_of_eventually_le (a := (1 : ℝ))
      (Filter.Eventually.of_forall fun n => packingDensity_le_one n)
  have hcb : Filter.atTop.IsCoboundedUnder (· ≤ ·)
      (fun n : ℕ => packingDensityInBall truncatedTetrahedron (n : ℝ)) :=
    Filter.IsCoboundedUnder.of_frequently_ge (a := (0 : ℝ))
      (Filter.Frequently.of_forall fun n => packingDensity_nonneg n)
  refine (Filter.limsup_le_iff hcb hbd).mpr ?_
  intro y hy
  exact Filter.Eventually.of_forall fun n =>
    (packingDensity_le_one (n : ℝ)).trans_lt hy

/-! ### The gauge body `Ω` and the critical-determinant bound -/

/-- Gauge of the 0-symmetric polytope
`Ω = { p | |x| ≤ 1, |y| ≤ 1, |z| ≤ 1, |x + y - z| ≤ 2 }`. -/
noncomputable def gOmega (p : ℝ³) : ℝ :=
  max (max (|p 0|) (|p 1|)) (max (|p 2|) (|p 0 + p 1 - p 2| / 2))

lemma gOmega_nonneg (p : ℝ³) : 0 ≤ gOmega p := by
  simp only [gOmega]
  exact le_max_of_le_left (le_max_of_le_left (abs_nonneg _))

lemma gOmega_neg (p : ℝ³) : gOmega (-p) = gOmega p := by
  unfold gOmega
  congr 1
  · congr 1 <;> simp [abs_neg]
  · congr 1
    · simp [abs_neg]
    · have : -p 0 + -p 1 - -p 2 = -(p 0 + p 1 - p 2) := by
        simp [PiLp.neg_apply]; ring
      simp only [PiLp.neg_apply]
      rw [this, abs_neg]

lemma gOmega_smul_nonneg {c : ℝ} (hc : 0 ≤ c) (p : ℝ³) :
    gOmega (c • p) = c * gOmega p := by
  unfold gOmega
  have hmul (x : ℝ) : |c * x| = c * |x| := by
    rw [abs_mul, abs_of_nonneg hc]
  simp only [PiLp.smul_apply, smul_eq_mul, hmul]
  have h2 : |c * p 0 + c * p 1 - c * p 2| = c * |p 0 + p 1 - p 2| := by
    have : c * p 0 + c * p 1 - c * p 2 = c * (p 0 + p 1 - p 2) := by ring
    rw [this, abs_mul, abs_of_nonneg hc]
  have h2' : |c * p 0 + c * p 1 - c * p 2| / 2 = c * (|p 0 + p 1 - p 2| / 2) := by
    rw [h2]; ring
  rw [h2']
  set a := |p 0|
  set b := |p 1|
  set d := |p 2|
  set e := |p 0 + p 1 - p 2| / 2
  change max (max (c * a) (c * b)) (max (c * d) (c * e)) = c * max (max a b) (max d e)
  rw [← mul_max_of_nonneg (a := c) a b hc, ← mul_max_of_nonneg (a := c) d e hc,
      ← mul_max_of_nonneg (a := c) (max a b) (max d e) hc]

/-- AM-GM for three nonnegative reals. -/
lemma am_gm3 {t s u : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hu : 0 ≤ u) :
    t * s * u ≤ ((t + s + u) / 3) ^ 3 := by
  have hw : (1 / 3 : ℝ) + 1 / 3 + 1 / 3 = 1 := by norm_num
  have h := Real.geom_mean_le_arith_mean3_weighted
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num) (by norm_num)
    ht hs hu hw
  have hnon : 0 ≤ t ^ (1 / 3 : ℝ) * s ^ (1 / 3 : ℝ) * u ^ (1 / 3 : ℝ) := by
    refine mul_nonneg (mul_nonneg ?_ ?_) ?_
    · exact Real.rpow_nonneg ht _
    · exact Real.rpow_nonneg hs _
    · exact Real.rpow_nonneg hu _
  have h3 := pow_le_pow_left₀ hnon h 3
  have ht3 : (t ^ (1 / 3 : ℝ)) ^ 3 = t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    norm_num
  have hs3 : (s ^ (1 / 3 : ℝ)) ^ 3 = s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    norm_num
  have hu3 : (u ^ (1 / 3 : ℝ)) ^ 3 = u := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu]
    norm_num
  have hprod : (t ^ (1 / 3 : ℝ) * s ^ (1 / 3 : ℝ) * u ^ (1 / 3 : ℝ)) ^ 3 =
      t * s * u := by
    rw [mul_pow, mul_pow, ht3, hs3, hu3]
  have hrhs : ((1 / 3 : ℝ) * t + (1 / 3) * s + (1 / 3) * u) ^ 3 =
      ((t + s + u) / 3) ^ 3 := by
    have : (1 / 3 : ℝ) * t + (1 / 3) * s + (1 / 3) * u = (t + s + u) / 3 := by
      ring
    rw [this]
  rw [hprod, hrhs] at h3
  exact h3

/-- The cyclic 3-parameter family containing the Jiao–Torquato lattice
in `Ω`-coordinates: columns `(1, 0, t)`, `(-s, 1, 0)`, `(0, u, 1)`.
Its determinant is `|1 - t * s * u|`.  Admissibility forces `t, s, u ≥ 0`
and `t + s + u ≤ 1` in the relevant chamber, hence AM-GM yields
`t * s * u ≤ 1/27` and `det ≥ 26/27`. -/
lemma cyclic_family_det_ge {t s u : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hu : 0 ≤ u) (hsum : t + s + u ≤ 1) :
    26 / 27 ≤ |1 - t * s * u| := by
  have hprod : t * s * u ≤ 1 / 27 := by
    have hgm := am_gm3 ht hs hu
    have h3 : ((t + s + u) / 3) ^ 3 ≤ (1 / 3 : ℝ) ^ 3 := by
      apply pow_le_pow_left₀
      · exact div_nonneg (add_nonneg (add_nonneg ht hs) hu) (by norm_num)
      · linarith
    have : (1 / 3 : ℝ) ^ 3 = 1 / 27 := by norm_num
    linarith
  have h1 : t * s * u ≤ 1 := le_trans hprod (by norm_num)
  have hnn : 0 ≤ 1 - t * s * u := sub_nonneg.mpr h1
  rw [abs_of_nonneg hnn]
  linarith

lemma cyclic_family_jt :
    let t := (1 / 3 : ℝ)
    |1 - t * t * t| = 26 / 27 := by
  norm_num

/-- Six-parameter based lattice with columns on the cube faces `x=1`, `y=1`, `z=1`. -/
noncomputable def xyzMatrix (b c d f g h : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, d, g; b, 1, h; c, f, 1]

lemma xyzMatrix_det (b c d f g h : ℝ) :
    Matrix.det (xyzMatrix b c d f g h) =
      1 - b * d - f * h - c * g + b * f * g + c * d * h := by
  simp [xyzMatrix, Matrix.det_fin_three]
  ring

lemma xyzMatrix_det_special (b f g : ℝ) :
    Matrix.det (xyzMatrix b 0 0 f g 0) = 1 + b * f * g := by
  rw [xyzMatrix_det]
  ring

/-- Cut linear form `L(p) = x + y - z`. -/
noncomputable def cutForm (p : ℝ³) : ℝ := p 0 + p 1 - p 2

lemma gOmega_ge_cut (p : ℝ³) : |cutForm p| / 2 ≤ gOmega p := by
  simp only [gOmega, cutForm]
  exact le_max_of_le_right (le_max_right _ _)

lemma gOmega_ge_coord (p : ℝ³) (i : Fin 3) : |p i| ≤ gOmega p := by
  simp only [gOmega]
  fin_cases i
  · exact le_max_of_le_left (le_max_left _ _)
  · exact le_max_of_le_left (le_max_right _ _)
  · exact le_max_of_le_right (le_max_left _ _)

/-- The corner tetrahedron `τ = { p | ‖p‖_∞ ≤ 1, x + y - z ≥ 2 }`. -/
def cornerTau : Set ℝ³ :=
  {p | |p 0| ≤ 1 ∧ |p 1| ≤ 1 ∧ |p 2| ≤ 1 ∧ 2 ≤ cutForm p}

lemma mem_cornerTau {p : ℝ³} :
    p ∈ cornerTau ↔ |p 0| ≤ 1 ∧ |p 1| ≤ 1 ∧ |p 2| ≤ 1 ∧ 2 ≤ cutForm p :=
  Iff.rfl

/-- If `gOmega p < 1` then `p` lies in the interior of `Ω`. -/
lemma gOmega_lt_one_of_int {p : ℝ³} (h : gOmega p < 1) :
    |p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1 ∧ |cutForm p| < 2 := by
  have h0 := (gOmega_ge_coord p 0).trans_lt h
  have h1 := (gOmega_ge_coord p 1).trans_lt h
  have h2 := (gOmega_ge_coord p 2).trans_lt h
  have hc := (gOmega_ge_cut p).trans_lt h
  refine ⟨h0, h1, h2, ?_⟩
  have : |cutForm p| / 2 < 1 := hc
  linarith

/-- A lattice generated by an `xyzMatrix` is encoded by integer combinations. -/
noncomputable def xyzVec (b c d f g h : ℝ) (n0 n1 n2 : ℤ) : ℝ³ :=
  (n0 : ℝ) • pt 1 b c + (n1 : ℝ) • pt d 1 f + (n2 : ℝ) • pt g h 1

lemma xyzVec_apply (b c d f g h : ℝ) (n0 n1 n2 : ℤ) :
    xyzVec b c d f g h n0 n1 n2 =
      pt ((n0 : ℝ) + n1 * d + n2 * g)
         ((n0 : ℝ) * b + n1 + n2 * h)
         ((n0 : ℝ) * c + n1 * f + n2) := by
  simp only [xyzVec, pt_smul, pt_add]
  congr 1 <;> ring

lemma xyzVec_cut (b c d f g h : ℝ) (n0 n1 n2 : ℤ) :
    cutForm (xyzVec b c d f g h n0 n1 n2) =
      ((n0 : ℝ) + n1 * d + n2 * g) + ((n0 : ℝ) * b + n1 + n2 * h)
        - ((n0 : ℝ) * c + n1 * f + n2) := by
  rw [xyzVec_apply, cutForm]
  simp [pt]

/-- The combination `(1,1,-1)` is the first vector that can enter the cut face. -/
lemma xyzVec_one_one_neg (b c d f g h : ℝ) :
    xyzVec b c d f g h 1 1 (-1) =
      pt (1 + d - g) (b + 1 - h) (c + f - 1) := by
  rw [xyzVec_apply]
  push_cast
  congr 1 <;> ring

lemma cutForm_one_one_neg (b c d f g h : ℝ) :
    cutForm (xyzVec b c d f g h 1 1 (-1)) =
      3 + b + d - c - f - g - h := by
  rw [xyzVec_one_one_neg, cutForm]
  simp [pt]
  ring

/-- In the cyclic chamber `c = d = h = 0`, `b = -t`, `f = s`, `g = u`
the cut form of `(1,1,-1)` is `3 - t - s - u`. -/
lemma cutForm_cyclic (t s u : ℝ) :
    cutForm (xyzVec (-t) 0 0 s u 0 1 1 (-1)) = 3 - t - s - u := by
  rw [cutForm_one_one_neg]
  ring

lemma pt_coord0 (x y z : ℝ) : (pt x y z) 0 = x := by simp [pt]
lemma pt_coord1 (x y z : ℝ) : (pt x y z) 1 = y := by simp [pt]
lemma pt_coord2 (x y z : ℝ) : (pt x y z) 2 = z := by simp [pt]

lemma gOmega_pt (x y z : ℝ) :
    gOmega (pt x y z) = max (max (|x|) (|y|)) (max (|z|) (|x + y - z| / 2)) := by
  simp only [gOmega, pt_coord0, pt_coord1, pt_coord2]

lemma max4_eq_one {a b c d : ℝ}
    (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) (hd : d ≤ 1)
    (h1 : a = 1 ∨ b = 1 ∨ c = 1 ∨ d = 1) :
    max (max a b) (max c d) = 1 := by
  have hle : max (max a b) (max c d) ≤ 1 := by
    exact max_le (max_le ha hb) (max_le hc hd)
  have hge : 1 ≤ max (max a b) (max c d) := by
    rcases h1 with h | h | h | h
    · exact le_trans (le_of_eq h.symm) (le_max_of_le_left (le_max_left _ _))
    · exact le_trans (le_of_eq h.symm) (le_max_of_le_left (le_max_right _ _))
    · exact le_trans (le_of_eq h.symm) (le_max_of_le_right (le_max_left _ _))
    · exact le_trans (le_of_eq h.symm) (le_max_of_le_right (le_max_right _ _))
  exact le_antisymm hle hge

/-- Basis vectors of the cyclic family lie on `∂Ω` when `0 ≤ t, s, u ≤ 1`. -/
lemma cyclic_gOmega_basis {t s u : ℝ}
    (ht0 : 0 ≤ t) (hs0 : 0 ≤ s) (hu0 : 0 ≤ u)
    (ht1 : t ≤ 1) (hs1 : s ≤ 1) (hu1 : u ≤ 1) :
    gOmega (xyzVec (-t) 0 0 s u 0 1 0 0) = 1 ∧
    gOmega (xyzVec (-t) 0 0 s u 0 0 1 0) = 1 ∧
    gOmega (xyzVec (-t) 0 0 s u 0 0 0 1) = 1 := by
  have hv1 : xyzVec (-t) 0 0 s u 0 1 0 0 = pt 1 (-t) 0 := by
    rw [xyzVec_apply]; push_cast; congr 1 <;> ring
  have hv2 : xyzVec (-t) 0 0 s u 0 0 1 0 = pt 0 1 s := by
    rw [xyzVec_apply]; push_cast; congr 1 <;> ring
  have hv3 : xyzVec (-t) 0 0 s u 0 0 0 1 = pt u 0 1 := by
    rw [xyzVec_apply]; push_cast; congr 1 <;> ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hv1, gOmega_pt, abs_one, abs_neg, abs_of_nonneg ht0, abs_zero]
    have hcut : |1 + -t - 0| / 2 = (1 - t) / 2 := by
      have : 1 + -t - 0 = 1 - t := by ring
      rw [this, abs_of_nonneg (sub_nonneg.mpr ht1)]
    rw [hcut]
    refine max4_eq_one (by norm_num) ht1 (by linarith) ?_ (Or.inl rfl)
    linarith
  · rw [hv2, gOmega_pt, abs_zero, abs_one, abs_of_nonneg hs0]
    have hcut : |0 + 1 - s| / 2 = (1 - s) / 2 := by
      have : 0 + 1 - s = 1 - s := by ring
      rw [this, abs_of_nonneg (sub_nonneg.mpr hs1)]
    rw [hcut]
    refine max4_eq_one (by norm_num) (by norm_num) hs1 ?_ (Or.inr (Or.inl rfl))
    linarith
  · rw [hv3, gOmega_pt, abs_of_nonneg hu0, abs_zero, abs_one]
    have hcut : |u + 0 - 1| / 2 = (1 - u) / 2 := by
      have : u + 0 - 1 = -(1 - u) := by ring
      rw [this, abs_neg, abs_of_nonneg (sub_nonneg.mpr hu1)]
    rw [hcut]
    refine max4_eq_one hu1 (by norm_num) (by norm_num) ?_ (Or.inr (Or.inr (Or.inl rfl)))
    linarith

/-! ### The body `Ω` -/

/-- The 0-symmetric polytope `{ p | gOmega p ≤ 1 }`. -/
def omegaBody : Set ℝ³ := {p | gOmega p ≤ 1}

lemma mem_omegaBody {p : ℝ³} : p ∈ omegaBody ↔ gOmega p ≤ 1 := Iff.rfl

lemma omegaBody_iff (p : ℝ³) :
    p ∈ omegaBody ↔ |p 0| ≤ 1 ∧ |p 1| ≤ 1 ∧ |p 2| ≤ 1 ∧ |cutForm p| ≤ 2 := by
  constructor
  · intro h
    have hc := (gOmega_ge_cut p).trans h
    exact ⟨(gOmega_ge_coord p 0).trans h, (gOmega_ge_coord p 1).trans h,
      (gOmega_ge_coord p 2).trans h, by linarith [hc]⟩
  · intro ⟨h0, h1, h2, hc⟩
    simp only [omegaBody, gOmega, cutForm, mem_setOf_eq] at *
    exact max_le (max_le h0 h1) (max_le h2 (by linarith))

lemma gOmega_add (p q : ℝ³) : gOmega (p + q) ≤ gOmega p + gOmega q := by
  have h0 : |p 0 + q 0| ≤ gOmega p + gOmega q :=
    (abs_add_le _ _).trans (add_le_add (gOmega_ge_coord p 0) (gOmega_ge_coord q 0))
  have h1 : |p 1 + q 1| ≤ gOmega p + gOmega q :=
    (abs_add_le _ _).trans (add_le_add (gOmega_ge_coord p 1) (gOmega_ge_coord q 1))
  have h2 : |p 2 + q 2| ≤ gOmega p + gOmega q :=
    (abs_add_le _ _).trans (add_le_add (gOmega_ge_coord p 2) (gOmega_ge_coord q 2))
  have hsum :
      |(p 0 + q 0) + (p 1 + q 1) - (p 2 + q 2)| ≤
        |p 0 + p 1 - p 2| + |q 0 + q 1 - q 2| := by
    have : (p 0 + q 0) + (p 1 + q 1) - (p 2 + q 2) =
        (p 0 + p 1 - p 2) + (q 0 + q 1 - q 2) := by ring
    rw [this]; exact abs_add_le _ _
  have hcut : |(p 0 + q 0) + (p 1 + q 1) - (p 2 + q 2)| / 2 ≤ gOmega p + gOmega q := by
    have := add_le_add (gOmega_ge_cut p) (gOmega_ge_cut q)
    simp only [cutForm] at this
    linarith
  simp only [gOmega, PiLp.add_apply]
  exact max_le (max_le h0 h1) (max_le h2 hcut)

lemma convex_omegaBody : Convex ℝ omegaBody := by
  intro x hx y hy a b ha hb hab
  simp only [omegaBody, mem_setOf_eq] at hx hy ⊢
  have := gOmega_add (a • x) (b • y)
  have ha' : gOmega (a • x) = a * gOmega x := gOmega_smul_nonneg ha x
  have hb' : gOmega (b • y) = b * gOmega y := gOmega_smul_nonneg hb y
  have : gOmega (a • x + b • y) ≤ a * gOmega x + b * gOmega y := by
    simpa [ha', hb'] using this
  calc gOmega (a • x + b • y) ≤ a * gOmega x + b * gOmega y := this
    _ ≤ a * 1 + b * 1 := by gcongr
    _ = 1 := by linarith

lemma omegaBody_neg {p : ℝ³} (hp : p ∈ omegaBody) : -p ∈ omegaBody := by
  simpa [omegaBody, gOmega_neg] using hp

lemma gOmega_zero : gOmega 0 = 0 := by
  simp [gOmega, PiLp.zero_apply]

lemma zero_mem_omegaBody : (0 : ℝ³) ∈ omegaBody := by
  simp [omegaBody, gOmega_zero]

lemma gOmega_eq_zero_iff {p : ℝ³} : gOmega p = 0 ↔ p = 0 := by
  constructor
  · intro h
    ext i
    have := (gOmega_ge_coord p i).trans_eq h
    exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
  · rintro rfl; exact gOmega_zero

/-- The closed cube `[-1, 1]³`. -/
def unitCubeSym : Set ℝ³ := {p | ∀ i : Fin 3, |p i| ≤ 1}

lemma mem_unitCubeSym {p : ℝ³} : p ∈ unitCubeSym ↔ |p 0| ≤ 1 ∧ |p 1| ≤ 1 ∧ |p 2| ≤ 1 := by
  constructor
  · intro h; exact ⟨h 0, h 1, h 2⟩
  · intro ⟨h0, h1, h2⟩ i; fin_cases i <;> assumption

lemma omegaBody_subset_unitCubeSym : omegaBody ⊆ unitCubeSym := by
  intro p hp
  rw [mem_unitCubeSym]
  rcases (omegaBody_iff p).1 hp with ⟨h0, h1, h2, _⟩
  exact ⟨h0, h1, h2⟩

/-- The two corner tetrahedra removed from the cube to obtain `Ω`. -/
def cornerTetPos : Set ℝ³ :=
  {p | |p 0| ≤ 1 ∧ |p 1| ≤ 1 ∧ |p 2| ≤ 1 ∧ 2 ≤ cutForm p}

def cornerTetNeg : Set ℝ³ :=
  {p | |p 0| ≤ 1 ∧ |p 1| ≤ 1 ∧ |p 2| ≤ 1 ∧ cutForm p ≤ -2}

lemma omegaBody_eq_cube_sdiff :
    omegaBody = unitCubeSym \ ( {p | 2 < cutForm p} ∪ {p | cutForm p < -2} ) := by
  ext p
  simp only [omegaBody_iff, mem_unitCubeSym, mem_diff, mem_union, mem_setOf_eq, cutForm]
  constructor
  · intro ⟨h0, h1, h2, hc⟩
    refine ⟨⟨h0, h1, h2⟩, ?_⟩
    intro h
    rcases h with h | h <;> linarith [le_abs_self (p 0 + p 1 - p 2), neg_le_abs (p 0 + p 1 - p 2)]
  · intro ⟨⟨h0, h1, h2⟩, hnot⟩
    refine ⟨h0, h1, h2, ?_⟩
    rw [abs_le]
    constructor
    · have : ¬ (p 0 + p 1 - p 2 < -2) := fun h => hnot (Or.inr h)
      linarith
    · have : ¬ (2 < p 0 + p 1 - p 2) := fun h => hnot (Or.inl h)
      linarith

lemma cornerTetPos_eq_simplex :
    cornerTetPos =
      (fun p : ℝ³ => pt 1 1 (-1) + linOfCols (pt 0 0 1) (pt 0 (-1) 0) (pt (-1) 0 0) p) ''
        stdSimp3 := by
  ext p
  simp only [cornerTetPos, mem_image, mem_setOf_eq]
  constructor
  · intro ⟨hx, hy, hz, hc⟩
    refine ⟨pt (p 2 + 1) (1 - p 1) (1 - p 0), ?_, ?_⟩
    · rw [stdSimp3, mem_setOf_eq, pt_coord0, pt_coord1, pt_coord2]
      refine ⟨?_, ?_, ?_, ?_⟩
      · linarith [abs_le.mp hz |>.1]
      · linarith [abs_le.mp hy |>.2]
      · linarith [abs_le.mp hx |>.2]
      · have : 2 ≤ cutForm p := hc
        simp only [cutForm] at this; linarith
    · simp only [linOfCols, LinearMap.coe_mk, AddHom.coe_mk]
      rw [pt_smul, pt_smul, pt_smul, pt_add, pt_add, pt_add]
      ext i; fin_cases i <;> simp [pt] <;> ring
  · rintro ⟨q, hq, rfl⟩
    have hq' : 0 ≤ q 0 ∧ 0 ≤ q 1 ∧ 0 ≤ q 2 ∧ q 0 + q 1 + q 2 ≤ 1 := by
      simpa [stdSimp3] using hq
    have himage :
        pt 1 1 (-1) + linOfCols (pt 0 0 1) (pt 0 (-1) 0) (pt (-1) 0 0) q =
          pt (1 - q 2) (1 - q 1) (q 0 - 1) := by
      simp only [linOfCols, LinearMap.coe_mk, AddHom.coe_mk]
      rw [pt_smul, pt_smul, pt_smul, pt_add, pt_add, pt_add]
      ext i; fin_cases i <;> simp [pt] <;> ring
    rw [himage]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [pt_coord0, abs_le]; constructor <;> linarith [hq'.2.2.1, hq'.2.2.2]
    · rw [pt_coord1, abs_le]; constructor <;> linarith [hq'.2.1, hq'.2.2.2]
    · rw [pt_coord2, abs_le]; constructor <;> linarith [hq'.1, hq'.2.2.2]
    · simp only [cutForm, pt_coord0, pt_coord1, pt_coord2]
      linarith [hq'.2.2.2]

lemma det_corner_edges :
    |Matrix.det (coordMatrix (pt 0 0 1) (pt 0 (-1) 0) (pt (-1) 0 0))| = 1 := by
  rw [coordMatrix_of_pt, Matrix.det_fin_three]
  simp

lemma volume_corner_tet_pos : volume cornerTetPos = ENNReal.ofReal (1 / 6 : ℝ) := by
  rw [cornerTetPos_eq_simplex, volume_affine_simplex, det_corner_edges]


lemma cornerTetNeg_eq_neg : cornerTetNeg = (fun p : ℝ³ => -p) '' cornerTetPos := by
  ext p
  simp only [cornerTetNeg, cornerTetPos, mem_image, mem_setOf_eq]
  constructor
  · intro ⟨hx, hy, hz, hc⟩
    refine ⟨-p, ?_, neg_neg p⟩
    have : cutForm (-p) = -cutForm p := by
      simp [cutForm, PiLp.neg_apply]; ring
    refine ⟨by simpa [abs_neg] using hx, by simpa [abs_neg] using hy,
      by simpa [abs_neg] using hz, ?_⟩
    rw [this]
    linarith
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨hx, hy, hz, hc⟩
    have : cutForm (-q) = -cutForm q := by
      simp [cutForm, PiLp.neg_apply]; ring
    refine ⟨by simpa [abs_neg] using hx, by simpa [abs_neg] using hy,
      by simpa [abs_neg] using hz, ?_⟩
    rw [this]; linarith

lemma det_neg_id : LinearMap.det (-LinearMap.id : ℝ³ →ₗ[ℝ] ℝ³) = -1 := by
  have hmat :
      LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin 3)) (PiLp.basisFun 2 ℝ (Fin 3))
        (-LinearMap.id : ℝ³ →ₗ[ℝ] ℝ³) = -1 := by
    ext i j
    simp [LinearMap.toMatrix_apply, PiLp.basisFun_apply, Pi.single]
    fin_cases i <;> fin_cases j <;> simp
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 3)), hmat]
  simp [Matrix.det_neg, Fintype.card_fin, Matrix.det_one]
  norm_num

lemma volume_corner_tet_neg : volume cornerTetNeg = ENNReal.ofReal (1 / 6 : ℝ) := by
  rw [cornerTetNeg_eq_neg]
  let f : ℝ³ →ₗ[ℝ] ℝ³ := -LinearMap.id
  have hf : (fun p : ℝ³ => -p) = ⇑f := by
    funext p; simp [f]
  rw [hf, Measure.addHaar_image_linearMap, det_neg_id]
  simp [volume_corner_tet_pos]

lemma pt_coord_all (x y z : ℝ) : (pt x y z) 0 = x ∧ (pt x y z) 1 = y ∧ (pt x y z) 2 = z :=
  ⟨pt_coord0 x y z, pt_coord1 x y z, pt_coord2 x y z⟩

lemma volume_unitCubeSym : volume unitCubeSym = ENNReal.ofReal 8 := by
  have himage :
      unitCubeSym = (fun p : ℝ³ => (2 : ℝ) • p + (-pt 1 1 1)) '' unitCube3' := by
    ext p
    constructor
    · intro hp
      refine ⟨(1 / 2 : ℝ) • (p + pt 1 1 1), ?_, ?_⟩
      · intro i
        have hi := hp i
        have hcoord : ((1 / 2 : ℝ) • (p + pt 1 1 1)) i = (p i + 1) / 2 := by
          have hpt : (pt 1 1 1) i = 1 := by fin_cases i <;> simp [pt]
          simp [PiLp.smul_apply, PiLp.add_apply, hpt]
          ring
        rw [hcoord]
        rcases abs_le.mp hi with ⟨hlo, hhi⟩
        constructor <;> linarith
      · ext i
        have hpt : (pt 1 1 1) i = 1 := by fin_cases i <;> simp [pt]
        simp [hpt]
    · rintro ⟨q, hq, rfl⟩
      intro i
      have hi := hq i
      have hpt : (pt 1 1 1) i = 1 := by fin_cases i <;> simp [pt]
      have hcoord : ((2 : ℝ) • q + (-pt 1 1 1)) i = 2 * q i - 1 := by
        simp [PiLp.smul_apply, PiLp.add_apply, PiLp.neg_apply, hpt]
        ring
      rw [hcoord, abs_le]
      constructor <;> linarith [hi.1, hi.2]
  rw [himage]
  have hsplit :
      (fun p : ℝ³ => (2 : ℝ) • p + (-pt 1 1 1)) '' unitCube3' =
        (fun p => p + (-pt 1 1 1)) '' ((fun p : ℝ³ => (2 : ℝ) • p) '' unitCube3') := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(2 : ℝ) • p, ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
  rw [hsplit]
  have hva : volume ((fun p : ℝ³ => p + (-pt 1 1 1)) '' ((fun p : ℝ³ => (2 : ℝ) • p) '' unitCube3')) =
      volume ((fun p : ℝ³ => (2 : ℝ) • p) '' unitCube3') := by
    have : (fun p : ℝ³ => p + (-pt 1 1 1)) = fun p => (-pt 1 1 1) + p :=
      funext fun p => add_comm _ _
    rw [this]; exact volume_vadd _ _
  rw [hva]
  let f : ℝ³ →ₗ[ℝ] ℝ³ := (2 : ℝ) • LinearMap.id
  have hf : (fun p : ℝ³ => (2 : ℝ) • p) = ⇑f := by
    funext p; simp [f]
  rw [hf, Measure.addHaar_image_linearMap]
  have hdet : LinearMap.det f = 8 := by
    have : f = (2 : ℝ) • LinearMap.id := rfl
    simp [f, LinearMap.det_smul, finrank_euclideanSpace, Fintype.card_fin]
    norm_num
  rw [hdet, volume_unitCube3']
  simp


lemma isClosed_unitCubeSym : IsClosed unitCubeSym := by
  have : unitCubeSym = ⋂ i : Fin 3, (fun p : ℝ³ => p i) ⁻¹' Icc (-1 : ℝ) 1 := by
    ext p
    simp [unitCubeSym, mem_iInter, mem_Icc, abs_le]
  rw [this]
  exact isClosed_iInter fun i => isClosed_Icc.preimage (continuous_coord i)

lemma cutForm_continuous : Continuous cutForm :=
  (continuous_coord 0).add (continuous_coord 1) |>.sub (continuous_coord 2)

/-- On the 4-contact slice `c = d = h = 0` with the cut constraint
`b - f - g = -1`, the determinant is `1 + f * g * (f + g - 1)`,
hence at least `26/27` by AM-GM whenever `f, g, 1 - f - g ≥ 0`. -/
lemma four_contact_det (f g : ℝ) :
    Matrix.det (xyzMatrix (f + g - 1) 0 0 f g 0) = 1 + f * g * (f + g - 1) := by
  rw [xyzMatrix_det]
  ring

lemma four_contact_det_ge {f g : ℝ}
    (hf : 0 ≤ f) (hg : 0 ≤ g) (hsum : f + g ≤ 1) :
    26 / 27 ≤ |Matrix.det (xyzMatrix (f + g - 1) 0 0 f g 0)| := by
  have hb : 0 ≤ 1 - f - g := by linarith
  have hprod : f * g * (1 - f - g) ≤ 1 / 27 := by
    have hgm := am_gm3 hf hg hb
    have : ((f + g + (1 - f - g)) / 3) ^ 3 = (1 / 3 : ℝ) ^ 3 := by
      congr 1; ring
    have h27 : (1 / 3 : ℝ) ^ 3 = 1 / 27 := by norm_num
    have hnn : 0 ≤ (f + g + (1 - f - g)) / 3 := by
      apply div_nonneg
      · linarith
      · norm_num
    have := hgm.trans (le_of_eq this)
    linarith
  rw [four_contact_det]
  have heq : 1 + f * g * (f + g - 1) = 1 - f * g * (1 - f - g) := by ring
  rw [heq]
  have hnn : 0 ≤ 1 - f * g * (1 - f - g) := by
    have : f * g * (1 - f - g) ≤ 1 := le_trans hprod (by norm_num)
    linarith
  rw [abs_of_nonneg hnn]
  linarith

lemma four_contact_jt :
    Matrix.det (xyzMatrix (1 / 3 + 1 / 3 - 1) 0 0 (1 / 3) (1 / 3) 0) = 26 / 27 := by
  rw [four_contact_det]; norm_num

/-- The Jiao–Torquato basis in `Ω`-coordinates. -/
noncomputable def jtOmega1 : ℝ³ := pt 1 (-1 / 3) 0
noncomputable def jtOmega2 : ℝ³ := pt 0 1 (1 / 3)
noncomputable def jtOmega3 : ℝ³ := pt (1 / 3) 0 1

lemma det_jtOmega :
    |Matrix.det (coordMatrix jtOmega1 jtOmega2 jtOmega3)| = 26 / 27 := by
  simp only [jtOmega1, jtOmega2, jtOmega3]
  rw [coordMatrix_of_pt, Matrix.det_fin_three]
  simp
  norm_num

lemma gOmega_jtOmega1 : gOmega jtOmega1 = 1 := by
  simp only [jtOmega1, gOmega_pt]
  have : |(-1 / 3 : ℝ)| = 1 / 3 := by norm_num
  have : |(1 : ℝ) + (-1 / 3) - 0| / 2 = (1 / 3 : ℝ) := by norm_num
  simp
  norm_num

lemma gOmega_jtOmega2 : gOmega jtOmega2 = 1 := by
  simp only [jtOmega2, gOmega_pt]
  simp
  norm_num

lemma gOmega_jtOmega3 : gOmega jtOmega3 = 1 := by
  simp only [jtOmega3, gOmega_pt]
  simp
  norm_num

lemma gOmega_jtOmega_cut :
    gOmega (jtOmega1 + jtOmega2 - jtOmega3) = 1 := by
  have hsum : jtOmega1 + jtOmega2 - jtOmega3 = pt (2 / 3) (2 / 3) (-2 / 3) := by
    simp only [jtOmega1, jtOmega2, jtOmega3, pt_add, pt_sub]
    congr 1 <;> norm_num
  rw [hsum, gOmega_pt]
  simp
  norm_num

/-- Integer combination of the JT `Ω`-basis. -/
noncomputable def jtOmegaVec (n0 n1 n2 : ℤ) : ℝ³ :=
  (n0 : ℝ) • jtOmega1 + (n1 : ℝ) • jtOmega2 + (n2 : ℝ) • jtOmega3

lemma jtOmegaVec_coord (n0 n1 n2 : ℤ) :
    jtOmegaVec n0 n1 n2 =
      pt ((n0 : ℝ) + (n2 : ℝ) / 3)
         (-(n0 : ℝ) / 3 + (n1 : ℝ))
         ((n1 : ℝ) / 3 + (n2 : ℝ)) := by
  simp only [jtOmegaVec, jtOmega1, jtOmega2, jtOmega3, pt_smul, pt_add]
  congr 1 <;> ring

lemma jtOmegaVec_gOmega (n0 n1 n2 : ℤ) :
    gOmega (jtOmegaVec n0 n1 n2) =
      max (max (|(n0 : ℝ) + (n2 : ℝ) / 3|) (|-(n0 : ℝ) / 3 + (n1 : ℝ)|))
          (max (|((n1 : ℝ) / 3 + (n2 : ℝ))|)
               (|(n0 : ℝ) + (n1 : ℝ) - (n2 : ℝ)| / 3)) := by
  rw [jtOmegaVec_coord, gOmega_pt]
  have hL : |((n0 : ℝ) + (n2 : ℝ) / 3) + (-(n0 : ℝ) / 3 + (n1 : ℝ))
      - ((n1 : ℝ) / 3 + (n2 : ℝ))| / 2
      = |(n0 : ℝ) + (n1 : ℝ) - (n2 : ℝ)| / 3 := by
    have : ((n0 : ℝ) + (n2 : ℝ) / 3) + (-(n0 : ℝ) / 3 + (n1 : ℝ))
        - ((n1 : ℝ) / 3 + (n2 : ℝ)) = (2 / 3) * ((n0 : ℝ) + (n1 : ℝ) - (n2 : ℝ)) := by
      ring
    rw [this, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    ring
  rw [hL]


lemma xyzMatrix_cyclic_det (t s u : ℝ) :
    Matrix.det (xyzMatrix (-t) 0 0 s u 0) = 1 - t * s * u := by
  rw [xyzMatrix_det_special]; ring

lemma xyz_cyclic_det_ge {t s u : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hu : 0 ≤ u) (hsum : t + s + u ≤ 1) :
    26 / 27 ≤ |Matrix.det (xyzMatrix (-t) 0 0 s u 0)| := by
  rw [xyzMatrix_cyclic_det]
  exact cyclic_family_det_ge ht hs hu hsum

/-- A lattice generated by three vectors is *admissible* for `Ω` if the only
lattice point in the interior of `Ω` is the origin. -/
def Admissible (v1 v2 v3 : ℝ³) : Prop :=
  ∀ (n0 n1 n2 : ℤ), n0 = 0 ∧ n1 = 0 ∧ n2 = 0 ∨
    1 ≤ gOmega ((n0 : ℝ) • v1 + (n1 : ℝ) • v2 + (n2 : ℝ) • v3)

lemma Admissible.gOmega_ge {v1 v2 v3 : ℝ³} (h : Admissible v1 v2 v3)
    (n0 n1 n2 : ℤ) (hne : ¬ (n0 = 0 ∧ n1 = 0 ∧ n2 = 0)) :
    1 ≤ gOmega ((n0 : ℝ) • v1 + (n1 : ℝ) • v2 + (n2 : ℝ) • v3) :=
  (h n0 n1 n2).resolve_left hne

lemma xyz_cyclic_cut_admissible_sum {t s u : ℝ}
    (ht0 : 0 ≤ t) (hs0 : 0 ≤ s) (hu0 : 0 ≤ u)
    (ht1 : t ≤ 1) (hs1 : s ≤ 1) (hu1 : u ≤ 1)
    (hsum : t + s + u ≤ 1) :
    1 ≤ gOmega (xyzVec (-t) 0 0 s u 0 1 1 (-1)) := by
  have hcut := cutForm_cyclic t s u
  have hv : xyzVec (-t) 0 0 s u 0 1 1 (-1) =
      pt (1 - u) (1 - t) (s - 1) := by
    rw [xyzVec_one_one_neg]
    push_cast
    congr 1 <;> ring
  rw [hv, gOmega_pt]
  have hx : |1 - u| = 1 - u := abs_of_nonneg (sub_nonneg.mpr hu1)
  have hy : |1 - t| = 1 - t := abs_of_nonneg (sub_nonneg.mpr ht1)
  have hz : |s - 1| = 1 - s := by
    have : s - 1 = -(1 - s) := by ring
    rw [this, abs_neg, abs_of_nonneg (sub_nonneg.mpr hs1)]
  have hL : |1 - u + (1 - t) - (s - 1)| / 2 = (3 - t - s - u) / 2 := by
    have : 1 - u + (1 - t) - (s - 1) = 3 - t - s - u := by ring
    rw [this, abs_of_nonneg (by linarith)]
  rw [hx, hy, hz, hL]
  apply le_max_of_le_right
  apply le_max_of_le_right
  linarith

lemma xyz_basis_gOmega {t s u : ℝ}
    (ht0 : 0 ≤ t) (hs0 : 0 ≤ s) (hu0 : 0 ≤ u)
    (ht1 : t ≤ 1) (hs1 : s ≤ 1) (hu1 : u ≤ 1) :
    gOmega (xyzVec (-t) 0 0 s u 0 1 0 0) = 1 ∧
    gOmega (xyzVec (-t) 0 0 s u 0 0 1 0) = 1 ∧
    gOmega (xyzVec (-t) 0 0 s u 0 0 0 1) = 1 :=
  cyclic_gOmega_basis ht0 hs0 hu0 ht1 hs1 hu1

/-- In the open cyclic chamber `0 < t,s,u < 1`, if `t+s+u > 1` then the
vector `(1,1,-1)` lies in the interior of `Ω`, so the lattice is not admissible. -/
lemma xyz_cyclic_inadmissible_of_sum_gt {t s u : ℝ}
    (ht0 : 0 < t) (hs0 : 0 < s) (hu0 : 0 < u)
    (ht1 : t < 1) (hs1 : s < 1) (hu1 : u < 1)
    (hsum : 1 < t + s + u) :
    gOmega (xyzVec (-t) 0 0 s u 0 1 1 (-1)) < 1 := by
  have hv : xyzVec (-t) 0 0 s u 0 1 1 (-1) = pt (1 - u) (1 - t) (s - 1) := by
    rw [xyzVec_one_one_neg]; congr 1 <;> ring
  rw [hv, gOmega_pt]
  have hx : |1 - u| = 1 - u := abs_of_pos (sub_pos.mpr hu1)
  have hy : |1 - t| = 1 - t := abs_of_pos (sub_pos.mpr ht1)
  have hz : |s - 1| = 1 - s := by
    have : s - 1 = -(1 - s) := by ring
    rw [this, abs_neg, abs_of_pos (sub_pos.mpr hs1)]
  have hL : |1 - u + (1 - t) - (s - 1)| / 2 = |3 - t - s - u| / 2 := by
    congr 1; ring
  rw [hx, hy, hz, hL]
  have hL2 : |3 - t - s - u| / 2 < 1 := by
    have : 0 < 3 - t - s - u := by linarith [ht1, hs1, hu1]
    rw [abs_of_pos this]
    linarith
  have h1 : 1 - u < 1 := by linarith
  have h2 : 1 - t < 1 := by linarith
  have h3 : 1 - s < 1 := by linarith
  apply max_lt
  · exact max_lt h1 h2
  · exact max_lt h3 hL2

lemma xyzVec_cyclic_sum (t s u : ℝ) :
    xyzVec (-t) 0 0 s u 0 1 1 (-1) =
      ((1 : ℤ) : ℝ) • pt 1 (-t) 0 + ((1 : ℤ) : ℝ) • pt 0 1 s +
        ((-1 : ℤ) : ℝ) • pt u 0 1 := by
  rfl

/-- If `t, s, u > 0` and `t + s + u > 1` (with each parameter at most `1`),
the combination `(1,1,-1)` lies in the interior of `Ω`. -/
lemma xyz_cyclic_inadmissible_of_pos_sum_gt {t s u : ℝ}
    (ht0 : 0 < t) (hs0 : 0 < s) (hu0 : 0 < u)
    (ht1 : t ≤ 1) (hs1 : s ≤ 1) (hu1 : u ≤ 1)
    (hsum : 1 < t + s + u) :
    gOmega (xyzVec (-t) 0 0 s u 0 1 1 (-1)) < 1 := by
  have hv : xyzVec (-t) 0 0 s u 0 1 1 (-1) = pt (1 - u) (1 - t) (s - 1) := by
    rw [xyzVec_one_one_neg]; congr 1 <;> ring
  rw [hv, gOmega_pt]
  have hx : |1 - u| = 1 - u := abs_of_nonneg (sub_nonneg.mpr hu1)
  have hy : |1 - t| = 1 - t := abs_of_nonneg (sub_nonneg.mpr ht1)
  have hz : |s - 1| = 1 - s := by
    have : s - 1 = -(1 - s) := by ring
    rw [this, abs_neg, abs_of_nonneg (sub_nonneg.mpr hs1)]
  have hL : |1 - u + (1 - t) - (s - 1)| / 2 = (3 - t - s - u) / 2 := by
    have : 1 - u + (1 - t) - (s - 1) = 3 - t - s - u := by ring
    have hnn : 0 ≤ 3 - t - s - u := by linarith
    rw [this, abs_of_nonneg hnn]
  rw [hx, hy, hz, hL]
  have h1 : 1 - u < 1 := sub_lt_self _ hu0
  have h2 : 1 - t < 1 := sub_lt_self _ ht0
  have h3 : 1 - s < 1 := sub_lt_self _ hs0
  have hL2 : (3 - t - s - u) / 2 < 1 := by linarith
  exact max_lt (max_lt h1 h2) (max_lt h3 hL2)

/-- Cyclic-chamber lattices that are admissible and lie in the unit parameter
box have determinant at least `26/27`. -/
lemma xyz_cyclic_admissible_det_ge {t s u : ℝ}
    (ht0 : 0 ≤ t) (hs0 : 0 ≤ s) (hu0 : 0 ≤ u)
    (ht1 : t ≤ 1) (hs1 : s ≤ 1) (hu1 : u ≤ 1)
    (hadm : Admissible (pt 1 (-t) 0) (pt 0 1 s) (pt u 0 1)) :
    26 / 27 ≤ |Matrix.det (xyzMatrix (-t) 0 0 s u 0)| := by
  by_cases hz : t = 0 ∨ s = 0 ∨ u = 0
  · rw [xyzMatrix_cyclic_det]
    have hprod : t * s * u = 0 := by
      rcases hz with hz | hz | hz <;> simp [hz]
    rw [hprod, sub_zero, abs_one]
    norm_num
  · push_neg at hz
    by_cases hsum : t + s + u ≤ 1
    · exact xyz_cyclic_det_ge ht0 hs0 hu0 hsum
    · have htpos : 0 < t := lt_of_le_of_ne ht0 hz.1.symm
      have hspos : 0 < s := lt_of_le_of_ne hs0 hz.2.1.symm
      have hupos : 0 < u := lt_of_le_of_ne hu0 hz.2.2.symm
      have hin := xyz_cyclic_inadmissible_of_pos_sum_gt
        htpos hspos hupos ht1 hs1 hu1 (lt_of_not_ge hsum)
      have hge := hadm.gOmega_ge 1 1 (-1) (by decide)
      rw [← xyzVec_cyclic_sum t s u] at hge
      exact (not_le_of_gt hin hge).elim


lemma jtOmega_forms_le_two (n0 n1 n2 : ℤ)
    (a0 : |3 * n0 + n2| ≤ 2) (a1 : |-n0 + 3 * n1| ≤ 2)
    (a2 : |n1 + 3 * n2| ≤ 2) (a3 : |n0 + n1 - n2| ≤ 2) :
    n0 = 0 ∧ n1 = 0 ∧ n2 = 0 := by
  have h0 := abs_le.mp a0
  have h1 := abs_le.mp a1
  have h2 := abs_le.mp a2
  have h3 := abs_le.mp a3
  omega

lemma jtOmega_int_max_ge (n0 n1 n2 : ℤ)
    (hne : ¬ (n0 = 0 ∧ n1 = 0 ∧ n2 = 0)) :
    (3 : ℤ) ≤
      max (max |3 * n0 + n2| |-n0 + 3 * n1|)
          (max |n1 + 3 * n2| |n0 + n1 - n2|) := by
  by_contra h
  have hle : max (max |3 * n0 + n2| |-n0 + 3 * n1|)
      (max |n1 + 3 * n2| |n0 + n1 - n2|) ≤ 2 := by linarith
  have a0 : |3 * n0 + n2| ≤ 2 :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hle)
  have a1 : |-n0 + 3 * n1| ≤ 2 :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hle)
  have a2 : |n1 + 3 * n2| ≤ 2 :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hle)
  have a3 : |n0 + n1 - n2| ≤ 2 :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hle)
  exact hne (jtOmega_forms_le_two n0 n1 n2 a0 a1 a2 a3)

lemma three_mul_jt_g (n0 n1 n2 : ℤ) :
    3 * gOmega (jtOmegaVec n0 n1 n2) =
      max (max (|(3 * n0 + n2 : ℝ)|) (|(-n0 + 3 * n1 : ℝ)|))
          (max (|(n1 + 3 * n2 : ℝ)|) (|(n0 + n1 - n2 : ℝ)|)) := by
  rw [jtOmegaVec_gOmega]
  have hpos : (0 : ℝ) < 3 := by norm_num
  have hnn : (0 : ℝ) ≤ 3 := hpos.le
  have habs (a : ℝ) : 3 * |a / 3| = |a| := by
    rw [abs_div, abs_of_pos hpos, mul_div_cancel₀ _ (ne_of_gt hpos)]
  have hx : 3 * |(n0 : ℝ) + (n2 : ℝ) / 3| = |(3 * n0 + n2 : ℝ)| := by
    have : (n0 : ℝ) + (n2 : ℝ) / 3 = ((3 : ℝ) * n0 + n2) / 3 := by ring
    rw [this, habs]
  have hy : 3 * |-(n0 : ℝ) / 3 + (n1 : ℝ)| = |(3 * n1 - n0 : ℝ)| := by
    have : -(n0 : ℝ) / 3 + (n1 : ℝ) = (3 * (n1 : ℝ) - n0) / 3 := by ring
    rw [this, habs]
  have hz : 3 * |(n1 : ℝ) / 3 + (n2 : ℝ)| = |(3 * n2 + n1 : ℝ)| := by
    have : (n1 : ℝ) / 3 + (n2 : ℝ) = (3 * (n2 : ℝ) + n1) / 3 := by ring
    rw [this, habs]
  have hL : 3 * (|(n0 : ℝ) + (n1 : ℝ) - (n2 : ℝ)| / 3) = |(n0 + n1 - n2 : ℝ)| := by
    field_simp
  have hy' : |(3 * n1 - n0 : ℝ)| = (|(-n0 + 3 * n1 : ℝ)|) := by
    congr 1; ring
  have hz' : |(3 * n2 + n1 : ℝ)| = (|(n1 + 3 * n2 : ℝ)|) := by
    congr 1; ring
  rw [mul_max_of_nonneg (a := (3 : ℝ)) _ _ hnn,
      mul_max_of_nonneg (a := (3 : ℝ)) _ _ hnn,
      mul_max_of_nonneg (a := (3 : ℝ)) _ _ hnn, hx, hy, hz, hL, hy', hz']

lemma Admissible_jtOmega : Admissible jtOmega1 jtOmega2 jtOmega3 := by
  intro n0 n1 n2
  by_cases h : n0 = 0 ∧ n1 = 0 ∧ n2 = 0
  · exact Or.inl h
  · refine Or.inr ?_
    have hint := jtOmega_int_max_ge n0 n1 n2 h
    have h3 := three_mul_jt_g n0 n1 n2
    have hcast :
        (3 : ℝ) ≤
          max (max (|(3 * n0 + n2 : ℝ)|) (|(-n0 + 3 * n1 : ℝ)|))
              (max (|(n1 + 3 * n2 : ℝ)|) (|(n0 + n1 - n2 : ℝ)|)) :=
      mod_cast hint
    have : (3 : ℝ) ≤ 3 * gOmega (jtOmegaVec n0 n1 n2) := by
      rwa [h3]
    exact (mul_le_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 3)).1 (by simpa using this)


noncomputable def cutFormLM : ℝ³ →ₗ[ℝ] ℝ where
  toFun := cutForm
  map_add' := by
    intro x y
    simp [cutForm, PiLp.add_apply]
    ring
  map_smul' := by
    intro r x
    simp [cutForm, PiLp.smul_apply, smul_eq_mul]
    ring

lemma cutFormLM_ne_zero : cutFormLM ≠ 0 := by
  intro h
  have : (cutFormLM (pt 1 0 0)) = 0 := by rw [h]; simp
  simp [cutFormLM, cutForm, pt_coord0, pt_coord1, pt_coord2] at this

lemma volume_ker_cutForm : volume (LinearMap.ker cutFormLM : Set ℝ³) = 0 :=
  Measure.addHaar_submodule volume (LinearMap.ker cutFormLM)
    (by
      intro htop
      exact cutFormLM_ne_zero (LinearMap.ker_eq_top.mp htop))

lemma cutForm_pt (x y z : ℝ) : cutForm (pt x y z) = x + y - z := by
  simp [cutForm, pt_coord0, pt_coord1, pt_coord2]

lemma volume_cutForm_eq_zero (c : ℝ) :
    volume {p : ℝ³ | cutForm p = c} = 0 := by
  let q : ℝ³ := pt c 0 0
  have hq : cutForm q = c := by
    simp [q, cutForm_pt]
  have himg :
      {p : ℝ³ | cutForm p = c} =
        (fun x : ℝ³ => q + x) '' (LinearMap.ker cutFormLM : Set ℝ³) := by
    ext p
    constructor
    · intro hp
      refine ⟨p - q, ?_, by simp⟩
      simp [LinearMap.mem_ker, cutFormLM, cutForm, PiLp.sub_apply]
      simp [cutForm] at hp hq
      linarith
    · rintro ⟨x, hx, rfl⟩
      have hx0 : cutForm x = 0 := by
        simpa [LinearMap.mem_ker, cutFormLM, cutForm] using hx
      have : cutForm (q + x) = cutForm q + cutForm x := by
        simp [cutForm, PiLp.add_apply]; ring
      simp [this, hq, hx0]
  rw [himg, volume_vadd, volume_ker_cutForm]


lemma gOmega_continuous : Continuous gOmega := by
  unfold gOmega
  exact (continuous_coord 0).abs.max (continuous_coord 1).abs |>.max
    ((continuous_coord 2).abs.max (cutForm_continuous.abs.div_const 2))

lemma isClosed_omegaBody : IsClosed omegaBody :=
  isClosed_le gOmega_continuous continuous_const

lemma cornerTets_disjoint : Disjoint cornerTetPos cornerTetNeg :=
  disjoint_left.mpr fun p hp hp' => by linarith [hp.2.2.2, hp'.2.2.2]

lemma cornerTetPos_subset_cube : cornerTetPos ⊆ unitCubeSym := by
  intro p hp
  rw [mem_unitCubeSym]
  exact ⟨hp.1, hp.2.1, hp.2.2.1⟩

lemma cornerTetNeg_subset_cube : cornerTetNeg ⊆ unitCubeSym := by
  intro p hp
  rw [mem_unitCubeSym]
  exact ⟨hp.1, hp.2.1, hp.2.2.1⟩

lemma isClosed_cornerTetPos : IsClosed cornerTetPos := by
  have : cornerTetPos =
      unitCubeSym ∩ cutForm ⁻¹' Ici (2 : ℝ) := by
    ext p
    simp [cornerTetPos, mem_unitCubeSym, mem_inter_iff, mem_preimage, mem_Ici, cutForm]
    tauto
  rw [this]
  exact isClosed_unitCubeSym.inter (isClosed_Ici.preimage cutForm_continuous)

lemma isClosed_cornerTetNeg : IsClosed cornerTetNeg := by
  have : cornerTetNeg =
      unitCubeSym ∩ cutForm ⁻¹' Iic (-2 : ℝ) := by
    ext p
    simp [cornerTetNeg, mem_unitCubeSym, mem_inter_iff, mem_preimage, mem_Iic, cutForm]
    tauto
  rw [this]
  exact isClosed_unitCubeSym.inter (isClosed_Iic.preimage cutForm_continuous)

lemma volume_cornerTets :
    volume (cornerTetPos ∪ cornerTetNeg) = ENNReal.ofReal (1 / 3 : ℝ) := by
  rw [measure_union cornerTets_disjoint isClosed_cornerTetNeg.measurableSet,
      volume_corner_tet_pos, volume_corner_tet_neg]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

lemma cube_sdiff_closedCorners_subset_omega :
    unitCubeSym \ (cornerTetPos ∪ cornerTetNeg) ⊆ omegaBody := by
  intro p hp
  have hpC := hp.1
  have hnot := hp.2
  rw [mem_unitCubeSym] at hpC
  apply (omegaBody_iff p).2
  refine ⟨hpC.1, hpC.2.1, hpC.2.2, ?_⟩
  rw [abs_le]
  constructor
  · have : ¬ cutForm p ≤ -2 := by
      intro h
      exact hnot (Or.inr ⟨hpC.1, hpC.2.1, hpC.2.2, h⟩)
    linarith
  · have : ¬ 2 ≤ cutForm p := by
      intro h
      exact hnot (Or.inl ⟨hpC.1, hpC.2.1, hpC.2.2, h⟩)
    linarith

lemma omega_sdiff_open_eq_planes :
    omegaBody \ (unitCubeSym \ (cornerTetPos ∪ cornerTetNeg)) ⊆
      {p : ℝ³ | cutForm p = 2 ∨ cutForm p = -2} := by
  intro p hp
  have hΩ := (omegaBody_iff p).1 hp.1
  have : p ∈ cornerTetPos ∪ cornerTetNeg := by
    have hC : p ∈ unitCubeSym := omegaBody_subset_unitCubeSym hp.1
    have hnot : ¬ p ∈ unitCubeSym \ (cornerTetPos ∪ cornerTetNeg) := hp.2
    rw [mem_diff, not_and, not_not] at hnot
    exact hnot hC
  rcases this with h | h
  · have : cutForm p = 2 := le_antisymm (abs_le.mp hΩ.2.2.2).2 h.2.2.2
    exact Or.inl this
  · have : cutForm p = -2 := le_antisymm h.2.2.2 (abs_le.mp hΩ.2.2.2).1
    exact Or.inr this

lemma volume_omegaBody : volume omegaBody = ENNReal.ofReal (23 / 3 : ℝ) := by
  have hmeasC : MeasurableSet (cornerTetPos ∪ cornerTetNeg) :=
    isClosed_cornerTetPos.measurableSet.union isClosed_cornerTetNeg.measurableSet
  have hsdiff :
      volume (unitCubeSym \ (cornerTetPos ∪ cornerTetNeg)) =
        volume unitCubeSym - volume (cornerTetPos ∪ cornerTetNeg) := by
    refine measure_diff
      (fun p hp => hp.elim (fun h => cornerTetPos_subset_cube h)
        (fun h => cornerTetNeg_subset_cube h))
      hmeasC.nullMeasurableSet ?_
    rw [volume_cornerTets]
    exact ENNReal.ofReal_ne_top
  have hvol_sdiff :
      volume (unitCubeSym \ (cornerTetPos ∪ cornerTetNeg)) =
        ENNReal.ofReal (23 / 3 : ℝ) := by
    rw [hsdiff, volume_unitCubeSym, volume_cornerTets]
    rw [← ENNReal.ofReal_sub]
    · norm_num
    · norm_num
  -- The two sets differ by a subset of two planes, hence have equal volume.
  have hsubset := cube_sdiff_closedCorners_subset_omega
  have hdiff := omega_sdiff_open_eq_planes
  have hnull : volume ({p : ℝ³ | cutForm p = 2 ∨ cutForm p = -2}) = 0 := by
    have : {p : ℝ³ | cutForm p = 2 ∨ cutForm p = -2} =
        {p | cutForm p = 2} ∪ {p | cutForm p = -2} := by
      ext p; simp [or_comm]
    rw [this, measure_union_null (volume_cutForm_eq_zero 2) (volume_cutForm_eq_zero (-2))]
  have hle : volume (unitCubeSym \ (cornerTetPos ∪ cornerTetNeg)) ≤ volume omegaBody :=
    measure_mono hsubset
  have hge : volume omegaBody ≤
      volume (unitCubeSym \ (cornerTetPos ∪ cornerTetNeg)) +
        volume ({p : ℝ³ | cutForm p = 2 ∨ cutForm p = -2}) := by
    have : omegaBody ⊆
        (unitCubeSym \ (cornerTetPos ∪ cornerTetNeg)) ∪
          {p : ℝ³ | cutForm p = 2 ∨ cutForm p = -2} := by
      intro p hp
      by_cases h : p ∈ unitCubeSym \ (cornerTetPos ∪ cornerTetNeg)
      · exact Or.inl h
      · exact Or.inr (hdiff ⟨hp, h⟩)
    exact (measure_mono this).trans (measure_union_le _ _)
  rw [hnull, add_zero] at hge
  exact le_antisymm (hge.trans_eq hvol_sdiff) (hvol_sdiff.symm.trans_le hle)


lemma volume_half_omegaBody :
    volume ((fun p : ℝ³ => (1 / 2 : ℝ) • p) '' omegaBody) =
      ENNReal.ofReal (23 / 24 : ℝ) := by
  let f : ℝ³ →ₗ[ℝ] ℝ³ := (1 / 2 : ℝ) • LinearMap.id
  have hf : (fun p : ℝ³ => (1 / 2 : ℝ) • p) = ⇑f := by
    funext p; simp [f]
  rw [hf, Measure.addHaar_image_linearMap]
  have hdet : |LinearMap.det f| = 1 / 8 := by
    simp [f, LinearMap.det_smul, finrank_euclideanSpace, Fintype.card_fin]
    norm_num
  rw [hdet, volume_omegaBody]
  rw [← ENNReal.ofReal_mul (by norm_num)]
  norm_num

lemma half_omega_sub_mem {x y : ℝ³}
    (hx : x ∈ (fun p : ℝ³ => (1 / 2 : ℝ) • p) '' omegaBody)
    (hy : y ∈ (fun p : ℝ³ => (1 / 2 : ℝ) • p) '' omegaBody) :
    gOmega (x - y) ≤ 1 := by
  rcases hx with ⟨a, ha, rfl⟩
  rcases hy with ⟨b, hb, rfl⟩
  have : (1 / 2 : ℝ) • a - (1 / 2 : ℝ) • b = (1 / 2 : ℝ) • (a - b) := by
    simp [smul_sub]
  rw [this, gOmega_smul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hab : gOmega (a - b) ≤ gOmega a + gOmega b := by
    simpa [sub_eq_add_neg, gOmega_neg] using gOmega_add a (-b)
  have ha1 : gOmega a ≤ 1 := (mem_omegaBody.mp ha)
  have hb1 : gOmega b ≤ 1 := (mem_omegaBody.mp hb)
  nlinarith


lemma linOfCols_pt (u v w : ℝ³) (n0 n1 n2 : ℝ) :
    linOfCols u v w (pt n0 n1 n2) = n0 • u + n1 • v + n2 • w := by
  simp [linOfCols, LinearMap.coe_mk, AddHom.coe_mk, pt_coord0, pt_coord1, pt_coord2]


lemma convex_omegaInterior : Convex ℝ {p : ℝ³ | gOmega p < 1} := by
  intro x hx y hy a b ha hb hab
  have h : gOmega (a • x + b • y) ≤ a * gOmega x + b * gOmega y := by
    have := gOmega_add (a • x) (b • y)
    rwa [gOmega_smul_nonneg ha, gOmega_smul_nonneg hb] at this
  simp only [mem_setOf_eq] at hx hy ⊢
  have hbound : a * gOmega x + b * gOmega y < a + b := by
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simp [ha0, hb1]; exact hy
    · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      nlinarith [hx, hy]
  have : gOmega (a • x + b • y) < a + b := h.trans_lt hbound
  rwa [hab] at this

lemma omegaInterior_neg {p : ℝ³} (hp : gOmega p < 1) : gOmega (-p) < 1 := by
  simpa [gOmega_neg] using hp

lemma omegaBody_subset_closedBall :
    omegaBody ⊆ closedBall (0 : ℝ³) 2 := by
  intro p hp
  have hpC := omegaBody_subset_unitCubeSym hp
  have hsq : ‖p‖ ^ 2 = |p 0| ^ 2 + |p 1| ^ 2 + |p 2| ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three, Real.norm_eq_abs]
  have hle : ‖p‖ ^ 2 ≤ 3 := by
    have a0 : |p 0| ^ 2 ≤ (1 : ℝ) := by
      have := pow_le_pow_left₀ (abs_nonneg (p 0)) (hpC 0) 2
      simpa using this
    have a1 : |p 1| ^ 2 ≤ (1 : ℝ) := by
      have := pow_le_pow_left₀ (abs_nonneg (p 1)) (hpC 1) 2
      simpa using this
    have a2 : |p 2| ^ 2 ≤ (1 : ℝ) := by
      have := pow_le_pow_left₀ (abs_nonneg (p 2)) (hpC 2) 2
      simpa using this
    linarith [hsq]
  have hnorm : ‖p‖ ≤ Real.sqrt 3 := by
    have : ‖p‖ ^ 2 ≤ (Real.sqrt 3) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; exact hle
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg 3)).mp this
  have hsqrt : Real.sqrt 3 ≤ 2 := (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  rw [mem_closedBall, dist_zero_right]
  exact hnorm.trans hsqrt

lemma isCompact_omegaBody : IsCompact omegaBody :=
  IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℝ³) 2)
    isClosed_omegaBody omegaBody_subset_closedBall

lemma volume_coord_eq (i : Fin 3) (c : ℝ) :
    volume {p : ℝ³ | p i = c} = 0 := by
  have hne : coordLM i ≠ 0 := by
    intro h
    have : coordLM i (pt 1 1 1) = 0 := by rw [h]; simp
    fin_cases i <;> simp [coordLM, pt_coord0, pt_coord1, pt_coord2] at this
  have hker : volume (LinearMap.ker (coordLM i) : Set ℝ³) = 0 :=
    Measure.addHaar_submodule volume (LinearMap.ker (coordLM i))
      (fun htop => hne (LinearMap.ker_eq_top.mp htop))
  let q : ℝ³ := pt (if i = 0 then c else 0) (if i = 1 then c else 0) (if i = 2 then c else 0)
  have hq : q i = c := by
    fin_cases i <;> simp [q, pt_coord0, pt_coord1, pt_coord2]
  have himg :
      {p : ℝ³ | p i = c} =
        (fun x : ℝ³ => q + x) '' (LinearMap.ker (coordLM i) : Set ℝ³) := by
    ext p
    constructor
    · intro hp
      refine ⟨p - q, ?_, by simp⟩
      simp [LinearMap.mem_ker, coordLM, PiLp.sub_apply]
      simp [coordLM] at hp
      linarith [hq]
    · rintro ⟨x, hx, rfl⟩
      have hx0 : x i = 0 := by
        simpa [LinearMap.mem_ker, coordLM] using hx
      simp [PiLp.add_apply, hx0, hq]
  rw [himg, volume_vadd, hker]

lemma volume_abs_coord_eq (i : Fin 3) :
    volume {p : ℝ³ | |p i| = 1} = 0 := by
  have : {p : ℝ³ | |p i| = 1} = {p | p i = 1} ∪ {p | p i = -1} := by
    ext p; simp [abs_eq]
  rw [this, measure_union_null (volume_coord_eq i 1) (volume_coord_eq i (-1))]

lemma volume_abs_cut_eq :
    volume {p : ℝ³ | |cutForm p| = 2} = 0 := by
  have : {p : ℝ³ | |cutForm p| = 2} = {p | cutForm p = 2} ∪ {p | cutForm p = -2} := by
    ext p; simp [abs_eq]
  rw [this, measure_union_null (volume_cutForm_eq_zero 2) (volume_cutForm_eq_zero (-2))]

lemma volume_gOmega_eq_one :
    volume {p : ℝ³ | gOmega p = 1} = 0 := by
  have hsub :
      {p : ℝ³ | gOmega p = 1} ⊆
        {p | |p 0| = 1} ∪ {p | |p 1| = 1} ∪ {p | |p 2| = 1} ∪
          {p | |cutForm p| = 2} := by
    intro p hp
    have h0 : |p 0| ≤ 1 := (gOmega_ge_coord p 0).trans (le_of_eq hp)
    have h1 : |p 1| ≤ 1 := (gOmega_ge_coord p 1).trans (le_of_eq hp)
    have h2 : |p 2| ≤ 1 := (gOmega_ge_coord p 2).trans (le_of_eq hp)
    have hc : |cutForm p| / 2 ≤ 1 := (gOmega_ge_cut p).trans (le_of_eq hp)
    unfold gOmega at hp
    have hm := max_eq_iff.mp hp
    rcases hm with ⟨hm, _⟩ | ⟨hm, _⟩
    · have hm' := max_eq_iff.mp hm
      rcases hm' with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h))
    · have hm' := max_eq_iff.mp hm
      rcases hm' with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl (Or.inr h)
      · have : |cutForm p| = 2 := by
          simp only [cutForm] at h ⊢
          linarith
        exact Or.inr this
  have hz01 :
      volume ({p : ℝ³ | |p 0| = 1} ∪ {p | |p 1| = 1}) = 0 :=
    measure_union_null (volume_abs_coord_eq 0) (volume_abs_coord_eq 1)
  have hz012 :
      volume (({p : ℝ³ | |p 0| = 1} ∪ {p | |p 1| = 1}) ∪ {p | |p 2| = 1}) = 0 :=
    measure_union_null hz01 (volume_abs_coord_eq 2)
  have hz :
      volume
        ((({p : ℝ³ | |p 0| = 1} ∪ {p | |p 1| = 1}) ∪ {p | |p 2| = 1}) ∪
          {p | |cutForm p| = 2}) = 0 :=
    measure_union_null hz012 volume_abs_cut_eq
  exact measure_mono_null hsub hz

lemma volume_omegaInterior :
    volume {p : ℝ³ | gOmega p < 1} = ENNReal.ofReal (23 / 3 : ℝ) := by
  have hunion : omegaBody = {p : ℝ³ | gOmega p < 1} ∪ {p | gOmega p = 1} := by
    ext p
    simp only [omegaBody, mem_union, mem_setOf_eq]
    constructor
    · intro h
      exact lt_or_eq_of_le h
    · intro h
      exact h.elim le_of_lt (fun heq => le_of_eq heq)
  have hdisj : Disjoint {p : ℝ³ | gOmega p < 1} {p | gOmega p = 1} :=
    disjoint_left.mpr fun p hp hp' => (hp.ne hp')
  have hmeas : MeasurableSet {p : ℝ³ | gOmega p = 1} :=
    (isClosed_eq gOmega_continuous continuous_const).measurableSet
  have : volume omegaBody =
      volume {p : ℝ³ | gOmega p < 1} + volume {p | gOmega p = 1} := by
    rw [hunion, measure_union hdisj hmeas]
  rw [volume_gOmega_eq_one, add_zero] at this
  rw [← this, volume_omegaBody]

/-- Three linearly independent vectors form a real basis of `ℝ³`. -/
noncomputable def basisOf3 {v1 v2 v3 : ℝ³}
    (hlin : LinearIndependent ℝ ![v1, v2, v3]) :
    Module.Basis (Fin 3) ℝ ℝ³ :=
  basisOfLinearIndependentOfCardEqFinrank hlin (by
    simp [finrank_euclideanSpace, Fintype.card_fin])

lemma basisOf3_apply {v1 v2 v3 : ℝ³}
    (hlin : LinearIndependent ℝ ![v1, v2, v3]) :
    ⇑(basisOf3 hlin) = ![v1, v2, v3] :=
  coe_basisOfLinearIndependentOfCardEqFinrank hlin _

lemma basisOf3_apply0 {v1 v2 v3 : ℝ³}
    (hlin : LinearIndependent ℝ ![v1, v2, v3]) : basisOf3 hlin 0 = v1 := by
  simp [basisOf3_apply hlin]

lemma basisOf3_apply1 {v1 v2 v3 : ℝ³}
    (hlin : LinearIndependent ℝ ![v1, v2, v3]) : basisOf3 hlin 1 = v2 := by
  simp [basisOf3_apply hlin]

lemma basisOf3_apply2 {v1 v2 v3 : ℝ³}
    (hlin : LinearIndependent ℝ ![v1, v2, v3]) : basisOf3 hlin 2 = v3 := by
  simp [basisOf3_apply hlin]

lemma basisOf3_repr_sum {v1 v2 v3 : ℝ³}
    (hlin : LinearIndependent ℝ ![v1, v2, v3]) (p : ℝ³) :
    p = (basisOf3 hlin).repr p 0 • v1 +
        (basisOf3 hlin).repr p 1 • v2 +
        (basisOf3 hlin).repr p 2 • v3 := by
  conv_lhs => rw [← (basisOf3 hlin).sum_repr p]
  rw [Fin.sum_univ_three, basisOf3_apply0, basisOf3_apply1, basisOf3_apply2]

lemma icoCube_volume :
    volume {p : ℝ³ | ∀ i : Fin 3, p i ∈ Set.Ico (0 : ℝ) 1} = 1 := by
  let S : Set ℝ³ := {p | ∀ i : Fin 3, p i ∈ Set.Ico (0 : ℝ) 1}
  have hmp := PiLp.volume_preserving_toLp (ι := Fin 3)
  have hpre :
      (@WithLp.toLp 2 (Fin 3 → ℝ)) ⁻¹' S =
        Set.pi Set.univ fun _ : Fin 3 => Set.Ico (0 : ℝ) 1 := by
    ext y
    simp [S, mem_preimage, mem_setOf_eq, Set.mem_pi]
  have hmeas : MeasurableSet S := by
    have : S = ⋂ i : Fin 3, (fun x : ℝ³ => x i) ⁻¹' Ico (0 : ℝ) 1 := by
      ext x; simp [S, mem_iInter, mem_Ico]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      measurableSet_Ico.preimage (continuous_coord i).measurable
  have : volume S = volume (Set.pi Set.univ fun _ : Fin 3 => Set.Ico (0 : ℝ) 1) := by
    rw [← hmp.map_eq, Measure.map_apply hmp.measurable hmeas, hpre]
  rw [this, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico]

lemma stdBasis_fund_eq :
    ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 3)) =
      {p : ℝ³ | ∀ i : Fin 3, p i ∈ Set.Ico (0 : ℝ) 1} := by
  ext p
  simp [ZSpan.fundamentalDomain, mem_Ico, PiLp.basisFun_repr]

lemma volume_stdBasis_fund :
    volume (ZSpan.fundamentalDomain (PiLp.basisFun 2 ℝ (Fin 3))) = 1 := by
  rw [stdBasis_fund_eq, icoCube_volume]

lemma basisOf3_toMatrix {v1 v2 v3 : ℝ³}
    (hlin : LinearIndependent ℝ ![v1, v2, v3]) :
    (PiLp.basisFun 2 ℝ (Fin 3)).toMatrix (basisOf3 hlin) =
      coordMatrix v1 v2 v3 := by
  ext i j
  simp only [Module.Basis.toMatrix_apply, PiLp.basisFun_repr, coordMatrix]
  fin_cases i <;> fin_cases j <;>
    simp [basisOf3_apply0, basisOf3_apply1, basisOf3_apply2]

lemma basisOf3_det {v1 v2 v3 : ℝ³}
    (hlin : LinearIndependent ℝ ![v1, v2, v3]) :
    (PiLp.basisFun 2 ℝ (Fin 3)).det (basisOf3 hlin) =
      Matrix.det (coordMatrix v1 v2 v3) := by
  rw [Module.Basis.det_apply, basisOf3_toMatrix]

lemma volume_basisOf3_fund {v1 v2 v3 : ℝ³}
    (hlin : LinearIndependent ℝ ![v1, v2, v3]) :
    volume (ZSpan.fundamentalDomain (basisOf3 hlin)) =
      ENNReal.ofReal |Matrix.det (coordMatrix v1 v2 v3)| := by
  rw [ZSpan.measure_fundamentalDomain (basisOf3 hlin) volume (PiLp.basisFun 2 ℝ (Fin 3)),
    volume_stdBasis_fund, basisOf3_det, mul_one]

lemma span_int_eq_int_combo {v1 v2 v3 : ℝ³}
    (hlin : LinearIndependent ℝ ![v1, v2, v3]) {x : ℝ³}
    (hx : x ∈ Submodule.span ℤ (Set.range (basisOf3 hlin))) :
    ∃ n0 n1 n2 : ℤ,
      x = (n0 : ℝ) • v1 + (n1 : ℝ) • v2 + (n2 : ℝ) • v3 := by
  have hx' := ((basisOf3 hlin).mem_span_iff_repr_mem ℤ x).mp hx
  obtain ⟨n0, hn0⟩ := hx' 0
  obtain ⟨n1, hn1⟩ := hx' 1
  obtain ⟨n2, hn2⟩ := hx' 2
  refine ⟨n0, n1, n2, ?_⟩
  have hsum := basisOf3_repr_sum hlin x
  rw [← hn0, ← hn1, ← hn2] at hsum
  simpa using hsum

/-- Minkowski: an admissible full-rank lattice for `Ω` has determinant at least `23/24`. -/
lemma Admissible.det_ge_minkowski {v1 v2 v3 : ℝ³}
    (hlin : LinearIndependent ℝ ![v1, v2, v3])
    (hadm : Admissible v1 v2 v3) :
    (23 : ℝ) / 24 ≤ |Matrix.det (coordMatrix v1 v2 v3)| := by
  by_contra hlt
  have hlt' : |Matrix.det (coordMatrix v1 v2 v3)| < 23 / 24 := lt_of_not_ge hlt
  let F := ZSpan.fundamentalDomain (basisOf3 hlin)
  let L := (Submodule.span ℤ (Set.range (basisOf3 hlin))).toAddSubgroup
  haveI : Countable L := by
    change Countable (Submodule.span ℤ (Set.range (basisOf3 hlin)))
    infer_instance
  have fund : IsAddFundamentalDomain L F volume :=
    ZSpan.isAddFundamentalDomain' (basisOf3 hlin) volume
  have hvol :
      volume F * 2 ^ Module.finrank ℝ ℝ³ < volume {p : ℝ³ | gOmega p < 1} := by
    have hF : volume F = ENNReal.ofReal |Matrix.det (coordMatrix v1 v2 v3)| :=
      volume_basisOf3_fund hlin
    have hr : Module.finrank ℝ ℝ³ = 3 := by
      simp [finrank_euclideanSpace, Fintype.card_fin]
    rw [hF, hr, volume_omegaInterior]
    have h8 : (2 : ENNReal) ^ 3 = ENNReal.ofReal 8 := by
      norm_num
    rw [h8, ← ENNReal.ofReal_mul (abs_nonneg _)]
    refine (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 23 / 3)).2 ?_
    nlinarith [hlt']
  obtain ⟨x, hx0, hxmem⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (s := {p : ℝ³ | gOmega p < 1}) fund
      (fun p hp => omegaInterior_neg hp) convex_omegaInterior hvol
  have hxL : (x : ℝ³) ∈ Submodule.span ℤ (Set.range (basisOf3 hlin)) := by
    simpa [L] using x.property
  obtain ⟨n0, n1, n2, hcombo⟩ := span_int_eq_int_combo hlin hxL
  have hne : ¬ (n0 = 0 ∧ n1 = 0 ∧ n2 = 0) := by
    intro h
    rcases h with ⟨h0, h1, h2⟩
    apply hx0
    apply Subtype.ext
    simp [hcombo, h0, h1, h2]
  have hge : 1 ≤ gOmega ((n0 : ℝ) • v1 + (n1 : ℝ) • v2 + (n2 : ℝ) • v3) :=
    hadm.gOmega_ge n0 n1 n2 hne
  have hltg : gOmega (x : ℝ³) < 1 := hxmem
  rw [hcombo] at hltg
  exact not_le_of_gt hltg hge

lemma gOmega_eq_one_face {p : ℝ³} (hp : gOmega p = 1) :
    |p 0| = 1 ∨ |p 1| = 1 ∨ |p 2| = 1 ∨ |cutForm p| = 2 := by
  have h0 : |p 0| ≤ 1 := (gOmega_ge_coord p 0).trans (le_of_eq hp)
  have h1 : |p 1| ≤ 1 := (gOmega_ge_coord p 1).trans (le_of_eq hp)
  have h2 : |p 2| ≤ 1 := (gOmega_ge_coord p 2).trans (le_of_eq hp)
  have hc : |cutForm p| / 2 ≤ 1 := (gOmega_ge_cut p).trans (le_of_eq hp)
  unfold gOmega at hp
  have hm := max_eq_iff.mp hp
  rcases hm with ⟨hm, _⟩ | ⟨hm, _⟩
  · have hm' := max_eq_iff.mp hm
    rcases hm' with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hm' := max_eq_iff.mp hm
    rcases hm' with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inr (Or.inr (Or.inl h))
    · have : |cutForm p| = 2 := by
        simp only [cutForm] at h ⊢
        linarith
      exact Or.inr (Or.inr (Or.inr this))

lemma convex_unitCubeInt : Convex ℝ {p : ℝ³ | |p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq] at hx hy ⊢
  have habs (p q : ℝ) (hp : |p| < 1) (hq : |q| < 1) :
      |a * p + b * q| < 1 := by
    have : |a * p + b * q| ≤ a * |p| + b * |q| := by
      calc |a * p + b * q| ≤ |a * p| + |b * q| := abs_add_le _ _
        _ = a * |p| + b * |q| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    have hbound : a * |p| + b * |q| < a + b := by
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simp [ha0, hb1]; exact hq
      · have : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        nlinarith [hp, hq]
    have := this.trans_lt hbound
    rwa [hab] at this
  exact ⟨habs (x 0) (y 0) hx.1 hy.1, habs (x 1) (y 1) hx.2.1 hy.2.1,
    habs (x 2) (y 2) hx.2.2 hy.2.2⟩

lemma unitCubeInt_neg {p : ℝ³}
    (hp : |p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1) :
    |(-p) 0| < 1 ∧ |(-p) 1| < 1 ∧ |(-p) 2| < 1 := by
  simpa [PiLp.neg_apply, abs_neg] using hp

lemma volume_unitCubeInt :
    volume {p : ℝ³ | |p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1} = ENNReal.ofReal 8 := by
  have hss : {p : ℝ³ | |p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1} ⊆ unitCubeSym := by
    intro p hp
    exact mem_unitCubeSym.mpr ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hz01 :
      volume ({p : ℝ³ | |p 0| = 1} ∪ {p | |p 1| = 1}) = 0 :=
    measure_union_null (volume_abs_coord_eq 0) (volume_abs_coord_eq 1)
  have hz :
      volume (({p : ℝ³ | |p 0| = 1} ∪ {p | |p 1| = 1}) ∪ {p | |p 2| = 1}) = 0 :=
    measure_union_null hz01 (volume_abs_coord_eq 2)
  have hdiff :
      unitCubeSym \ {p : ℝ³ | |p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1} ⊆
        ({p | |p 0| = 1} ∪ {p | |p 1| = 1}) ∪ {p | |p 2| = 1} := by
    intro p hp
    have hpC := mem_unitCubeSym.mp hp.1
    have : ¬ (|p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1) := hp.2
    rw [not_and_or, not_and_or] at this
    rcases this with h | h | h
    · exact Or.inl (Or.inl (le_antisymm hpC.1 (le_of_not_gt h)))
    · exact Or.inl (Or.inr (le_antisymm hpC.2.1 (le_of_not_gt h)))
    · exact Or.inr (le_antisymm hpC.2.2 (le_of_not_gt h))
  have hle : volume {p : ℝ³ | |p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1} ≤ volume unitCubeSym :=
    measure_mono hss
  have hge : volume unitCubeSym ≤
      volume {p : ℝ³ | |p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1} +
        volume (({p : ℝ³ | |p 0| = 1} ∪ {p | |p 1| = 1}) ∪ {p | |p 2| = 1}) := by
    have : unitCubeSym ⊆
        {p : ℝ³ | |p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1} ∪
          (({p | |p 0| = 1} ∪ {p | |p 1| = 1}) ∪ {p | |p 2| = 1}) := by
      intro p hp
      by_cases h : |p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1
      · exact Or.inl h
      · exact Or.inr (hdiff ⟨hp, h⟩)
    exact (measure_mono this).trans (measure_union_le _ _)
  rw [hz, add_zero] at hge
  exact le_antisymm (hle.trans_eq volume_unitCubeSym) (volume_unitCubeSym.symm.trans_le hge)

/-- If an admissible full-rank lattice has determinant `< 1`, it meets the open cube. -/
lemma Admissible.exists_mem_unitCubeInt {v1 v2 v3 : ℝ³}
    (hlin : LinearIndependent ℝ ![v1, v2, v3])
    (hadm : Admissible v1 v2 v3)
    (hdet : |Matrix.det (coordMatrix v1 v2 v3)| < 1) :
    ∃ n0 n1 n2 : ℤ, ¬ (n0 = 0 ∧ n1 = 0 ∧ n2 = 0) ∧
      let p := (n0 : ℝ) • v1 + (n1 : ℝ) • v2 + (n2 : ℝ) • v3
      |p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1 := by
  let F := ZSpan.fundamentalDomain (basisOf3 hlin)
  let L := (Submodule.span ℤ (Set.range (basisOf3 hlin))).toAddSubgroup
  haveI : Countable L := by
    change Countable (Submodule.span ℤ (Set.range (basisOf3 hlin)))
    infer_instance
  have fund : IsAddFundamentalDomain L F volume :=
    ZSpan.isAddFundamentalDomain' (basisOf3 hlin) volume
  have hvol :
      volume F * 2 ^ Module.finrank ℝ ℝ³ <
        volume {p : ℝ³ | |p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1} := by
    have hF : volume F = ENNReal.ofReal |Matrix.det (coordMatrix v1 v2 v3)| :=
      volume_basisOf3_fund hlin
    have hr : Module.finrank ℝ ℝ³ = 3 := by
      simp [finrank_euclideanSpace, Fintype.card_fin]
    rw [hF, hr, volume_unitCubeInt]
    have h8 : (2 : ENNReal) ^ 3 = ENNReal.ofReal 8 := by norm_num
    rw [h8, ← ENNReal.ofReal_mul (abs_nonneg _)]
    refine (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 8)).2 ?_
    nlinarith [hdet]
  obtain ⟨x, hx0, hxmem⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (s := {p : ℝ³ | |p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1}) fund
      (fun p hp => unitCubeInt_neg hp) convex_unitCubeInt hvol
  have hxL : (x : ℝ³) ∈ Submodule.span ℤ (Set.range (basisOf3 hlin)) := by
    simpa [L] using x.property
  obtain ⟨n0, n1, n2, hcombo⟩ := span_int_eq_int_combo hlin hxL
  refine ⟨n0, n1, n2, ?_, ?_⟩
  · intro h
    rcases h with ⟨h0, h1, h2⟩
    apply hx0
    apply Subtype.ext
    simp [hcombo, h0, h1, h2]
  · simpa [hcombo] using hxmem






/- ### Unique cube point and the main-chamber determinant bound -/

lemma Admissible.cube_point_cut {v1 v2 v3 : ℝ³}
    (hadm : Admissible v1 v2 v3) {n0 n1 n2 : ℤ}
    (hne : ¬ (n0 = 0 ∧ n1 = 0 ∧ n2 = 0))
    {p : ℝ³} (hp : p = (n0 : ℝ) • v1 + (n1 : ℝ) • v2 + (n2 : ℝ) • v3)
    (hcube : |p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1) :
    2 ≤ |cutForm p| := by
  have hge : 1 ≤ gOmega p := by
    simpa [hp] using hadm.gOmega_ge n0 n1 n2 hne
  have hx := hcube.1
  have hy := hcube.2.1
  have hz := hcube.2.2
  have hcut : 1 ≤ |cutForm p| / 2 := by
    by_contra h
    have hlt : |cutForm p| / 2 < 1 := lt_of_not_ge h
    have : gOmega p < 1 := by
      unfold gOmega
      have h01 : max (|p 0|) (|p 1|) < 1 := max_lt hx hy
      have h2c : max (|p 2|) (|p 0 + p 1 - p 2| / 2) < 1 := by
        have hc' : |p 0 + p 1 - p 2| / 2 < 1 := by simpa [cutForm] using hlt
        exact max_lt hz hc'
      exact max_lt h01 h2c
    exact not_le_of_gt this hge
  linarith

lemma cornerPos_coords {p : ℝ³}
    (hcube : |p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1) (hcut : 2 ≤ cutForm p) :
    0 < p 0 ∧ 0 < p 1 ∧ p 2 < 0 := by
  have hxlt := abs_lt.mp hcube.1
  have hylt := abs_lt.mp hcube.2.1
  have hzlt := abs_lt.mp hcube.2.2
  have hc : 2 ≤ p 0 + p 1 - p 2 := by simpa [cutForm] using hcut
  have hx0 : 0 < p 0 := by
    have hge : 2 - p 1 + p 2 ≤ p 0 := by linarith
    have hpos : 0 < 2 - p 1 + p 2 := by linarith [hylt.2, hzlt.1]
    exact lt_of_lt_of_le hpos hge
  have hy0 : 0 < p 1 := by
    have hge : 2 - p 0 + p 2 ≤ p 1 := by linarith
    have hpos : 0 < 2 - p 0 + p 2 := by linarith [hxlt.2, hzlt.1]
    exact lt_of_lt_of_le hpos hge
  have hz0 : p 2 < 0 := by
    have hle : p 2 ≤ p 0 + p 1 - 2 := by linarith
    have hneg : p 0 + p 1 - 2 < 0 := by linarith [hxlt.2, hylt.2]
    exact lt_of_le_of_lt hle hneg
  exact ⟨hx0, hy0, hz0⟩

lemma gOmega_sub_lt_one_of_cornerPos {p q : ℝ³}
    (hpC : |p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1)
    (hqC : |q 0| < 1 ∧ |q 1| < 1 ∧ |q 2| < 1)
    (hp : 2 ≤ cutForm p) (hq : 2 ≤ cutForm q) :
    gOmega (p - q) < 1 := by
  have hp0 := cornerPos_coords hpC hp
  have hq0 := cornerPos_coords hqC hq
  have hx : |p 0 - q 0| < 1 := by
    have hpl := abs_lt.mp hpC.1
    have hql := abs_lt.mp hqC.1
    have hposp := hp0.1
    have hposq := hq0.1
    rw [abs_lt]
    constructor <;> linarith
  have hy : |p 1 - q 1| < 1 := by
    have hpl := abs_lt.mp hpC.2.1
    have hql := abs_lt.mp hqC.2.1
    rw [abs_lt]
    constructor <;> linarith [hp0.2.1, hq0.2.1]
  have hz : |p 2 - q 2| < 1 := by
    have hpl := abs_lt.mp hpC.2.2
    have hql := abs_lt.mp hqC.2.2
    rw [abs_lt]
    constructor <;> linarith [hp0.2.2, hq0.2.2]
  have hcut : |cutForm (p - q)| / 2 < 1 := by
    have : cutForm (p - q) = cutForm p - cutForm q := by
      simp [cutForm, PiLp.sub_apply]; ring
    have hp2 : cutForm p < 3 := by
      have h0 := abs_lt.mp hpC.1
      have h1 := abs_lt.mp hpC.2.1
      have h2 := abs_lt.mp hpC.2.2
      simp [cutForm]
      linarith
    have hq2 : cutForm q < 3 := by
      have h0 := abs_lt.mp hqC.1
      have h1 := abs_lt.mp hqC.2.1
      have h2 := abs_lt.mp hqC.2.2
      simp [cutForm]
      linarith
    have hdiff : |cutForm p - cutForm q| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [hp, hq]
    rw [this]
    linarith
  unfold gOmega
  have hx' : |(p - q) 0| < 1 := by simp [PiLp.sub_apply]; exact hx
  have hy' : |(p - q) 1| < 1 := by simp [PiLp.sub_apply]; exact hy
  have hz' : |(p - q) 2| < 1 := by simp [PiLp.sub_apply]; exact hz
  have hc' : |(p - q) 0 + (p - q) 1 - (p - q) 2| / 2 < 1 := by
    simpa [cutForm, PiLp.sub_apply] using hcut
  exact max_lt (max_lt hx' hy') (max_lt hz' hc')

lemma xyzVec_gOmega_coord (b c d f g h : ℝ) (n0 n1 n2 : ℤ) :
    xyzVec b c d f g h n0 n1 n2 =
      (n0 : ℝ) • pt 1 b c + (n1 : ℝ) • pt d 1 f + (n2 : ℝ) • pt g h 1 :=
  rfl

/-- In the Jiao–Torquato chamber `b ≤ 0 ≤ f,g,c`, `d ≤ 0 ≤ h` with
parameters in `[-1,1]`, admissibility forces the cyclic slice
`c = d = h = 0` (or a degenerate face with determinant `1`). -/
lemma xyz_chamber_v1_sub_v3 (b c d f g h : ℝ)
    (hb0 : b ≤ 0) (_hf0 : 0 ≤ f) (_hg0 : 0 ≤ g) (_hc0 : 0 ≤ c)
    (_hd0 : d ≤ 0) (hh0 : 0 ≤ h)
    (_hb1 : -1 ≤ b) (hc1 : c ≤ 1) (_hd1 : -1 ≤ d) (_hf1 : f ≤ 1)
    (hg1 : g ≤ 1) (_hh1 : h ≤ 1) :
    let p := xyzVec b c d f g h 1 0 (-1)
    |p 0| = 1 - g ∧ |p 1| = -b + h ∧ |p 2| = 1 - c ∧
      cutForm p = 2 + b - c - g - h := by
  intro p
  have hv : p = pt (1 - g) (b - h) (c - 1) := by
    simp only [p, xyzVec_apply]
    push_cast
    congr 1 <;> ring
  have hx : |p 0| = 1 - g := by
    rw [hv, pt_coord0, abs_of_nonneg (sub_nonneg.mpr hg1)]
  have hy : |p 1| = -b + h := by
    rw [hv, pt_coord1]
    have : b - h ≤ 0 := by linarith
    rw [abs_of_nonpos this]; ring
  have hz : |p 2| = 1 - c := by
    rw [hv, pt_coord2]
    have : c - 1 ≤ 0 := by linarith
    rw [abs_of_nonpos this]; ring
  have hc : cutForm p = 2 + b - c - g - h := by
    rw [hv, cutForm_pt]; ring
  exact ⟨hx, hy, hz, hc⟩



lemma xyz_chamber_gOmega_v1_sub_v3 (b c d f g h : ℝ)
    (hb0 : b ≤ 0) (hh0 : 0 ≤ h) (hc1 : c ≤ 1) (hg1 : g ≤ 1) :
    gOmega (xyzVec b c d f g h 1 0 (-1)) =
      max (max (1 - g) (-b + h)) (max (1 - c) (|2 + b - c - g - h| / 2)) := by
  have hv : xyzVec b c d f g h 1 0 (-1) = pt (1 - g) (b - h) (c - 1) := by
    simp only [xyzVec_apply]; push_cast; congr 1 <;> ring
  rw [hv, gOmega_pt]
  have hx : |1 - g| = 1 - g := abs_of_nonneg (by linarith)
  have hy : |b - h| = -b + h := by
    have : b - h ≤ 0 := by linarith
    rw [abs_of_nonpos this]; ring
  have hz : |c - 1| = 1 - c := by
    have : c - 1 ≤ 0 := by linarith
    rw [abs_of_nonpos this]; ring
  have hc : |1 - g + (b - h) - (c - 1)| / 2 = |2 + b - c - g - h| / 2 := by
    congr 2; ring
  rw [hx, hy, hz, hc]

lemma xyz_admissible_v1_sub_v3 {b c d f g h : ℝ}
    (hb0 : b ≤ 0) (hh0 : 0 ≤ h)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hadm : Admissible (pt 1 b c) (pt d 1 f) (pt g h 1)) :
    g = 0 ∨ c = 0 ∨ 1 ≤ -b + h ∨ 2 + b - c - g - h ≤ -2 := by
  have hge := hadm.gOmega_ge 1 0 (-1) (by decide)
  have hgval := xyz_chamber_gOmega_v1_sub_v3 b c d f g h hb0 hh0 hc1 hg1
  have hcombo : xyzVec b c d f g h 1 0 (-1) =
      ((1 : ℤ) : ℝ) • pt 1 b c + ((0 : ℤ) : ℝ) • pt d 1 f +
        ((-1 : ℤ) : ℝ) • pt g h 1 := rfl
  rw [hcombo] at hgval
  rw [hgval] at hge
  rw [le_max_iff, le_max_iff, le_max_iff] at hge
  rcases hge with (hg1le | hbhle) | (hc1le | hcle)
  · exact Or.inl (le_antisymm (by linarith) hg0)
  · exact Or.inr (Or.inr (Or.inl hbhle))
  · exact Or.inr (Or.inl (le_antisymm (by linarith) hc0))
  · have habs2 : 2 ≤ |2 + b - c - g - h| := by linarith
    rw [le_abs] at habs2
    rcases habs2 with hpos | hneg
    · have hg00 : g = 0 := le_antisymm (by linarith) hg0
      exact Or.inl hg00
    · exact Or.inr (Or.inr (Or.inr (by linarith)))


lemma xyz_chamber_gOmega_v2_sub_v3 (b c d f g h : ℝ)
    (hd0 : d ≤ 0) (hh0 : 0 ≤ h) (hf1 : f ≤ 1) (hg0 : 0 ≤ g) (hh1 : h ≤ 1) :
    gOmega (xyzVec b c d f g h 0 1 (-1)) =
      max (max (-d + g) (1 - h)) (max (1 - f) (|2 + d - f - g - h| / 2)) := by
  have hv : xyzVec b c d f g h 0 1 (-1) = pt (d - g) (1 - h) (f - 1) := by
    simp only [xyzVec_apply]; push_cast; congr 1 <;> ring
  rw [hv, gOmega_pt]
  have hx : |d - g| = -d + g := by
    have : d - g ≤ 0 := by linarith
    rw [abs_of_nonpos this]; ring
  have hy : |1 - h| = 1 - h := abs_of_nonneg (sub_nonneg.mpr hh1)
  have hz : |f - 1| = 1 - f := by
    have : f - 1 ≤ 0 := by linarith
    rw [abs_of_nonpos this]; ring
  have hc : |d - g + (1 - h) - (f - 1)| / 2 = |2 + d - f - g - h| / 2 := by
    congr 2; ring
  rw [hx, hy, hz, hc]

lemma xyz_admissible_v2_sub_v3 {b c d f g h : ℝ}
    (hd0 : d ≤ 0) (hh0 : 0 ≤ h)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (hg0 : 0 ≤ g) (hh1 : h ≤ 1)
    (hadm : Admissible (pt 1 b c) (pt d 1 f) (pt g h 1)) :
    h = 0 ∨ f = 0 ∨ 1 ≤ -d + g ∨ 2 + d - f - g - h ≤ -2 := by
  have hge := hadm.gOmega_ge 0 1 (-1) (by decide)
  have hgval := xyz_chamber_gOmega_v2_sub_v3 b c d f g h hd0 hh0 hf1 hg0 hh1
  have hcombo : xyzVec b c d f g h 0 1 (-1) =
      ((0 : ℤ) : ℝ) • pt 1 b c + ((1 : ℤ) : ℝ) • pt d 1 f +
        ((-1 : ℤ) : ℝ) • pt g h 1 := rfl
  rw [hcombo] at hgval
  rw [hgval] at hge
  rw [le_max_iff, le_max_iff, le_max_iff] at hge
  rcases hge with (hdgle | hh1le) | (hf1le | hcle)
  · exact Or.inr (Or.inr (Or.inl hdgle))
  · exact Or.inl (le_antisymm (by linarith) hh0)
  · exact Or.inr (Or.inl (le_antisymm (by linarith) hf0))
  · have habs2 : 2 ≤ |2 + d - f - g - h| := by linarith
    rw [le_abs] at habs2
    rcases habs2 with hpos | hneg
    · exact Or.inl (le_antisymm (by linarith) hh0)
    · exact Or.inr (Or.inr (Or.inr (by linarith)))

lemma xyz_chamber_gOmega_v1_add_v2 (b c d f g h : ℝ)
    (hb0 : b ≤ 0) (hd0 : d ≤ 0) (hf0 : 0 ≤ f) (hb1 : -1 ≤ b) (hd1 : -1 ≤ d) :
    gOmega (xyzVec b c d f g h 1 1 0) =
      max (max (1 + d) (1 + b)) (max (|c + f|) (|2 + b - c + d - f| / 2)) := by
  have hv : xyzVec b c d f g h 1 1 0 = pt (1 + d) (b + 1) (c + f) := by
    simp only [xyzVec_apply]; push_cast; congr 1 <;> ring
  rw [hv, gOmega_pt]
  have hdnn : 0 ≤ 1 + d := by nlinarith
  have hbnn : 0 ≤ 1 + b := by nlinarith
  have hx : |1 + d| = 1 + d := abs_of_nonneg hdnn
  have hy : |b + 1| = 1 + b := by rw [add_comm b 1, abs_of_nonneg hbnn]
  have hc : |1 + d + (b + 1) - (c + f)| / 2 = |2 + b - c + d - f| / 2 := by
    congr 2; ring
  rw [hx, hy, hc]

lemma xyz_admissible_v1_add_v2 {b c d f g h : ℝ}
    (hb0 : b ≤ 0) (hd0 : d ≤ 0) (hf0 : 0 ≤ f)
    (hb1 : -1 ≤ b) (hd1 : -1 ≤ d) (hf1 : f ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hadm : Admissible (pt 1 b c) (pt d 1 f) (pt g h 1)) :
    d = 0 ∨ b = 0 ∨ f = 1 ∨ 1 ≤ |c + f| := by
  have hge := hadm.gOmega_ge 1 1 0 (by decide)
  have hgval := xyz_chamber_gOmega_v1_add_v2 b c d f g h hb0 hd0 hf0 hb1 hd1
  have hcombo : xyzVec b c d f g h 1 1 0 =
      ((1 : ℤ) : ℝ) • pt 1 b c + ((1 : ℤ) : ℝ) • pt d 1 f +
        ((0 : ℤ) : ℝ) • pt g h 1 := rfl
  rw [hcombo] at hgval
  rw [hgval] at hge
  rw [le_max_iff, le_max_iff, le_max_iff] at hge
  rcases hge with (hdle | hble) | (hfle | hcle)
  · exact Or.inl (le_antisymm hd0 (by linarith))
  · exact Or.inr (Or.inl (le_antisymm hb0 (by linarith)))
  · exact Or.inr (Or.inr (Or.inr hfle))
  · have habs2 : 2 ≤ |2 + b - c + d - f| := by linarith
    rw [le_abs] at habs2
    rcases habs2 with hpos | hneg
    · exact Or.inr (Or.inl (le_antisymm hb0 (by linarith)))
    · exact Or.inr (Or.inr (Or.inl (le_antisymm hf1 (by linarith))))


lemma two_cornerPos_lattice_overlap {v1 v2 v3 : ℝ³}
    (hadm : Admissible v1 v2 v3)
    {n0 n1 n2 m0 m1 m2 : ℤ}
    (hne : ¬ (n0 = m0 ∧ n1 = m1 ∧ n2 = m2)) :
    let p := (n0 : ℝ) • v1 + (n1 : ℝ) • v2 + (n2 : ℝ) • v3
    let q := (m0 : ℝ) • v1 + (m1 : ℝ) • v2 + (m2 : ℝ) • v3
    (|p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1) → (2 ≤ cutForm p) →
    (|q 0| < 1 ∧ |q 1| < 1 ∧ |q 2| < 1) → (2 ≤ cutForm q) →
    False := by
  intro p q hpC hp2 hqC hq2
  have hlt := gOmega_sub_lt_one_of_cornerPos hpC hqC hp2 hq2
  have hdiff : p - q =
      ((n0 - m0 : ℤ) : ℝ) • v1 + ((n1 - m1 : ℤ) : ℝ) • v2 +
        ((n2 - m2 : ℤ) : ℝ) • v3 := by
    simp only [p, q, Int.cast_sub, sub_smul]
    abel
  have hne' : ¬ (n0 - m0 = 0 ∧ n1 - m1 = 0 ∧ n2 - m2 = 0) := by
    intro h
    apply hne
    exact ⟨eq_of_sub_eq_zero h.1, eq_of_sub_eq_zero h.2.1, eq_of_sub_eq_zero h.2.2⟩
  have hge := hadm.gOmega_ge (n0 - m0) (n1 - m1) (n2 - m2) hne'
  rw [hdiff] at hlt
  exact not_le_of_gt hlt hge



lemma Admissible.unique_pos_corner {v1 v2 v3 : ℝ³}
    (hadm : Admissible v1 v2 v3)
    {n0 n1 n2 m0 m1 m2 : ℤ}
    (hpC : let p := (n0 : ℝ) • v1 + (n1 : ℝ) • v2 + (n2 : ℝ) • v3
           |p 0| < 1 ∧ |p 1| < 1 ∧ |p 2| < 1)
    (hp2 : let p := (n0 : ℝ) • v1 + (n1 : ℝ) • v2 + (n2 : ℝ) • v3
           2 ≤ cutForm p)
    (hqC : let q := (m0 : ℝ) • v1 + (m1 : ℝ) • v2 + (m2 : ℝ) • v3
           |q 0| < 1 ∧ |q 1| < 1 ∧ |q 2| < 1)
    (hq2 : let q := (m0 : ℝ) • v1 + (m1 : ℝ) • v2 + (m2 : ℝ) • v3
           2 ≤ cutForm q) :
    n0 = m0 ∧ n1 = m1 ∧ n2 = m2 := by
  by_contra h
  exact two_cornerPos_lattice_overlap hadm h hpC hp2 hqC hq2


lemma xyz_cdh0_admissible_det_ge {b f g : ℝ}
    (hb0 : b ≤ 0) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hb1 : -1 ≤ b) (hf1 : f ≤ 1) (hg1 : g ≤ 1)
    (hadm : Admissible (pt 1 b 0) (pt 0 1 f) (pt g 0 1)) :
    26 / 27 ≤ |Matrix.det (xyzMatrix b 0 0 f g 0)| := by
  have ht : 0 ≤ -b := neg_nonneg.mpr hb0
  have ht1 : -b ≤ 1 := neg_le.mpr (by linarith)
  have hadm' : Admissible (pt 1 (-(-b)) 0) (pt 0 1 f) (pt g 0 1) := by
    simpa [neg_neg] using hadm
  have hmat : xyzMatrix b 0 0 f g 0 = xyzMatrix (-(-b)) 0 0 f g 0 := by
    simp [neg_neg]
  rw [hmat]
  exact xyz_cyclic_admissible_det_ge ht hf0 hg0 ht1 hf1 hg1 hadm'


lemma xyzMatrix_det_b_neg (t c d s u h : ℝ) :
    Matrix.det (xyzMatrix (-t) c d s u h) =
      1 + t * d - s * h - c * u - t * s * u + c * d * h := by
  rw [xyzMatrix_det]; ring


lemma xyzMatrix_det_gh0 (b c d f : ℝ) :
    Matrix.det (xyzMatrix b c d f 0 0) = 1 - b * d := by
  rw [xyzMatrix_det]; ring

lemma xyzMatrix_det_cd0 (b f g h : ℝ) :
    Matrix.det (xyzMatrix b 0 0 f g h) = 1 - f * h + b * f * g := by
  rw [xyzMatrix_det]; ring

lemma xyzMatrix_det_bd0 (c f g h : ℝ) :
    Matrix.det (xyzMatrix 0 c 0 f g h) = 1 - f * h - c * g := by
  rw [xyzMatrix_det]; ring

lemma xyz_det_one_of_b_d_zero {c f g h : ℝ} :
    |Matrix.det (xyzMatrix 0 c 0 f g h)| = |1 - f * h - c * g| := by
  rw [xyzMatrix_det_bd0]


lemma xyz_gh0_b_or_d_zero_det_ge {b c d f : ℝ}
    (hbd : b = 0 ∨ d = 0) :
    26 / 27 ≤ |Matrix.det (xyzMatrix b c d f 0 0)| := by
  rw [xyzMatrix_det_gh0]
  rcases hbd with hb | hd
  · simp [hb, abs_one]; norm_num
  · simp [hd, abs_one]; norm_num

lemma xyzVec_v1_add_v2_sub_v3 (b c d f g h : ℝ) :
    xyzVec b c d f g h 1 1 (-1) = pt (1 + d - g) (b + 1 - h) (c + f - 1) := by
  rw [xyzVec_apply]
  push_cast
  congr 1 <;> ring


lemma xyz_gh0_admissible_b_or_d_or {b c d f : ℝ}
    (hb0 : b ≤ 0) (hd0 : d ≤ 0) (hc0 : 0 ≤ c) (hf0 : 0 ≤ f)
    (hb1 : -1 ≤ b) (hd1 : -1 ≤ d) (hc1 : c ≤ 1) (hf1 : f ≤ 1)
    (hadm : Admissible (pt 1 b c) (pt d 1 f) (pt 0 0 1)) :
    b = 0 ∨ d = 0 ∨ f = 1 ∨ 1 ≤ c + f := by
  have hge := xyz_admissible_v1_add_v2 (b := b) (c := c) (d := d) (f := f)
      (g := (0 : ℝ)) (h := (0 : ℝ)) hb0 hd0 hf0 hb1 hd1 hf1 hc0 hc1 hadm
  rcases hge with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr ?_))
    have habs : 1 ≤ |c + f| := h
    have hnn : |c + f| = c + f := abs_of_nonneg (add_nonneg hc0 hf0)
    linarith


lemma xyz_gh0_gOmega_v1_add_v2_sub_v3 (b c d f : ℝ)
    (hb1 : -1 ≤ b) (hd1 : -1 ≤ d) :
    gOmega (xyzVec b c d f 0 0 1 1 (-1)) =
      max (max (1 + d) (1 + b))
          (max (|c + f - 1|) (|3 + b + d - c - f| / 2)) := by
  rw [xyzVec_v1_add_v2_sub_v3, gOmega_pt]
  have hdnn : 0 ≤ 1 + d := by linarith
  have hbnn : 0 ≤ 1 + b := by linarith
  have hx : |1 + d - 0| = 1 + d := by
    have : 1 + d - 0 = 1 + d := by ring
    rw [this, abs_of_nonneg hdnn]
  have hy : |b + 1 - 0| = 1 + b := by
    have : b + 1 - 0 = 1 + b := by ring
    rw [this, abs_of_nonneg hbnn]
  have hc : |(1 + d - 0) + (b + 1 - 0) - (c + f - 1)| / 2 =
      |3 + b + d - c - f| / 2 := by
    congr 2; ring
  rw [hx, hy, hc]

lemma xyz_gh0_admissible_v111 {b c d f : ℝ}
    (hb0 : b ≤ 0) (hd0 : d ≤ 0)
    (hb1 : -1 ≤ b) (hd1 : -1 ≤ d)
    (hadm : Admissible (pt 1 b c) (pt d 1 f) (pt 0 0 1)) :
    d = 0 ∨ b = 0 ∨ 1 ≤ |c + f - 1| ∨ 2 ≤ |3 + b + d - c - f| := by
  have hge := hadm.gOmega_ge 1 1 (-1) (by decide)
  have hgval := xyz_gh0_gOmega_v1_add_v2_sub_v3 b c d f hb1 hd1
  have hcombo : xyzVec b c d f 0 0 1 1 (-1) =
      ((1 : ℤ) : ℝ) • pt 1 b c + ((1 : ℤ) : ℝ) • pt d 1 f +
        ((-1 : ℤ) : ℝ) • pt 0 0 1 := rfl
  rw [hcombo] at hgval
  rw [hgval] at hge
  rw [le_max_iff, le_max_iff, le_max_iff] at hge
  rcases hge with (hdle | hble) | (hfle | hcle)
  · exact Or.inl (le_antisymm hd0 (by linarith))
  · exact Or.inr (Or.inl (le_antisymm hb0 (by linarith)))
  · exact Or.inr (Or.inr (Or.inl hfle))
  · exact Or.inr (Or.inr (Or.inr (by linarith)))


lemma xyz_gh0_det_ge_of_b_eq_zero (c d f : ℝ) :
    26 / 27 ≤ |Matrix.det (xyzMatrix 0 c d f 0 0)| := by
  rw [xyzMatrix_det_gh0]
  simp [abs_one]
  norm_num

lemma xyz_gh0_det_ge_of_d_eq_zero (b c f : ℝ) :
    26 / 27 ≤ |Matrix.det (xyzMatrix b c 0 f 0 0)| := by
  rw [xyzMatrix_det_gh0]
  simp [abs_one]
  norm_num


lemma xyzVec_v1_add_v2_sub_v3_twice (b c d f : ℝ) :
    xyzVec b c d f 0 0 1 1 (-2) = pt (1 + d) (b + 1) (c + f - 2) := by
  rw [xyzVec_apply]
  push_cast
  congr 1 <;> ring

lemma xyz_gh0_gOmega_of_c_f_one (b d : ℝ)
    (hb1 : -1 ≤ b) (hd1 : -1 ≤ d) :
    gOmega (xyzVec b 1 d 1 0 0 1 1 (-2)) =
      max (max (1 + d) (1 + b)) ((2 + b + d) / 2) := by
  rw [xyzVec_v1_add_v2_sub_v3_twice, gOmega_pt]
  have h0 : (1 : ℝ) + 1 - 2 = 0 := by norm_num
  rw [h0]
  have hdnn : 0 ≤ 1 + d := by linarith
  have hbnn : 0 ≤ 1 + b := by linarith
  have hsum : 0 ≤ 2 + b + d := by linarith
  have hx : |1 + d| = 1 + d := abs_of_nonneg hdnn
  have hy : |b + 1| = 1 + b := by
    rw [add_comm b, abs_of_nonneg hbnn]
  have hz : |(0 : ℝ)| = 0 := abs_zero
  have hc : |1 + d + (b + 1) - 0| / 2 = (2 + b + d) / 2 := by
    have : 1 + d + (b + 1) - 0 = 2 + b + d := by ring
    rw [this, abs_of_nonneg hsum]
  rw [hx, hy, hz, hc, max_eq_right (show (0 : ℝ) ≤ (2 + b + d) / 2 by linarith)]

lemma xyz_gh0_not_adm_of_c_f_one {b d : ℝ}
    (hb0 : b < 0) (hd0 : d < 0) (hb1 : -1 ≤ b) (hd1 : -1 ≤ d) :
    ¬ Admissible (pt 1 b 1) (pt d 1 1) (pt 0 0 1) := by
  intro hadm
  have hge := hadm.gOmega_ge 1 1 (-2) (by decide)
  have hgval := xyz_gh0_gOmega_of_c_f_one b d hb1 hd1
  have hcombo : xyzVec b 1 d 1 0 0 1 1 (-2) =
      ((1 : ℤ) : ℝ) • pt 1 b 1 + ((1 : ℤ) : ℝ) • pt d 1 1 +
        ((-2 : ℤ) : ℝ) • pt 0 0 1 := rfl
  rw [hcombo] at hgval
  rw [hgval] at hge
  have hlt1 : max (max (1 + d) (1 + b)) ((2 + b + d) / 2) < 1 := by
    refine max_lt (max_lt ?_ ?_) ?_
    · linarith
    · linarith
    · linarith
  exact (not_le_of_gt hlt1) hge


lemma xyz_gh0_cf_sum_of_abs {c f : ℝ}
    (hc0 : 0 ≤ c) (hf0 : 0 ≤ f) (hc1 : c ≤ 1) (hf1 : f ≤ 1)
    (habs : 1 ≤ |c + f - 1|) :
    c + f = 0 ∨ c + f = 2 := by
  have hbound : |c + f - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have heq : |c + f - 1| = 1 := le_antisymm hbound habs
  rcases eq_or_eq_neg_of_abs_eq heq with h | h
  · exact Or.inr (by linarith)
  · exact Or.inl (by linarith)

lemma xyz_gh0_triple_ge {b c d f : ℝ}
    (hb1 : -1 ≤ b) (hd1 : -1 ≤ d) (hc1 : c ≤ 1) (hf1 : f ≤ 1) :
    -1 ≤ 3 + b + d - c - f := by
  linarith

lemma xyz_gh0_admissible_b_eq_or_d_eq {b c d f : ℝ}
    (hb0 : b ≤ 0) (hd0 : d ≤ 0) (hc0 : 0 ≤ c) (hf0 : 0 ≤ f)
    (hb1 : -1 ≤ b) (hd1 : -1 ≤ d) (hc1 : c ≤ 1) (hf1 : f ≤ 1)
    (hadm : Admissible (pt 1 b c) (pt d 1 f) (pt 0 0 1)) :
    b = 0 ∨ d = 0 := by
  have hforce := xyz_gh0_admissible_b_or_d_or hb0 hd0 hc0 hf0 hb1 hd1 hc1 hf1 hadm
  have hv111 := xyz_gh0_admissible_v111 hb0 hd0 hb1 hd1 hadm
  by_cases hbz : b = 0
  · exact Or.inl hbz
  by_cases hdz : d = 0
  · exact Or.inr hdz
  have hbneg : b < 0 := lt_of_le_of_ne hb0 hbz
  have hdneg : d < 0 := lt_of_le_of_ne hd0 hdz
  have hcf : f = 1 ∨ 1 ≤ c + f := by
    rcases hforce with h | h | h | h
    · exact (hbz h).elim
    · exact (hdz h).elim
    · exact Or.inl h
    · exact Or.inr h
  have hcf1 : 1 ≤ c + f := by
    rcases hcf with hf | h
    · linarith
    · exact h
  rcases hv111 with h | h | habs | hcut
  · exact (hdz h).elim
  · exact (hbz h).elim
  · have hsum := xyz_gh0_cf_sum_of_abs hc0 hf0 hc1 hf1 habs
    rcases hsum with h0 | h2
    · linarith
    · have hc : c = 1 := by linarith
      have hf : f = 1 := by linarith
      subst hc; subst hf
      exact (xyz_gh0_not_adm_of_c_f_one hbneg hdneg hb1 hd1 hadm).elim
  · have hge : -1 ≤ 3 + b + d - c - f := xyz_gh0_triple_ge hb1 hd1 hc1 hf1
    have hpos : 2 ≤ 3 + b + d - c - f := by
      rw [le_abs] at hcut
      rcases hcut with hpos | hneg
      · exact hpos
      · linarith
    linarith

lemma xyz_gh0_admissible_det_ge {b c d f : ℝ}
    (hb0 : b ≤ 0) (hd0 : d ≤ 0) (hc0 : 0 ≤ c) (hf0 : 0 ≤ f)
    (hb1 : -1 ≤ b) (hd1 : -1 ≤ d) (hc1 : c ≤ 1) (hf1 : f ≤ 1)
    (hadm : Admissible (pt 1 b c) (pt d 1 f) (pt 0 0 1)) :
    26 / 27 ≤ |Matrix.det (xyzMatrix b c d f 0 0)| := by
  have hbd := xyz_gh0_admissible_b_eq_or_d_eq hb0 hd0 hc0 hf0 hb1 hd1 hc1 hf1 hadm
  exact xyz_gh0_b_or_d_zero_det_ge hbd


lemma xyzMatrix_det_dh0 (b c f g : ℝ) :
    Matrix.det (xyzMatrix b c 0 f g 0) = 1 + g * (b * f - c) := by
  rw [xyzMatrix_det]; ring

lemma xyz_dh0_det_ge_of_g_zero (b c f : ℝ) :
    26 / 27 ≤ |Matrix.det (xyzMatrix b c 0 f 0 0)| := by
  rw [xyzMatrix_det_dh0]
  simp [abs_one]
  norm_num

lemma xyz_dh0_admissible_v1_sub_v3 {b c f g : ℝ}
    (hb0 : b ≤ 0) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hadm : Admissible (pt 1 b c) (pt 0 1 f) (pt g 0 1)) :
    g = 0 ∨ c = 0 ∨ 1 ≤ -b ∨ 2 + b - c - g ≤ -2 := by
  have h := xyz_admissible_v1_sub_v3 (b := b) (c := c) (d := (0 : ℝ)) (f := f)
      (g := g) (h := (0 : ℝ)) hb0 (le_refl 0) hc0 hc1 hg0 hg1 hadm
  simpa using h


lemma xyzVec_dh0_v112 (b c f g : ℝ) :
    xyzVec b c 0 f g 0 1 1 (-2) = pt (1 - 2 * g) (b + 1) (c + f - 2) := by
  rw [xyzVec_apply]
  push_cast
  congr 1 <;> ring

lemma xyz_dh0_b_neg_one_v111 (c f g : ℝ)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    gOmega (xyzVec (-1) c 0 f g 0 1 1 (-1)) =
      max (max (1 - g) (0 : ℝ))
          (max (|c + f - 1|) (|2 - g - c - f| / 2)) := by
  rw [xyzVec_v1_add_v2_sub_v3, gOmega_pt]
  have h1 : (1 : ℝ) + 0 - g = 1 - g := by ring
  have h2 : (-1 : ℝ) + 1 - 0 = 0 := by ring
  rw [h1, h2, abs_zero]
  have hx : |1 - g| = 1 - g := abs_of_nonneg (sub_nonneg.mpr hg1)
  rw [hx]
  have hc : |1 - g + 0 - (c + f - 1)| / 2 = |2 - g - c - f| / 2 := by
    congr 2; ring
  rw [hc]

lemma xyz_b_neg_one_cf_one_not_adm {g : ℝ}
    (hg0 : 0 < g) (hg1 : g < 1) :
    ¬ Admissible (pt 1 (-1) 1) (pt 0 1 1) (pt g 0 1) := by
  intro hadm
  have hge := hadm.gOmega_ge 1 1 (-2) (by decide)
  have hv : xyzVec (-1) 1 0 1 g 0 1 1 (-2) = pt (1 - 2 * g) 0 0 := by
    rw [xyzVec_dh0_v112]; congr 1 <;> ring
  have hcombo : xyzVec (-1) 1 0 1 g 0 1 1 (-2) =
      ((1 : ℤ) : ℝ) • pt 1 (-1) 1 + ((1 : ℤ) : ℝ) • pt 0 1 1 +
        ((-2 : ℤ) : ℝ) • pt g 0 1 := rfl
  rw [← hcombo, hv, gOmega_pt] at hge
  have hx : |1 - 2 * g| < 1 := by
    refine abs_lt.mpr ⟨?_, ?_⟩ <;> linarith
  have hz : |(0 : ℝ)| = 0 := abs_zero
  have hc : |1 - 2 * g + 0 - 0| / 2 = |1 - 2 * g| / 2 := by
    congr 1; ring
  rw [hz, hc] at hge
  have hlt : max (max (|1 - 2 * g|) 0) (max 0 (|1 - 2 * g| / 2)) < 1 := by
    refine max_lt (max_lt hx (by norm_num)) (max_lt (by norm_num) ?_)
    linarith
  exact (not_le_of_gt hlt) hge


lemma xyz_dh0_b_neg_one_admissible_det_ge {c f g : ℝ}
    (hc0 : 0 ≤ c) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hc1 : c ≤ 1) (hf1 : f ≤ 1) (hg1 : g ≤ 1)
    (hadm : Admissible (pt 1 (-1) c) (pt 0 1 f) (pt g 0 1)) :
    26 / 27 ≤ |Matrix.det (xyzMatrix (-1) c 0 f g 0)| := by
  rw [xyzMatrix_det_dh0]
  have hge := hadm.gOmega_ge 1 1 (-1) (by decide)
  have hgval := xyz_dh0_b_neg_one_v111 c f g hg0 hg1
  have hcombo : xyzVec (-1) c 0 f g 0 1 1 (-1) =
      ((1 : ℤ) : ℝ) • pt 1 (-1) c + ((1 : ℤ) : ℝ) • pt 0 1 f +
        ((-1 : ℤ) : ℝ) • pt g 0 1 := rfl
  rw [hcombo] at hgval
  rw [hgval] at hge
  rw [le_max_iff, le_max_iff, le_max_iff] at hge
  rcases hge with (hgle | h0le) | (hcfle | hcut)
  · have hg00 : g = 0 := le_antisymm (by linarith) hg0
    subst hg00
    simp [abs_one]
    norm_num
  · -- 1 ≤ 0, impossible
    linarith
  · have hsum := xyz_gh0_cf_sum_of_abs hc0 hf0 hc1 hf1 hcfle
    rcases hsum with h0 | h2
    · have hc00 : c = 0 := by linarith
      have hf00 : f = 0 := by linarith
      subst hc00
      subst hf00
      simp [abs_one]
      norm_num
    · have hc : c = 1 := by linarith
      have hf : f = 1 := by linarith
      subst hc; subst hf
      by_cases hgpos : g = 0
      · subst hgpos
        simp [abs_one]
        norm_num
      by_cases hgone : g = 1
      · subst hgone
        -- det = 1 + 1*((-1)*1 - 1) = 1 + (-1-1) = -1, abs=1
        norm_num
      · have hglt : g < 1 := lt_of_le_of_ne hg1 hgone
        have hggt : 0 < g := lt_of_le_of_ne hg0 (Ne.symm hgpos)
        exact (xyz_b_neg_one_cf_one_not_adm hggt hglt hadm).elim
  · have : |2 - g - c - f| ≤ 3 := by
      have : -3 ≤ 2 - g - c - f ∧ 2 - g - c - f ≤ 2 := by constructor <;> linarith
      exact abs_le.mpr (by constructor <;> linarith)
    have hge2 : 2 ≤ |2 - g - c - f| := by linarith
    rw [le_abs] at hge2
    rcases hge2 with hpos | hneg
    · -- 2 ≤ 2-g-c-f ⇒ 0 ≤ -g-c-f ⇒ g=c=f=0
      have hg00 : g = 0 := by linarith
      subst hg00
      simp [abs_one]
      norm_num
    · -- 2 ≤ -(2-g-c-f) ⇒ g+c+f ≥ 4, impossible
      linarith

lemma xyz_dh0_admissible_det_ge {b c f g : ℝ}
    (hb0 : b ≤ 0) (hc0 : 0 ≤ c) (hf0 : 0 ≤ f)
    (hb1 : -1 ≤ b) (hc1 : c ≤ 1) (hf1 : f ≤ 1)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hadm : Admissible (pt 1 b c) (pt 0 1 f) (pt g 0 1)) :
    26 / 27 ≤ |Matrix.det (xyzMatrix b c 0 f g 0)| := by
  have hA := xyz_dh0_admissible_v1_sub_v3 hb0 hc0 hc1 hg0 hg1 hadm
  rcases hA with hg | hc | hb | hext
  · subst hg
    exact xyz_dh0_det_ge_of_g_zero b c f
  · subst hc
    exact xyz_cdh0_admissible_det_ge hb0 hf0 hg0 hb1 hf1 hg1 hadm
  · have hbval : b = -1 := le_antisymm (le_neg.mp hb) hb1
    subst hbval
    exact xyz_dh0_b_neg_one_admissible_det_ge hc0 hf0 hg0 hc1 hf1 hg1 hadm
  · -- 2+b-c-g ≤ -2 ⇒ b-c-g ≤ -4, but b-c-g ≥ -1-1-1 = -3
    linarith

