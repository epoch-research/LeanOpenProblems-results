import Submission.CharThreeNorm
import Submission.AffineSlices

/-!
A uniform obstruction to a cubic norm/trace shear code, including arbitrary
nonzero fixed weights and deletion of zero points and zero coordinates.
This file does not settle Erdős 714.
-/

open SimpleGraph Polynomial
open Erdos714CharThreeNorm (normForm)

namespace Erdos714CubicTraceShear

variable {F : Type*} [Field F] [CharP F 3]
abbrev Point (F : Type*) := F × F × F
abbrev NonzeroPoint (F : Type*) [Zero F] := {x : Point F // x ≠ 0}

/-- Multiplication in the basis `1,θ,θ²`, where `θ³=θ+d`. -/
def pointMul (d : F) (x y : Point F) : Point F :=
  (x.1*y.1 + d*(x.2.1*y.2.2+x.2.2*y.2.1),
   x.1*y.2.1+x.2.1*y.1+x.2.1*y.2.2+x.2.2*y.2.1+d*x.2.2*y.2.2,
   x.1*y.2.2+x.2.1*y.2.1+x.2.2*y.1+x.2.2*y.2.2)

/-- The trace pairing in this Artin–Schreier basis. -/
def traceProduct (x y : Point F) : F :=
  -(x.1*y.2.2+x.2.1*y.2.1+x.2.2*y.1+x.2.2*y.2.2)

/-- This is the trace of the actual coordinate multiplication matrix. -/
theorem traceProduct_eq_trace (d : F) (x y : Point F) :
    let v := pointMul d x y
    traceProduct x y = Matrix.trace
      !![v.1, d*v.2.2, d*v.2.1;
         v.2.1, v.1+v.2.2, v.2.1+d*v.2.2;
         v.2.2, v.2.1, v.1+v.2.2] := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  dsimp only
  rw [Matrix.trace_fin_three]
  change traceProduct x y = (pointMul d x y).1 +
    ((pointMul d x y).1 + (pointMul d x y).2.2) +
    ((pointMul d x y).1 + (pointMul d x y).2.2)
  dsimp only [pointMul, traceProduct]
  linear_combination -(x.1*y.1+d*(x.2.1*y.2.2+x.2.2*y.2.1)+
    x.1*y.2.2+x.2.1*y.2.1+x.2.2*y.1+x.2.2*y.2.2)*h3

def code (d a k : F) (x t : Point F) : F :=
  k + traceProduct x t + normForm d (x + a • t)

def restrictedCode (d a k : F) (x t : NonzeroPoint F) : F := code d a k x t

omit [CharP F 3] in
lemma norm_smul (d a : F) (x : Point F) : normForm d (a • x) = a ^ 3 * normForm d x := by
  rcases x with ⟨x,y,z⟩
  change normForm d (a*x,a*y,a*z) = a^3 * normForm d (x,y,z)
  dsimp only [normForm]
  ring

omit [CharP F 3] in
lemma traceProduct_smul (a b : F) (x y : Point F) :
    traceProduct (a • x) (b • y) = a*b*traceProduct x y := by
  rcases x with ⟨x₀,x₁,x₂⟩
  rcases y with ⟨y₀,y₁,y₂⟩
  change traceProduct (a*x₀,a*x₁,a*x₂) (b*y₀,b*y₁,b*y₂) =
    a*b*traceProduct (x₀,x₁,x₂) (y₀,y₁,y₂)
  dsimp only [traceProduct]
  ring

omit [CharP F 3] in
lemma code_scaled (d a k l : F) (x t : Point F) :
    code d a k ((a*l) • x) (l • t) =
      k + a*l^2*traceProduct x t + a^3*l^3*normForm d (x+t) := by
  have he : (a*l) • x + a • l • t = (a*l) • (x+t) := by
    rw [smul_add, smul_smul]
  rw [code, traceProduct_smul, he, norm_smul]
  ring

def rows (s : F) : Fin 4 → Point F := ![(s,0,0), (s+1,0,0), (s-1,0,0), (s,1,0)]
def columns (d s : F) : Fin 4 → Point F :=
  ![(-s,1,0), (1-s,1,0), (-1-s,1,0), (d-s,-1,0)]

omit [CharP F 3] in
lemma trace_table (d s : F) (i j : Fin 4) :
    traceProduct (rows s i) (columns d s j) =
      if i = 3 then (if j = 3 then 1 else -1) else 0 := by
  fin_cases i <;> fin_cases j <;> simp [traceProduct, rows, columns]

lemma norm_table (d s : F) (i j : Fin 4) :
    normForm d (rows s i + columns d s j) =
      if i = 3 then (if j = 3 then d^3 else -d) else
        (if j = 3 then d^3+d else d) := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have h2 : (2 : F) = -1 := by linear_combination h3
  have h6 : (6 : F) = 0 := by linear_combination 2*h3
  have h8 : (8 : F) = -1 := by linear_combination 3*h3
  fin_cases i <;> fin_cases j <;>
    simp [normForm, rows, columns] <;> ring_nf <;> simp [h2,h3,h6,h8]

/-- The same four rows agree at all four coordinates after any scalar translation. -/
theorem code_table (d a k l s : F) (h : a^2*l*d = 1) (i j : Fin 4) :
    code d a k ((a*l) • rows s i) (l • columns d s j) =
      k + a*l^2 + if j = 3 then a^3*l^3*d^3 else 0 := by
  have hcd : a^3*l^3*d = a*l^2 := by linear_combination a*l^2*h
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  rw [code_scaled, trace_table, norm_table]
  by_cases hi : i = 3 <;> by_cases hj : j = 3 <;> simp [hi,hj]
  · linear_combination -hcd - a*l^2*h3
  · linear_combination hcd
  · exact hcd

private lemma neg_one_ne_one : (-1 : F) ≠ 1 := by
  intro h
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have : (1 : F) = 0 := by linear_combination h3 + h
  exact one_ne_zero this

lemma rows_injective (s : F) : Function.Injective (rows s) := by
  have hb : Function.Injective (rows (0 : F)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [rows, neg_one_ne_one, Ne.symm neg_one_ne_one] at hij ⊢
  have he (i : Fin 4) : rows s i = (s,0,0) + rows 0 i := by
    fin_cases i <;> simp [rows, sub_eq_add_neg]
  intro i j hij
  apply hb
  apply add_left_cancel (a := (s,0,0))
  rw [← he i, ← he j, hij]

lemma columns_injective (d s : F) : Function.Injective (columns d s) := by
  have hb : Function.Injective (columns d (0 : F)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [columns, neg_one_ne_one, Ne.symm neg_one_ne_one] at hij ⊢
  have he (i : Fin 4) : columns d s i = columns d 0 i - (s,0,0) := by
    fin_cases i <;> simp [columns]
  intro i j hij
  apply hb
  have h := congrArg (fun x : Point F => x+(s,0,0)) hij
  simpa only [he, sub_add_cancel] using h

omit [CharP F 3] in
lemma rows_nonzero (s : F) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsn : s ≠ -1) (i : Fin 4) :
    rows s i ≠ 0 := by
  fin_cases i <;> simp [rows, hs0, hs1, hsn, sub_eq_zero, add_eq_zero_iff_eq_neg]

omit [CharP F 3] in
lemma columns_nonzero (d s : F) (i : Fin 4) : columns d s i ≠ 0 := by
  fin_cases i <;> simp [columns]

/-- The copy avoids zero message points and zero coordinate points. -/
def parameterCopy (d a k l s : F) (ha : a ≠ 0) (hl : l ≠ 0)
    (h : a^2*l*d = 1) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsn : s ≠ -1) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy
      (Erdos714AffineSlices.graph (restrictedCode d a k)) := by
  let L : Fin 4 ↪ NonzeroPoint F := ⟨fun i =>
      ⟨(a*l) • rows s i, smul_ne_zero (mul_ne_zero ha hl) (rows_nonzero s hs0 hs1 hsn i)⟩,
    fun i j he => rows_injective s
      ((smul_right_injective (Point F) (mul_ne_zero ha hl)) (congrArg Subtype.val he))⟩
  let T : Fin 4 ↪ NonzeroPoint F := ⟨fun j =>
      ⟨l • columns d s j, smul_ne_zero hl (columns_nonzero d s j)⟩,
    fun i j he => columns_injective d s
      ((smul_right_injective (Point F) hl) (congrArg Subtype.val he))⟩
  let R : Fin 4 ↪ NonzeroPoint F × F := ⟨fun j =>
      (T j, k+a*l^2+if j=3 then a^3*l^3*d^3 else 0),
    fun i j he => T.injective (congrArg Prod.fst he)⟩
  refine ⟨⟨L.sumMap R, ?_⟩, (L.sumMap R).injective⟩
  rintro (i | i) (j | j) he
  · simp at he
  · exact code_table d a k l s h i j
  · exact code_table d a k l s h j i
  · simp at he

/-- The same obstruction works for every nonzero parameter, not just a specially
chosen irreducible presentation. -/
theorem fixed_weight_not_free [Fintype F] (hq : 4 ≤ Fintype.card F)
    (d a k : F) (hd0 : d ≠ 0) (ha : a ≠ 0) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714AffineSlices.graph (restrictedCode d a k)) := by
  classical
  have hex : ∃ s : F, s ≠ 0 ∧ s ≠ 1 ∧ s ≠ -1 := by
    by_contra! h
    have he : (Finset.univ : Finset F) ⊆ {0,1,-1} := by
      intro s _
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hs0 : s = 0
      · exact Or.inl hs0
      by_cases hs1 : s = 1
      · exact Or.inr (Or.inl hs1)
      exact Or.inr (Or.inr (h s hs0 hs1))
    have hc := Finset.card_le_card he
    have hb : ({0,1,-1} : Finset F).card ≤ 3 := by
      exact (Finset.card_insert_le _ _).trans (by
        have h := Finset.card_insert_le (1 : F) {-1}
        simp only [Finset.card_singleton] at h
        omega)
    rw [Finset.card_univ] at hc
    omega
  obtain ⟨s,hs0,hs1,hsn⟩ := hex
  let l := (a^2*d)⁻¹
  have hl : l ≠ 0 := inv_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) hd0)
  have he : a^2*l*d = 1 := by
    dsimp [l]
    field_simp
  exact fun hf => hf ⟨parameterCopy d a k l s ha hl he hs0 hs1 hsn⟩

/-- In particular one can require the cubic defining the norm to be irreducible. -/
theorem finite_fixed_weight_obstruction [Fintype F] (hq : 4 ≤ Fintype.card F)
    (a k : F) (ha : a ≠ 0) :
    ∃ d : F, Irreducible (X^3-X-C d : F[X]) ∧
      ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
        (Erdos714AffineSlices.graph (restrictedCode d a k)) := by
  obtain ⟨d, hd⟩ := Erdos714CharThreeNorm.exists_outside_artinSchreier (F := F)
  have hd0 : d ≠ 0 := by intro h; exact hd 0 (by simp [h])
  refine ⟨d, ?_, fixed_weight_not_free hq d a k hd0 ha⟩
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : (X^3-X-C d : F[X]).natDegree = 3 := by compute_degree!
    rw [hdeg]
    decide
  · intro x hx
    exact hd x (by simpa only [Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_C,
      sub_eq_zero] using hx)

/-- A fixed weight embeds into any larger selection of weights, with arbitrary offsets. -/
def fixedWeightCopy {A : Type*} (d : F) (w k : A → F) (a : A) :
    (Erdos714AffineSlices.graph (restrictedCode d (w a) (k a))).Copy
      (Erdos714AffineSlices.graph (fun (p : A × NonzeroPoint F) (t : NonzeroPoint F) =>
        restrictedCode d (w p.1) (k p.1) p.2 t)) where
  toHom := {
    toFun := Sum.map (fun x => (a,x)) id
    map_rel' := by
      rintro (x | x) (y | y) h <;> exact h }
  injective' := Sum.map_injective.mpr ⟨fun _ _ h => congrArg Prod.snd h, Function.injective_id⟩

/-- Even an arbitrary weight selection fails as soon as it retains one nonzero weight.
The only point/coordinate deletions covered here are deletion of zero. -/
theorem weight_selection_not_free {A : Type*} [Fintype F]
    (hq : 4 ≤ Fintype.card F) (d : F) (hd : d ≠ 0) (w k : A → F)
    (a : A) (ha : w a ≠ 0) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714AffineSlices.graph (fun (p : A × NonzeroPoint F) (t : NonzeroPoint F) =>
        restrictedCode d (w p.1) (k p.1) p.2 t)) := by
  intro hf
  apply fixed_weight_not_free hq d (w a) (k a) hd ha
  rintro ⟨f⟩
  exact hf ⟨(fixedWeightCopy d w k a).comp f⟩

#print axioms traceProduct_eq_trace
#print axioms code_table
#print axioms parameterCopy
#print axioms fixed_weight_not_free
#print axioms finite_fixed_weight_obstruction
#print axioms weight_selection_not_free

end Erdos714CubicTraceShear
