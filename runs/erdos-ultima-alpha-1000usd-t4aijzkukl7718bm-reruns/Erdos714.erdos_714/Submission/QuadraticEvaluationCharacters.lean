import Submission.QuadraticEvaluationGluing

/-!
An odd-characteristic quadratic-evaluation certificate survives two nonzero
square edge filters and five coefficient guards. The certificate lifts from
F83 to every characteristic-83 field admitting the displayed quadratic power
basis. This is a construction obstruction, not a disproof of Erdős714.
-/
noncomputable section
open Classical SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714QuadraticEvaluationCharacters
open Erdos714QuadraticEvaluation (Coeff Vertex eval realPart imagPart relation normGraph)
variable {F K E : Type*} [Field F] [Field K] [Field E]

def valid (p : Coeff F) : Prop :=
  p.1 ≠ 0 ∧ p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧ p.1+p.2.1 ≠ 0 ∧ p.1-p.2.1 ≠ 0

def support (x : F) : Prop := x ≠ 0 ∧ IsSquare x

def score (δ : F) (x y : Vertex F) : F := eval x.2 y.1+δ*(x.2.1+y.2.1)

def allowed (δ : F) (x y : Vertex F) : Prop :=
  valid x.2 ∧ valid y.2 ∧ support (score δ x y) ∧ support (score δ y x)

variable [Algebra F E]

def graph (δ : F) (θ : E) : SimpleGraph (Vertex F ⊕ Vertex F) where
  Adj x y := (normGraph θ).Adj x y ∧ match x,y with
    | .inl x,.inr y | .inr y,.inl x => allowed δ x y
    | _,_ => False
  symm := by intro x y h; cases x <;> cases y <;> exact ⟨h.1.symm,h.2⟩
  loopless := by intro x h; exact (normGraph θ).loopless x h.1

def vertexMap (f : F →+* K) (x : Vertex F) : Vertex K :=
  (f x.1,f x.2.1,f x.2.2.1,f x.2.2.2)

lemma vertexMap_injective (f : F →+* K) : Function.Injective (vertexMap f) := by
  intro x y h
  have hs := f.injective (congrArg Prod.fst h)
  have ha := f.injective (congrArg (fun v : Vertex K => v.2.1) h)
  have hb := f.injective (congrArg (fun v : Vertex K => v.2.2.1) h)
  have hc := f.injective (congrArg (fun v : Vertex K => v.2.2.2) h)
  exact Prod.ext hs (Prod.ext ha (Prod.ext hb hc))

lemma valid_map (f : F →+* K) (x : Vertex F) (h : valid x.2) :
    valid (vertexMap f x).2 := by
  simpa only [valid,vertexMap,←map_add,←map_sub,map_ne_zero] using h

lemma support_map (f : F →+* K) (x : F) (h : support x) : support (f x) :=
  ⟨(map_ne_zero f).mpr h.1,h.2.map f⟩

lemma eval_map (f : F →+* K) (x y : Vertex F) :
    eval (vertexMap f x).2 (vertexMap f y).1=f (eval x.2 y.1) := by
  simp [vertexMap,eval]

lemma score_map (f : F →+* K) (δ : F) (x y : Vertex F) :
    score (f δ) (vertexMap f x) (vertexMap f y)=f (score δ x y) := by
  simp [score,eval,vertexMap]

lemma allowed_map (f : F →+* K) (δ : F) (x y : Vertex F) (h : allowed δ x y) :
    allowed (f δ) (vertexMap f x) (vertexMap f y) := by
  refine ⟨valid_map f x h.1,valid_map f y h.2.1,?_,?_⟩
  · rw [score_map]; exact support_map f _ h.2.2.1
  · rw [score_map]; exact support_map f _ h.2.2.2

lemma relation_map (f : F →+* K) (δ : F) (x y : Vertex F) (h : relation δ x y) :
    relation (f δ) (vertexMap f x) (vertexMap f y) := by
  rcases h with ⟨ha,hA,hα,hβ,he⟩
  refine ⟨(map_ne_zero f).mpr ha,(map_ne_zero f).mpr hA,?_,?_,?_⟩
  · rw [eval_map]; exact (map_ne_zero f).mpr hα
  · rw [eval_map]; exact (map_ne_zero f).mpr hβ
  · have hh := congrArg f he
    simpa only [vertexMap,Erdos714QuadraticEvaluation.realPart,imagPart,eval,map_add,map_mul,map_sub,map_pow,map_ofNat] using hh

abbrev Base := ZMod 83
instance : Fact (Nat.Prime 83) := ⟨by decide⟩

def rows : Fin 4 → Vertex Base :=
  ![(82,39,78,12),(82,17,34,56),(82,34,68,80),(82,5,10,65)]
def columns : Fin 4 → Vertex Base :=
  ![(55,36,46,72),(55,31,53,74),(26,36,15,41),(26,31,71,9)]
def rowRoots : Fin 4 → Fin 4 → Base :=
  ![![21,23,21,23],![26,10,26,10],![32,38,32,38],![26,10,26,10]]
def columnRoots : Fin 4 → Fin 4 → Base :=
  ![![30,27,30,27],![3,2,3,2],![18,30,18,30],![41,4,41,4]]

lemma rows_injective : Function.Injective rows := by decide +kernel
lemma columns_injective : Function.Injective columns := by decide +kernel

/-- Both square predicates are checked with explicit witnesses. -/
lemma allowed_edges (i j : Fin 4) : allowed (-1) (rows i) (columns j) := by
  have hrow : valid (rows i).2 := by fin_cases i <;> norm_num [Base,valid,rows] <;> decide +kernel
  have hcol : valid (columns j).2 := by fin_cases j <;> norm_num [Base,valid,columns] <;> decide +kernel
  refine ⟨hrow,hcol,?_,?_⟩
  · refine ⟨?_,(isSquare_iff_exists_sq _).mpr ⟨rowRoots i j,?_⟩⟩
    · fin_cases i <;> fin_cases j <;> norm_num [Base,score,eval,rows,columns] <;> decide +kernel
    · fin_cases i <;> fin_cases j <;> norm_num [Base,score,eval,rows,columns,rowRoots] <;> decide +kernel
  · refine ⟨?_,(isSquare_iff_exists_sq _).mpr ⟨columnRoots i j,?_⟩⟩
    · fin_cases i <;> fin_cases j <;> norm_num [Base,score,eval,rows,columns] <;> decide +kernel
    · fin_cases i <;> fin_cases j <;> norm_num [Base,score,eval,rows,columns,columnRoots] <;> decide +kernel

lemma coordinate_edges (i j : Fin 4) : relation (-1) (rows i) (columns j) := by
  fin_cases i <;> fin_cases j <;> norm_num [Base,relation,eval,Erdos714QuadraticEvaluation.realPart,imagPart,rows,columns] <;> decide +kernel

variable [CharP F 83]

/-- The copy survives arbitrary field extensions, with the actual quadratic norm. -/
def parameterCopy (θ : E) (hθ : θ^2=algebraMap F E (-1))
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ)) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy (graph (-1 : F) θ) := by
  let f : Base →+* F := ZMod.castHom (dvd_refl 83) F
  let L : Fin 4 ↪ Vertex F := ⟨fun i => vertexMap f (rows i),(vertexMap_injective f).comp rows_injective⟩
  let R : Fin 4 ↪ Vertex F := ⟨fun i => vertexMap f (columns i),(vertexMap_injective f).comp columns_injective⟩
  have hedge (i j : Fin 4) : (graph (-1 : F) θ).Adj (.inl (L i)) (.inr (R j)) := by
    constructor
    · rw [Erdos714QuadraticEvaluation.normGraph_eq (-1) θ hθ B hB]
      change relation (-1) (vertexMap f (rows i)) (vertexMap f (columns j))
      simpa only [map_neg,map_one] using relation_map f (-1) (rows i) (columns j) (coordinate_edges i j)
    · exact (by simpa only [map_neg,map_one] using allowed_map f (-1) (rows i) (columns j) (allowed_edges i j))
  refine ⟨⟨L.sumMap R,?_⟩,(L.sumMap R).injective⟩
  intro x y hxy
  cases x with
  | inl i => cases y with
    | inl j => simp at hxy
    | inr j => exact hedge i j
  | inr i => cases y with
    | inr j => simp at hxy
    | inl j => exact (hedge j i).symm

theorem not_free (θ : E) (hθ : θ^2=algebraMap F E (-1))
    (B : Module.Basis (Fin 2) F E) (hB : ∀ i, B i=θ^(i : ℕ)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (-1 : F) θ) :=
  fun hf => hf ⟨parameterCopy θ hθ B hB⟩

/-- The parameter is genuinely nonsquare in the certificate field. -/
lemma minus_one_not_square : ¬ IsSquare (-1 : Base) := by decide +kernel

instance : Fact (∀ r : Base, r^2 ≠ (-1 : Base)+0*r) := by
  refine ⟨?_⟩
  intro r hr
  apply minus_one_not_square
  exact (isSquare_iff_exists_sq _).mpr ⟨r,by simpa using hr.symm⟩

abbrev Extension := QuadraticAlgebra Base (-1) 0

def imaginaryUnit : Extension := ⟨0,1⟩

lemma imaginaryUnit_sq : imaginaryUnit^2=algebraMap Base Extension (-1) := by
  ext <;> simp [imaginaryUnit,pow_two] <;> rfl

lemma basis_powers (i : Fin 2) :
    (QuadraticAlgebra.basis (-1 : Base) 0) i=imaginaryUnit^(i : ℕ) := by
  apply (QuadraticAlgebra.basis (-1 : Base) 0).repr.injective
  ext j
  fin_cases i <;> fin_cases j <;> simp [QuadraticAlgebra.basis_repr_apply,imaginaryUnit] <;> rfl

/-- An unconditional specialization with a constructed quadratic extension. -/
theorem concrete_not_free :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (-1 : Base) imaginaryUnit) :=
  not_free imaginaryUnit imaginaryUnit_sq (QuadraticAlgebra.basis (-1 : Base) 0) basis_powers

#print axioms allowed_edges
#print axioms coordinate_edges
#print axioms relation_map
#print axioms parameterCopy
#print axioms not_free
#print axioms concrete_not_free
end Erdos714QuadraticEvaluationCharacters
