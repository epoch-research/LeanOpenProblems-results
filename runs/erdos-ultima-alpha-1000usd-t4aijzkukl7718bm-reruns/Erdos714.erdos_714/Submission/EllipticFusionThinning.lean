import Submission.EllipticClassFusion
import Submission.MultiOrbitAveraging
import Submission.UpperBounds
import Submission.Packing

/-!
An arbitrary-edge-thinning obstruction for sparse elliptic trace--determinant
fusions. All counting is on actual matrix vertices and undirected edges.
This file does not resolve Erdős Problem 714.
-/

noncomputable section
open Finset SimpleGraph Classical
set_option maxHeartbeats 2000000

namespace Erdos714EllipticThinning
open Erdos714EllipticFusion
variable {F : Type*} [Field F] [Fintype F]
abbrev MatGroup := Matrix.GeneralLinearGroup (Fin 2) F

omit [Fintype F] in
lemma invariants_conjugate (q g : MatGroup (F := F)) :
    invariants (q*g*q⁻¹) = invariants g := by
  apply Prod.ext
  · change Matrix.det (↑(q*g*q⁻¹) : Matrix (Fin 2) (Fin 2) F) = _
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul]
    have hi : (q : Matrix (Fin 2) (Fin 2) F).det *
        (↑q⁻¹ : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [← Matrix.det_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel]
      simp
    change _ = (g : Matrix (Fin 2) (Fin 2) F).det
    calc
      _ = (q : Matrix (Fin 2) (Fin 2) F).det * (↑q⁻¹ : Matrix (Fin 2) (Fin 2) F).det *
        (g : Matrix (Fin 2) (Fin 2) F).det := by ring
      _ = _ := by rw [hi, one_mul]
  · change Matrix.trace (↑(q*g*q⁻¹) : Matrix (Fin 2) (Fin 2) F) = _
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    rw [Matrix.trace_mul_cycle, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel]
    simp [invariants]

/-- Independent left and right translations preserve each class, not merely their union. -/
def transform (S : Finset (F × F)) (p q : MatGroup (F := F)) : graph S ≃g graph S where
  toEquiv := Equiv.sumCongr ((Equiv.mulLeft p).trans (Equiv.mulRight q⁻¹))
    ((Equiv.mulLeft p).trans (Equiv.mulRight q⁻¹))
  map_rel_iff' := by
    intro x y
    have he (g h : MatGroup (F := F)) :
        invariants ((p*g*q⁻¹)⁻¹*(p*h*q⁻¹)) = invariants (g⁻¹*h) := by
      have hh : (p*g*q⁻¹)⁻¹*(p*h*q⁻¹) = q*(g⁻¹*h)*q⁻¹ := by group
      rw [hh, invariants_conjugate]
    cases x <;> cases y <;> dsimp [graph] <;> first | rfl | rw [he]

def transforms (S : Finset (F × F)) :
    (MatGroup (F := F) × MatGroup (F := F)) →* (graph S ≃g graph S) where
  toFun a := transform S a.1 a.2
  map_one' := by
    apply RelIso.ext
    intro x
    cases x <;> simp [transform]
  map_mul' a b := by
    apply RelIso.ext
    intro x
    cases x <;> simp [transform, mul_assoc]

def edgeAction (S : Finset (F × F)) :
    (MatGroup (F := F) × MatGroup (F := F)) →* Equiv.Perm (graph S).edgeSet :=
  (Erdos714GraphAveraging.edgeAction (graph S)).comp (transforms S)

/-- A cyclic basis exists for every elliptic two-by-two matrix. -/
def cyclicBasis (g : MatGroup (F := F)) (hg : Elliptic (invariants g)) : MatGroup (F := F) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0,g 0 1;1,g 1 1] (by
    simpa [Matrix.det_fin_two] using offDiagonal_ne_zero g hg)

def companion (c : F × F) (hc : c.1 ≠ 0) : MatGroup (F := F) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0,-c.1;1,c.2] (by
    simpa [Matrix.det_fin_two] using hc)

omit [Fintype F] in
lemma cyclic_identity (g : MatGroup (F := F)) (hg : Elliptic (invariants g)) :
    g * cyclicBasis g hg = cyclicBasis g hg * companion (invariants g) hg.1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change ((g : Matrix (Fin 2) (Fin 2) F) * !![0,g 0 1;1,g 1 1]) i j =
    (!![0,g 0 1;1,g 1 1] * !![0,-(invariants g).1;1,(invariants g).2]) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, invariants, Matrix.det_fin_two,
      Matrix.trace, Matrix.diag] <;> ring

omit [Fintype F] in
lemma elliptic_conjugate (g h : MatGroup (F := F)) (hg : Elliptic (invariants g))
    (hh : Elliptic (invariants h)) (he : invariants g = invariants h) :
    ∃ q : MatGroup (F := F), q*g*q⁻¹ = h := by
  have eg : g = cyclicBasis g hg * companion (invariants g) hg.1 * (cyclicBasis g hg)⁻¹ :=
    (eq_mul_inv_iff_mul_eq).mpr (cyclic_identity g hg)
  have eh : h = cyclicBasis h hh * companion (invariants h) hh.1 * (cyclicBasis h hh)⁻¹ :=
    (eq_mul_inv_iff_mul_eq).mpr (cyclic_identity h hh)
  refine ⟨cyclicBasis h hh * (cyclicBasis g hg)⁻¹, ?_⟩
  conv_lhs => arg 1; arg 2; rw [eg]
  conv_rhs => rw [eh]
  have ec : companion (invariants g) hg.1 = companion (invariants h) hh.1 := by
    simp only [he]
  rw [ec]
  group

/-- A unique orientation and a unique relative matrix for every undirected host edge. -/
def edgeEquiv (S : Finset (F × F)) :
    (MatGroup (F := F) × Connection S) ≃ (graph S).edgeSet :=
  Equiv.ofBijective (fun p => ⟨s(Sum.inl p.1, Sum.inr (p.1*p.2.val)), by
    change invariants (p.1⁻¹*(p.1*p.2.val)) ∈ S
    simpa only [inv_mul_cancel_left] using p.2.property⟩) (by
      constructor
      · rintro ⟨g,s⟩ ⟨h,t⟩ he
        have he' := congrArg Subtype.val he
        simp only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
          Sum.inr_ne_inl, and_false, or_false] at he'
        apply Prod.ext he'.1
        apply Subtype.ext
        exact mul_left_cancel (he'.1 ▸ he'.2)
      · rintro ⟨e,he⟩
        induction e using Sym2.ind with
        | _ x y =>
          cases x with
          | inl g =>
            cases y with
            | inl h => exact False.elim he
            | inr h =>
              refine ⟨(g,⟨g⁻¹*h,he⟩), Subtype.ext ?_⟩
              simp
          | inr h =>
            cases y with
            | inr g => exact False.elim he
            | inl g =>
              refine ⟨(g,⟨g⁻¹*h,he⟩), Subtype.ext ?_⟩
              simp [Sym2.eq_swap])

def color (S : Finset (F × F)) (e : (graph S).edgeSet) : S :=
  ⟨invariants ((edgeEquiv S).symm e).2.val, ((edgeEquiv S).symm e).2.property⟩

omit [Fintype F] in
@[simp] lemma color_edge (S : Finset (F × F)) (g : MatGroup (F := F)) (s : Connection S) :
    color S (edgeEquiv S (g,s)) = ⟨invariants s.val,s.property⟩ := by
  simp [color]

omit [Fintype F] in
lemma action_edge (S : Finset (F × F)) (p q g : MatGroup (F := F)) (s : Connection S) :
    edgeAction S (p,q) (edgeEquiv S (g,s)) =
      edgeEquiv S (p*g*q⁻¹, ⟨q*s.val*q⁻¹, by
        rw [invariants_conjugate]; exact s.property⟩) := by
  apply Subtype.ext
  change s(Sum.inl (p*g*q⁻¹), Sum.inr (p*(g*s.val)*q⁻¹)) =
    s(Sum.inl (p*g*q⁻¹), Sum.inr (p*g*q⁻¹*(q*s.val*q⁻¹)))
  congr 2
  group

lemma color_preserved (S : Finset (F × F)) (a : MatGroup (F := F) × MatGroup (F := F))
    (e : (graph S).edgeSet) : color S (edgeAction S a e) = color S e := by
  obtain ⟨⟨g,s⟩,rfl⟩ := (edgeEquiv S).surjective e
  rcases a with ⟨p,q⟩
  rw [action_edge, color_edge, color_edge]
  exact Subtype.ext (invariants_conjugate q s.val)

lemma transitive_on_color (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (e f : (graph S).edgeSet) (he : color S e = color S f) :
    ∃ a, edgeAction S a e = f := by
  obtain ⟨⟨g,s⟩,rfl⟩ := (edgeEquiv S).surjective e
  obtain ⟨⟨h,t⟩,rfl⟩ := (edgeEquiv S).surjective f
  have he' : invariants s.val = invariants t.val := by
    simpa only [color_edge] using congrArg Subtype.val he
  obtain ⟨q,hq⟩ := elliptic_conjugate s.val t.val (hS _ s.property) (hS _ t.property) he'
  refine ⟨(h*q*g⁻¹,q), ?_⟩
  rw [action_edge]
  apply congrArg (edgeEquiv S)
  apply Prod.ext
  · group
  · exact Subtype.ext hq

/-- All color classes of actual edges have the same cardinality. -/
lemma color_card (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c) (c : S) :
    (univ.filter (fun e : (graph S).edgeSet => color S e = c)).card =
      Fintype.card (MatGroup (F := F)) * Fintype.card F * (Fintype.card F - 1) := by
  let ec : (MatGroup (F := F) × (S × (F × Fˣ))) ≃ (graph S).edgeSet :=
    (Equiv.prodCongr (Equiv.refl _) (connectionEquiv S hS).symm).trans (edgeEquiv S)
  have hcolor (p : MatGroup (F := F) × (S × (F × Fˣ))) : color S (ec p) = p.2.1 := by
    apply Subtype.ext
    simp [ec, color, connectionEquiv, classMatrix_invariants]
  let ef : (MatGroup (F := F) × (F × Fˣ)) ≃ {e : (graph S).edgeSet // color S e = c} :=
    Equiv.ofBijective (fun p => ⟨ec (p.1,(c,p.2)),hcolor _⟩) (by
      constructor
      · intro p q hpq
        have he := ec.injective (congrArg Subtype.val hpq)
        apply Prod.ext
        · exact congrArg (fun a : MatGroup (F := F) × (S × (F × Fˣ)) => a.1) he
        · exact congrArg (fun a : MatGroup (F := F) × (S × (F × Fˣ)) => a.2.2) he
      · rintro ⟨e,he⟩
        obtain ⟨⟨g,d,v⟩,rfl⟩ := ec.surjective e
        have hd : d = c := (hcolor _).symm.trans he
        subst d
        exact ⟨(g,v),rfl⟩)
  rw [← Fintype.card_subtype, ← Fintype.card_congr ef]
  simp [Fintype.card_prod, Fintype.card_units, mul_assoc]


/-- Parameterization of the edges of a complete bipartite graph. -/
def bipartiteEdgeEquiv (X Y : Type*) :
    (X × Y) ≃ (completeBipartiteGraph X Y).edgeSet :=
  Equiv.ofBijective (fun p => ⟨s(Sum.inl p.1, Sum.inr p.2),by simp⟩) (by
    constructor
    · rintro ⟨x,y⟩ ⟨x',y'⟩ h
      have hh := congrArg Subtype.val h
      simp only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
        Sum.inl_ne_inr, Sum.inr_ne_inl, and_false, or_false] at hh
      exact Prod.ext hh.1 hh.2
    · rintro ⟨e,he⟩
      induction e using Sym2.ind with
      | _ x y =>
        cases x <;> cases y
        · simp at he
        · exact ⟨(_, _),rfl⟩
        · exact ⟨(_, _),Subtype.ext (Sym2.eq_swap ..)⟩
        · simp at he)

abbrev Rows (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c) (k : Ratio (F := F)) :=
  {p : Parameter S // ratioMap S hS p = k}

def gridEmbedding (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c) (k : Ratio (F := F)) :
    (Rows S hS k × Fˣ) ↪ (graph S).edgeSet :=
  (bipartiteEdgeEquiv (Rows S hS k) Fˣ).toEmbedding.trans (fiberCopy S hS k).mapEdgeSet

def block (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c) (k : Ratio (F := F)) :
    Finset (graph S).edgeSet := univ.map (gridEmbedding S hS k)

lemma block_eq (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c) (k : Ratio (F := F)) :
    block S hS k = univ.map (fiberCopy S hS k).mapEdgeSet := by
  rw [block, gridEmbedding, ← Finset.map_map]
  congr 1
  exact Finset.univ_map_equiv_to_embedding _

omit [Fintype F] in
lemma color_grid (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (k : Ratio (F := F)) (p : Rows S hS k × Fˣ) :
    color S (gridEmbedding S hS k p) = p.1.val.1 := by
  have hm : invariants ((fiberRow S hS k p.1)⁻¹ * column k p.2) ∈ S := by
    rw [fiber_invariants]; exact p.1.val.1.property
  have he : gridEmbedding S hS k p =
      edgeEquiv S (fiberRow S hS k p.1, ⟨(fiberRow S hS k p.1)⁻¹ * column k p.2,hm⟩) := by
    apply Subtype.ext
    change s(Sum.inl (fiberRow S hS k p.1), Sum.inr (column k p.2)) =
      s(Sum.inl (fiberRow S hS k p.1),
        Sum.inr (fiberRow S hS k p.1 * ((fiberRow S hS k p.1)⁻¹ * column k p.2)))
    simp
  rw [he, color_edge]
  exact Subtype.ext (fiber_invariants S hS k p.1 p.2)

lemma block_color_sum (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (k : Ratio (F := F)) (c : S) :
    ((block S hS k).filter (fun e => color S e = c)).card =
      ∑ p : Rows S hS k, if p.val.1 = c then Fintype.card F - 1 else 0 := by
  rw [Finset.card_filter]
  simp only [block, sum_map, color_grid, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro p _
  by_cases hp : p.val.1 = c <;> simp [hp, Fintype.card_units]

/-- Trace-zero classes can contribute q-1 parameters. The q-2 lower bound,
    unlike an asserted uniform exact formula, is valid in all characteristics. -/
lemma block_meeting_lower (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c) (c : S) :
    (Fintype.card F - 2) * (Fintype.card F - 1) ≤
      ∑ k : Ratio (F := F), ((block S hS k).filter (fun e => color S e = c)).card := by
  have hs : (∑ k : Ratio (F := F),
      ∑ p : Rows S hS k, if p.val.1 = c then Fintype.card F - 1 else 0) =
      ∑ p : Parameter S, if p.1 = c then Fintype.card F - 1 else 0 := by
    rw [← Fintype.sum_sigma (fun p : Σ k, Rows S hS k =>
      if p.2.val.1 = c then Fintype.card F - 1 else 0)]
    exact (Equiv.sigmaFiberEquiv (ratioMap S hS)).sum_comp
      (fun p : Parameter S => if p.1 = c then Fintype.card F - 1 else 0)
  simp_rw [block_color_sum]
  rw [hs]
  change _ ≤ ∑ p : (Σ d : S, {x : F // x ≠ 0 ∧ x ≠ d.val.2}),
    if p.1 = c then Fintype.card F - 1 else 0
  rw [Fintype.sum_sigma]
  rw [Fintype.sum_eq_single c (by intro d hd; simp [hd])]
  simpa using Nat.mul_le_mul_right (Fintype.card F - 1) (card_excluding c.val.2)

lemma rows_card_bound (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (k : Ratio (F := F)) : Fintype.card (Rows S hS k) ≤ 2 * S.card := by
  let tag : Rows S hS k → S := fun p => p.val.1
  have hf (c : S) : Fintype.card {p : Rows S hS k // tag p = c} ≤ 2 := by
    let P : Polynomial F := Polynomial.X^2 - Polynomial.C c.val.2 * Polynomial.X +
      Polynomial.C ((k : F)*c.val.1)
    have hp0 : P ≠ 0 := by
      intro hp
      have he := congrArg (fun f : Polynomial F => f.coeff 2) hp
      norm_num [P, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X] at he
    have hdeg : P.natDegree ≤ 2 := by dsimp [P]; compute_degree!
    let f : {p : Rows S hS k // tag p = c} → {x : F // x ∈ P.roots.toFinset} :=
      fun p => ⟨p.val.val.2.val, by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
        have he := congrArg Subtype.val p.val.property
        have ht : p.val.val.1 = c := p.property
        change p.val.val.2.val * (p.val.val.1.val.2 - p.val.val.2.val) /
          p.val.val.1.val.1 = (k : F) at he
        simp only [ht] at he
        have hd : c.val.1 ≠ 0 := (hS _ c.property).1
        have he' := (div_eq_iff hd).mp he
        simp only [Polynomial.IsRoot, P, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
        linear_combination -he'⟩
    have hinj : Function.Injective f := by
      intro p q hpq
      apply Subtype.ext
      apply Subtype.ext
      have hx : p.val.val.2.val = q.val.val.2.val := congrArg Subtype.val hpq
      have ht : p.val.val.1 = q.val.val.1 := p.property.trans q.property.symm
      rcases p with ⟨⟨⟨a,x⟩,ha⟩,hp⟩
      rcases q with ⟨⟨⟨b,y⟩,hb⟩,hq⟩
      change a = b at ht
      subst b
      change x.val = y.val at hx
      have hxy : x = y := Subtype.ext hx
      subst y
      rfl
    calc
      _ ≤ Fintype.card {x : F // x ∈ P.roots.toFinset} := Fintype.card_le_of_injective f hinj
      _ = P.roots.toFinset.card := Fintype.card_coe _
      _ ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' _
      _ ≤ 2 := hdeg
  calc
    _ = Fintype.card (Σ c : S, {p : Rows S hS k // tag p = c}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv tag)).symm
    _ = ∑ c : S, Fintype.card {p : Rows S hS k // tag p = c} := Fintype.card_sigma
    _ ≤ ∑ _c : S, 2 := sum_le_sum (fun c _ => hf c)
    _ = 2*S.card := by simp [mul_comm]


lemma biclique_nonisolated (v : Fin 4 ⊕ Fin 4) :
    ∃ w, (completeBipartiteGraph (Fin 4) (Fin 4)).Adj v w := by
  cases v with
  | inl x => exact ⟨.inr 0,by simp⟩
  | inr x => exact ⟨.inl 0,by simp⟩

/-- The local KST bound is applied to the selected edges of every translated
    block; no complete block is assumed to survive the thinning. -/
lemma selected_block_bound (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (H : SimpleGraph (MatGroup (F := F) ⊕ MatGroup (F := F)))
    (hH : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (k : Ratio (F := F)) (a : MatGroup (F := F) × MatGroup (F := F)) :
    ((univ.filter (fun e : (graph S).edgeSet => e.val ∈ H.edgeSet)).filter
      (fun e => e ∈ Erdos714Averaging.translate (edgeAction S) a (block S hS k))).card ≤
      extremalNumber (2*S.card + Fintype.card F) (completeBipartiteGraph (Fin 4) (Fin 4)) := by
  rw [block_eq]
  have hb := Erdos714GraphAveraging.block_bound (completeBipartiteGraph (Fin 4) (Fin 4))
    H (graph S) (completeBipartiteGraph (Rows S hS k) Fˣ) (fiberCopy S hS k) hH
    (transform S a.1 a.2)
  have hbsize : extremalNumber (Fintype.card (Rows S hS k ⊕ Fˣ))
      (completeBipartiteGraph (Fin 4) (Fin 4)) ≤
      extremalNumber (2*S.card + Fintype.card F) (completeBipartiteGraph (Fin 4) (Fin 4)) := by
    apply Erdos714Reduction.extremalNumber_monotone_of_no_isolated _ biclique_nonisolated
    rw [Fintype.card_sum, Fintype.card_units]
    have := rows_card_bound S hS k
    omega
  convert hb.trans hbsize using 1
  congr 1
  ext e
  simp [Erdos714Averaging.translate, edgeAction, transforms]

/-- An exact finite bound valid for every K44-free spanning subgraph. -/
theorem thinning_extremal_bound (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (hq : 2 < Fintype.card F)
    (H : SimpleGraph (MatGroup (F := F) ⊕ MatGroup (F := F))) (hHG : H ≤ graph S)
    (hH : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card ≤ Fintype.card (MatGroup (F := F)) * Fintype.card F *
      extremalNumber (2*S.card + Fintype.card F) (completeBipartiteGraph (Fin 4) (Fin 4)) := by
  have hb := Erdos714MultiOrbit.bound (edgeAction S) (color S) (color_preserved S)
    (transitive_on_color S hS)
    (Fintype.card (MatGroup (F := F)) * Fintype.card F * (Fintype.card F - 1))
    (fun c => by
      convert color_card S hS c using 1
      congr 1
      ext e
      simp) (block S hS)
    (univ.filter (fun e : (graph S).edgeSet => e.val ∈ H.edgeSet))
    ((Fintype.card F - 2) * (Fintype.card F - 1))
    (fun _ => extremalNumber (2*S.card + Fintype.card F) (completeBipartiteGraph (Fin 4) (Fin 4)))
    (fun c => by
      convert block_meeting_lower S hS c using 1
      apply sum_congr rfl
      intro k _
      congr 1
      ext e
      simp) (fun k a => by
        convert selected_block_bound S hS H hH k a using 1)
  simp only [Erdos714GraphAveraging.selected_edge_card H (graph S) hHG,
    sum_const, card_univ, smul_eq_mul, ratio_card] at hb
  apply Nat.le_of_mul_le_mul_left (c := (Fintype.card F - 2) * (Fintype.card F - 1)) _
    (Nat.mul_pos (by omega) (by omega))
  convert hb using 1
  ring

/-- A convenient integral consequence of the previously proved KST theorem. -/
lemma extremal_fourth_power (n : ℕ) :
    (extremalNumber n (completeBipartiteGraph (Fin 4) (Fin 4)))^4 ≤ 81*n^7 := by
  have hne : completeBipartiteGraph (Fin 4) (Fin 4) ≠ ⊥ := by
    intro he
    have ha : (completeBipartiteGraph (Fin 4) (Fin 4)).Adj (.inl 0) (.inr 0) := by simp
    simp [he] at ha
  obtain ⟨G,_,hG⟩ := exists_isExtremal_free (V := Fin n) hne
  obtain ⟨hfree,he⟩ := isExtremal_free_iff.mp hG
  simp only [Fintype.card_fin] at he
  rw [← he]
  have hp := Erdos714Upper.edge_power_bound (by decide : 1 ≤ 4) G hfree
  norm_num only [Fintype.card_fin] at hp
  by_cases hn : G.edgeFinset.card ≤ 3*n
  · have hn' : n^4 ≤ n^7 := by
      by_cases hzero : n = 0
      · simp [hzero]
      · exact pow_le_pow_right' (Nat.one_le_iff_ne_zero.mpr hzero) (by decide)
    calc
      _ ≤ (3*n)^4 := Nat.pow_le_pow_left hn 4
      _ = 81*n^4 := by ring
      _ ≤ 81*n^7 := Nat.mul_le_mul_left _ hn'
  · have he' : G.edgeFinset.card ≤ 2*G.edgeFinset.card - 3*n := by omega
    exact (Nat.pow_le_pow_left he' 4).trans (hp.trans (by omega))

/-- For O(q) accepted classes this is O(q^27), strictly below the fourth
    power q^28 of the desired edge scale. -/
theorem thinning_fourth_power (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (hq : 2 < Fintype.card F)
    (H : SimpleGraph (MatGroup (F := F) ⊕ MatGroup (F := F))) (hHG : H ≤ graph S)
    (hH : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 81 * Fintype.card F^20 * (2*S.card + Fintype.card F)^7 := by
  have hb := thinning_extremal_bound S hS hq H hHG hH
  have hc := matrix_card_bound (F := F)
  calc
    _ ≤ (Fintype.card (MatGroup (F := F)) * Fintype.card F *
        extremalNumber (2*S.card + Fintype.card F) (completeBipartiteGraph (Fin 4) (Fin 4)))^4 :=
      Nat.pow_le_pow_left hb 4
    _ = Fintype.card (MatGroup (F := F))^4 * Fintype.card F^4 *
        (extremalNumber (2*S.card + Fintype.card F) (completeBipartiteGraph (Fin 4) (Fin 4)))^4 := by ring
    _ ≤ (Fintype.card F^4)^4 * Fintype.card F^4 *
        (81*(2*S.card + Fintype.card F)^7) := by
      gcongr
      exact extremal_fourth_power _
    _ = _ := by ring

/-- Uniformly bounded class-density and a positive critical edge constant
    force the field size to be bounded, even for arbitrary edge thinnings. -/
theorem critical_size_bound (S : Finset (F × F)) (hS : ∀ c ∈ S, Elliptic c)
    (hq : 2 < Fintype.card F)
    (H : SimpleGraph (MatGroup (F := F) ⊕ MatGroup (F := F))) (hHG : H ≤ graph S)
    (hH : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (C D : ℕ) (hclasses : S.card ≤ C*Fintype.card F)
    (hedges : Fintype.card F^7 ≤ D*H.edgeFinset.card) :
    Fintype.card F ≤ 81 * D^4 * (2*C+1)^7 := by
  have hb := thinning_fourth_power S hS hq H hHG hH
  have hsize : 2*S.card + Fintype.card F ≤ (2*C+1)*Fintype.card F := by nlinarith
  have hh : Fintype.card F^27 * Fintype.card F ≤
      Fintype.card F^27 * (81*D^4*(2*C+1)^7) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (D*H.edgeFinset.card)^4 := Nat.pow_le_pow_left hedges 4
      _ = D^4*H.edgeFinset.card^4 := by ring
      _ ≤ D^4*(81*Fintype.card F^20*(2*S.card+Fintype.card F)^7) := Nat.mul_le_mul_left _ hb
      _ ≤ D^4*(81*Fintype.card F^20*((2*C+1)*Fintype.card F)^7) := by gcongr
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (pow_pos (by omega) 27)

#print axioms transitive_on_color
#print axioms color_card
#print axioms block_meeting_lower
#print axioms rows_card_bound
#print axioms thinning_extremal_bound
#print axioms thinning_fourth_power
#print axioms critical_size_bound

end Erdos714EllipticThinning
