import Submission.LinearBlockThinning
import Submission.TensorObstruction

/-!
A coordinate-independent version of the complementary-block obstruction.
Projectively injective point families in six coordinates, with at most q^4
points on either side, admit no critical-density K44-free orthogonality
thinning. Arbitrary maps with large projective fibers are NOT covered.
-/
noncomputable section
open Classical Finset SimpleGraph Module
set_option maxHeartbeats 4000000
namespace Erdos714RankSix
open Erdos714LinearBlocks
variable {F : Type*} [Field F]
abbrev V (F : Type*) := Fin 6 → F
abbrev U (F : Type*) := Fin 3 → F
abbrev Perm := Equiv.Perm (Fin 6)

def first (p : Perm) (v : V F) : U F := fun i => v (p (Fin.castAdd 3 i))
def second (p : Perm) (v : V F) : U F := fun i => v (p (Fin.natAdd 3 i))
def split (p : Perm) (v : V F) : U F × U F := (first p v,second p v)

lemma split_smul (p : Perm) (a : F) (v : V F) : split p (a • v)=a • split p v := rfl

omit [Field F] in
lemma split_injective (p : Perm) : Function.Injective (split (F := F) p) := by
  intro v w h
  funext i
  obtain ⟨j,rfl⟩ := p.surjective i
  fin_cases j
  all_goals first
    | exact congrFun (congrArg Prod.fst h) 0
    | exact congrFun (congrArg Prod.fst h) 1
    | exact congrFun (congrArg Prod.fst h) 2
    | exact congrFun (congrArg Prod.snd h) 0
    | exact congrFun (congrArg Prod.snd h) 1
    | exact congrFun (congrArg Prod.snd h) 2

lemma dot_split (p : Perm) (v w : V F) :
    v ⬝ᵥ w = first p v ⬝ᵥ first p w + second p v ⬝ᵥ second p w := by
  unfold dotProduct
  rw [← Equiv.sum_comp p (fun i => v i*w i)]
  exact Fin.sum_univ_add (fun i : Fin (3+3) => v (p i)*w (p i))

/-- Two distinct coordinates can be put in opposite halves by an actual permutation. -/
lemma permutation_pair (i j : Fin 6) (hij : i ≠ j) :
    ∃ p : Perm, p 0=i ∧ p 3=j := by
  let e : Perm := Equiv.swap 0 i
  let k := e.symm j
  have hk : k ≠ 0 := by
    intro h
    have he := congrArg e h
    have hj : j=i := by simpa [k,e] using he
    exact hij hj.symm
  refine ⟨(Equiv.swap 3 k).trans e,?_,?_⟩
  · change e ((Equiv.swap 3 k) 0)=i
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hk)]
    exact Equiv.swap_apply_left _ _
  · change e ((Equiv.swap 3 k) 3)=j
    rw [Equiv.swap_apply_left]
    exact e.apply_symm_apply j

/-- Nonzero orthogonal vectors always have nonzero projections in some chart. -/
lemma chart_cover (v w : V F) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ⬝ᵥ w=0) :
    ∃ p : Perm, first p v ≠ 0 ∧ second p w ≠ 0 := by
  obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  have hj : ∃ j, j ≠ i ∧ w j ≠ 0 := by
    by_contra! h
    have hdot : v ⬝ᵥ w=v i*w i := by
      unfold dotProduct
      apply sum_eq_single i
      · intro j _ hji
        rw [h j hji,mul_zero]
      · simp
    have hwi : w i=0 := (mul_eq_zero.mp (hdot.symm.trans hvw)).resolve_left hi
    apply hw
    funext j
    by_cases hji : j=i
    · simpa [hji] using hwi
    · exact h j hji
  obtain ⟨j,hji,hj⟩ := hj
  obtain ⟨p,hp0,hp3⟩ := permutation_pair i j (Ne.symm hji)
  refine ⟨p,?_,?_⟩
  · intro h
    have h0 := congrFun h 0
    change v (p 0)=0 at h0
    rw [hp0] at h0
    exact hi h0
  · intro h
    have h0 := congrFun h 0
    change w (p 3)=0 at h0
    rw [hp3] at h0
    exact hj h0

variable {A B : Type*}
abbrev Left (R : A → V F) (p : Perm) := {a : A // first p (R a) ≠ 0}
abbrev Right (C : B → V F) (p : Perm) := {b : B // second p (C b) ≠ 0}

def row (R : A → V F) (p : Perm) (a : Left R p) : U F × U F := split p (R a.val)
def column (C : B → V F) (p : Perm) (b : Right C p) :
    Module.Dual F (U F) × Module.Dual F (U F) :=
  (dotProductEquiv F (Fin 3) (second p (C b.val)),
    dotProductEquiv F (Fin 3) (-first p (C b.val)))

lemma row_ray (R : A → V F) (hR : RayInjective (F := F) R) (p : Perm) :
    RayInjective (F := F) (row R p) := by
  intro x y a h
  apply Subtype.ext
  apply hR x.val y.val a
  apply split_injective p
  simpa only [split_smul] using h

lemma column_ray (C : B → V F) (hC : RayInjective (F := F) C) (p : Perm) :
    RayInjective (F := F) (column C p) := by
  intro x y a h
  have hs : second p (C x.val)=a • second p (C y.val) := by
    apply (dotProductEquiv F (Fin 3)).injective
    rw [map_smul]
    exact congrArg Prod.fst h
  have hf : -first p (C x.val)=a • -first p (C y.val) := by
    apply (dotProductEquiv F (Fin 3)).injective
    rw [map_smul]
    exact congrArg Prod.snd h
  rw [smul_neg,neg_inj] at hf
  apply Subtype.ext
  apply hC x.val y.val a
  apply split_injective p
  exact Prod.ext hf hs

lemma column_nonzero (C : B → V F) (p : Perm) (b : Right C p) :
    (column C p b).1 ≠ 0 := by
  intro h
  apply b.property
  apply (dotProductEquiv F (Fin 3)).injective
  simpa only [map_zero] using h

lemma compatibility (R : A → V F) (C : B → V F) (p : Perm)
    (a : Left R p) (b : Right C p) (h : R a.val ⬝ᵥ C b.val=0) :
    (column C p b).1 (row R p a).2 = (column C p b).2 (row R p a).1 := by
  rw [dot_split p] at h
  change second p (C b.val) ⬝ᵥ second p (R a.val)=
    (-first p (C b.val)) ⬝ᵥ first p (R a.val)
  rw [neg_dotProduct,dotProduct_comm (second p (C b.val)),dotProduct_comm (first p (C b.val))]
  linear_combination h

variable [Fintype F] [Fintype A] [Fintype B]

def selected (E : Finset (A × B)) (R : A → V F) (C : B → V F) (p : Perm) :
    Finset (Left R p × Right C p) := univ.filter (fun z => (z.1.val,z.2.val) ∈ E)

def chartEdges (E : Finset (A × B)) (R : A → V F) (C : B → V F) (p : Perm) :
    Finset (A × B) := E.filter (fun z => first p (R z.1) ≠ 0 ∧ second p (C z.2) ≠ 0)

omit [Fintype F] in
lemma selected_card (E : Finset (A × B)) (R : A → V F) (C : B → V F) (p : Perm) :
    (selected E R C p).card=(chartEdges E R C p).card := by
  let e : Left R p × Right C p ↪ A × B :=
    (Function.Embedding.subtype _).prodMap (Function.Embedding.subtype _)
  have he : (selected E R C p).map e=chartEdges E R C p := by
    ext z
    constructor
    · intro hz
      obtain ⟨w,hw,rfl⟩ := mem_map.mp hz
      exact mem_filter.mpr ⟨(mem_filter.mp hw).2,w.1.property,w.2.property⟩
    · intro hz
      obtain ⟨hz,ha,hb⟩ := mem_filter.mp hz
      exact mem_map.mpr ⟨(⟨z.1,ha⟩,⟨z.2,hb⟩),mem_filter.mpr ⟨mem_univ _,hz⟩,rfl⟩
  rw [← he,card_map]

lemma chart_bound (E : Finset (A × B)) (R : A → V F) (C : B → V F)
    (hR : RayInjective (F := F) R) (hC : RayInjective (F := F) C)
    (hfree : NoRectangle E) (hE : ∀ z ∈ E, R z.1 ⬝ᵥ C z.2=0)
    (hA : Fintype.card A ≤ Fintype.card F^4) (hB : Fintype.card B ≤ Fintype.card F^4)
    (p : Perm) : (chartEdges E R C p).card^4 ≤ 456976*Fintype.card F^27 := by
  rw [← selected_card]
  apply chart_fourth_power (by simp [Module.finrank_fintype_fun_eq_card])
    (row R p) (column C p) (row_ray R hR p) (column_ray C hC p)
    (fun a => a.property) (column_nonzero C p) (selected E R C p)
  · intro f g hfg
    apply hfree (f.trans (Function.Embedding.subtype _))
      (g.trans (Function.Embedding.subtype _))
    intro i j
    exact (mem_filter.mp (hfg i j)).2
  · intro z hz
    exact compatibility R C p z.1 z.2 (hE _ (mem_filter.mp hz).2)
  · exact (Fintype.card_subtype_le _).trans hA
  · exact (Fintype.card_subtype_le _).trans hB

/-- No preferred coordinate chart is assumed: every selected edge is covered
by at least one of the 720 charts, and each chart is bounded separately. -/
theorem fourth_power (E : Finset (A × B)) (R : A → V F) (C : B → V F)
    (hR : RayInjective (F := F) R) (hC : RayInjective (F := F) C)
    (hnR : ∀ a, R a ≠ 0) (hnC : ∀ b, C b ≠ 0)
    (hfree : NoRectangle E) (hE : ∀ z ∈ E, R z.1 ⬝ᵥ C z.2=0)
    (hA : Fintype.card A ≤ Fintype.card F^4) (hB : Fintype.card B ≤ Fintype.card F^4) :
    E.card^4 ≤ 456976*720^4*Fintype.card F^27 := by
  have hcover : E ⊆ univ.biUnion (chartEdges E R C) := by
    intro z hz
    obtain ⟨p,hp,hp'⟩ := chart_cover (R z.1) (C z.2) (hnR _) (hnC _) (hE _ hz)
    exact mem_biUnion.mpr ⟨p,mem_univ _,mem_filter.mpr ⟨hz,hp,hp'⟩⟩
  have he : E.card ≤ ∑ p : Perm, (chartEdges E R C p).card :=
    (card_le_card hcover).trans card_biUnion_le
  have hp := pow_sum_le_card_mul_sum_pow (s := (univ : Finset Perm))
    (f := fun p => (chartEdges E R C p).card) (by intros; omega) 3
  have hc : Fintype.card Perm=720 := by norm_num [Perm,Fintype.card_perm]
  calc
    _ ≤ (∑ p : Perm, (chartEdges E R C p).card)^4 := Nat.pow_le_pow_left he 4
    _ ≤ Fintype.card Perm^3*∑ p : Perm, (chartEdges E R C p).card^4 := by simpa using hp
    _ ≤ Fintype.card Perm^3*∑ _p : Perm, (456976*Fintype.card F^27) := by
      gcongr with p _
      exact chart_bound E R C hR hC hfree hE hA hB p
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,hc]; ring

/-- The actual graph formulation, with arbitrary edge deletion. -/
theorem graph_fourth_power (R : A → V F) (C : B → V F)
    (hR : RayInjective (F := F) R) (hC : RayInjective (F := F) C)
    (hnR : ∀ a, R a ≠ 0) (hnC : ∀ b, C b ≠ 0)
    (hA : Fintype.card A ≤ Fintype.card F^4) (hB : Fintype.card B ≤ Fintype.card F^4)
    (H : SimpleGraph (A ⊕ B))
    (hH : H ≤ Erdos714Tensor.incidence (fun a b => R a ⬝ᵥ C b=0))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 456976*720^4*Fintype.card F^27 := by
  let E : Finset (A × B) := univ.filter (fun z => H.Adj (.inl z.1) (.inr z.2))
  have hbi : H ≤ completeBipartiteGraph A B := by
    intro x y hxy
    have h := hH hxy
    cases x <;> cases y <;> simp_all [Erdos714Tensor.incidence]
  have he : E.card=H.edgeFinset.card := by
    have hc := Erdos714Packing.incidence_edges (Erdos714Unbalanced.neighborhoods H)
    rw [Erdos714Unbalanced.incidence_neighborhoods H hbi] at hc
    rw [hc]
    have hc' : (∑ z : A × B, if H.Adj (.inl z.1) (.inr z.2) then 1 else 0 : ℕ)=E.card := by
      simp only [sum_boole,Nat.cast_id]
      rfl
    rw [← hc',Fintype.sum_prod_type]
    simp only [sum_boole,Nat.cast_id,Erdos714Unbalanced.neighborhoods]
  have hf : NoRectangle E := by
    intro f g hfg
    have hf := (Erdos714Packing.free_iff_no_rectangle (Erdos714Unbalanced.neighborhoods H)
      (by decide : 0 < 4)).mp (by
        rwa [Erdos714Unbalanced.incidence_neighborhoods H hbi])
    apply hf f g
    intro i j
    simpa only [E,Erdos714Unbalanced.neighborhoods,mem_filter,mem_univ,true_and] using hfg i j
  rw [← he]
  apply fourth_power E R C hR hC hnR hnC hf _ hA hB
  intro z hz
  exact hH (mem_filter.mp hz).2

end Erdos714RankSix
#print axioms Erdos714RankSix.chart_cover
#print axioms Erdos714RankSix.row_ray
#print axioms Erdos714RankSix.column_ray
#print axioms Erdos714RankSix.chart_bound
#print axioms Erdos714RankSix.fourth_power
#print axioms Erdos714RankSix.graph_fourth_power
