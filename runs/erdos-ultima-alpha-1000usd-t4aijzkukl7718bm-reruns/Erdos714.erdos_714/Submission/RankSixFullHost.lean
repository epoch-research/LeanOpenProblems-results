import Submission.RankSixThinning
import Submission.QuadraticRecoveryAll

/-!
Full orthogonality hosts in six coordinates, with arbitrary vertex maps.
The full-host hypothesis is essential: repeated vectors with arbitrary edge
thinnings are not covered. This is not a resolution of Erdős Problem 714.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 4000000
namespace Erdos714RankSixFull
open Erdos714LinearBlocks
variable {A B F : Type*} [Fintype A] [Fintype B] [Field F]

abbrev V (F : Type*) := Fin 6 → F

def edges (R : A → V F) (C : B → V F) : Finset (A × B) :=
  univ.filter (fun z => R z.1 ⬝ᵥ C z.2=0)

def neighbors (R : A → V F) (C : B → V F) (a : A) : Finset B :=
  univ.filter (fun b => R a ⬝ᵥ C b=0)

@[simp] lemma mem_edges (R : A → V F) (C : B → V F) (a : A) (b : B) :
    (a,b) ∈ edges R C ↔ R a ⬝ᵥ C b=0 := by simp [edges]

omit [Fintype A] in
@[simp] lemma mem_neighbors (R : A → V F) (C : B → V F) (a : A) (b : B) :
    b ∈ neighbors R C a ↔ R a ⬝ᵥ C b=0 := by simp [neighbors]

lemma transpose_free (R : A → V F) (C : B → V F)
    (hf : NoRectangle (edges R C)) : NoRectangle (edges C R) := by
  intro f g hfg
  apply hf g f
  intro i j
  simpa only [mem_edges,dotProduct_comm] using hfg j i

omit [Fintype B] in
/-- Large twin classes have at most three members. -/
lemma large_twins {T : Type*} [Fintype T] (S : T → Finset B)
    (hf : ∀ f : Fin 4 ↪ T, ∀ g : Fin 4 ↪ B, ¬ ∀ i j, g j ∈ S (f i))
    (hlarge : ∀ t, 4 ≤ (S t).card) (b : Finset B) :
    (univ.filter (fun t => S t=b)).card ≤ 3 := by
  by_contra! h
  obtain ⟨f,hfmem⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 4) (s := univ.filter (fun t => S t=b)) (by simpa using h)
  have he (i : Fin 4) : S (f i)=b := (mem_filter.mp (hfmem ⟨i,rfl⟩)).2
  have hb : 4 ≤ b.card := by simpa only [he 0] using hlarge (f 0)
  obtain ⟨g,hg⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 4) (s := b) (by simpa using hb)
  apply hf f g
  intro i j
  rw [he i]
  exact hg ⟨j,rfl⟩

abbrev Good (R : A → V F) (C : B → V F) :=
  {a : A // R a ≠ 0 ∧ 4 ≤ (neighbors R C a).card}

omit [Fintype A] in
lemma ray_neighbors (R : A → V F) (C : B → V F) (a b : A) (s : F)
    (ha : R a ≠ 0) (hab : R a=s • R b) : neighbors R C a=neighbors R C b := by
  have hs : s ≠ 0 := by
    intro hz
    exact ha (by simpa [hz] using hab)
  ext c
  simp only [mem_neighbors,hab,smul_dotProduct,smul_eq_mul,mul_eq_zero,hs,false_or]

/-- Three colors suffice for high-degree, nonzero vertices of a free FULL host. -/
lemma good_colors (R : A → V F) (C : B → V F)
    (hf : NoRectangle (edges R C)) :
    ∃ c : Good R C → Fin 3, ∀ i : Fin 3,
      RayInjective (F := F) (fun a : {a : Good R C // c a=i} => R a.val.val) := by
  have htwins : ∀ b : Finset B,
      (univ.filter (fun a : Good R C => neighbors R C a.val=b)).card ≤ 3 := by
    apply large_twins (fun a : Good R C => neighbors R C a.val)
    · intro f g hfg
      apply hf (f.trans (Function.Embedding.subtype _)) g
      intro i j
      exact (mem_edges _ _ _ _).mpr ((mem_neighbors _ _ _ _).mp (hfg i j))
    · exact fun a => a.property.2
  obtain ⟨c,hc⟩ := Erdos714QuadraticAll.color_fibers
    (fun a : Good R C => neighbors R C a.val) 3 (fun b => by
      convert htwins b using 1
      apply congrArg Finset.card
      ext a
      simp only [mem_filter,mem_univ,true_and])
  refine ⟨c,?_⟩
  intro i a b s hab
  apply Subtype.ext
  apply hc a.val b.val
  · exact ray_neighbors R C a.val.val b.val.val s a.val.property.1 hab
  · exact a.property.trans b.property.symm

/-- A simple row-degree count, independent of any field structure. -/
lemma row_count {T U : Type*} [Fintype T] [Fintype U]
    (S : T → Finset U) (p : T → Prop) (k : ℕ)
    (hk : ∀ t, p t → (S t).card ≤ k) :
    (univ.filter (fun z : T × U => z.2 ∈ S z.1 ∧ p z.1)).card ≤ k*Fintype.card T := by
  simp only [card_filter,Fintype.sum_prod_type]
  calc
    _ ≤ ∑ _t : T, k := by
      apply sum_le_sum
      intro t _
      by_cases ht : p t
      · simpa only [ht,and_true,sum_boole,Nat.cast_id,filter_mem_eq_inter,univ_inter] using hk t ht
      · simp [ht]
    _ = _ := by simp [mul_comm]

lemma zero_rows (R : A → V F) (C : B → V F)
    (hf : NoRectangle (edges R C)) (hB : 4 ≤ Fintype.card B) :
    (univ.filter (fun a => R a=0)).card ≤ 3 := by
  by_contra! h
  obtain ⟨f,hfm⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 4) (s := univ.filter (fun a => R a=0)) (by simpa using h)
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le (show Fintype.card (Fin 4) ≤ Fintype.card B by simpa)
  apply hf f g
  intro i j
  have hi := (mem_filter.mp (hfm ⟨i,rfl⟩)).2
  simp [hi]


def badRows (R : A → V F) (C : B → V F) : Finset (A × B) :=
  (edges R C).filter (fun z => ¬ (R z.1 ≠ 0 ∧ 4 ≤ (neighbors R C z.1).card))

lemma bad_rows_bound (R : A → V F) (C : B → V F)
    (hf : NoRectangle (edges R C)) (hB : 4 ≤ Fintype.card B) :
    (badRows R C).card ≤ 3*(Fintype.card A+Fintype.card B) := by
  let L := univ.filter (fun z : A × B =>
    z.2 ∈ neighbors R C z.1 ∧ (neighbors R C z.1).card ≤ 3)
  let Z := (univ.filter (fun a => R a=0)) ×ˢ (univ : Finset B)
  have hL : L.card ≤ 3*Fintype.card A := by
    convert row_count (neighbors R C) (fun a => (neighbors R C a).card ≤ 3) 3 (fun _ h => h) using 1
    apply congrArg Finset.card
    ext z
    simp only [L,mem_filter,mem_univ,true_and]
  have hZ : Z.card ≤ 3*Fintype.card B := by
    dsimp [Z]
    rw [card_product,card_univ]
    exact Nat.mul_le_mul_right _ (zero_rows R C hf hB)
  have hsub : badRows R C ⊆ L ∪ Z := by
    intro z hz
    obtain ⟨he,hbad⟩ := mem_filter.mp hz
    by_cases h0 : R z.1=0
    · apply mem_union_right
      simp [Z,h0]
    · apply mem_union_left
      have hd : (neighbors R C z.1).card ≤ 3 := by
        by_contra! h
        exact hbad ⟨h0,h⟩
      exact mem_filter.mpr ⟨mem_univ _,(mem_neighbors _ _ _ _).mpr ((mem_edges _ _ _ _).mp he),hd⟩
  have hcard := (card_le_card hsub).trans (card_union_le _ _)
  omega

lemma edges_card_le (R : A → V F) (C : B → V F) :
    (edges R C).card ≤ Fintype.card A*Fintype.card B := by
  exact (card_le_card (filter_subset _ _)).trans (by simp)

variable [Fintype F]

/-- After an explicitly bounded low-degree/zero-vector part is removed, nine
projectively injective blocks bound the full host. -/
theorem full_decomposition (R : A → V F) (C : B → V F)
    (hf : NoRectangle (edges R C))
    (hA : Fintype.card A ≤ Fintype.card F^4) (hB : Fintype.card B ≤ Fintype.card F^4) :
    ∃ m : ℕ, (edges R C).card ≤ m+6*(Fintype.card A+Fintype.card B) ∧
      m^4 ≤ 9^4*(456976*720^4)*Fintype.card F^27 := by
  by_cases h4A : 4 ≤ Fintype.card A
  swap
  · refine ⟨0,?_,by simp⟩
    have h := (edges_card_le R C).trans
      (Nat.mul_le_mul_right (Fintype.card B) (show Fintype.card A ≤ 3 by omega))
    omega
  by_cases h4B : 4 ≤ Fintype.card B
  swap
  · refine ⟨0,?_,by simp⟩
    have h := (edges_card_le R C).trans
      (Nat.mul_le_mul_left (Fintype.card A) (show Fintype.card B ≤ 3 by omega))
    omega
  obtain ⟨c,hc⟩ := good_colors R C hf
  obtain ⟨d,hd⟩ := good_colors C R (transpose_free R C hf)
  let S (i : Fin 3) := {a : Good R C // c a=i}
  let U (j : Fin 3) := {b : Good C R // d b=j}
  let e (i : Fin 3) : S i ↪ A :=
    (Function.Embedding.subtype _).trans (Function.Embedding.subtype _)
  let f (j : Fin 3) : U j ↪ B :=
    (Function.Embedding.subtype _).trans (Function.Embedding.subtype _)
  let T (p : Fin 3 × Fin 3) :=
    (edges (fun a : S p.1 => R (e p.1 a)) (fun b : U p.2 => C (f p.2 b))).map
      ((e p.1).prodMap (f p.2))
  have hT (p : Fin 3 × Fin 3) :
      (T p).card^4 ≤ (456976*720^4)*Fintype.card F^27 := by
    dsimp only [T]
    rw [card_map]
    apply Erdos714RankSix.fourth_power _ _ _ (hc p.1) (hd p.2)
      (fun a => a.val.property.1) (fun b => b.val.property.1)
    · intro g h hgh
      apply hf (g.trans (e p.1)) (h.trans (f p.2))
      intro i j
      simpa [edges,e,f] using hgh i j
    · intro z hz
      simpa [edges,e,f] using hz
    · exact (Fintype.card_le_of_injective _ (e p.1).injective).trans hA
    · exact (Fintype.card_le_of_injective _ (f p.2).injective).trans hB
  let L := badRows R C
  let D := (badRows C R).map (Equiv.prodComm B A).toEmbedding
  have hL : L.card ≤ 3*(Fintype.card A+Fintype.card B) := bad_rows_bound R C hf h4B
  have hD : D.card ≤ 3*(Fintype.card B+Fintype.card A) := by
    rw [Finset.card_map]
    exact bad_rows_bound C R (transpose_free R C hf) h4A
  have hcover : edges R C ⊆ univ.biUnion T ∪ L ∪ D := by
    intro z hz
    by_cases ha : R z.1 ≠ 0 ∧ 4 ≤ (neighbors R C z.1).card
    · by_cases hb : C z.2 ≠ 0 ∧ 4 ≤ (neighbors C R z.2).card
      · apply mem_union_left
        apply mem_union_left
        let a : Good R C := ⟨z.1,ha⟩
        let b : Good C R := ⟨z.2,hb⟩
        apply mem_biUnion.mpr
        refine ⟨(c a,d b),mem_univ _,?_⟩
        apply mem_map.mpr
        refine ⟨(⟨a,rfl⟩,⟨b,rfl⟩),?_,rfl⟩
        exact (mem_edges _ _ _ _).mpr ((mem_edges _ _ _ _).mp hz)
      · apply mem_union_right
        apply mem_map.mpr
        refine ⟨(z.2,z.1),mem_filter.mpr ⟨?_,hb⟩,rfl⟩
        simpa [edges,dotProduct_comm] using hz
    · apply mem_union_left
      apply mem_union_right
      exact mem_filter.mpr ⟨hz,ha⟩
  have hsize : (edges R C).card ≤ (∑ p, (T p).card)+L.card+D.card := by
    calc
      _ ≤ (univ.biUnion T ∪ L ∪ D).card := card_le_card hcover
      _ ≤ (univ.biUnion T ∪ L).card+D.card := card_union_le _ _
      _ ≤ (univ.biUnion T).card+L.card+D.card := Nat.add_le_add_right (card_union_le _ _) _
      _ ≤ _ := by gcongr; exact card_biUnion_le
  refine ⟨∑ p, (T p).card,by omega,?_⟩
  have hp := pow_sum_le_card_mul_sum_pow (s := (univ : Finset (Fin 3 × Fin 3)))
    (f := fun p => (T p).card) (by intros; omega) 3
  calc
    _ ≤ 9^3*∑ p, (T p).card^4 := by simpa using hp
    _ ≤ 9^3*∑ _p : Fin 3 × Fin 3, (456976*720^4)*Fintype.card F^27 := by
      gcongr with p _
      exact hT p
    _ = _ := by simp; ring

/-- No injectivity or nonzero assumptions on the vertex maps are needed for
the FULL graph. The exponent is 27/4 in q, strictly below the target 7. -/
theorem full_fourth_power (R : A → V F) (C : B → V F)
    (hf : NoRectangle (edges R C))
    (hA : Fintype.card A ≤ Fintype.card F^4) (hB : Fintype.card B ≤ Fintype.card F^4) :
    (edges R C).card^4 ≤
      8*(9^4*(456976*720^4)+12^4)*Fintype.card F^27 := by
  obtain ⟨m,hm,hmp⟩ := full_decomposition R C hf hA hB
  let b := 6*(Fintype.card A+Fintype.card B)
  have hb : b ≤ 12*Fintype.card F^4 := by dsimp [b]; omega
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have hbp : b^4 ≤ 12^4*Fintype.card F^27 := by
    calc
      _ ≤ (12*Fintype.card F^4)^4 := Nat.pow_le_pow_left hb 4
      _ = 12^4*Fintype.card F^16 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq (by omega))
  have hadd : (m+b)^4 ≤ 8*(m^4+b^4) := by
    have h := pow_sum_le_card_mul_sum_pow (s := (univ : Finset (Fin 2)))
      (f := ![m,b]) (by intros; omega) 3
    simpa [Fin.sum_univ_two] using h
  calc
    _ ≤ (m+b)^4 := Nat.pow_le_pow_left hm 4
    _ ≤ 8*(m^4+b^4) := hadd
    _ ≤ 8*(9^4*(456976*720^4)*Fintype.card F^27+12^4*Fintype.card F^27) := by gcongr
    _ = _ := by ring


/-- The same bound for the actual bipartite simple graph. -/
theorem graph_fourth_power (R : A → V F) (C : B → V F)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Tensor.incidence (fun a b => R a ⬝ᵥ C b=0)))
    (hA : Fintype.card A ≤ Fintype.card F^4) (hB : Fintype.card B ≤ Fintype.card F^4) :
    (Erdos714Tensor.incidence (fun a b => R a ⬝ᵥ C b=0)).edgeFinset.card^4 ≤
      8*(9^4*(456976*720^4)+12^4)*Fintype.card F^27 := by
  have hg : Erdos714Tensor.incidence (fun a b => R a ⬝ᵥ C b=0)=
      Erdos714Packing.incidence (neighbors R C) := by
    ext x y
    cases x <;> cases y <;> simp [Erdos714Tensor.incidence,Erdos714Packing.incidence]
  have hrect : NoRectangle (edges R C) := by
    intro f g hfg
    apply (Erdos714Packing.free_iff_no_rectangle (neighbors R C) (by decide : 0 < 4)).mp
      (by rwa [← hg]) f g
    intro i j
    exact (mem_neighbors _ _ _ _).mpr ((mem_edges _ _ _ _).mp (hfg i j))
  have he : (Erdos714Tensor.incidence (fun a b => R a ⬝ᵥ C b=0)).edgeFinset.card=
      (edges R C).card := by
    rw [hg,Erdos714Packing.incidence_edges]
    simp only [edges,neighbors,card_filter,Fintype.sum_prod_type]
  rw [he]
  exact full_fourth_power R C hrect hA hB

/-- Four bilinear coordinates plus two arbitrary nonlinear scalar features
still form a six-coordinate full host. -/
theorem two_feature_graph_fourth_power
    (x : A → Fin 4 → F) (y : B → Fin 4 → F) (u v : A → F) (f g : B → F)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Tensor.incidence (fun a b => x a ⬝ᵥ y b=u a*f b+v a*g b)))
    (hA : Fintype.card A ≤ Fintype.card F^4) (hB : Fintype.card B ≤ Fintype.card F^4) :
    (Erdos714Tensor.incidence (fun a b => x a ⬝ᵥ y b=u a*f b+v a*g b)).edgeFinset.card^4 ≤
      8*(9^4*(456976*720^4)+12^4)*Fintype.card F^27 := by
  let R (a : A) : V F := ![x a 0,x a 1,x a 2,x a 3,u a,v a]
  let C (b : B) : V F := ![y b 0,y b 1,y b 2,y b 3,-f b,-g b]
  have hdot (a : A) (b : B) :
      R a ⬝ᵥ C b=x a ⬝ᵥ y b-(u a*f b+v a*g b) := by
    simp [R,C,dotProduct,Fin.sum_univ_succ]
    ring
  have he : Erdos714Tensor.incidence (fun a b => x a ⬝ᵥ y b=u a*f b+v a*g b)=
      Erdos714Tensor.incidence (fun a b => R a ⬝ᵥ C b=0) := by
    ext a b
    cases a <;> cases b <;> simp [Erdos714Tensor.incidence,hdot,sub_eq_zero]
  rw [he] at hf ⊢
  exact graph_fourth_power R C hf hA hB

/-- In particular, arbitrary nonlinear two-scalar matrix recovery laws cannot
supply full K44-free hosts at the critical density. Any endpoint guards can
be encoded by the indexing types A and B. -/
theorem matrix_recovery_fourth_power
    (R : A → Matrix (Fin 2) (Fin 2) F) (C : B → Matrix (Fin 2) (Fin 2) F)
    (u v : A → F) (f g : B → F)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Tensor.incidence (fun a b => (R a*C b).trace=u a*f b+v a*g b)))
    (hA : Fintype.card A ≤ Fintype.card F^4) (hB : Fintype.card B ≤ Fintype.card F^4) :
    (Erdos714Tensor.incidence (fun a b => (R a*C b).trace=u a*f b+v a*g b)).edgeFinset.card^4 ≤
      8*(9^4*(456976*720^4)+12^4)*Fintype.card F^27 := by
  let x (a : A) : Fin 4 → F := ![R a 0 0,R a 0 1,R a 1 0,R a 1 1]
  let y (b : B) : Fin 4 → F := ![C b 0 0,C b 1 0,C b 0 1,C b 1 1]
  have hdot (a : A) (b : B) : x a ⬝ᵥ y b=(R a*C b).trace := by
    simp [x,y,dotProduct,Fin.sum_univ_succ,Matrix.trace,Matrix.mul_apply]
    ring
  have he : Erdos714Tensor.incidence (fun a b => (R a*C b).trace=u a*f b+v a*g b)=
      Erdos714Tensor.incidence (fun a b => x a ⬝ᵥ y b=u a*f b+v a*g b) := by
    simp_rw [hdot]
  rw [he] at hf ⊢
  exact two_feature_graph_fourth_power x y u v f g hf hA hB

/-- A critical integer lower constant permits only bounded field order in
this full-host model. This is not an upper bound on all K44-free graphs. -/
theorem critical_field_budget (R : A → V F) (C : B → V F)
    (hf : NoRectangle (edges R C))
    (hA : Fintype.card A ≤ Fintype.card F^4) (hB : Fintype.card B ≤ Fintype.card F^4)
    (d : ℕ) (hd : Fintype.card F^7 ≤ d*(edges R C).card) :
    Fintype.card F ≤ 8*(9^4*(456976*720^4)+12^4)*d^4 := by
  let K := 8*(9^4*(456976*720^4)+12^4)
  have hbound := full_fourth_power R C hf hA hB
  have hp : Fintype.card F*Fintype.card F^27 ≤ K*d^4*Fintype.card F^27 := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (d*(edges R C).card)^4 := Nat.pow_le_pow_left hd 4
      _ = d^4*(edges R C).card^4 := by ring
      _ ≤ d^4*(K*Fintype.card F^27) := Nat.mul_le_mul_left _ hbound
      _ = _ := by ring
  exact (mul_le_mul_iff_left₀ (pow_pos (show 0 < Fintype.card F from Fintype.card_pos) 27)).mp
    (by simpa [mul_comm] using hp)

end Erdos714RankSixFull

#print axioms Erdos714RankSixFull.large_twins
#print axioms Erdos714RankSixFull.good_colors
#print axioms Erdos714RankSixFull.row_count
#print axioms Erdos714RankSixFull.zero_rows

#print axioms Erdos714RankSixFull.bad_rows_bound
#print axioms Erdos714RankSixFull.full_decomposition
#print axioms Erdos714RankSixFull.full_fourth_power

#print axioms Erdos714RankSixFull.graph_fourth_power
#print axioms Erdos714RankSixFull.two_feature_graph_fourth_power
#print axioms Erdos714RankSixFull.matrix_recovery_fourth_power
#print axioms Erdos714RankSixFull.critical_field_budget
