import Submission.InterceptGoodTranslationExplore
import Submission.InterceptCollisionCorrectionExplore

/-! A translation outside the explicit bad set bounds the collision
correction at every target, not merely on average. -/
namespace Erdos66InterceptCollisionIncidence
open Erdos66InterceptEdgePolynomial Erdos66InterceptConcurrencyPolynomial
  Erdos66InterceptGoodTranslation Erdos66InterceptCurve Erdos66InterceptCollisionCorrection
  Erdos66InheritedOriginLift Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 2600000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [Fintype F] [DecidableEq F] in
lemma sameEdge_symm (e f : F × F) (h : SameEdge e f) : SameEdge f e := by
  rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl ⟨h1.symm,h2.symm⟩
  · exact Or.inr ⟨h2.symm,h1.symm⟩

def edgePoints (a : F) (e : F × F) : Finset (F × F) :=
  Finset.univ.filter (fun z ↦ z.1=(a+e.1)+(a+e.2) ∧ z.2^2=(a+e.1)*(a+e.2))

lemma mem_edgePoints (a : F) (e z : F × F) : z∈edgePoints a e ↔
    z.1=(a+e.1)+(a+e.2) ∧ z.2^2=(a+e.1)*(a+e.2) := by
  simp only [edgePoints,Finset.mem_filter,Finset.mem_univ,true_and]

lemma edgePoints_card (a : F) (e : F × F) : (edgePoints a e).card≤ 2 := by
  by_cases hn : (edgePoints a e).Nonempty
  · obtain ⟨z,hz⟩ := hn
    have hs : edgePoints a e⊆{z,(z.1,-z.2)} := by
      intro y hy
      obtain ⟨hz1,hz2⟩ := (mem_edgePoints a e z).mp hz
      obtain ⟨hy1,hy2⟩ := (mem_edgePoints a e y).mp hy
      have hyz : y.1=z.1 := hy1.trans hz1.symm
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy2.trans hz2.symm) with h | h
      · have heq : y=z := Prod.ext hyz h
        simp only [heq,Finset.mem_insert,Finset.mem_singleton,true_or]
      · have heq : y=(z.1,-z.2) := Prod.ext hyz h
        simp only [heq,Finset.mem_insert,Finset.mem_singleton,or_true]
    exact (Finset.card_le_card hs).trans Finset.card_le_two
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp

lemma edgePoints_sameEdge (a : F) (e f : F × F) (h : SameEdge e f) : edgePoints a e=edgePoints a f := by
  ext z
  simp only [mem_edgePoints]
  rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · rw [h1,h2]
  · rw [h1,h2,add_comm (a+f.2) (a+f.1),mul_comm (a+f.2) (a+f.1)]

lemma collision_has_edge (U : Finset F) (a : F)
    (hU : ∀u∈translated U a,u≠0) (z : F × F) (hz : z∈collisionSet (translated U a)) :
    ∃e∈edges U, e.1≠e.2 ∧ z∈edgePoints a e := by
  have hm : 2≤ multiplicity (translated U a) z := by
    simpa only [collisionSet,Erdos66TwofoldFamily.collisions,Finset.mem_filter,Finset.mem_univ,
      true_and,familyMult_eq] using hz
  obtain ⟨u,v,hu,hv,huv⟩ := Finset.one_lt_card_iff.mp
    (show 1<((translated U a).filter (fun u ↦ z∈curve u)).card by exact lt_of_lt_of_le (by norm_num) hm)
  obtain ⟨hu,hzu⟩ := Finset.mem_filter.mp hu
  obtain ⟨hv,hzv⟩ := Finset.mem_filter.mp hv
  have hu0 := hU u hu
  have hv0 := hU v hv
  have hval : value u z.2=value v z.2 := ((mem_curve u z).mp hzu).symm.trans ((mem_curve v z).mp hzv)
  have hprod : z.2^2=u*v := ((value_collision u v z.2 hu0 hv0).mp hval |>.resolve_left huv).symm
  have hsum : z.1=u+v := by
    rw [(mem_curve u z).mp hzu,value,hprod,mul_div_cancel_left₀ v hu0]
  change u∈U.image (fun x ↦ a+x) at hu
  change v∈U.image (fun x ↦ a+x) at hv
  obtain ⟨u0,hu0',rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨v0,hv0',rfl⟩ := Finset.mem_image.mp hv
  refine ⟨(u0,v0),Finset.mem_product.mpr ⟨hu0',hv0'⟩,?_,?_⟩
  · exact fun h ↦ huv (congrArg (a+·) h)
  · exact (mem_edgePoints a (u0,v0) z).mpr ⟨hsum,hprod⟩

lemma edge_hit_of_membership (a w q t : F) (e z : F × F)
    (hz : z∈edgePoints a e) (hc : (t,q)-z∈curve (a+w)) : EdgeHit a w q t e z.2 := by
  obtain ⟨hx,hk⟩ := (mem_edgePoints a e z).mp hz
  have hv := (mem_curve (a+w) ((t,q)-z)).mp hc
  refine ⟨hk,?_⟩
  change t-z.1=value (a+w) (q-z.2) at hv
  rw [hx] at hv
  exact hv.symm

/-- For each old label, its reflected curve contains at most four collision
points. Three distinct unordered collision pairs were excluded uniformly. -/
theorem collision_curve_cap (h2 : (2 : F)≠0) (U : Finset F) (a : F)
    (ha : a∉allForbidden U) (w : F) (hw : w∈U) (q t : F) :
    pairCount (collisionSet (translated U a)) (curve (a+w)) (t,q)≤ 4 := by
  obtain ⟨hU,_⟩ := outside_admissible h2 U a ha
  have hw0 : a+w≠0 := hU _ (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
  have ha' : a∉collisionForbidden U := fun h ↦ ha (Finset.mem_union_left _ h)
  let S := (collisionSet (translated U a)).filter (fun z ↦ (t,q)-z∈curve (a+w))
  change S.card≤ 4
  have getEdge (z : F × F) (hz : z∈S) : ∃e∈edges U, e.1≠e.2 ∧ z∈edgePoints a e :=
    collision_has_edge U a hU z (Finset.mem_filter.mp hz).1
  have getHit (z : F × F) (hz : z∈S) (e : F × F) (he : z∈edgePoints a e) :
      EdgeHit a w q t e z.2 :=
    edge_hit_of_membership a w q t e z he (Finset.mem_filter.mp hz).2
  by_cases hn : S.Nonempty
  · obtain ⟨z0,hz0⟩ := hn
    obtain ⟨e,heU,he,hze⟩ := getEdge z0 hz0
    by_cases hsecond : ∃z∈S,∃f∈edges U, f.1≠f.2 ∧ z∈edgePoints a f ∧ ¬SameEdge e f
    · obtain ⟨z1,hz1,f,hfU,_,hzf,hef⟩ := hsecond
      have hsub : S⊆edgePoints a e∪edgePoints a f := by
        intro z hz
        obtain ⟨g,hgU,hg,hzg⟩ := getEdge z hz
        by_cases hge : SameEdge g e
        · exact Finset.mem_union_left _ ((edgePoints_sameEdge a g e hge) ▸ hzg)
        by_cases hgf : SameEdge g f
        · exact Finset.mem_union_right _ ((edgePoints_sameEdge a g f hgf) ▸ hzg)
        have hfg : ¬SameEdge f g := fun h ↦ hgf (sameEdge_symm f g h)
        exact False.elim (outside_no_three_hits h2 U a ha' w hw e f g heU hfU hgU he hef hfg hge
          q t z0.2 z1.2 z.2 hw0 (getHit z0 hz0 e hze) (getHit z1 hz1 f hzf) (getHit z hz g hzg))
      have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hec := edgePoints_card a e
      have hfc := edgePoints_card a f
      omega
    · have hsub : S⊆edgePoints a e := by
        intro z hz
        obtain ⟨f,hfU,hf,hzf⟩ := getEdge z hz
        have hef : SameEdge e f := by
          by_contra hh
          exact hsecond ⟨z,hz,f,hfU,hf,hzf,hh⟩
        rw [edgePoints_sameEdge a e f hef]
        exact hzf
      exact (Finset.card_le_card hsub).trans ((edgePoints_card a e).trans (by norm_num))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp

lemma collision_subset_union (U : Finset F) : collisionSet U⊆curveUnion U := by
  intro z hz
  have hm : 2≤ multiplicity U z := by
    simpa only [collisionSet,Erdos66TwofoldFamily.collisions,Finset.mem_filter,Finset.mem_univ,
      true_and,familyMult_eq] using hz
  have hp : 0<Erdos66TwofoldFamily.familyMult U curve z := by change 0 < multiplicity U z; omega
  exact (Erdos66TwofoldFamily.familyMult_pos_iff U curve z).mp hp

lemma collision_union_cap (h2 : (2 : F)≠0) (U : Finset F) (a : F)
    (ha : a∉allForbidden U) (z : F × F) :
    pairCount (collisionSet (translated U a)) (curveUnion (translated U a)) z≤ 4*U.card := by
  obtain ⟨t,q⟩ := z
  have hh := Erdos66ParabolaRepair.pairCount_biUnion_right_le (translated U a) curve (collisionSet (translated U a)) (t,q)
  change _ ≤  ∑u∈translated U a, pairCount (collisionSet (translated U a)) (curve u) (t,q) at hh
  have hs : (∑u∈translated U a, pairCount (collisionSet (translated U a)) (curve u) (t,q))≤ 
      ∑_u∈translated U a,4 := by
    apply Finset.sum_le_sum
    intro u hu
    change u∈U.image (fun x ↦ a+x) at hu
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hu
    exact collision_curve_cap h2 U a ha w hw q t
  exact hh.trans (by simpa only [Finset.sum_const,nsmul_eq_mul,translated_card,Nat.mul_comm] using hs)

lemma collision_self_cap (h2 : (2 : F)≠0) (U : Finset F) (a : F)
    (ha : a∉allForbidden U) (z : F × F) :
    pairCount (collisionSet (translated U a)) (collisionSet (translated U a)) z≤ 4*U.card := by
  apply le_trans _ (collision_union_cap h2 U a ha z)
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hx,hzx⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hx,collision_subset_union _ hzx⟩

end Erdos66InterceptCollisionIncidence
