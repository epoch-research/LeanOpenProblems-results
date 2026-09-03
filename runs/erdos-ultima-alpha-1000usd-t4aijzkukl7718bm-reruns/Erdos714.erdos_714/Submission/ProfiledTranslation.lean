import Submission.BinaryLift
import Submission.Packing

/-! A large-fiber obstruction to binary translation graphs with a row-profile
correction. This is not a solution of Erdős 714. -/
noncomputable section
open Classical Finset SimpleGraph
open scoped CharTwo
set_option maxHeartbeats 2000000

namespace Erdos714ProfiledTranslation
variable {G F : Type*} [Ring G] [CharP G 2] [AddCommGroup F]

def graph (f : G → F) (P : F → G → F) : SimpleGraph ((G × F) ⊕ (G × F)) where
  Adj p q := match p,q with
    | .inl x,.inr y => f (x.1+y.1)+P (f x.1) y.1=x.2+y.2
    | .inr y,.inl x => f (x.1+y.1)+P (f x.1) y.1=x.2+y.2
    | _,_ => False
  symm := by intro p q; cases p <;> cases q <;> simp_all
  loopless := by intro p; cases p <;> simp

/-- All four rows have the same profile, so their correction is absorbed by
one column weight. No algebraic assumption on the correction is needed. -/
def planeCopy (f : G → F) (P : F → G → F) (c p u v : G)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (hplane : ∀ i, f (p+Erdos714BinaryLift.plane u v i)=f c) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph f P) := by
  let L (i : Fin 4) : G × F := (p+Erdos714BinaryLift.plane u v i,0)
  let R (i : Fin 4) : G × F := (Erdos714BinaryLift.plane u v i,
    f c+P (f c) (Erdos714BinaryLift.plane u v i))
  have hL : Function.Injective L := by
    intro i j h
    exact Erdos714BinaryLift.plane_injective hu hv huv
      (add_left_cancel (congrArg Prod.fst h))
  have hR : Function.Injective R := by
    intro i j h
    exact Erdos714BinaryLift.plane_injective hu hv huv (congrArg Prod.fst h)
  have hE (i j : Fin 4) : (graph f P).Adj (.inl (L i)) (.inr (R j)) := by
    obtain ⟨k,hk⟩ := Erdos714BinaryLift.plane_closed u v i j
    change f ((p+Erdos714BinaryLift.plane u v i)+Erdos714BinaryLift.plane u v j)+
      P (f (p+Erdos714BinaryLift.plane u v i)) (Erdos714BinaryLift.plane u v j)=_
    rw [add_assoc,hk,hplane,hplane]
    exact (zero_add _).symm
  refine ⟨⟨Sum.map L R,?_⟩,Sum.map_injective.mpr ⟨hL,hR⟩⟩
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j => simp at hij
    | inr j => exact hE i j
  | inr i =>
    cases j with
    | inl j => exact (hE j i).symm
    | inr j => simp at hij

/-- Every profile fiber of a free full graph must be Sidon-sized. -/
theorem fiber_bound [Fintype G] (f : G → F) (P : F → G → F)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph f P)) (t : F) :
    let m := (univ.filter (fun x => f x=t)).card
    m*(m-1) ≤ 2*Fintype.card G := by
  by_contra h
  obtain ⟨p,u,v,hu,hv,huv,hS⟩ := Erdos714BinaryLift.exists_plane_of_card
    (univ.filter (fun x => f x=t)) (by simpa using (lt_of_not_ge h))
  have hp : f p=t := by simpa [Erdos714BinaryLift.plane] using hS 0
  exact hfree ⟨planeCopy f P p p u v hu hv huv (fun i => by
    rw [hp]
    exact (mem_filter.mp (hS i)).2)⟩

/-- Pigeonhole yields a uniform obstruction at cubic input scale, including
unbalanced profile fibers and arbitrary column-dependent corrections. -/
theorem cubic_not_free [Fintype G] [Fintype F] (f : G → F) (P : F → G → F)
    (hq : 4 ≤ Fintype.card F) (hG : Fintype.card G=Fintype.card F^3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph f P) := by
  let q := Fintype.card F
  have hq' : 4 ≤ q := hq
  have hc : Fintype.card F*(q^2-1)<Fintype.card G := by
    rw [hG]
    change q*(q^2-1)<q^3
    have hs : q^2-1+1=q^2 := Nat.sub_add_cancel (by nlinarith)
    nlinarith [congrArg (fun z : ℕ => q*z) hs]
  obtain ⟨t,ht⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f hc
  let m := (univ.filter (fun x => f x=t)).card
  have hm : q^2 ≤ m := by change q^2-1 < m at ht; omega
  intro hfree
  have hb := fiber_bound f P hfree t
  change m*(m-1)≤ 2*Fintype.card G at hb
  rw [hG] at hb
  have hmul : q^2*(q^2-1)≤ m*(m-1) := Nat.mul_le_mul hm (Nat.sub_le_sub_right hm 1)
  have hs : q^2-1+1=q^2 := Nat.sub_add_cancel (by nlinarith)
  have hlarge : 2*q<q^2-1 := by nlinarith
  have hlt := Nat.mul_lt_mul_of_pos_left hlarge (show 0<q^2 by positivity)
  nlinarith


omit [CharP G 2] in
lemma row_card [Fintype G] [Fintype F] (f : G → F) (P : F → G → F) (x : G × F) :
    (univ.filter (fun y : G × F => f (x.1+y.1)+P (f x.1) y.1=x.2+y.2)).card =
      Fintype.card G := by
  rw [← card_univ (α := G)]
  apply card_bij (fun y _ => y.1)
  · intro y _
    exact mem_univ _
  · intro y hy z hz he
    apply Prod.ext he
    have hy' := (mem_filter.mp hy).2
    have hz' := (mem_filter.mp hz).2
    rw [he] at hy'
    exact add_left_cancel (hy'.symm.trans hz')
  · intro y _
    refine ⟨(y,f (x.1+y)+P (f x.1) y-x.2),?_,rfl⟩
    simp

omit [CharP G 2] in
/-- The row-profile correction never changes the exact edge count. -/
theorem edge_count [Fintype G] [Fintype F] (f : G → F) (P : F → G → F) :
    (graph f P).edgeFinset.card = Fintype.card G^2*Fintype.card F := by
  have he : graph f P = Erdos714Packing.incidence (fun x : G × F =>
      univ.filter (fun y : G × F => f (x.1+y.1)+P (f x.1) y.1=x.2+y.2)) := by
    ext x y
    cases x <;> cases y <;> simp [graph,Erdos714Packing.incidence]
  rw [he,Erdos714Packing.incidence_edges]
  simp_rw [row_card]
  simp only [sum_const,card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_id]
  ring

end Erdos714ProfiledTranslation
#print axioms Erdos714ProfiledTranslation.planeCopy
#print axioms Erdos714ProfiledTranslation.fiber_bound
#print axioms Erdos714ProfiledTranslation.cubic_not_free

#print axioms Erdos714ProfiledTranslation.edge_count
