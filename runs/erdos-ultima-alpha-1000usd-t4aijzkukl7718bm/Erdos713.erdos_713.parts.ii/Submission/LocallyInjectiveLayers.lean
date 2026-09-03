import FormalConjecturesUtil
import Submission.ProductCoverObstructions
import Submission.OrientedCloneCount

/-! Layer bounds for arbitrary locally injective graph homomorphisms.
No surjectivity, uniform fibers, or connected base is assumed. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713LocallyInjectiveLayers
open Erdos713ProductCover Erdos713OrientedCloneCount
variable {V W : Type*} [Fintype V] [Fintype W]
variable {G : SimpleGraph V} {F : SimpleGraph W}
set_option maxHeartbeats 2000000

noncomputable def fiberSize (f : V → W) (w : W) : ℕ := Fintype.card {x // f x=w}
noncomputable def layer (f : V → W) (j : ℕ) : Finset W := univ.filter (fun w => j < fiberSize f w)
noncomputable def block (f : G →g F) (u v : W) : ℕ :=
  Nat.card {p : {x // f x=u} × {y // f y=v} // G.Adj p.1.val p.2.val}

omit [Fintype W] in
lemma fiberSize_le (f : V → W) (w : W) : fiberSize f w ≤ Fintype.card V :=
  Fintype.card_le_of_injective Subtype.val Subtype.val_injective

omit [Fintype W] in
lemma block_le (f : G →g F) (hLocal : ∀ x, Function.Injective (neighborMap f x)) (u v : W) :
    block f u v ≤ if F.Adj u v then min (fiberSize f u) (fiberSize f v) else 0 := by
  by_cases huv : F.Adj u v
  · rw [if_pos huv]
    unfold block fiberSize
    simp only [← Nat.card_eq_fintype_card]
    apply le_min
    · apply Nat.card_le_card_of_injective
        (fun p : {p : {x // f x=u} × {y // f y=v} // G.Adj p.1.val p.2.val} => p.val.1)
      intro p q he
      apply Subtype.ext
      apply Prod.ext he
      apply Subtype.ext
      have hfirst : p.val.1.val=q.val.1.val := congrArg Subtype.val he
      have hq : G.Adj p.val.1.val q.val.2.val := by rw [hfirst]; exact q.property
      have hh : neighborMap f p.val.1.val ⟨p.val.2.val,p.property⟩ =
          neighborMap f p.val.1.val ⟨q.val.2.val,hq⟩ :=
        Subtype.ext (p.val.2.property.trans q.val.2.property.symm)
      exact congrArg (fun z : G.neighborSet p.val.1.val => z.val) (hLocal _ hh)
    · apply Nat.card_le_card_of_injective
        (fun p : {p : {x // f x=u} × {y // f y=v} // G.Adj p.1.val p.2.val} => p.val.2)
      intro p q he
      apply Subtype.ext
      apply Prod.ext _ he
      apply Subtype.ext
      have hsecond : p.val.2.val=q.val.2.val := congrArg Subtype.val he
      have hq : G.Adj p.val.2.val q.val.1.val := by rw [hsecond]; exact q.property.symm
      have hh : neighborMap f p.val.2.val ⟨p.val.1.val,p.property.symm⟩ =
          neighborMap f p.val.2.val ⟨q.val.1.val,hq⟩ :=
        Subtype.ext (p.val.1.property.trans q.val.1.property.symm)
      exact congrArg (fun z : G.neighborSet p.val.2.val => z.val) (hLocal _ hh)
  · rw [if_neg huv]
    haveI : IsEmpty {p : {x // f x=u} × {y // f y=v} // G.Adj p.1.val p.2.val} :=
      ⟨fun p => huv (by simpa only [p.val.1.property,p.val.2.property] using f.map_adj p.property)⟩
    simp [block]

lemma block_sum (f : G →g F) : (∑ u : W, ∑ v : W, block f u v) = 2*Nat.card G.edgeSet := by
  have hb (u v : W) : block f u v =
      ∑ x : {x // f x=u}, ∑ y : {y // f y=v}, if G.Adj x.val y.val then 1 else 0 := by
    simp only [block,Nat.card_eq_fintype_card,Fintype.card_subtype,card_filter,Fintype.sum_prod_type]
  have he : 2*Nat.card G.edgeSet = ∑ x : V, ∑ y : V, if G.Adj x y then 1 else 0 := by
    have hh := G.two_mul_card_edgeFinset
    simpa only [edgeFinset_card,Fintype.card_eq_nat_card,card_filter,Fintype.sum_prod_type] using hh
  calc
    _ = ∑ u : W, ∑ v : W, ∑ x : {x // f x=u}, ∑ y : {y // f y=v},
        if G.Adj x.val y.val then 1 else 0 := by simp only [hb]
    _ = ∑ u : W, ∑ x : {x // f x=u}, ∑ v : W, ∑ y : {y // f y=v},
        if G.Adj x.val y.val then 1 else 0 := sum_congr rfl (fun _ _ => sum_comm)
    _ = ∑ u : W, ∑ x : {x // f x=u}, ∑ y : V, if G.Adj x.val y then 1 else 0 := by
      apply sum_congr rfl
      intro u _
      exact sum_congr rfl (fun x _ => Fintype.sum_fiberwise f (fun y => if G.Adj x.val y then 1 else 0))
    _ = ∑ x : V, ∑ y : V, if G.Adj x y then 1 else 0 :=
      Fintype.sum_fiberwise f (fun x : V => ∑ y : V, if G.Adj x y then 1 else 0)
    _ = _ := he.symm

lemma minimum_as_layers {a b N : ℕ} (ha : a ≤ N) (_hb : b ≤ N) :
    (∑ j ∈ range N, if j<a ∧ j<b then 1 else 0 : ℕ) = min a b := by
  have he : (range N).filter (fun j => j<a ∧ j<b) = range (min a b) := by
    ext j
    simp only [mem_filter,mem_range,lt_min_iff]
    omega
  rw [← card_filter,he,card_range]

lemma indicator_as_layers {a N : ℕ} (ha : a ≤ N) :
    (∑ j ∈ range N, if j<a then 1 else 0 : ℕ) = a := by
  simpa only [and_self,min_self] using minimum_as_layers ha ha

/-- The sum of the layer orders is exactly the source order. -/
theorem layer_vertices (f : V → W) :
    (∑ j ∈ range (Fintype.card V), (layer f j).card) = Fintype.card V := by
  have hl (j : ℕ) : (layer f j).card = ∑ w : W, if j<fiberSize f w then 1 else 0 := by
    simp only [layer,card_filter]
  calc
    _ = ∑ j ∈ range (Fintype.card V), ∑ w : W, if j<fiberSize f w then 1 else 0 := by simp only [hl]
    _ = ∑ w : W, ∑ j ∈ range (Fintype.card V), if j<fiberSize f w then 1 else 0 := sum_comm
    _ = ∑ w : W, fiberSize f w := sum_congr rfl (fun w _ => indicator_as_layers (fiberSize_le f w))
    _ = _ := by
      simp only [fiberSize,← Fintype.card_sigma]
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)

/-- Every pair of fibers supports at most a matching. Summing its maximum
size is equivalent to summing the induced base graphs over all layers. -/
theorem edge_layers (f : G →g F) (hLocal : ∀ x, Function.Injective (neighborMap f x)) :
    Nat.card G.edgeSet ≤ ∑ j ∈ range (Fintype.card V), Nat.card (F.induce (layer f j : Set W)).edgeSet := by
  letI : LinearOrder W := LinearOrder.lift' (Fintype.equivFin W) (Fintype.equivFin W).injective
  have hp (u v : W) :
      (if F.Adj u v then min (fiberSize f u) (fiberSize f v) else 0 : ℕ) =
        ∑ j ∈ range (Fintype.card V), if u ∈ layer f j ∧ v ∈ layer f j ∧ F.Adj u v then 1 else 0 := by
    by_cases h : F.Adj u v
    · simpa only [h,ite_true,layer,mem_filter,mem_univ,true_and,and_true] using
        (minimum_as_layers (fiberSize_le f u) (fiberSize_le f v)).symm
    · simp only [h,ite_false,and_false,sum_const_zero]
  have hsum := sum_le_sum (s := (univ : Finset W)) (fun u _ =>
    sum_le_sum (s := (univ : Finset W)) (fun v _ => block_le f hLocal u v))
  rw [block_sum] at hsum
  have he : (∑ u : W, ∑ v : W, if F.Adj u v then min (fiberSize f u) (fiberSize f v) else 0) =
      2*(∑ j ∈ range (Fintype.card V), Nat.card (F.induce (layer f j : Set W)).edgeSet) := by
    calc
      _ = ∑ u : W, ∑ v : W, ∑ j ∈ range (Fintype.card V),
          if u ∈ layer f j ∧ v ∈ layer f j ∧ F.Adj u v then 1 else 0 := by simp only [hp]
      _ = ∑ u : W, ∑ j ∈ range (Fintype.card V), ∑ v : W,
          if u ∈ layer f j ∧ v ∈ layer f j ∧ F.Adj u v then 1 else 0 := sum_congr rfl (fun _ _ => sum_comm)
      _ = ∑ j ∈ range (Fintype.card V), ∑ u : W, ∑ v : W,
          if u ∈ layer f j ∧ v ∈ layer f j ∧ F.Adj u v then 1 else 0 := sum_comm
      _ = ∑ j ∈ range (Fintype.card V), 2*Nat.card (F.induce (layer f j : Set W)).edgeSet := by
        exact sum_congr rfl (fun j _ => (induced_twice_edges F (layer f j)).symm)
      _ = _ := (mul_sum _ _ _).symm
  rw [he] at hsum
  omega

/-- Only the target is required to avoid H. Each induced target layer
inherits that freeness; no freeness of their disjoint union is presumed. -/
theorem extremal_layers {T : Type*} (H : SimpleGraph T) (f : G →g F)
    (hLocal : ∀ x, Function.Injective (neighborMap f x)) (hFree : H.Free F) :
    Nat.card G.edgeSet ≤ ∑ j ∈ range (Fintype.card V), extremalNumber (layer f j).card H := by
  apply (edge_layers f hLocal).trans
  apply sum_le_sum
  intro j _
  have hf : H.Free (F.induce (layer f j : Set W)) := fun hh => hFree (hh.trans ⟨Copy.induce F _⟩)
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card,Nat.card_coe_set_eq,Set.ncard_coe_finset] using
    card_edgeFinset_le_extremalNumber hf

#print axioms block_le
#print axioms layer_vertices
#print axioms edge_layers
#print axioms extremal_layers
end Erdos713LocallyInjectiveLayers
