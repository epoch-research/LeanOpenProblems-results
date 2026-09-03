import Submission.HeptagonSplitFinite

/-! Expansion and coordinates for the exceptional split-gap certificates. -/
namespace Erdos583HeptagonSplitRoutesDevelopment
open SimpleGraph Erdos583Work Erdos583Work.PieceRoutes
open Erdos583HeptagonRoutesDevelopment (Exceptional)
set_option maxHeartbeats 2000000

lemma extended_zero (p : Fin 6 → Fin 6) : extended p 0=(p 0).castSucc.castSucc := by
  simp [extended]

lemma extended_last (p : Fin 6 → Fin 6) : extended p 6=(p 5).castSucc.castSucc := by
  simp [extended]

lemma extended_injective (p : Fin 6 → Fin 6) (hp : Function.Injective p) :
    Function.Injective (extended p) := by
  intro i j he
  have hh := congrArg Fin.val he
  unfold extended at hh
  split_ifs at hh <;> simp only [Fin.val_castSucc] at hh
  all_goals first
    | exact Fin.ext (by omega)
    | have h := congrArg Fin.val (hp (Fin.ext hh)); exact Fin.ext (by dsimp at h; omega)

lemma extended_visit (p : Fin 6 → Fin 6) (hp : Function.Injective p) (x : Fin 8) (hx : x ≠ 6) :
    ∃ i, extended p i=x := by
  by_cases h7 : x=7
  · exact ⟨2, by simp [extended,h7]⟩
  have hlt : x.val < 6 := by
    have h6 : x.val ≠ 6 := fun he ↦ hx (Fin.ext he)
    have h7' : x.val ≠ 7 := fun he ↦ h7 (Fin.ext he)
    omega
  obtain ⟨j,hj⟩ := (Finite.injective_iff_surjective.mp hp) ⟨x.val,hlt⟩
  by_cases hj1 : j.val ≤ 1
  · refine ⟨⟨j.val,by omega⟩,?_⟩
    simp only [extended,hj1,↓reduceDIte]
    exact Fin.ext (congrArg (fun y : Fin 6 ↦ y.val) hj)
  · refine ⟨⟨j.val+1,by omega⟩,?_⟩
    simp only [extended,show ¬j.val+1 ≤ 1 by omega,show j.val+1 ≠ 2 by omega,↓reduceDIte,
      ↓reduceIte,Nat.add_sub_cancel]
    exact Fin.ext (congrArg (fun y : Fin 6 ↦ y.val) hj)

lemma cycle_source (p : Fin 6 → Fin 6) (i : Fin 7) :
    pieceSource p (Fin.castAdd 6 i)=i.castSucc := by simp [pieceSource,i.isLt]

lemma cycle_target (p : Fin 6 → Fin 6) (i : Fin 7) :
    pieceTarget p (Fin.castAdd 6 i)=(⟨(i.val+1)%7,Nat.mod_lt _ (by decide)⟩ : Fin 7).castSucc := by
  simp [pieceTarget,i.isLt]

lemma path_source (p : Fin 6 → Fin 6) (i : Fin 6) :
    pieceSource p (Fin.natAdd 7 i)=extended p i.castSucc := by
  simp [pieceSource,Fin.natAdd,Nat.add_comm]
  rfl

lemma path_target (p : Fin 6 → Fin 6) (i : Fin 6) :
    pieceTarget p (Fin.natAdd 7 i)=extended p i.succ := by
  simp [pieceTarget,Fin.natAdd,Nat.add_comm]
  rfl

lemma expand_certificate {V : Type*} {G : SimpleGraph V}
    (p : Fin 6 → Fin 6) (hp : Function.Injective p) (hex : Exceptional p)
    (f : Fin 8 → V) (hf : Function.Injective f)
    (R : ∀ e : Fin 13, G.Walk (f (pieceSource p e)) (f (pieceTarget p e)))
    (hpath : ∀ e, (R e).IsPath)
    (hcore : ∀ e x, f x ∈ (R e).support → x=pieceSource p e ∨ x=pieceTarget p e)
    (hinter : ∀ e j, e ≠ j → ∀ x ∈ (R e).support, x ∈ (R j).support → ∃ a, x=f a)
    (hdis : ∀ e j, e ≠ j → Disjoint (R e).toSubgraph.edgeSet (R j).toSubgraph.edgeSet) :
    ∃ X : G.Walk (f (p 0).castSucc.castSucc) (f 7),
    ∃ Y : G.Walk (f (p 5).castSucc.castSucc) (f 7),
      X.IsPath ∧ Y.IsPath ∧ Disjoint X.toSubgraph.edgeSet Y.toSubgraph.edgeSet ∧
        X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet=⋃ e, (R e).toSubgraph.edgeSet := by
  obtain ⟨X,Y,hX,hY,hd,hc⟩ := exists_routes p hp hex
  exact ⟨X.expand f R,Y.expand f R,Route.expand_two_cover f R hf hpath hcore hinter hdis X Y hX hY hd hc⟩

lemma extend_injective {V : Type*} {n : ℕ} (c : Fin n → V) (hc : Function.Injective c)
    (z : V) (hz : ∀ i, z ≠ c i) :
    Function.Injective (Fin.lastCases z c : Fin (n+1) → V) := by
  intro i j he
  revert he
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · intro _; rfl
    · intro he; exact (hz j (by simpa using he)).elim
  · refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · intro he; exact (hz i (by simpa using he.symm)).elim
    · intro he
      exact congrArg Fin.castSucc (hc (by simpa using he))

lemma inserted_coordinates {V : Type*} {G : SimpleGraph V} {a b : V}
    (P : G.Walk a b) (c : Fin 7 → V) (h : Fin 6 → ℕ) (p : Fin 6 → Fin 6)
    (hc : ∀ i, P.getVert (h i)=c (p i).castSucc) (m : ℕ) (z : V) (hz : P.getVert m=z) :
    ∀ i : Fin 7, P.getVert (HexagonExcursionCoordinates.insertCut h 1 m i)=
      (Fin.lastCases z c : Fin 8 → V) (extended p i) := by
  intro i
  unfold HexagonExcursionCoordinates.insertCut extended
  simp only [Fin.val_one]
  split_ifs <;> simp [hz,hc]
  rfl

end Erdos583HeptagonSplitRoutesDevelopment
