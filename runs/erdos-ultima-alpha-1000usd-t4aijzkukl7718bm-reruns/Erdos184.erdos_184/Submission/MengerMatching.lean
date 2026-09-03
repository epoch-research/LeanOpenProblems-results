import FormalConjecturesUtil

/-!
A finite Hall-matching formulation of vertex-disjoint paths. Source and sink
copies provide the endpoint multiplicities; internal vertices have unit capacity.
This file is independent of the conjecture definitions.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.MengerMatching

variable {V : Type*} [Fintype V]

abbrev Internal (u v : V) := {x : V // x ≠ u ∧ x ≠ v}
abbrev Node (k : ℕ) (u v : V) := Fin k ⊕ Internal u v

def source {k : ℕ} {u v : V} : Node k u v → V
  | .inl _ => u
  | .inr x => x.val

def target {k : ℕ} {u v : V} : Node k u v → V
  | .inl _ => v
  | .inr x => x.val

def Rel (G : SimpleGraph V) (k : ℕ) (u v : V) (x y : Node k u v) : Prop :=
  (∃ w : Internal u v, x = .inr w ∧ y = .inr w) ∨ G.Adj (source x) (target y)

omit [Fintype V] in
lemma reachable_closed {G : SimpleGraph V} {P : V → Prop}
    (hclosed : ∀ x y, P x → G.Adj x y → P y) {u v : V}
    (hu : P u) (h : G.Reachable u v) : P v := by
  have hw : ∀ {a b : V}, G.Walk a b → P a → P b := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons a b c hab p ih => exact fun ha => ih (hclosed a b ha hab)
  exact hw h.some hu

/-- If no set of fewer than k internal vertices separates u and v, the
unit-capacity matching system has a supported permutation. -/
lemma exists_supported_permutation (G : SimpleGraph V) (k : ℕ) {u v : V}
    (huv : u ≠ v)
    (hconn : ∀ S : Set V, S.ncard < k → (hu : u ∉ S) → (hv : v ∉ S) →
      (G.induce Sᶜ).Reachable ⟨u,hu⟩ ⟨v,hv⟩) :
    ∃ f : Equiv.Perm (Node k u v), ∀ x, Rel G k u v x (f x) := by
  have hhall : ∀ A : Finset (Node k u v),
      A.card ≤ (Finset.univ.filter (fun y => ∃ x ∈ A, Rel G k u v x y)).card := by
    intro A
    let N : Finset (Node k u v) := Finset.univ.filter (fun y => ∃ x ∈ A, Rel G k u v x y)
    have hN (y : Node k u v) : y ∈ N ↔ ∃ x ∈ A, Rel G k u v x y := by simp [N]
    have hright : A.toRight ⊆ N.toRight := by
      intro x hx
      apply Finset.mem_toRight.mpr
      exact (hN _).mpr ⟨.inr x,Finset.mem_toRight.mp hx,Or.inl ⟨x,rfl,rfl⟩⟩
    have hAr := A.card_toLeft_add_card_toRight
    have hNr := N.card_toLeft_add_card_toRight
    have hrightcard := Finset.card_le_card hright
    have hleftcard : A.toLeft.card ≤ k := (Finset.card_le_univ _).trans_eq (Fintype.card_fin k)
    by_contra! hbad
    change N.card < A.card at hbad
    have hApos : 0 < A.toLeft.card := by omega
    obtain ⟨i,hi⟩ := Finset.card_pos.mp hApos
    have hleftempty : N.toLeft = ∅ := by
      by_contra hn
      obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr hn
      obtain ⟨x,hx,hr⟩ := (hN _).mp (Finset.mem_toLeft.mp hj)
      have hadj : G.Adj (source x) v := by
        rcases hr with ⟨w,_,h⟩ | h
        · cases h
        · exact h
      have hall : N.toLeft = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro t
        apply Finset.mem_toLeft.mpr
        exact (hN _).mpr ⟨x,hx,Or.inr hadj⟩
      have hc : N.toLeft.card = k := by rw [hall,Finset.card_univ,Fintype.card_fin]
      omega
    have hnc : N.toLeft.card = 0 := by rw [hleftempty]; rfl
    have hdiff : (N.toRight \ A.toRight).card < k := by
      rw [Finset.card_sdiff_of_subset hright]
      omega
    let T : Finset V := (N.toRight \ A.toRight).image Subtype.val
    have hTcard : (T : Set V).ncard < k := by
      rw [Set.ncard_coe_finset]
      exact Finset.card_image_le.trans_lt hdiff
    have huT : u ∉ (T : Set V) := by
      rintro hx
      obtain ⟨x,_,hxu⟩ := Finset.mem_image.mp hx
      exact x.property.1 hxu
    have hvT : v ∉ (T : Set V) := by
      rintro hx
      obtain ⟨x,_,hxv⟩ := Finset.mem_image.mp hx
      exact x.property.2 hxv
    let Q : V → Prop := fun x => x = u ∨ ∃ hx : x ≠ u ∧ x ≠ v,
      (⟨x,hx⟩ : Internal u v) ∈ A.toRight
    have huQ : Q u := Or.inl rfl
    have hvQ : ¬Q v := by
      rintro (h | ⟨hx,_⟩)
      · exact huv h.symm
      · exact hx.2 rfl
    have hclosed (x y : V) (hxQ : Q x) (hxy : G.Adj x y) (hyT : y ∉ (T : Set V)) : Q y := by
      have hex : ∃ a ∈ A, source a = x := by
        rcases hxQ with rfl | ⟨hx,hxA⟩
        · exact ⟨.inl i,Finset.mem_toLeft.mp hi,rfl⟩
        · exact ⟨.inr ⟨x,hx⟩,Finset.mem_toRight.mp hxA,rfl⟩
      obtain ⟨a,ha,hax⟩ := hex
      by_cases hyu : y = u
      · exact Or.inl hyu
      by_cases hyv : y = v
      · subst y
        have hh : Sum.inl i ∈ N := (hN _).mpr ⟨a,ha,Or.inr (hax.symm ▸ hxy)⟩
        have hh' := Finset.mem_toLeft.mpr hh
        rw [hleftempty] at hh'
        simp at hh'
      let z : Internal u v := ⟨y,hyu,hyv⟩
      have hzN : z ∈ N.toRight := by
        apply Finset.mem_toRight.mpr
        exact (hN _).mpr ⟨a,ha,Or.inr (hax.symm ▸ hxy)⟩
      have hzA : z ∈ A.toRight := by
        by_contra hz
        apply hyT
        exact Finset.mem_image.mpr ⟨z,Finset.mem_sdiff.mpr ⟨hzN,hz⟩,rfl⟩
      exact Or.inr ⟨⟨hyu,hyv⟩,hzA⟩
    have hr := hconn (T : Set V) hTcard huT hvT
    have hh : Q v := reachable_closed (P := fun x : ↥((T : Set V)ᶜ) => Q x.val)
      (fun x y hx hxy => hclosed x.val y.val hx hxy y.property) huQ hr
    exact hvQ hh
  obtain ⟨f,hf,hrel⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective (Rel G k u v)).mp hhall
  exact ⟨Equiv.ofBijective f ⟨hf,Finite.surjective_of_injective hf⟩,hrel⟩

end Erdos184.MengerMatching
