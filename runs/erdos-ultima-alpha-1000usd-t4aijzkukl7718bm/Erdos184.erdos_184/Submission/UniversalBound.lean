import Submission.UniversalConnectedBase
import Submission.VertexSeparatorReduction

/-! The linear cycle-and-edge bound for graphs with a universal vertex. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.UniversalCycles
open Critical SparseCuts
set_option maxHeartbeats 2000000
universe u
variable {V : Type*} [Fintype V]

noncomputable def canonicalNumber {W : Type*} [Finite W] (G : SimpleGraph W) : ℕ :=
  @number W (Fintype.ofFinite W) G

lemma number_fintype_normalize (G : SimpleGraph V) :
    number G = canonicalNumber G := by
  exact congrArg (fun i : Fintype V => @number V i G) (Subsingleton.elim _ _)

lemma split_at_vertex (G : SimpleGraph V) (A B : Set V) (v : V)
    (hu : A ∪ B = Set.univ) (hi : A ∩ B = {v})
    (hx : ∀ x ∈ A \ B, ∀ y ∈ B \ A, ¬ G.Adj x y) :
    number G ≤ number (G.induce A) + number (G.induce B) := by
  let K := (G.induce A).spanningCoe
  let R := (G.induce B).spanningCoe
  have hKG : K ≤ G := G.spanningCoe_induce_le A
  have hRG : R ≤ G := G.spanningCoe_induce_le B
  have he : K ⊔ R = G := by
    apply le_antisymm (sup_le hKG hRG)
    intro x y hxy
    have hab (z : V) : z ∈ A ∨ z ∈ B := by
      change z ∈ A ∪ B
      rw [hu]
      trivial
    by_cases hxa : x ∈ A
    · by_cases hya : y ∈ A
      · exact Or.inl ((spanningCoe_induce_adj G A x y).mpr ⟨hxy,hxa,hya⟩)
      · have hyb := (hab y).resolve_left hya
        have hxb : x ∈ B := by
          by_contra hn
          exact hx x ⟨hxa,hn⟩ y ⟨hyb,hya⟩ hxy
        exact Or.inr ((spanningCoe_induce_adj G B x y).mpr ⟨hxy,hxb,hyb⟩)
    · have hxb := (hab x).resolve_left hxa
      have hyb : y ∈ B := by
        by_contra hn
        exact hx y ⟨(hab y).resolve_right hn,hn⟩ x ⟨hxb,hxa⟩ hxy.symm
      exact Or.inr ((spanningCoe_induce_adj G B x y).mpr ⟨hxy,hxb,hyb⟩)
  have hd : Disjoint K.edgeSet R.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heK heR
    induction e using Sym2.ind with | h x y =>
    have hk := (spanningCoe_induce_adj G A x y).mp heK
    have hr := (spanningCoe_induce_adj G B x y).mp heR
    have hxx : x = v := Set.mem_singleton_iff.mp (hi ▸ (show x ∈ A ∩ B from ⟨hk.2.1,hr.2.1⟩))
    have hyy : y = v := Set.mem_singleton_iff.mp (hi ▸ (show y ∈ A ∩ B from ⟨hk.2.2,hr.2.2⟩))
    exact hk.1.ne (hxx.trans hyy.symm)
  obtain ⟨D,hD,hdD,hcD⟩ := exists_minimum K
  obtain ⟨E,hE,hdE,hcE⟩ := exists_minimum R
  obtain ⟨F,hF,hdF,hcF⟩ := combine_decompositions hKG hRG hd
    (by rw [← SimpleGraph.edgeSet_sup,he]) D E hD hdD hE hdE
  have hb := number_le F hF hdF
  have hk := VertexSeparators.number_spanning_le (G.induce A)
  have hr := VertexSeparators.number_spanning_le (G.induce B)
  change number K ≤ _ at hk
  change number R ≤ _ at hr
  omega

lemma universal_bound : ∀ {W : Type u} [Fintype W] (G : SimpleGraph W) (v : W),
    (∀ x : W, x ≠ v → G.Adj v x) → number G ≤ 3 * (Fintype.card W - 1) := by
  have main : ∀ n : ℕ, ∀ {W : Type u} [Fintype W] (G : SimpleGraph W) (v : W),
      Fintype.card W = n → (∀ x : W, x ≠ v → G.Adj v x) → number G ≤ 3 * (n-1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ G v hW hv
      cases isEmpty_or_nonempty (Rest v) with
      | inl hEmpty =>
        have he : G = ⊥ := by
          ext x y
          have hx : x = v := by by_contra hx; exact isEmptyElim (⟨x,hx⟩ : Rest v)
          have hy : y = v := by by_contra hy; exact isEmptyElim (⟨y,hy⟩ : Rest v)
          simp [hx,hy]
        simp [he,number_bot]
      | inr hNonempty =>
        by_cases hc : (Base (G := G) v).Preconnected
        · simpa only [hW] using universal_connected_base_bound v hv ⟨hc⟩
        · change ¬ ∀ a b : Rest v, (Base (G := G) v).Reachable a b at hc
          push_neg at hc
          obtain ⟨a,b,hab⟩ := hc
          let S : Set W := {x | ∃ hx : x ≠ v, (Base (G := G) v).Reachable a ⟨x,hx⟩}
          let A : Set W := insert v S
          let B : Set W := insert v Sᶜ
          have haS : a.val ∈ S := ⟨a.property,.rfl⟩
          have hbS : b.val ∉ S := by rintro ⟨_,h⟩; exact hab h
          have hvA : v ∈ A := Set.mem_insert _ _
          have hvB : v ∈ B := Set.mem_insert _ _
          have hA : A ≠ Set.univ := by
            intro he
            have hb : b.val ∈ A := he.symm ▸ Set.mem_univ _
            exact hb.elim b.property hbS
          have hB : B ≠ Set.univ := by
            intro he
            have ha : a.val ∈ B := he.symm ▸ Set.mem_univ _
            exact ha.elim a.property (fun h => h haS)
          have hu : A ∪ B = Set.univ := by
            ext x
            simp only [A,B,Set.mem_union,Set.mem_insert_iff,Set.mem_compl_iff,Set.mem_univ,iff_true]
            tauto
          have hi : A ∩ B = {v} := by
            ext x
            simp only [A,B,Set.mem_inter_iff,Set.mem_insert_iff,Set.mem_compl_iff,Set.mem_singleton_iff]
            tauto
          have hcross : ∀ x ∈ A \ B, ∀ y ∈ B \ A, ¬ G.Adj x y := by
            intro x hx y hy hxy
            have hxv : x ≠ v := fun h => hx.2 (h ▸ hvB)
            have hyv : y ≠ v := fun h => hy.2 (h ▸ hvA)
            have hxS : x ∈ S := hx.1.resolve_left hxv
            have hyS : y ∉ S := fun h => hy.2 (Or.inr h)
            obtain ⟨_,hr⟩ := hxS
            exact hyS ⟨hyv,hr.trans (show (Base (G := G) v).Adj ⟨x,hxv⟩ ⟨y,hyv⟩ from hxy).reachable⟩
          have hsmallA : Fintype.card A < n := by
            obtain ⟨x,hx⟩ := Set.nonempty_compl.mpr hA
            exact (Fintype.card_subtype_lt hx).trans_eq hW
          have hsmallB : Fintype.card B < n := by
            obtain ⟨x,hx⟩ := Set.nonempty_compl.mpr hB
            exact (Fintype.card_subtype_lt hx).trans_eq hW
          have hnA := ih _ hsmallA (G.induce A) ⟨v,hvA⟩ rfl (by
            intro x hx
            exact hv x.val (fun h => hx (Subtype.ext h)))
          have hnB := ih _ hsmallB (G.induce B) ⟨v,hvB⟩ rfl (by
            intro x hx
            exact hv x.val (fun h => hx (Subtype.ext h)))
          have hsum := Set.ncard_union_add_ncard_inter A B
          rw [hu,hi,Set.ncard_univ,Set.ncard_singleton] at hsum
          have hposA : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨⟨v,hvA⟩⟩
          have hposB : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ⟨⟨v,hvB⟩⟩
          have hn := split_at_vertex G A B v hu hi hcross
          simp only [← Nat.card_eq_fintype_card] at hsum hnA hnB hW hposA hposB
          simp only [← Nat.card_coe_set_eq] at hsum
          simp only [number_fintype_normalize] at hn hnA hnB ⊢
          omega
  intro W _ G v hv
  exact main _ G v rfl hv

end Erdos184Work.UniversalCycles
#print axioms Erdos184Work.UniversalCycles.universal_bound
