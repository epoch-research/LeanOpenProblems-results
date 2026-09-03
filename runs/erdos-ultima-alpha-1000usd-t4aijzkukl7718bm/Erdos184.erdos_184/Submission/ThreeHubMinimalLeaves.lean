import Submission.OptimalSingletonForest
import Submission.MaximizerReachability
import Submission.ParityDegreeLower

/-! Necessary structure of globally minimal graphs with three hubs.
This does not establish the original linear decomposition conjecture. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ThreeHubMinimalLeaves
open Critical EdgeHull SingletonExchange
set_option maxHeartbeats 1200000
variable {A B : Type*} [Fintype A] [Fintype B]

lemma degree_right {G : SimpleGraph (A ⊕ B)}
    (hG : G ≤ completeBipartiteGraph A B) (b : B) :
    Nat.card (G.neighborSet (.inr b)) =
      Nat.card {a : A // G.Adj (.inr b) (.inl a)} := by
  let f : {a : A // G.Adj (.inr b) (.inl a)} → G.neighborSet (.inr b) :=
    fun a => ⟨.inl a.val,a.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact Sum.inl.inj (congrArg Subtype.val h)
    · rintro ⟨x,hx⟩
      cases x with
      | inl a => exact ⟨⟨a,hx⟩,rfl⟩
      | inr c => simpa [completeBipartiteGraph] using hG hx
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

lemma degree_right_full (b : B) :
    Nat.card ((completeBipartiteGraph A B).neighborSet (.inr b)) = Fintype.card A := by
  rw [degree_right le_rfl]
  simp [completeBipartiteGraph]

variable {G : SimpleGraph (Fin 3 ⊕ B)}

/-- Degree-two vertices on the independent side induce bridge paths through
only three hubs. There can be at most two such vertices. -/
lemma degree_two_card_le (hm : Minimal G)
    (hG : G ≤ completeBipartiteGraph (Fin 3) B) :
    Nat.card {b : B // G.degree (.inr b) = 2} ≤ 2 := by
  let T := {b : B // G.degree (.inr b) = 2}
  let e : Fin 3 ⊕ T ↪ Fin 3 ⊕ B :=
    ⟨Sum.map id Subtype.val, by
      intro x y h
      cases x <;> cases y <;> simp_all
      exact Subtype.ext h⟩
  let M := G.comap e
  let f : M ↪g G := SimpleGraph.Embedding.comap e G
  have hM : M ≤ completeBipartiteGraph (Fin 3) T := by
    intro x y hxy
    have hh := hG hxy
    cases x <;> cases y <;> simpa [M,e,completeBipartiteGraph] using hh
  have hacy : M.IsAcyclic := by
    intro x p hp
    have hpG := hp.map (f := f.toHom) f.injective
    have hleaf (b : T) (hb : .inr b ∈ p.support) : False := by
      have hh := hm.cycle_vertex_degree hpG (v := .inr b.val) (by
        rw [Walk.support_map]
        exact List.mem_map.mpr ⟨.inr b,hb,rfl⟩)
      have he := b.property
      omega
    cases x with
    | inr b => exact hleaf b p.start_mem_support
    | inl a =>
      have hs := hM (p.adj_snd hp.not_nil)
      cases he : p.snd with
      | inl c => simp [he,completeBipartiteGraph] at hs
      | inr b =>
        apply hleaf b
        rw [← he]
        simpa using p.getVert_mem_support 1
  have hdeg (b : T) : M.degree (.inr b) = 2 := by
    have hn : Nat.card (M.neighborSet (.inr b)) = Nat.card (G.neighborSet (.inr b.val)) := by
      rw [degree_right hM,degree_right hG]
      rfl
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hn.trans (by
        simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
          using b.property)
  let L : Finset (Fin 3 ⊕ T) := Finset.univ.image Sum.inr
  have hL : L.card = Fintype.card T := by
    rw [Finset.card_image_of_injective _ Sum.inr_injective,Finset.card_univ]
  have hb := ParityDegreeLower.independent_degree_sum_le M L (by
    intro x hx y hy hxy
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hy
    simpa [completeBipartiteGraph] using hM hxy)
  have hd : (∑ v ∈ L, M.degree v) = 2 * Fintype.card T := by
    calc
      _ = ∑ _v ∈ L, 2 := Finset.sum_congr rfl (by
        intro v hv
        obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hv
        exact hdeg b)
      _ = _ := by simp [hL,mul_comm]
  have hu := acyclic_card_edges_lt M hacy
  rw [hd] at hb
  simp only [Fintype.card_sum,Fintype.card_fin] at hu
  simp only [← Nat.card_eq_fintype_card] at hb hu
  change Nat.card T ≤ 2
  omega

/-- Almost every vertex on the independent side must be odd, and each of
these vertices forces a different singleton edge in an optimal split. -/
lemma optimal_singleton_lower (hm : Minimal G)
    (hG : G ≤ completeBipartiteGraph (Fin 3) B) (hc : G.Connected)
    {F : SimpleGraph (Fin 3 ⊕ B)} (hf : Optimal G F) :
    Fintype.card B ≤ Nat.card F.edgeSet + 2 := by
  letI : Nontrivial (Fin 3 ⊕ B) := ⟨⟨.inl 0,.inl 1,by simp⟩⟩
  let T : Finset B := Finset.univ.filter (fun b => G.degree (.inr b) = 2)
  let S : Finset B := Finset.univ \ T
  let L : Finset (Fin 3 ⊕ B) := S.image Sum.inr
  have ht : T.card ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype,T]
      using degree_two_card_le hm hG
  have hs : S.card + T.card = Fintype.card B := by
    simpa only [S,Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  have hl : L.card = S.card := Finset.card_image_of_injective _ Sum.inr_injective
  have hd (b : B) (hb : b ∈ S) : 1 ≤ F.degree (.inr b) := by
    have hne : G.degree (.inr b) ≠ 2 := by
      simpa only [S,T,Finset.mem_sdiff,Finset.mem_univ,true_and,
        Finset.mem_filter,not_true_eq_false] using hb
    have hp := hc.preconnected.degree_pos_of_nontrivial (.inr b)
    have hu := SimpleGraph.degree_le_of_le hG (v := .inr b)
    have hh : Nat.card ((completeBipartiteGraph (Fin 3) B).neighborSet (.inr b)) = 3 := by
      simpa only [Fintype.card_fin] using degree_right_full (A := Fin 3) b
    simp only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hp hu hne ⊢
    have he := Nat.even_iff.mp (hf.2.1 (.inr b))
    have ha := degree_sdiff_add G F hf.1 (.inr b)
    simp only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at ha
    omega
  have hi := ParityDegreeLower.independent_degree_sum_le F L (by
    intro x hx y hy hxy
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hy
    simpa [completeBipartiteGraph] using hG (hf.1 hxy))
  have hb : L.card ≤ ∑ v ∈ L, F.degree v := by
    have h := Finset.sum_le_sum (s := L) (f := fun _ => 1) (g := fun v => F.degree v) (by
      intro v hv
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
      exact hd b hb)
    simpa only [Finset.sum_const,smul_eq_mul,mul_one] using h
  rw [hl] at hb
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hi
  omega

end Erdos184Work.ThreeHubMinimalLeaves
#print axioms Erdos184Work.ThreeHubMinimalLeaves.degree_two_card_le

#print axioms Erdos184Work.ThreeHubMinimalLeaves.optimal_singleton_lower
