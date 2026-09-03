import Submission.FiniteSwapAlgebraExplore

/-! A finite count-preserving target repair chosen from order-matched candidate
moves. Explicit source-degree and selection-budget hypotheses are required. -/
namespace Erdos66SparseOrderedSwap
open AdditiveCombinatorics Erdos66OrderedPartialReplacement Erdos66FiniteSwapAlgebra
  Erdos66NatPairAlgebra Erdos66NaturalSidonExtraction Erdos66SidonSelection
  Erdos66UniformSelection Erdos66Counting
open scoped Classical
set_option maxHeartbeats 2600000

noncomputable def hitSet {M : ℕ} (A : Finset ℕ) (x : Fin M → ℕ) (n : ℕ) : Finset (Fin M) :=
  Finset.univ.filter (fun i ↦ x i ≤ n ∧ n-x i∈A)

 theorem exists_sparse_ordered_swap (A : Finset ℕ) (M k n : ℕ) (hM : 0<M)
    (x y : Fin M → ℕ) (hx : StrictMono x) (hy : StrictMono y)
    (hxA : ∀ i, x i∈A) (hyA : ∀ i, y i∉A)
    (hxhalf : ∀ i, n<2*x i) (hyhalf : ∀ i, n<2*y i)
    (B : Finset (Fin M))
    (hgood : ∀ i∉B, (x i ≤ n → n-x i∉A) ∧ (y i ≤ n ∧ n-y i∈A))
    (Δ : ℝ) (hpref : ∀ N,
      |(((Finset.univ.image y∩Finset.range N).card : ℝ)-(Finset.univ.image x∩Finset.range N).card)| ≤ Δ)
    (T : Finset ℕ) (K R t : ℝ)
    (hX : ∀ z∈T, ((hitSet A x z).card : ℝ) ≤ K)
    (hY : ∀ z∈T, ((hitSet A y z).card : ℝ) ≤ K) (ht : 0<t)
    (hsmall : ((k:ℝ)^4+k*B.card)/M+
      2*T.card*Real.exp ((k:ℝ)*Real.exp t*K/M-t*R)<1) :
    ∃ D F : Finset ℕ, D⊆A ∧ Disjoint A F ∧ D.card=k ∧ F.card=k ∧ NatSidon F ∧
      (∀ N, |(count (swapped A D F : Set ℕ) N : ℝ)-count (A : Set ℕ) N| ≤ Δ) ∧
      sumRep (swapped A D F : Set ℕ) n=sumRep (A : Set ℕ) n+2*k ∧
      (∀ z∈T, |(sumRep (swapped A D F : Set ℕ) z : ℝ)-sumRep (A : Set ℕ) z| ≤ 2*R+2) := by
  letI : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  let Y : Fin M → ℤ := fun i ↦ y i
  have hYinj : Function.Injective Y := by
    intro i j he
    apply hy.injective
    dsimp only [Y] at he
    exact_mod_cast he
  let Q : Finset (ℕ × Bool) := T ×ˢ Finset.univ
  let S : ℕ × Bool → Finset (Fin M) := fun q ↦ if q.2 then hitSet A y q.1 else hitSet A x q.1
  have hS : ∀ q∈Q, ((S q).card : ℝ) ≤ K := by
    intro q hq
    have hz := (Finset.mem_product.mp hq).1
    cases hb : q.2 <;> simp only [S,hb,Bool.false_eq_true,if_false,if_true]
    · exact hX _ hz
    · exact hY _ hz
  have hbudget : ((Fintype.card (Fin k):ℝ)^4+Fintype.card (Fin k)*B.card)/Fintype.card (Fin M)+
      Q.card*Real.exp ((Fintype.card (Fin k):ℝ)*Real.exp t*K/Fintype.card (Fin M)-t*R)<1 := by
    simpa only [Q,Finset.card_product,Finset.card_univ,Fintype.card_bool,Fintype.card_fin,
      Nat.cast_mul,Nat.cast_ofNat,mul_comm (T.card:ℝ) 2] using hsmall
  obtain ⟨ω,hω,havoid,hsidon,hhits⟩ := exists_sidon_avoid_and_hits (ι := Fin k)
    Y hYinj B Q S K R t hS ht hbudget
  let D : Finset ℕ := Finset.univ.image (fun i : Fin k ↦ x (ω i))
  let F : Finset ℕ := Finset.univ.image (fun i : Fin k ↦ y (ω i))
  have hdx : Function.Injective (fun i : Fin k ↦ x (ω i)) := hx.injective.comp hω
  have hfy : Function.Injective (fun i : Fin k ↦ y (ω i)) := hy.injective.comp hω
  have hDA : D⊆A := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact hxA _
  have hAF : Disjoint A F := by
    apply Finset.disjoint_left.mpr
    intro a ha hf
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hf
    exact hyA _ ha
  have hDc : D.card=k := by dsimp only [D]; rw [Finset.card_image_of_injective _ hdx,Finset.card_univ,Fintype.card_fin]
  have hFc : F.card=k := by dsimp only [F]; rw [Finset.card_image_of_injective _ hfy,Finset.card_univ,Fintype.card_fin]
  have hFs : NatSidon F := by
    intro a ha b hb c hc d hd he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hd
    have hh := hsidon i j u v (by dsimp [Y]; exact_mod_cast he)
    rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
  refine ⟨D,F,hDA,hAF,hDc,hFc,hFs,?_,?_,?_⟩
  · let J : Finset (Fin M) := Finset.univ.image ω
    have heD : J.image x=D := by simp [J,D,Finset.image_image,Function.comp_def]
    have heF : J.image y=F := by simp [J,F,Finset.image_image,Function.comp_def]
    have hh := partial_swap_prefix_bound (A : Set ℕ) x y hx hy hxA hyA Δ hpref J
    simpa only [heD,heF,←swapped_coe] using hh
  · have hD0 : pairs D A n=0 := by
      apply pairs_eq_zero_of_no_partner
      intro a ha han
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
      exact (hgood _ (havoid i)).1 han
    have hFfull : pairs F A n=F.card := by
      apply pairs_eq_card_of_partner
      intro a ha
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
      exact (hgood _ (havoid i)).2
    have hFhalf : ∀ a∈F, n<2*a := by
      intro a ha
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
      exact hyhalf _
    have hDhalf : ∀ a∈D, n<2*a := by
      intro a ha
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
      exact hxhalf _
    have hFD := pairs_above_half F D n hFhalf hDhalf
    have hFF : sumRep (F : Set ℕ) n=0 := by rw [←pairs_self]; exact pairs_above_half F F n hFhalf hFhalf
    simpa only [hFc] using swapped_target_exact A D F hDA hAF n hD0 hFfull hFD hFF
  · intro z hz
    have hxd : (pairs D A z : ℝ)<R := by
      have hh := hhits (z,false) (Finset.mem_product.mpr ⟨hz,Finset.mem_univ _⟩)
      simp only [S,Bool.false_eq_true,if_false] at hh
      rw [image_pairs_hits x hx.injective ω hω A z]
      simpa only [hits,hitSet,Finset.mem_filter,Finset.mem_univ,true_and] using hh
    have hyf : (pairs F A z : ℝ)<R := by
      have hh := hhits (z,true) (Finset.mem_product.mpr ⟨hz,Finset.mem_univ _⟩)
      simp only [S,if_true] at hh
      rw [image_pairs_hits y hy.injective ω hω A z]
      simpa only [hits,hitSet,Finset.mem_filter,Finset.mem_univ,true_and] using hh
    have hu := sumRep_swapped_upper A D F hAF z
    have hl := sumRep_swapped_lower A D F hDA z
    have hs := natSidon_rep_le_two hFs z
    have hu' : (sumRep (swapped A D F : Set ℕ) z : ℝ) ≤
        sumRep (A : Set ℕ) z+2*(pairs F A z:ℝ)+(sumRep (F : Set ℕ) z:ℝ) := by exact_mod_cast hu
    have hl' : (sumRep (A : Set ℕ) z : ℝ) ≤
        sumRep (swapped A D F : Set ℕ) z+2*(pairs D A z:ℝ) := by exact_mod_cast hl
    have hs' : (sumRep (F : Set ℕ) z:ℝ) ≤ 2 := by exact_mod_cast hs
    rw [abs_le]
    constructor <;> linarith

end Erdos66SparseOrderedSwap
