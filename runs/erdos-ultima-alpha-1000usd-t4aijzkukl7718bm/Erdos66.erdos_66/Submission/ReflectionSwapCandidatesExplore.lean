import Submission.SparseOrderedSwapExplore

/-! Nearly flat windows provide many order-matched candidate swaps. Only a
bounded number fail to gain a representation at the reflection center. -/
namespace Erdos66ReflectionSwapCandidates
open AdditiveCombinatorics Erdos66ReflectionRoundingPatch Erdos66NatPairAlgebra
  Erdos66NaturalSidonExtraction Erdos66FiniteSwapAlgebra Erdos66OrderedPartialReplacement
  Erdos66Counting Erdos66Rounding Erdos66Generating Erdos66Explore
open scoped Classical
set_option maxHeartbeats 2600000

variable {α : Type*} [DecidableEq α]

lemma sdiff_card_difference (X Y : Finset α) :
    ((X\Y).card:ℝ)-(Y\X).card=(X.card:ℝ)-Y.card := by
  have h1 := Finset.card_sdiff_add_card_inter X Y
  have h2 := Finset.card_sdiff_add_card_inter Y X
  rw [Finset.inter_comm Y X] at h2
  have h1' : ((X\Y).card:ℝ)+(X∩Y).card=X.card := by exact_mod_cast h1
  have h2' : ((Y\X).card:ℝ)+(X∩Y).card=Y.card := by exact_mod_cast h2
  linarith

lemma sdiff_prefix_difference (X Y T : Finset α) :
    (((X\Y)∩T).card:ℝ)-((Y\X)∩T).card=((X∩T).card:ℝ)-(Y∩T).card := by
  have h1 : (X\Y)∩T=(X∩T)\(Y∩T) := by ext a; simp only [Finset.mem_inter,Finset.mem_sdiff]; tauto
  have h2 : (Y\X)∩T=(Y∩T)\(X∩T) := by ext a; simp only [Finset.mem_inter,Finset.mem_sdiff]; tauto
  rw [h1,h2,sdiff_card_difference]

lemma symmetric_difference_card (X Y : Finset α)
    (h : min X.card Y.card ≤ (X∩Y).card) :
    ((X\Y).card:ℝ)+(Y\X).card=|(X.card:ℝ)-Y.card| := by
  have h1 := Finset.card_sdiff_add_card_inter X Y
  have h2 := Finset.card_sdiff_add_card_inter Y X
  rw [Finset.inter_comm Y X] at h2
  have hiX := Finset.card_le_card (Finset.inter_subset_left (s₁ := X) (s₂ := Y))
  have hiY := Finset.card_le_card (Finset.inter_subset_right (s₁ := X) (s₂ := Y))
  by_cases hXY : X.card ≤ Y.card
  · rw [min_eq_left hXY] at h
    have he : (X\Y).card=0 := by omega
    have he' : (Y\X).card+X.card=Y.card := by omega
    have hr : (X.card:ℝ) ≤ Y.card := by exact_mod_cast hXY
    have hr' : ((Y\X).card:ℝ)+X.card=Y.card := by exact_mod_cast he'
    rw [he,Nat.cast_zero,zero_add,abs_of_nonpos (sub_nonpos.mpr hr)]
    linarith
  · have hYX : Y.card ≤ X.card := by omega
    rw [min_eq_right hYX] at h
    have he : (Y\X).card=0 := by omega
    have he' : (X\Y).card+Y.card=X.card := by omega
    have hr : (Y.card:ℝ) ≤ X.card := by exact_mod_cast hYX
    have hr' : ((X\Y).card:ℝ)+Y.card=X.card := by exact_mod_cast he'
    rw [he,Nat.cast_zero,add_zero,abs_of_nonneg (sub_nonneg.mpr hr)]
    linarith

 theorem exists_reflection_swap_candidates (A : Set ℕ) (p : ℕ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hA : ∀ N, |(count A N:ℝ)-cumulative p N| ≤ D) (hp : Antitone p)
    (L W : ℕ) (hW : 0<W) (hosc : (2*W:ℕ)*(p L-p (L+2*W)) ≤ 1) :
    ∃ (M : ℕ) (x y : Fin M → ℕ) (B : Finset (Fin M)),
      StrictMono x ∧ StrictMono y ∧
      (∀ i, L+W ≤ x i ∧ x i<L+2*W ∧ x i∈A) ∧
      (∀ i, L+W ≤ y i ∧ y i<L+2*W ∧ y i∉A) ∧
      ((B.card:ℝ) ≤ 4*D+1) ∧
      ((intervalPart A (L+W) (L+2*W)).card:ℝ)-sumRep A (2*L+2*W-1)-(4*D+1) ≤ M ∧
      (∀ N, |(((Finset.univ.image y∩Finset.range N).card:ℝ)-
        (Finset.univ.image x∩Finset.range N).card)| ≤ 8*D+2) ∧
      (∀ i∉B, (x i ≤ 2*L+2*W-1 → 2*L+2*W-1-x i∉A) ∧
        (y i ≤ 2*L+2*W-1 ∧ 2*L+2*W-1-y i∈A)) := by
  let F := intervalPart A L (L+W)
  let R := intervalPart A (L+W) (L+2*W)
  let t := 2*L+2*W-1
  let Q := natReflect t F
  obtain ⟨G,hG,hGc,hpref,hpeak⟩ := exists_reflection_patch A p D hD hA hp L W hW hosc
  have hQ : Q⊆Finset.Ico (L+W) (L+2*W) := reflected_interval_bounds A L W hW
  have hQc : Q.card=F.card := reflected_card A L W hW
  have hFt : ∀ a∈F, a ≤ t := by
    intro a ha
    have hh := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
    dsimp only [t]
    omega
  have hFG : Disjoint F G := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have ha' := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
    have hb' := Finset.mem_Ico.mp (hG hb)
    omega
  have hFF : sumRep (F:Set ℕ) t=0 := by
    rw [←pairs_self,pairs,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
    intro a ha he
    have h1 := Finset.mem_Ico.mp (Finset.mem_filter.mp (Finset.mem_product.mp ha).1).1
    have h2 := Finset.mem_Ico.mp (Finset.mem_filter.mp (Finset.mem_product.mp ha).2).1
    dsimp only [t] at he
    omega
  have hGG : sumRep (G:Set ℕ) t=0 := by
    rw [←pairs_self]
    apply pairs_above_half
    all_goals intro a ha; have hh := Finset.mem_Ico.mp (hG ha); dsimp only [t]; omega
  have hinter : min Q.card G.card ≤ (Q∩G).card := by
    change 2*min F.card R.card ≤ sumRep ((F∪G:Finset ℕ):Set ℕ) t at hpeak
    rw [sumRep_union_self F G t hFG,hFF,hGG,reflected_pairs_card F G t hFt] at hpeak
    rw [hQc,hGc]
    change min F.card R.card ≤ (natReflect t F∩G).card
    omega
  have hdist : ((G\Q).card:ℝ)+(Q\G).card ≤ 4*D+1 := by
    rw [symmetric_difference_card G Q (by simpa only [min_comm,Finset.inter_comm] using hinter),hGc,hQc]
    have hh := equal_length_counts_close A p D hA hp L (L+2*W) (L+W) L W
      (by omega) le_rfl (by omega) (by omega) (by simpa using hosc)
    simpa only [R,F,show L+W+W=L+2*W by omega] using hh
  let X := R\G
  let Y := G\R
  have hXY : X.card=Y.card := by
    have hh := sdiff_card_difference R G
    rw [hGc] at hh
    have he : (X.card:ℝ)=(Y.card:ℝ) := by dsimp only [X,Y]; linarith
    exact_mod_cast he
  let x := X.orderEmbOfFin rfl
  let y := Y.orderEmbOfFin hXY.symm
  let Bx : Finset (Fin X.card) := Finset.univ.filter (fun i ↦ x i∈Q)
  let By : Finset (Fin X.card) := Finset.univ.filter (fun i ↦ y i∉Q)
  let B := Bx∪By
  have hxmem (i : Fin X.card) : x i∈X := Finset.orderEmbOfFin_mem X rfl i
  have hymem (i : Fin X.card) : y i∈Y := Finset.orderEmbOfFin_mem Y hXY.symm i
  have hxA (i : Fin X.card) : L+W ≤ x i ∧ x i<L+2*W ∧ x i∈A := by
    have hh := Finset.mem_filter.mp (Finset.mem_sdiff.mp (hxmem i)).1
    exact ⟨(Finset.mem_Ico.mp hh.1).1,(Finset.mem_Ico.mp hh.1).2,hh.2⟩
  have hyA (i : Fin X.card) : L+W ≤ y i ∧ y i<L+2*W ∧ y i∉A := by
    have hh := Finset.mem_sdiff.mp (hymem i)
    have hyb := Finset.mem_Ico.mp (hG hh.1)
    refine ⟨hyb.1,hyb.2,?_⟩
    intro hiA
    exact hh.2 (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hyb,hiA⟩)
  have hBx : Bx.card ≤ (Q\G).card := by
    rw [←Finset.card_image_of_injective Bx x.injective]
    apply Finset.card_le_card
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hi).2,(Finset.mem_sdiff.mp (hxmem i)).2⟩
  have hBy : By.card ≤ (G\Q).card := by
    rw [←Finset.card_image_of_injective By y.injective]
    apply Finset.card_le_card
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp (hymem i)).1,(Finset.mem_filter.mp hi).2⟩
  refine ⟨X.card,x,y,B,x.strictMono,y.strictMono,hxA,hyA,?_,?_,?_,?_⟩
  · have hh : B.card ≤ (Q\G).card+(G\Q).card :=
      (Finset.card_union_le Bx By).trans (Nat.add_le_add hBx hBy)
    have hh' : (B.card:ℝ) ≤ (Q\G).card+(G\Q).card := by exact_mod_cast hh
    linarith
  · have hRG : R∩G⊆(R∩Q)∪(G\Q) := by
      intro a ha
      obtain ⟨haR,haG⟩ := Finset.mem_inter.mp ha
      by_cases haQ : a∈Q
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨haR,haQ⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨haG,haQ⟩)
    have hFR : Disjoint F R := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      have ha' := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
      have hb' := Finset.mem_Ico.mp (Finset.mem_filter.mp hb).1
      omega
    have hsub : ((F∪R:Finset ℕ):Set ℕ)⊆A := by
      intro a ha
      change a∈F∪R at ha
      rcases Finset.mem_union.mp ha with ha | ha <;> exact (Finset.mem_filter.mp ha).2
    have hr := sumRep_mono hsub t
    rw [sumRep_union_self F R t hFR,reflected_pairs_card F R t hFt] at hr
    have hRQ : (R∩Q).card ≤ sumRep A t := by
      rw [Finset.inter_comm]
      change (natReflect t F∩R).card ≤ sumRep A t
      omega
    have hcard := (Finset.card_le_card hRG).trans (Finset.card_union_le _ _)
    have hx := Finset.card_sdiff_add_card_inter R G
    have hmass : R.card ≤ X.card+sumRep A t+(G\Q).card := by dsimp only [X]; omega
    have hmass' : (R.card:ℝ) ≤ X.card+sumRep A t+(G\Q).card := by exact_mod_cast hmass
    have hn : (0:ℝ) ≤ (Q\G).card := Nat.cast_nonneg _
    change (R.card:ℝ)-sumRep A t-(4*D+1) ≤ X.card
    linarith
  · intro N
    rw [Finset.image_orderEmbOfFin_univ X rfl,Finset.image_orderEmbOfFin_univ Y hXY.symm]
    change |(((G\R)∩Finset.range N).card:ℝ)-((R\G)∩Finset.range N).card| ≤ _
    rw [sdiff_prefix_difference]
    exact hpref N
  · intro i hi
    have hxi : x i∉Q := by
      intro hh
      exact hi (Finset.mem_union_left By (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩))
    have hyi : y i∈Q := by
      by_contra hh
      exact hi (Finset.mem_union_right Bx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩))
    constructor
    · intro hxt hxpartner
      have hxb := hxA i
      have hpF : t-x i∈F := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Ico.mpr ⟨?_,?_⟩,hxpartner⟩ <;> dsimp only [t] <;> omega
      exact hxi ((mem_natReflect_iff F t (x i) hFt).mpr ⟨hxt,hpF⟩)
    · obtain ⟨hyt,hyF⟩ := (mem_natReflect_iff F t (y i) hFt).mp hyi
      exact ⟨hyt,(Finset.mem_filter.mp hyF).2⟩

end Erdos66ReflectionSwapCandidates
