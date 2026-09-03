import Submission.SetIntervalReplacementExplore

/-! Any subset of order-matched replacements inherits the full replacement's
prefix discrepancy bound. Removed and inserted supports must be disjoint. -/
namespace Erdos66OrderedPartialReplacement
open Erdos66Counting Erdos66Generating Erdos66Rounding Erdos66SetIntervalReplacement
open scoped Classical
set_option maxHeartbeats 2200000

variable {ι : Type*} [DecidableEq ι]

lemma inter_card_difference_le (S X Y : Finset ι) (hXY : X⊆Y) :
    |(((S∩X).card : ℝ)-((S∩Y).card : ℝ))| ≤ |(X.card : ℝ)-Y.card| := by
  have hsub : S∩X⊆S∩Y := Finset.inter_subset_inter_left hXY
  have hdiff : (S∩Y)\(S∩X)⊆Y\X := by
    intro a ha
    simp only [Finset.mem_sdiff,Finset.mem_inter] at ha ⊢
    tauto
  have hc := Finset.card_le_card hdiff
  have he := Finset.card_sdiff_add_card_eq_card hsub
  have he' := Finset.card_sdiff_add_card_eq_card hXY
  have hx : ((S∩X).card : ℝ) ≤ (S∩Y).card := by exact_mod_cast Finset.card_le_card hsub
  have hy : (X.card : ℝ) ≤ Y.card := by exact_mod_cast Finset.card_le_card hXY
  rw [abs_of_nonpos (sub_nonpos.mpr hx),abs_of_nonpos (sub_nonpos.mpr hy)]
  have hh : (S∩Y).card+X.card ≤ Y.card+(S∩X).card := by omega
  have hh' : ((S∩Y).card : ℝ)+X.card ≤ Y.card+(S∩X).card := by exact_mod_cast hh
  linarith

variable {m : ℕ}

noncomputable def cut (x : Fin m → ℕ) (N : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i ↦ x i<N)

lemma cuts_comparable (x y : Fin m → ℕ) (hx : Monotone x) (hy : Monotone y) (N : ℕ) :
    cut x N⊆cut y N ∨ cut y N⊆cut x N := by
  by_cases h : cut x N⊆cut y N
  · exact Or.inl h
  · right
    obtain ⟨i,hi,hiy⟩ := Finset.not_subset.mp h
    have hix : x i<N := (Finset.mem_filter.mp hi).2
    have hiy' : N ≤ y i := by simpa only [cut,Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hiy
    intro j hj
    have hjy : y j<N := (Finset.mem_filter.mp hj).2
    have hji : j ≤ i := by
      by_contra hn
      have hh := hy (le_of_lt (lt_of_not_ge hn))
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_le_of_lt (hx hji) hix⟩

lemma image_prefix_card (x : Fin m → ℕ) (hx : Function.Injective x)
    (S : Finset (Fin m)) (N : ℕ) :
    ((S.image x)∩Finset.range N).card=(S∩cut x N).card := by
  have he : (S.image x)∩Finset.range N=(S∩cut x N).image x := by
    ext a
    simp only [Finset.mem_inter,Finset.mem_image,Finset.mem_range,cut,Finset.mem_filter,
      Finset.mem_univ,true_and]
    constructor
    · rintro ⟨⟨i,hi,rfl⟩,hN⟩
      exact ⟨i,⟨hi,hN⟩,rfl⟩
    · rintro ⟨i,⟨hi,hN⟩,rfl⟩
      exact ⟨⟨i,hi,rfl⟩,hN⟩
  rw [he,Finset.card_image_of_injective _ hx]

lemma partial_prefix_difference_le (x y : Fin m → ℕ) (hx : StrictMono x) (hy : StrictMono y)
    (S : Finset (Fin m)) (N : ℕ) :
    |(((S.image y∩Finset.range N).card : ℝ)-(S.image x∩Finset.range N).card)| ≤
      |(((Finset.univ.image y∩Finset.range N).card : ℝ)-(Finset.univ.image x∩Finset.range N).card)| := by
  simp only [image_prefix_card _ hx.injective,image_prefix_card _ hy.injective,Finset.univ_inter]
  rcases cuts_comparable y x hy.monotone hx.monotone N with h | h
  · exact inter_card_difference_le S _ _ h
  · simpa only [abs_sub_comm] using inter_card_difference_le S _ _ h

noncomputable def swap (A : Set ℕ) (D F : Finset ℕ) : Set ℕ := (A \ (D : Set ℕ)) ∪ (F : Set ℕ)

lemma swap_count_difference (A : Set ℕ) (D F : Finset ℕ)
    (hD : (D : Set ℕ)⊆A) (hF : Disjoint (F : Set ℕ) A) (N : ℕ) :
    (count (swap A D F) N : ℝ)-count A N=
      ((F∩Finset.range N).card : ℝ)-(D∩Finset.range N).card := by
  rw [Erdos66SetIntervalReplacement.count_sum,Erdos66SetIntervalReplacement.count_sum,
    card_inter_sum,card_inter_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hd : i∈D → i∈A := fun hh ↦ hD hh
  have hf : i∈F → i∉A := fun hh hia ↦ Set.disjoint_left.mp hF hh hia
  simp only [indicator,swap,Set.mem_union,Set.mem_diff,Finset.mem_coe]
  split_ifs <;> norm_num <;> tauto

 theorem partial_swap_prefix_bound (A : Set ℕ) (x y : Fin m → ℕ)
    (hx : StrictMono x) (hy : StrictMono y) (hxA : ∀ i, x i∈A) (hyA : ∀ i, y i∉A)
    (D : ℝ) (hfull : ∀ N,
      |(((Finset.univ.image y∩Finset.range N).card : ℝ)-(Finset.univ.image x∩Finset.range N).card)| ≤ D)
    (S : Finset (Fin m)) :
    ∀ N, |(count (swap A (S.image x) (S.image y)) N : ℝ)-count A N| ≤ D := by
  intro N
  have hsub : (S.image x : Set ℕ)⊆A := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact hxA i
  have hdis : Disjoint (S.image y : Set ℕ) A := by
    apply Set.disjoint_left.mpr
    intro a ha hA
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact hyA i hA
  rw [swap_count_difference A (S.image x) (S.image y) hsub hdis]
  exact (partial_prefix_difference_le x y hx hy S N).trans (hfull N)

lemma partial_swap_card (x y : Fin m → ℕ) (hx : Function.Injective x) (hy : Function.Injective y)
    (S : Finset (Fin m)) : (S.image x).card=(S.image y).card := by
  simp only [Finset.card_image_of_injective _ hx,Finset.card_image_of_injective _ hy]

 theorem exists_ordered_swap_family (A : Set ℕ) (X Y : Finset ℕ)
    (hX : (X : Set ℕ)⊆A) (hY : Disjoint (Y : Set ℕ) A) (hcard : X.card=Y.card)
    (D : ℝ) (hpref : ∀ N, |((Y∩Finset.range N).card : ℝ)-(X∩Finset.range N).card| ≤ D) :
    ∃ x y : Fin X.card → ℕ, StrictMono x ∧ StrictMono y ∧
      Finset.univ.image x=X ∧ Finset.univ.image y=Y ∧
      (∀ S : Finset (Fin X.card), ∀ N,
        |(count (swap A (S.image x) (S.image y)) N : ℝ)-count A N| ≤ D) := by
  let x := X.orderEmbOfFin rfl
  let y := Y.orderEmbOfFin hcard.symm
  have hx : StrictMono x := x.strictMono
  have hy : StrictMono y := y.strictMono
  have hxi : Finset.univ.image x=X := Finset.image_orderEmbOfFin_univ X rfl
  have hyi : Finset.univ.image y=Y := Finset.image_orderEmbOfFin_univ Y hcard.symm
  refine ⟨x,y,hx,hy,hxi,hyi,?_⟩
  intro S
  apply partial_swap_prefix_bound A x y hx hy
  · intro i
    exact hX (Finset.orderEmbOfFin_mem X rfl i)
  · intro i hi
    exact Set.disjoint_left.mp hY (Finset.orderEmbOfFin_mem Y hcard.symm i) hi
  · simpa only [hxi,hyi] using hpref

end Erdos66OrderedPartialReplacement
