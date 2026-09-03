import Submission.OrderedPartialReplacementExplore
import Submission.ClampedPrefixContinuationExplore

/-! Every subset of order-matched exchanges between two bracket-feasible
sets is bracket-feasible. The conclusion is exact, with no extra unit of
prefix discrepancy. -/
namespace Erdos66BracketOrderedExchange
open Erdos66OrderedPartialReplacement Erdos66ClampedPrefixContinuation
  Erdos66Counting Erdos66SetIntervalReplacement Erdos66Generating
open scoped Classical
set_option maxHeartbeats 1800000

lemma inter_card_difference_between {ι : Type*} [DecidableEq ι]
    (S X Y : Finset ι) (h : X ⊆ Y ∨ Y ⊆ X) :
    min 0 ((Y.card : ℝ)-X.card) ≤ ((S∩Y).card : ℝ)-(S∩X).card ∧
      ((S∩Y).card : ℝ)-(S∩X).card ≤ max 0 ((Y.card : ℝ)-X.card) := by
  rcases h with h | h
  · have hfull : (X.card : ℝ) ≤ Y.card := by exact_mod_cast Finset.card_le_card h
    have hpart : ((S∩X).card : ℝ) ≤ (S∩Y).card := by
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_left h)
    have hb := inter_card_difference_le S X Y h
    rw [abs_of_nonpos (sub_nonpos.mpr hpart),abs_of_nonpos (sub_nonpos.mpr hfull)] at hb
    rw [min_eq_left (by linarith : (0 : ℝ) ≤ (Y.card : ℝ)-X.card),
      max_eq_right (by linarith : (0 : ℝ) ≤ (Y.card : ℝ)-X.card)]
    constructor <;> linarith
  · have hfull : (Y.card : ℝ) ≤ X.card := by exact_mod_cast Finset.card_le_card h
    have hpart : ((S∩Y).card : ℝ) ≤ (S∩X).card := by
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_left h)
    have hb := inter_card_difference_le S Y X h
    rw [abs_of_nonpos (sub_nonpos.mpr hpart),abs_of_nonpos (sub_nonpos.mpr hfull)] at hb
    rw [min_eq_right (by linarith : (Y.card : ℝ)-X.card ≤ 0),
      max_eq_left (by linarith : (Y.card : ℝ)-X.card ≤ 0)]
    constructor <;> linarith

lemma partial_prefix_difference_between {m : ℕ} (x y : Fin m → ℕ)
    (hx : StrictMono x) (hy : StrictMono y) (S : Finset (Fin m)) (N : ℕ) :
    min 0 (((Finset.univ.image y∩Finset.range N).card : ℝ)-
      (Finset.univ.image x∩Finset.range N).card) ≤
      ((S.image y∩Finset.range N).card : ℝ)-(S.image x∩Finset.range N).card ∧
    ((S.image y∩Finset.range N).card : ℝ)-(S.image x∩Finset.range N).card ≤
      max 0 (((Finset.univ.image y∩Finset.range N).card : ℝ)-
        (Finset.univ.image x∩Finset.range N).card) := by
  simp only [image_prefix_card _ hx.injective,image_prefix_card _ hy.injective,Finset.univ_inter]
  exact inter_card_difference_between S (cut x N) (cut y N)
    (cuts_comparable x y hx.monotone hy.monotone N)

/-- Each partial exchange has a prefix count between those of the two full
endpoint sets, even when different cutoffs have different directions. -/
theorem partial_swap_count_between (A : Set ℕ) {m : ℕ} (x y : Fin m → ℕ)
    (hx : StrictMono x) (hy : StrictMono y)
    (hxA : ∀ i, x i∈A) (hyA : ∀ i, y i∉A) (S : Finset (Fin m)) (N : ℕ) :
    min (count A N : ℝ)
      (count (swap A (Finset.univ.image x) (Finset.univ.image y)) N) ≤
        count (swap A (S.image x) (S.image y)) N ∧
    (count (swap A (S.image x) (S.image y)) N : ℝ) ≤
      max (count A N : ℝ)
        (count (swap A (Finset.univ.image x) (Finset.univ.image y)) N) := by
  have hD (U : Finset (Fin m)) : (U.image x : Set ℕ) ⊆ A := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact hxA i
  have hF (U : Finset (Fin m)) : Disjoint (U.image y : Set ℕ) A := by
    apply Set.disjoint_left.mpr
    intro a ha hia
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact hyA i hia
  have hp := swap_count_difference A (S.image x) (S.image y) (hD S) (hF S) N
  have hf := swap_count_difference A (Finset.univ.image x) (Finset.univ.image y)
    (hD Finset.univ) (hF Finset.univ) N
  have hb := partial_prefix_difference_between x y hx hy S N
  rw [←hp,←hf] at hb
  constructor
  · have hh := add_le_add_left hb.1 (count A N : ℝ)
    rw [min_add] at hh
    simpa only [zero_add,sub_add_cancel] using hh
  · have hh := add_le_add_left hb.2 (count A N : ℝ)
    rw [max_add] at hh
    simpa only [zero_add,sub_add_cancel] using hh

lemma mass_indicator_eq_count (A : Set ℕ) (N : ℕ) :
    mass (indicator A) N=(count A N : ℝ) := (count_sum A N).symm

/-- Exact original floor/ceiling brackets survive every partial ordered
exchange if both endpoint sets satisfy them. -/
theorem partial_swap_brackets (p : ℕ → ℝ) (A : Set ℕ) (L : ℕ)
    {m : ℕ} (x y : Fin m → ℕ) (hx : StrictMono x) (hy : StrictMono y)
    (hxA : ∀ i, x i∈A) (hyA : ∀ i, y i∉A)
    (hA : PrefixBrackets p A L)
    (hB : PrefixBrackets p (swap A (Finset.univ.image x) (Finset.univ.image y)) L)
    (S : Finset (Fin m)) : PrefixBrackets p (swap A (S.image x) (S.image y)) L := by
  intro N hN
  have hb := partial_swap_count_between A x y hx hy hxA hyA S N
  have ha := hA N hN
  have hc := hB N hN
  simp only [mass_indicator_eq_count] at ha hc ⊢
  exact ⟨(le_min ha.1 hc.1).trans hb.1,hb.2.trans (max_le ha.2 hc.2)⟩

/-- Any two finite bracket-feasible sets of equal cardinality admit an
order-matched exchange cube all of whose vertices satisfy the same brackets. -/
theorem exists_bracket_exchange_cube (p : ℕ → ℝ) (A B : Finset ℕ) (L : ℕ)
    (hcard : A.card=B.card) (hA : PrefixBrackets p (A : Set ℕ) L)
    (hB : PrefixBrackets p (B : Set ℕ) L) :
    ∃ x y : Fin (A \ B).card → ℕ, StrictMono x ∧ StrictMono y ∧
      Finset.univ.image x=A \ B ∧ Finset.univ.image y=B \ A ∧
      (∀ i, x i∈A ∧ y i∉A) ∧
      (∀ S : Finset (Fin (A \ B).card),
        PrefixBrackets p (swap (A : Set ℕ) (S.image x) (S.image y)) L) := by
  have hc : (A \ B).card=(B \ A).card := by
    have h1 := Finset.card_sdiff_add_card_inter A B
    have h2 := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm B A] at h2
    omega
  let x := (A \ B).orderEmbOfFin rfl
  let y := (B \ A).orderEmbOfFin hc.symm
  have hx : StrictMono x := x.strictMono
  have hy : StrictMono y := y.strictMono
  have hxi : Finset.univ.image x=A \ B := Finset.image_orderEmbOfFin_univ _ _
  have hyi : Finset.univ.image y=B \ A := Finset.image_orderEmbOfFin_univ _ _
  have hxA (i : Fin (A \ B).card) : x i∈A :=
    (Finset.mem_sdiff.mp (Finset.orderEmbOfFin_mem (A \ B) rfl i)).1
  have hyA (i : Fin (A \ B).card) : y i∉A :=
    (Finset.mem_sdiff.mp (Finset.orderEmbOfFin_mem (B \ A) hc.symm i)).2
  have he : swap (A : Set ℕ) (Finset.univ.image x) (Finset.univ.image y)=(B : Set ℕ) := by
    rw [hxi,hyi]
    ext a
    simp only [swap,Set.mem_union,Set.mem_diff,Finset.mem_coe,Finset.mem_sdiff]
    tauto
  refine ⟨x,y,hx,hy,hxi,hyi,fun i ↦ ⟨hxA i,hyA i⟩,?_⟩
  intro S
  apply partial_swap_brackets p (A : Set ℕ) L x y hx hy hxA hyA hA
  rwa [he]

end Erdos66BracketOrderedExchange
