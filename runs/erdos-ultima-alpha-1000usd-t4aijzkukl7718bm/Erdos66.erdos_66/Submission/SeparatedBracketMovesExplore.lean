import Submission.BracketRankMoveExplore

/-! Simultaneous separated one-point moves preserve exact prefix brackets. -/
namespace Erdos66SeparatedBracketMoves
open Erdos66Counting Erdos66Generating Erdos66ClampedPrefixContinuation
  Erdos66BracketOrderedExchange Erdos66OrderedPartialReplacement Erdos66BracketRankMove
open scoped Classical
set_option maxHeartbeats 2400000

noncomputable def delta (d f N : ℕ) : ℝ :=
  (if f<N then 1 else 0)-(if d<N then 1 else 0)

lemma delta_ne_zero_location (d f N : ℕ) (h : delta d f N≠0) :
    min d f<N ∧ N ≤ max d f := by
  by_cases hd : d<N <;> by_cases hf : f<N
  all_goals simp only [delta,hd,hf,if_true,if_false] at h
  all_goals norm_num at h
  all_goals constructor <;> omega

lemma image_prefix_sum {ι : Type*} [Fintype ι] (g : ι → ℕ)
    (hg : Function.Injective g) (N : ℕ) :
    ((Finset.univ.image g∩Finset.range N).card : ℝ)=∑ i, if g i<N then (1 : ℝ) else 0 := by
  have he : Finset.univ.image g∩Finset.range N=
      (Finset.univ.filter (fun i ↦ g i<N)).image g := by
    ext a
    simp only [Finset.mem_inter,Finset.mem_image,Finset.mem_univ,true_and,
      Finset.mem_range,Finset.mem_filter]
    constructor
    · rintro ⟨⟨i,rfl⟩,hi⟩
      exact ⟨i,hi,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,rfl⟩,hi⟩
  rw [he,Finset.card_image_of_injective _ hg,Finset.card_filter]
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

lemma family_swap_difference {ι : Type*} [Fintype ι] (A : Set ℕ) (d f : ι → ℕ)
    (hd : Function.Injective d) (hf : Function.Injective f)
    (hdA : ∀ i, d i∈A) (hfA : ∀ i, f i∉A) (N : ℕ) :
    (count (swap A (Finset.univ.image d) (Finset.univ.image f)) N : ℝ)-count A N=
      ∑ i, delta (d i) (f i) N := by
  have hD : (Finset.univ.image d : Set ℕ) ⊆ A := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact hdA i
  have hF : Disjoint (Finset.univ.image f : Set ℕ) A := by
    apply Set.disjoint_left.mpr
    intro a ha hia
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact hfA i hia
  rw [swap_count_difference A _ _ hD hF,image_prefix_sum f hf,image_prefix_sum d hd,
    ←Finset.sum_sub_distrib]
  rfl

lemma sum_zero_or_single {ι : Type*} [Fintype ι] (g : ι → ℝ)
    (h : ∀ i j, g i≠0 → g j≠0 → i=j) :
    (∑ i, g i)=0 ∨ ∃ i, (∑ j, g j)=g i := by
  by_cases hz : ∀ i, g i=0
  · left
    simp only [hz,Finset.sum_const_zero]
  · push_neg at hz
    obtain ⟨i,hi⟩ := hz
    right
    refine ⟨i,Finset.sum_eq_single i ?_ (fun hh ↦ False.elim (hh (Finset.mem_univ _)))⟩
    intro j hj hji
    by_contra hj0
    exact hji (h j i hj0 hi)

/-- At any cutoff, at most one move is visible. Its individual bracket
certificate therefore also certifies the entire finite family. -/
theorem family_brackets {ι : Type*} [Fintype ι] (p : ℕ → ℝ) (A : Set ℕ)
    (d f : ι → ℕ) (hd : Function.Injective d) (hf : Function.Injective f)
    (hdA : ∀ i, d i∈A) (hfA : ∀ i, f i∉A)
    (hA : ∀ L, PrefixBrackets p A L)
    (hsingle : ∀ i L, PrefixBrackets p (swap A {d i} {f i}) L)
    (hsep : ∀ N i j, delta (d i) (f i) N≠0 → delta (d j) (f j) N≠0 → i=j) :
    ∀ L, PrefixBrackets p (swap A (Finset.univ.image d) (Finset.univ.image f)) L := by
  intro L N hN
  have he := family_swap_difference A d f hd hf hdA hfA N
  rcases sum_zero_or_single (fun i ↦ delta (d i) (f i) N) (hsep N) with hz | ⟨i,hi⟩
  · rw [hz] at he
    have hc : (count (swap A (Finset.univ.image d) (Finset.univ.image f)) N : ℝ)=count A N := by
      linarith
    have hh := hA L N hN
    simpa only [mass_indicator_eq_count,hc] using hh
  · rw [hi] at he
    have hs := singleton_swap_difference A (d i) (f i) N (hdA i) (hfA i)
    change _=delta (d i) (f i) N at hs
    have hc : (count (swap A (Finset.univ.image d) (Finset.univ.image f)) N : ℝ)=
        count (swap A {d i} {f i}) N := by linarith
    have hh := hsingle i L N hN
    simpa only [mass_indicator_eq_count,hc] using hh

end Erdos66SeparatedBracketMoves
