import Submission.BracketOrderedExchangeExplore

/-! An omitted point of positive profile mass admits an exact bracket-preserving
one-point exchange. The removed point is chosen by its cumulative rank. -/
namespace Erdos66BracketRankMove
open Erdos66Counting Erdos66Generating Erdos66ClampedPrefixContinuation
  Erdos66BracketOrderedExchange Erdos66OrderedPartialReplacement
open scoped Classical
set_option maxHeartbeats 2200000

lemma count_zero (A : Set ℕ) : count A 0=0 := by simp [count,cutoff]

lemma count_succ (A : Set ℕ) (N : ℕ) :
    count A (N+1)=count A N+if N∈A then 1 else 0 := by
  by_cases h : N∈A <;> simp [count,cutoff,Finset.range_add_one,Finset.filter_insert,h]

lemma count_monotone (A : Set ℕ) : Monotone (count A) := by
  apply monotone_nat_of_le_succ
  intro N
  rw [count_succ]
  omega

lemma exists_point_at_rank (A : Set ℕ) (hA : ∀ j, ∃ N, j<count A N) (j : ℕ) :
    ∃ d, d∈A ∧ count A d=j := by
  let N := Nat.find (hA j)
  have hN : j<count A N := Nat.find_spec (hA j)
  have hN0 : 0<N := by
    by_contra hn
    have he : N=0 := by omega
    rw [he,count_zero] at hN
    omega
  have hpre : count A (N-1) ≤ j := by
    have hh := Nat.find_min (hA j) (show N-1<N by omega)
    omega
  have hsucc : N-1+1=N := by omega
  have hs := count_succ A (N-1)
  rw [hsucc] at hs
  have hm : N-1∈A := by
    by_contra hn
    rw [if_neg hn] at hs
    omega
  refine ⟨N-1,hm,?_⟩
  rw [if_pos hm] at hs
  omega

noncomputable def rankPoint (A : Set ℕ) (hA : ∀ j, ∃ N, j<count A N) (j : ℕ) : ℕ :=
  Classical.choose (exists_point_at_rank A hA j)

lemma rankPoint_mem (A : Set ℕ) (hA : ∀ j, ∃ N, j<count A N) (j : ℕ) :
    rankPoint A hA j∈A := (Classical.choose_spec (exists_point_at_rank A hA j)).1
lemma rankPoint_count (A : Set ℕ) (hA : ∀ j, ∃ N, j<count A N) (j : ℕ) :
    count A (rankPoint A hA j)=j := (Classical.choose_spec (exists_point_at_rank A hA j)).2

lemma rankPoint_strictMono (A : Set ℕ) (hA : ∀ j, ∃ N, j<count A N) :
    StrictMono (rankPoint A hA) := by
  intro i j hij
  by_contra hn
  have hh := count_monotone A (show rankPoint A hA j ≤ rankPoint A hA i by omega)
  rw [rankPoint_count,rankPoint_count] at hh
  omega

lemma singleton_swap_difference (A : Set ℕ) (d f N : ℕ) (hd : d∈A) (hf : f∉A) :
    (count (swap A {d} {f}) N : ℝ)-count A N=
      (if f<N then (1 : ℝ) else 0)-(if d<N then (1 : ℝ) else 0) := by
  have hD : (({d} : Finset ℕ) : Set ℕ) ⊆ A := by simpa using Set.singleton_subset_iff.mpr hd
  have hF : Disjoint (({f} : Finset ℕ) : Set ℕ) A := by simpa using Set.disjoint_singleton_left.mpr hf
  rw [swap_count_difference A {d} {f} hD hF]
  by_cases hdN : d<N <;> by_cases hfN : f<N <;>
    simp [Finset.mem_range,hdN,hfN]

/-- The two rank-admissibility inequalities suffice for a single move. -/
theorem rank_move_brackets (p : ℕ → ℝ) (A : Set ℕ)
    (hp : ∀ k, 0 ≤ p k) (hbr : ∀ L, PrefixBrackets p A L)
    (j d f : ℕ) (hd : d∈A) (hf : f∉A) (hcount : count A d=j)
    (hlo : (j : ℝ)< mass p (f+1)) (hhi : mass p f<(j : ℝ)+1) :
    ∀ L, PrefixBrackets p (swap A {d} {f}) L := by
  intro L N hN
  have ha := hbr L N hN
  simp only [mass_indicator_eq_count] at ha ⊢
  have he := singleton_swap_difference A d f N hd hf
  by_cases hdN : d<N <;> by_cases hfN : f<N
  · simp only [if_pos hdN,if_pos hfN,sub_self] at he
    have hc : (count (swap A {d} {f}) N : ℝ)=count A N := by linarith
    rwa [hc]
  · simp only [if_pos hdN,if_neg hfN] at he
    have hc := count_monotone A (show d+1 ≤ N by omega)
    rw [count_succ,hcount,if_pos hd] at hc
    have hcr : (j : ℝ)+1 ≤ count A N := by exact_mod_cast hc
    have hmp := mass_mono hp (show N ≤ f by omega)
    have hfl : ⌊mass p N⌋ ≤ (j : ℤ) := by
      have hh : ⌊mass p N⌋ < (j : ℤ)+1 := Int.floor_lt.mpr (by push_cast; linarith)
      omega
    have hflr : (⌊mass p N⌋ : ℝ) ≤ (j : ℝ) := by exact_mod_cast hfl
    constructor <;> linarith
  · simp only [if_neg hdN,if_pos hfN] at he
    have hc := count_monotone A (show N ≤ d by omega)
    rw [hcount] at hc
    have hcr : (count A N : ℝ) ≤ j := by exact_mod_cast hc
    have hmp := mass_mono hp (show f+1 ≤ N by omega)
    have hcl : (j : ℤ)+1 ≤ ⌈mass p N⌉ := by
      have hh : (j : ℤ)<⌈mass p N⌉ := Int.lt_ceil.mpr (by exact_mod_cast hlo.trans_le hmp)
      omega
    have hclr : (j : ℝ)+1 ≤ (⌈mass p N⌉ : ℝ) := by exact_mod_cast hcl
    constructor <;> linarith
  · simp only [if_neg hdN,if_neg hfN,sub_self] at he
    have hc : (count (swap A {d} {f}) N : ℝ)=count A N := by linarith
    rwa [hc]

/-- Every absent point with positive profile weight can be inserted by one
cardinality-preserving exchange, without weakening any prefix bracket. -/
theorem omitted_point_admits_rank_move (p : ℕ → ℝ) (A : Set ℕ)
    (hp : ∀ k, 0 ≤ p k) (hbr : ∀ L, PrefixBrackets p A L)
    (hunb : ∀ j, ∃ N, j<count A N) (f : ℕ) (hf : f∉A) (hpf : 0<p f) :
    let j := ⌊mass p f⌋₊
    let d := rankPoint A hunb j
    d∈A ∧ d≠f ∧ ∀ L, PrefixBrackets p (swap A {d} {f}) L := by
  dsimp only
  have hd := rankPoint_mem A hunb ⌊mass p f⌋₊
  refine ⟨hd,fun he ↦ hf (he ▸ hd),?_⟩
  apply rank_move_brackets p A hp hbr ⌊mass p f⌋₊ _ f hd hf (rankPoint_count A hunb _)
  · have hm : 0 ≤ mass p f := Finset.sum_nonneg (fun i _ ↦ hp i)
    have hh := Nat.floor_le hm
    rw [mass_succ]
    linarith
  · exact Nat.lt_floor_add_one _

end Erdos66BracketRankMove
