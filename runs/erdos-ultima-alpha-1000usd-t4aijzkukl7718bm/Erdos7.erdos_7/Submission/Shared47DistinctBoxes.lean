import Submission.Shared47BlockBoxes

/-! Transfer the shared-prefix obstruction to distinct labelled boxes.
This remains a restricted obstruction, not the unrestricted odd-cover theorem. -/
namespace Erdos7Shared47DistinctBoxes
open scoped BigOperators
open Erdos7CompleteFamilyModel Erdos7TernaryTwoCoherentMixture
set_option maxHeartbeats 3000000
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

def primes : Fin 14 → ℕ := ![3,5,7,11,13,17,19,23,29,31,37,41,43,47]
lemma primes_gt_one : ∀ i,1<primes i := by decide +kernel
lemma primes_coprime : Pairwise (Function.onFun Nat.Coprime primes) := by
  unfold Pairwise Function.onFun
  decide +kernel
lemma primes_injective : Function.Injective primes := by decide +kernel
lemma primes_later (j : Fin 12) :
    (primes (j.natAdd 2):ℝ)=(Erdos7Shared47Schedule.later j).p := by
  fin_cases j <;> norm_num [primes,Fin.natAdd,Erdos7Shared47Schedule.later,Erdos7Shared47Rows.stage7,
    Erdos7Shared47Rows.stage11,Erdos7Shared47Rows.stage13,Erdos7Shared47Rows.stage17,
    Erdos7Shared47Rows.stage19,Erdos7Shared47Rows.stage23,Erdos7Shared47Rows.stage29,
    Erdos7Shared47Rows.stage31,Erdos7Shared47Rows.stage37,Erdos7Shared47Rows.stage41,
    Erdos7Shared47Rows.stage43,Erdos7Shared47Rows.stage47]

variable (A : Fin 14 → Type) [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]

lemma indicator_first (e : Fin 14 → ℕ) (X : ∀ i,Finset (A i)) (x : ∀ i,A i)
    (he : e 0≠0) : indicator A 1 e X x=(if x 0∈X 0 then 1 else 0) := by
  have hh := indicator_step A 0 (show 0<14 by omega) e X x (x 0)
  change indicator A 1 e X (Function.update x 0 (x 0)) =
    (if e 0=0 ∨ x 0∈X 0 then indicator A 0 e X x else 0) at hh
  simpa only [Function.update_eq_self,indicator_zero,he,false_or] using hh

/-- Pure ternary boxes are avoided; all other ternary sections are contained
in one branch or one point. Missing patterns are padded by empty boxes. -/
theorem not_cover {κ : Type} [Fintype κ]
    (E : Fin 14 → ℕ) (D : ℕ) (hE0 : E 0=2) (hE1 : E 1=D+1)
    (e : κ → Fin 14 → ℕ) (he : Function.Injective e) (heE : ∀ k i,e k i≤E i)
    (he0 : ∀ k,∃ i,e k i≠0) (X : κ → ∀ i,Finset (A i))
    (ξ : Fin 5 → ∀ i,A i)
    (havoid : ∀ k,(∀ i : Fin 14, 1 ≤ i.val → e k i=0) → ∀ x,ξ x 0∉X k 0)
    (hbranch : ∀ k,e k 0=1 → ∃ q : Fin 2,∀ x,ξ x 0∈X k 0 → branch x=q)
    (hpoint : ∀ k,e k 0=2 → ∃ y : Fin 5,∀ x,ξ x 0∈X k 0 → x=y)
    (ρ : ∀ i,A i → ℝ) (hρ : ∀ i y,0≤ρ i y) (hρmass : ∀ i,(∑ y,ρ i y)=1)
    (hd : ∀ k i,e k i≠0 →
      (∑ y,if y∈X k i then ρ i y else 0)≤1/(primes i:ℝ)^(e k i)) :
    ¬ (∀ x : ∀ i,A i,∃ k,∀ i,e k i≠0 → x i∈X k i) := by
  classical
  let X' (k : Pattern E) (i : Fin 14) : Finset (A i) :=
    if h : ∃ l,e l=exponent E k then X h.choose i else ∅
  have hd' (i : Fin 14) (k : Pattern E) (hi : exponent E k i≠0) :
      (∑ y,if y∈X' k i then ρ i y else 0)≤1/(primes i:ℝ)^(exponent E k i) := by
    dsimp only [X']
    split_ifs with h
    · have hh := hd h.choose i (by rw [congrFun h.choose_spec i]; exact hi)
      simpa only [congrFun h.choose_spec i] using hh
    · simp only [Finset.notMem_empty,if_false,Finset.sum_const_zero]
      positivity
  have ha' : ∀ x,¬coveredAt A E X' 0 (ξ x) := by
    intro x hc
    obtain ⟨a,k,hk,_,hmem⟩ := hc
    have hkp := (currentFamily_labels E 0 (by omega) a k).mp hk
    dsimp only [X'] at hmem
    split_ifs at hmem with h
    · exact havoid h.choose (fun i hi => by rw [congrFun h.choose_spec i]; exact hkp.2 i hi) x hmem
    · exact Finset.notMem_empty _ hmem
  have hb' : ∀ k,exponent E k 0=1 → ∃ q : Fin 2,∀ x,
      indicator A 1 (exponent E k) (X' k) (ξ x)≤(if branch x=q then (1:ℝ) else 0) := by
    intro k hk
    by_cases h : ∃ l,e l=exponent E k
    · obtain ⟨q,hq⟩ := hbranch h.choose (by rw [congrFun h.choose_spec 0,hk])
      refine ⟨q,fun x => ?_⟩
      rw [indicator_first A _ _ _ (by omega)]
      simp only [X',dif_pos h]
      by_cases hm : ξ x 0∈X h.choose 0
      · simp only [if_pos hm,if_pos (hq x hm),le_refl]
      · simp only [if_neg hm]; split_ifs <;> norm_num
    · refine ⟨0,fun x => ?_⟩
      rw [indicator_first A _ _ _ (by omega)]
      simp only [X',dif_neg h,Finset.notMem_empty,if_false]
      split_ifs <;> norm_num
  have hp' : ∀ k,exponent E k 0=2 → ∃ y : Fin 5,∀ x,
      indicator A 1 (exponent E k) (X' k) (ξ x)≤(if x=y then (1:ℝ) else 0) := by
    intro k hk
    by_cases h : ∃ l,e l=exponent E k
    · obtain ⟨y,hy⟩ := hpoint h.choose (by rw [congrFun h.choose_spec 0,hk])
      refine ⟨y,fun x => ?_⟩
      rw [indicator_first A _ _ _ (by omega)]
      simp only [X',dif_pos h]
      by_cases hm : ξ x 0∈X h.choose 0
      · simp only [if_pos hm,if_pos (hy x hm),le_refl]
      · simp only [if_neg hm]; split_ifs <;> norm_num
    · refine ⟨0,fun x => ?_⟩
      rw [indicator_first A _ _ _ (by omega)]
      simp only [X',dif_neg h,Finset.notMem_empty,if_false]
      split_ifs <;> norm_num
  intro hcover
  apply Erdos7Shared47BlockBoxes.not_full_cover A E X' D hE0 hE1 ξ ha' hb' hp' ρ hρ hρmass
    (by simpa only [show primes 1=5 from rfl] using hd' 1)
    (fun j k hk => by simpa only [primes_later] using hd' (j.natAdd 2) k hk)
  intro x
  obtain ⟨k,hk⟩ := hcover x
  let l : Pattern E := fun i => ⟨e k i,by have := heE k i; omega⟩
  have hl : exponent E l=e k := rfl
  have hex : ∃ j,e j=exponent E l := ⟨k,rfl⟩
  have hchoice : hex.choose=k := he (hex.choose_spec.trans hl)
  have hX : X' l=X k := by funext i; simp only [X',dif_pos hex,hchoice]
  refine ⟨l,by simpa only [hl] using he0 k,?_⟩
  rw [hX]
  dsimp only [indicator]
  rw [project_full,hl,Erdos7Distortion.boxIndicator,if_pos]
  · norm_num
  · intro i hi
    exact hk i ((Erdos7CompressionSieve.mem_expSupport _ _).mp hi)

#print axioms not_cover
end Erdos7Shared47DistinctBoxes
