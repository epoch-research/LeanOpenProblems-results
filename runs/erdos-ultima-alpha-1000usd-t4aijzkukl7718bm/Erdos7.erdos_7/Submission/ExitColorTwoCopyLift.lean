import Submission.ExitColorCoverLift

/-! A two-copy nonunary box cover on alphabets p-3 is a sufficient finite
 construction criterion for an odd strict covering system. -/
namespace Erdos7ExitColorTwoCopyLift
open scoped BigOperators
open Finset
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

section
variable {I K : Type} [Fintype I] [DecidableEq I]
variable (p : I → ℕ) (S : K → Finset I) (tag : K → Bool)

noncomputable def extendedSupport : I ⊕ K → Finset (Option I)
  | .inl i => {none,some i}
  | .inr k => if tag k then insert none ((S k).image some) else (S k).image some

lemma some_mem (j : I ⊕ K) (i : I) :
    some i ∈ extendedSupport S tag j ↔
      match j with | .inl k => i=k | .inr k => i ∈ S k := by
  classical
  cases j <;> simp [extendedSupport]
  split <;> simp

lemma none_mem (k : K) : none ∈ extendedSupport S tag (.inr k) ↔ tag k = true := by
  classical
  simp [extendedSupport]
  cases tag k <;> simp

lemma support_card_mixed (k : K) :
    (extendedSupport S tag (.inr k)).card = (S k).card + if tag k then 1 else 0 := by
  classical
  have hn : none ∉ (S k).image some := by simp
  have hi : Function.Injective (some : I → Option I) := Option.some_injective I
  simp only [extendedSupport]
  cases ht : tag k <;> simp [card_image_of_injective _ hi,hn,ht,Nat.add_comm]

lemma extendedSupport_injective (hSi : Function.Injective (fun k => (S k,tag k)))
    (hS : ∀ k, 2 ≤ (S k).card) : Function.Injective (extendedSupport S tag) := by
  classical
  intro j k he
  have hs (i : I) : some i ∈ extendedSupport S tag j ↔ some i ∈ extendedSupport S tag k := by rw [he]
  cases j with
  | inl i =>
    cases k with
    | inl k =>
      have hi := (hs i).mp (by simp [extendedSupport])
      have hik : i=k := (some_mem S tag (.inl k) i).mp hi
      subst k
      rfl
    | inr k =>
      have hset : S k = {i} := by
        ext a
        have hh := hs a
        simpa only [some_mem,mem_singleton] using hh.symm
      have hh := hS k
      rw [hset,card_singleton] at hh
      omega
  | inr j =>
    cases k with
    | inl i =>
      have hset : S j = {i} := by
        ext a
        have hh := hs a
        simpa only [some_mem,mem_singleton] using hh
      have hh := hS j
      rw [hset,card_singleton] at hh
      omega
    | inr k =>
      have hset : S j=S k := by ext i; simpa only [some_mem] using hs i
      have ht : tag j=tag k := by
        have hh : none ∈ extendedSupport S tag (.inr j) ↔ none ∈ extendedSupport S tag (.inr k) := by rw [he]
        rw [none_mem,none_mem] at hh
        cases hj : tag j <;> cases hk : tag k <;> simp_all
      exact congrArg Sum.inr (hSi (Prod.ext hset ht))

lemma extendedSupport_large (hS : ∀ k, 2 ≤ (S k).card) (j : I ⊕ K) :
    2 ≤ (extendedSupport S tag j).card := by
  classical
  cases j with
  | inl i => simp [extendedSupport]
  | inr k => rw [support_card_mixed]; have := hS k; omega

variable (a : K → (i : I) → Fin (p i-3))
variable (hp : ∀ i, 5 ≤ p i)

noncomputable def extendedColor (j : I ⊕ K) (i : Option I) :
    Fin (Erdos7ExitColorPatterns.base p 3 i - 2) := by
  cases i with
  | none => change Fin 1; exact 0
  | some i =>
    cases j with
    | inl j => exact ⟨0, by have := hp i; change 0 < p i-2; omega⟩
    | inr k => exact ⟨(a k i).val+1, by have := (a k i).isLt; change (a k i).val+1 < p i-2; omega⟩

lemma extended_color_cover
    (hc : ∀ x : (i : I) → Fin (p i-3), ∃ k, ∀ i ∈ S k, x i=a k i) :
    ∀ v : (i : Option I) → Fin (Erdos7ExitColorPatterns.base p 3 i - 2),
      ∃ j, ∀ i ∈ extendedSupport S tag j, v i=extendedColor p a hp j i := by
  classical
  intro v
  have hv0 (j : I ⊕ K) : v none = extendedColor p a hp j none := by
    change @Eq (Fin 1) _ _
    exact Subsingleton.elim _ _
  by_cases hz : ∃ i, (v (some i)).val=0
  · obtain ⟨i,hi⟩ := hz
    refine ⟨.inl i,fun k hk => ?_⟩
    cases k with
    | none => exact hv0 _
    | some k =>
      have hki := (some_mem S tag (.inl i) k).mp hk
      subst k
      exact Fin.ext hi
  · have hn (i : I) : 1 ≤ (v (some i)).val := by
      have : (v (some i)).val ≠ 0 := fun h => hz ⟨i,h⟩
      omega
    let x (i : I) : Fin (p i-3) := ⟨(v (some i)).val-1, by
      have hb := (v (some i)).isLt
      change (v (some i)).val < p i-2 at hb
      have := hn i
      omega⟩
    obtain ⟨k,hk⟩ := hc x
    refine ⟨.inr k,fun i hi => ?_⟩
    cases i with
    | none => exact hv0 _
    | some i =>
      have his := (some_mem S tag (.inr k) i).mp hi
      have hh := congrArg Fin.val (hk i his)
      change (v (some i)).val-1=(a k i).val at hh
      apply Fin.ext
      change (v (some i)).val=(a k i).val+1
      have := hn i
      omega

include hp in
/-- The finite model being searched: at most two boxes per nonunary support,
indexed by different Boolean tags, on alphabets p-3 for distinct odd primes p>=5. -/
theorem exists_cover_of_two_copy_colors
    (hpP : ∀ i, (p i).Prime) (hpi : Function.Injective p)
    (hSi : Function.Injective (fun k => (S k,tag k))) (hS : ∀ k, 2 ≤ (S k).card)
    (hc : ∀ x : (i : I) → Fin (p i-3), ∃ k, ∀ i ∈ S k, x i=a k i) :
    ∃ C : StrictCoveringSystem ℤ, ∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  apply Erdos7ExitColorCoverLift.exists_cover_of_colors
    (Erdos7ExitColorPatterns.base p 3) (extendedSupport S tag) (extendedColor p a hp)
  · intro i
    cases i with
    | none => norm_num [Erdos7ExitColorPatterns.base]
    | some i => exact ⟨hpP i,by have := hp i; change 3 ≤ p i; omega⟩
  · exact Erdos7ExitColorPatterns.base_injective p 3 hpi (fun i => by have := hp i; omega)
  · exact extendedSupport_injective S tag hSi hS
  · exact extendedSupport_large S tag hS
  · exact extended_color_cover p S tag a hp hc
end

#print axioms exists_cover_of_two_copy_colors
end Erdos7ExitColorTwoCopyLift
