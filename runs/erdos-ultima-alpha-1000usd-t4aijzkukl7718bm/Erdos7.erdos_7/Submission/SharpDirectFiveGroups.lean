import Submission.SixNoThreeObstruction

/-! Small two-group obstructions using an explicitly processed modulus five. -/
namespace Erdos7SharpDirectFiveGroups
open scoped BigOperators
open Erdos7SharpDirectFiveWeight Erdos7SharpDirectFiveArithmetic
open Erdos7SharpDirectFiveScalar (cap)
open Erdos7MinimumTernaryClass
set_option autoImplicit false
set_option maxHeartbeats 5000000

lemma weight_le_max (d : ℕ) (hd : 1 < d) (ho : Odd d) (h3 : ¬ 3 ∣ d) :
    weight d ≤ (4/11 : ℚ) := by
  have hh := (weight_le_old d).trans (mul_le_mul_of_nonneg_left
    (Erdos7ThreeDistinctExceptions.weight_le_quarter d hd ho h3)
    (by norm_num : (0 : ℚ) ≤ 16/11))
  linarith

lemma weight_missing_five (d : ℕ) (hd : 1 < d) (ho : Odd d) (h3 : ¬ 3 ∣ d)
    (h5 : d≠5) : weight d ≤ (5/28 : ℚ) := by
  by_cases h7 : d=7
  · rw [h7]; norm_num [prime_weight 7 (by decide),cap]
  by_cases h11 : d=11
  · rw [h11]; norm_num [prime_weight 11 (by decide),cap]
  exact (weight_outside d hd ho h3 h5 h7 h11).trans (by norm_num)

lemma weight_missing_five_seven (d : ℕ) (hd : 1 < d) (ho : Odd d) (h3 : ¬ 3 ∣ d)
    (h5 : d≠5) (h7 : d≠7) : weight d ≤ (5/44 : ℚ) := by
  by_cases h11 : d=11
  · rw [h11]; norm_num [prime_weight 11 (by decide),cap]
  exact (weight_outside d hd ho h3 h5 h7 h11).trans (by norm_num)

lemma sum_le_card {K : Type*} [Fintype K] (d : K → ℕ) (B : ℚ)
    (hB : ∀ k, weight (d k) ≤ B) : (∑ k, weight (d k)) ≤ Fintype.card K*B := by
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
    Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => hB k)

lemma two_distinct_weight {K : Type*} [Fintype K] (d : K → ℕ) (hdi : Function.Injective d)
    (hd : ∀ k, 1 < d k ∧ Odd (d k)) (h3 : ∀ k, ¬ 3 ∣ d k) (hK : Fintype.card K ≤ 2) :
    (∑ k, weight (d k)) ≤ (4/11+5/28 : ℚ) := by
  classical
  have hb (k : K) : weight (d k) ≤ 5/28+(if d k=5 then 4/11-5/28 else 0) := by
    by_cases h5 : d k=5
    · rw [h5]; norm_num [prime_weight 5 (by decide),cap]
    · simpa only [if_neg h5,add_zero] using weight_missing_five (d k) (hd k).1 (hd k).2 (h3 k) h5
  have hh := Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => hb k)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have hi := Erdos7FiveExceptionWeights.indicator_sum_le d hdi 5 (4/11-5/28) (by norm_num)
  have hk : (Fintype.card K : ℚ) ≤ 2 := by exact_mod_cast hK
  linarith

lemma two_missing_five_weight {K : Type*} [Fintype K] (d : K → ℕ) (hdi : Function.Injective d)
    (hd : ∀ k, 1 < d k ∧ Odd (d k)) (h3 : ∀ k, ¬ 3 ∣ d k)
    (h5 : ∀ k, d k≠5) (hK : Fintype.card K ≤ 2) :
    (∑ k, weight (d k)) ≤ (5/28+5/44 : ℚ) := by
  classical
  have hb (k : K) : weight (d k) ≤ 5/44+(if d k=7 then 5/28-5/44 else 0) := by
    by_cases h7 : d k=7
    · rw [h7]; norm_num [prime_weight 7 (by decide),cap]
    · simpa only [if_neg h7,add_zero] using
        weight_missing_five_seven (d k) (hd k).1 (hd k).2 (h3 k) (h5 k) h7
  have hh := Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => hb k)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have hi := Erdos7FiveExceptionWeights.indicator_sum_le d hdi 7 (5/28-5/44) (by norm_num)
  have hk : (Fintype.card K : ℚ) ≤ 2 := by exact_mod_cast hK
  linarith

lemma group_weight {K U : Type*} [Fintype K] [Fintype U]
    (d : K → ℕ) (hdi : Function.Injective d) (hd : ∀ k, 1 < d k ∧ Odd (d k))
    (hd3 : ∀ k, ¬ 3 ∣ d k) (hd5 : ∀ k, d k≠5)
    (n : U → ℕ) (hni : Function.Injective n) (hn : ∀ u, 1 < n u ∧ Odd (n u))
    (hn3 : ∀ u, ¬ 3 ∣ n u)
    (hshape : (Fintype.card K ≤ 1 ∧ Fintype.card U ≤ 1) ∨
      (Fintype.card K=0 ∧ Fintype.card U ≤ 2) ∨
      (Fintype.card K ≤ 2 ∧ Fintype.card U ≤ 1 ∧ ∀ u, n u≠5)) :
    (∑ k, weight (d k))+(∑ u, weight (n u)) ≤ (11/20 : ℚ) := by
  rcases hshape with ⟨hk,hu⟩ | ⟨hk,hu⟩ | ⟨hk,hu,h5⟩
  · have h1 := sum_le_card d (5/28) (fun k => weight_missing_five (d k) (hd k).1 (hd k).2 (hd3 k) (hd5 k))
    have h2 := sum_le_card n (4/11) (fun u => weight_le_max (n u) (hn u).1 (hn u).2 (hn3 u))
    have hk' : (Fintype.card K : ℚ) ≤ 1 := by exact_mod_cast hk
    have hu' : (Fintype.card U : ℚ) ≤ 1 := by exact_mod_cast hu
    linarith
  · have h1 := sum_le_card d (5/28) (fun k => weight_missing_five (d k) (hd k).1 (hd k).2 (hd3 k) (hd5 k))
    have h2 := two_distinct_weight n hni hn hn3 hu
    rw [hk] at h1
    norm_num at h1
    linarith
  · have h1 := two_missing_five_weight d hdi hd hd3 hd5 hk
    have h2 := sum_le_card n (5/28) (fun u => weight_missing_five (n u) (hn u).1 (hn u).2 (hn3 u) (h5 u))
    have hu' : (Fintype.card U : ℚ) ≤ 1 := by exact_mod_cast hu
    linarith

lemma not_cover_pure_groups_no_three {I K U : Type*} [Fintype I] [Fintype K] [Fintype U]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i) (c₅ : ℤ)
    (d : K → ℕ) (b : K → ℤ) (hdi : Function.Injective d)
    (hd : ∀ k, 1 < d k ∧ Odd (d k)) (hd3 : ∀ k, ¬ 3 ∣ d k) (hd5 : ∀ k, d k≠5)
    (n : U → ℕ) (c : U → ℤ) (hni : Function.Injective n)
    (hn : ∀ u, 1 < n u ∧ Odd (n u)) (hn3 : ∀ u, ¬ 3 ∣ n u)
    (hshape : (Fintype.card K ≤ 1 ∧ Fintype.card U ≤ 1) ∨
      (Fintype.card K=0 ∧ Fintype.card U ≤ 2) ∨
      (Fintype.card K ≤ 2 ∧ Fintype.card U ≤ 1 ∧ ∀ u, n u≠5)) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ (5 : ℤ) ∣ x-c₅ ∨
      (∃ k, (d k : ℤ) ∣ x-b k) ∨ ∃ u, (n u : ℤ) ∣ x-c u) := by
  let D : K ⊕ U → ℕ := Sum.elim d n
  let B : K ⊕ U → ℤ := Sum.elim b c
  have hD (j : K ⊕ U) : 0 < D j ∧ Odd (D j) := by
    cases j with
    | inl j => exact ⟨by have := (hd j).1; change 0 < d j; omega,(hd j).2⟩
    | inr j => exact ⟨by have := (hn j).1; change 0 < n j; omega,(hn j).2⟩
  have hD3 (j : K ⊕ U) : ¬ 3 ∣ D j := by
    cases j with
    | inl j => exact hd3 j
    | inr j => exact hn3 j
  have hw : (∑ j, weight (D j)) ≤ (11/20 : ℚ) := by
    simpa only [D,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr] using
      group_weight d hdi hd hd3 hd5 n hni hn hn3 hshape
  intro hcover
  apply not_cover_with_weighted_exceptions m a hinj hm h3 D B c₅ hD hD3 hw
  intro x
  rcases hcover x with hi | h5 | ⟨k,hk⟩ | ⟨u,hu⟩
  · exact Or.inl hi
  · exact Or.inr (Or.inl h5)
  · exact Or.inr (Or.inr ⟨Sum.inl k,hk⟩)
  · exact Or.inr (Or.inr ⟨Sum.inr u,hu⟩)

lemma not_cover_pure_groups {I K U : Type*} [Fintype I] [Fintype K] [Fintype U]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i) (c₅ : ℤ)
    (d : K → ℕ) (b : K → ℤ) (hdi : Function.Injective d)
    (hd : ∀ k, 1 < d k ∧ Odd (d k)) (hd3 : ∀ k, ¬ 3 ∣ d k) (hd5 : ∀ k, d k≠5)
    (n : U → ℕ) (c : U → ℤ) (hni : Function.Injective n)
    (hn : ∀ u, 1 < n u ∧ Odd (n u))
    (hshape : (Fintype.card K ≤ 1 ∧ Fintype.card U ≤ 1) ∨
      (Fintype.card K=0 ∧ Fintype.card U ≤ 2) ∨
      (Fintype.card K ≤ 2 ∧ Fintype.card U ≤ 1 ∧ ∀ u, n u≠5)) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ (5 : ℤ) ∣ x-c₅ ∨
      (∃ k, (d k : ℤ) ∣ x-b k) ∨ ∃ u, (n u : ℤ) ∣ x-c u) := by
  classical
  by_cases hno : ∀ u, ¬ 3 ∣ n u
  · exact not_cover_pure_groups_no_three m a hinj hm h3 c₅ d b hdi hd hd3 hd5 n c hni hn hno hshape
  have hU : Fintype.card U ≤ 2 := by rcases hshape with h | h | h <;> omega
  obtain ⟨r,hr⟩ := Erdos7SmallTernaryBranches.free_ternary_residue c hU
  let V := {u : U // ¬ 3 ∣ n u}
  have hV : Fintype.card V ≤ Fintype.card U := Fintype.card_subtype_le _
  choose a' ha' using fun i => affine_residue (m i) (h3 i) (a i) r
  choose b' hb' using fun k => affine_residue (d k) (hd3 k) (b k) r
  choose c' hc' using fun u : V => affine_residue (n u) u.property (c u) r
  obtain ⟨c₅',hc₅⟩ := affine_residue 5 (by decide) c₅ r
  have hshape' : (Fintype.card K ≤ 1 ∧ Fintype.card V ≤ 1) ∨
      (Fintype.card K=0 ∧ Fintype.card V ≤ 2) ∨
      (Fintype.card K ≤ 2 ∧ Fintype.card V ≤ 1 ∧ ∀ u : V, n u≠5) := by
    rcases hshape with ⟨hk,hu⟩ | ⟨hk,hu⟩ | ⟨hk,hu,h5⟩
    · exact Or.inl ⟨hk,hV.trans hu⟩
    · exact Or.inr (Or.inl ⟨hk,hV.trans hu⟩)
    · exact Or.inr (Or.inr ⟨hk,hV.trans hu,fun u => h5 u⟩)
  intro hcover
  apply not_cover_pure_groups_no_three m a' hinj hm h3 c₅' d b' hdi hd hd3 hd5
    (fun u : V => n u) c' (hni.comp Subtype.val_injective) (fun u => hn u) (fun u => u.property) hshape'
  intro x
  rcases hcover (3*x+r) with ⟨i,hi⟩ | h5 | ⟨k,hk⟩ | ⟨u,hu⟩
  · exact Or.inl ⟨i,ha' i x hi⟩
  · exact Or.inr (Or.inl (hc₅ x h5))
  · exact Or.inr (Or.inr (Or.inl ⟨k,hb' k x hk⟩))
  · have hu3 : ¬ 3 ∣ n u := by
      intro hh
      have hz := (Int.natCast_dvd_natCast.mpr hh).trans hu
      exact hr u (by omega)
    exact Or.inr (Or.inr (Or.inr ⟨⟨u,hu3⟩,hc' ⟨u,hu3⟩ x hu⟩))

theorem not_cover_small_groups {I K U : Type*} [Fintype I] [Fintype K] [Fintype U]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : K → ℕ) (b : K → ℤ) (hdi : Function.Injective d)
    (hd : ∀ k, 1 < d k ∧ Odd (d k)) (hd3 : ∀ k, ¬ 3 ∣ d k) (hex5 : ∃ k, d k=5)
    (n : U → ℕ) (c : U → ℤ) (hni : Function.Injective n)
    (hn : ∀ u, 1 < n u ∧ Odd (n u))
    (hshape : (Fintype.card K ≤ 2 ∧ Fintype.card U ≤ 1) ∨
      (Fintype.card K ≤ 1 ∧ Fintype.card U ≤ 2) ∨
      (Fintype.card K ≤ 3 ∧ Fintype.card U ≤ 1 ∧ ∀ u, n u≠5)) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨
      (∃ k, (d k : ℤ) ∣ x-b k) ∨ ∃ u, (n u : ℤ) ∣ x-c u) := by
  classical
  obtain ⟨k₀,hk₀⟩ := hex5
  let V := {k : K // k≠k₀}
  have hV : Fintype.card V < Fintype.card K := Fintype.card_subtype_lt (x := k₀) (by simp)
  have h5 (k : V) : d k≠5 := fun h => k.property (hdi (h.trans hk₀.symm))
  have hshape' : (Fintype.card V ≤ 1 ∧ Fintype.card U ≤ 1) ∨
      (Fintype.card V=0 ∧ Fintype.card U ≤ 2) ∨
      (Fintype.card V ≤ 2 ∧ Fintype.card U ≤ 1 ∧ ∀ u, n u≠5) := by
    rcases hshape with ⟨hk,hu⟩ | ⟨hk,hu⟩ | ⟨hk,hu,h5⟩
    · exact Or.inl ⟨by omega,hu⟩
    · exact Or.inr (Or.inl ⟨by omega,hu⟩)
    · exact Or.inr (Or.inr ⟨by omega,hu,h5⟩)
  intro hcover
  apply not_cover_pure_groups m a hinj hm h3 (b k₀)
    (fun k : V => d k) (fun k => b k) (hdi.comp Subtype.val_injective)
    (fun k => hd k) (fun k => hd3 k) h5 n c hni hn hshape'
  intro x
  rcases hcover x with hi | ⟨k,hk⟩ | hu
  · exact Or.inl hi
  · by_cases he : k=k₀
    · subst k
      exact Or.inr (Or.inl (by simpa only [hk₀] using hk))
    · exact Or.inr (Or.inr (Or.inl ⟨⟨k,he⟩,hk⟩))
  · exact Or.inr (Or.inr (Or.inr hu))

theorem singleton_repair_is_five {I K : Type*} [Fintype I] [Fintype K]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : K → ℕ) (b : K → ℤ) (hdi : Function.Injective d)
    (hd : ∀ k, 1 < d k ∧ Odd (d k)) (hd3 : ∀ k, ¬ 3 ∣ d k)
    (hex5 : ∃ k, d k=5) (hK : Fintype.card K ≤ 3)
    (q : ℕ) (hq : 1 < q ∧ Odd q) (c : ℤ)
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨
      (∃ k, (d k : ℤ) ∣ x-b k) ∨ (q : ℤ) ∣ x-c) : q=5 := by
  by_contra h5
  apply not_cover_small_groups m a hinj hm h3 d b hdi hd hd3 hex5
    (fun _ : Unit => q) (fun _ => c) (fun _ _ _ => Subsingleton.elim _ _) (fun _ => hq)
    (Or.inr (Or.inr ⟨hK,by simp,fun _ => h5⟩))
  intro x
  rcases hcover x with hi | hk | hq
  · exact Or.inl hi
  · exact Or.inr (Or.inl hk)
  · exact Or.inr (Or.inr ⟨(),hq⟩)

#print axioms not_cover_pure_groups
#print axioms not_cover_small_groups
#print axioms singleton_repair_is_five
end Erdos7SharpDirectFiveGroups
