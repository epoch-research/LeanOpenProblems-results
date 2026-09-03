import FormalConjecturesUtil

/-!
# Erdős Problem 41

*Reference:* [erdosproblems.com/41](https://www.erdosproblems.com/41)
-/

open Filter Set

namespace Erdos41
variable {α : Type} [AddCommMonoid α]

/--
For a given set `A`, the n-tuple sums `a₁ + ... + aₙ` are all distinct for `a₁, ..., aₙ` in `A`
(aside from the trivial coincidences).
-/
def NtupleCondition (A : Set α) (n : ℕ) : Prop := ∀ (I : Finset α) (J : Finset α),
  ↑I ⊆ A ∧ ↑J ⊆ A ∧ I.card = n ∧ J.card = n ∧
  (∑ i ∈ I, i = ∑ j ∈ J, j) → I = J

lemma NtupleCondition.choose_card_le {A : Set ℕ} {n : ℕ}
    (h : NtupleCondition A n) (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A)
    (N : ℕ) (hN : ∀ a ∈ S, a ≤ N) : S.card.choose n ≤ n * N + 1 := by
  classical
  rw [← Finset.card_powersetCard n S, ← Finset.card_range (n * N + 1)]
  apply Finset.card_le_card_of_injOn (fun I : Finset ℕ => ∑ a ∈ I, a)
  · intro I hI
    obtain ⟨hIS, hIc⟩ := Finset.mem_powersetCard.mp hI
    apply Finset.mem_range.mpr
    have hb : ∑ a ∈ I, a ≤ ∑ a ∈ I, N :=
      Finset.sum_le_sum fun a ha => hN a (hIS ha)
    simpa [hIc, Nat.lt_add_one_iff] using hb
  · intro I hI J hJ heq
    obtain ⟨hIS, hIc⟩ := Finset.mem_powersetCard.mp hI
    obtain ⟨hJS, hJc⟩ := Finset.mem_powersetCard.mp hJ
    exact h I J ⟨fun a ha => hS (hIS ha), fun a ha => hS (hJS ha), hIc, hJc, heq⟩

lemma NtupleCondition.choose_ncard_le {A : Set ℕ} {n : ℕ}
    (h : NtupleCondition A n) (N : ℕ) : (A ∩ Icc 1 N).ncard.choose n ≤ n * N + 1 := by
  classical
  have hfin : (A ∩ Icc 1 N).Finite := (finite_Icc 1 N).inter_of_right A
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact h.choose_card_le hfin.toFinset
    (fun a ha => (hfin.mem_toFinset.mp ha).1) N
    (fun a ha => (hfin.mem_toFinset.mp ha).2.2)

lemma NtupleCondition.of_succ {A : Set α} {n : ℕ}
    (h : NtupleCondition A (n + 1)) (hA : A.Infinite) : NtupleCondition A n := by
  classical
  intro I J ⟨hI, hJ, hIc, hJc, he⟩
  obtain ⟨a, ha, hn⟩ := hA.exists_notMem_finset (I ∪ J)
  have hni : a ∉ I := fun hm => hn (Finset.mem_union_left J hm)
  have hnj : a ∉ J := fun hm => hn (Finset.mem_union_right I hm)
  have heq : insert a I = insert a J := h _ _ ⟨by simpa using Set.insert_subset ha hI,
    by simpa using Set.insert_subset ha hJ,
    by simp [Finset.card_insert_of_notMem hni, hIc],
    by simp [Finset.card_insert_of_notMem hnj, hJc],
    by simpa [Finset.sum_insert hni, Finset.sum_insert hnj] using congrArg (a + ·) he⟩
  have heq' := congrArg (fun S : Finset α => S.erase a) heq
  simpa [Finset.erase_insert hni, Finset.erase_insert hnj] using heq'

lemma NtupleCondition.cube_bound {A : Set ℕ} (h : NtupleCondition A 3) (N : ℕ) :
    (((A ∩ Icc 1 N).ncard + 1 - 3 : ℕ) : ℝ) ^ 3 ≤ 18 * (N : ℝ) + 6 := by
  have hb : (((A ∩ Icc 1 N).ncard.choose 3 : ℕ) : ℝ) ≤ 3 * (N : ℝ) + 1 := by
    exact_mod_cast h.choose_ncard_le N
  have hp := Nat.pow_le_choose (α := ℝ) 3 (A ∩ Icc 1 N).ncard
  norm_num at hp
  linarith

lemma NtupleCondition.ratio_le_five {A : Set ℕ} (h : NtupleCondition A 3) (N : ℕ) :
    (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ) ≤ 5 := by
  by_cases hN : N = 0
  · subst N
    norm_num
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  have hr : 1 ≤ (N : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hr0 : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by positivity
  have hr3 : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = (N : ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
    norm_num
  have hcube := h.cube_bound N
  have hsmall : (((A ∩ Icc 1 N).ncard + 1 - 3 : ℕ) : ℝ) ≤
      3 * (N : ℝ) ^ (1 / 3 : ℝ) := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 3 ≠ 0)).mp
    rw [mul_pow, hr3]
    norm_num
    linarith
  have hcard : ((A ∩ Icc 1 N).ncard : ℝ) ≤
      (((A ∩ Icc 1 N).ncard + 1 - 3 : ℕ) : ℝ) + 2 := by
    exact_mod_cast (show (A ∩ Icc 1 N).ncard ≤ (A ∩ Icc 1 N).ncard + 1 - 3 + 2 by omega)
  apply (div_le_iff₀ (by positivity : 0 < (N : ℝ) ^ (1 / 3 : ℝ))).mpr
  linarith

lemma NtupleCondition.liminf_nonneg {A : Set ℕ} (h : NtupleCondition A 3) :
    0 ≤ Filter.atTop.liminf (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) := by
  apply Filter.le_liminf_of_le (Filter.isCoboundedUnder_ge_of_le _ h.ratio_le_five)
  exact Filter.Eventually.of_forall (fun N => by positivity)

/-- A sufficient entirely discrete counting estimate for the conjectured limit. -/
lemma liminf_eq_zero_of_cubic_sparsity {A : Set ℕ} (h : NtupleCondition A 3)
    (hs : ∀ k M : ℕ, ∃ N ≥ M, k * (A ∩ Icc 1 N).ncard ^ 3 ≤ N) :
    Filter.atTop.liminf (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) = 0 := by
  apply le_antisymm ?_ h.liminf_nonneg
  have hlo : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) :=
    Filter.isBoundedUnder_of ⟨0, fun N => by positivity⟩
  apply (Filter.liminf_le_iff
    (Filter.isCoboundedUnder_ge_of_le _ h.ratio_le_five) hlo).mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt ((ε ^ 3)⁻¹)
  have hε3 : 0 < ε ^ 3 := by positivity
  have hk0 : 0 < (k : ℝ) := lt_trans (by positivity) hk
  have hkε : 1 < ε ^ 3 * (k : ℝ) := by
    calc
      1 = ε ^ 3 * (ε ^ 3)⁻¹ := by rw [mul_inv_cancel₀ (ne_of_gt hε3)]
      _ < ε ^ 3 * (k : ℝ) := mul_lt_mul_of_pos_left hk hε3
  rw [Filter.frequently_atTop]
  intro M
  obtain ⟨N, hNM, hN⟩ := hs k (max M 1)
  have hNM' : M ≤ N := le_trans (le_max_left _ _) hNM
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hNM
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN1)
  refine ⟨N, hNM', ?_⟩
  have hc : (k : ℝ) * ((A ∩ Icc 1 N).ncard : ℝ) ^ 3 ≤ (N : ℝ) := by
    exact_mod_cast hN
  have hc' : ((A ∩ Icc 1 N).ncard : ℝ) ^ 3 < ε ^ 3 * (N : ℝ) := by
    apply (mul_lt_mul_iff_right₀ hk0).mp
    calc
      (k : ℝ) * ((A ∩ Icc 1 N).ncard : ℝ) ^ 3 ≤ N := hc
      _ < (ε ^ 3 * (k : ℝ)) * (N : ℝ) := by nlinarith
      _ = (k : ℝ) * (ε ^ 3 * (N : ℝ)) := by ring
  have hr3 : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = (N : ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
    norm_num
  have hc'' : ((A ∩ Icc 1 N).ncard : ℝ) < ε * (N : ℝ) ^ (1 / 3 : ℝ) := by
    apply (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by decide : 3 ≠ 0)).mp
    simpa only [mul_pow, hr3] using hc'
  exact (div_lt_iff₀ (by positivity : 0 < (N : ℝ) ^ (1 / 3 : ℝ))).mpr hc''

/-- A fixed positive difference can only occur at three possible starting points
once one occurrence is fixed. This bound uses only distinct-pair uniqueness. -/
lemma NtupleCondition.difference_bases_subset {A : Set ℕ} (h : NtupleCondition A 2)
    {b d : ℕ} (hd : 0 < d) (hb : b ∈ A) (hbd : b + d ∈ A) :
    {a | a ∈ A ∧ a + d ∈ A} ⊆ ({b - d, b, b + d} : Set ℕ) := by
  classical
  intro a ha
  by_cases hab : a = b
  · simp [hab]
  by_cases habd : a = b + d
  · simp [habd]
  by_cases hadb : a + d = b
  · have : a = b - d := by omega
    simp [this]
  have hI : ({b + d, a} : Finset ℕ) = {b, a + d} := by
    apply h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [Finset.coe_pair, Set.pair_subset_iff]
      exact ⟨hbd, ha.1⟩
    · simp only [Finset.coe_pair, Set.pair_subset_iff]
      exact ⟨hb, ha.2⟩
    · exact Finset.card_pair (Ne.symm habd)
    · exact Finset.card_pair (Ne.symm hadb)
    · simp [Finset.sum_pair (Ne.symm habd), Finset.sum_pair (Ne.symm hadb)]
      omega
  have hm : b + d ∈ ({b, a + d} : Finset ℕ) := by
    rw [← hI]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm <;> omega

lemma NtupleCondition.finite_difference_bases {A : Set ℕ} (h : NtupleCondition A 2)
    {d : ℕ} (hd : 0 < d) : {a | a ∈ A ∧ a + d ∈ A}.Finite := by
  by_cases hn : ({a | a ∈ A ∧ a + d ∈ A} : Set ℕ).Nonempty
  · obtain ⟨b, hb, hbd⟩ := hn
    exact (Set.toFinite ({b - d, b, b + d} : Set ℕ)).subset
      (h.difference_bases_subset hd hb hbd)
  · simp [Set.not_nonempty_iff_eq_empty.mp hn]


/-- A collision between two signed triple sums either is trivial or has a
cross-overlap. No uniqueness assertion involving repeated elements is assumed. -/
lemma NtupleCondition.signed_collision {A : Set α} (h : NtupleCondition A 3)
    {I J : Finset α} {c d : α}
    (hI : (I : Set α) ⊆ A) (hJ : (J : Set α) ⊆ A)
    (hIc : I.card = 2) (hJc : J.card = 2)
    (hcA : c ∈ A) (hdA : d ∈ A) (hcI : c ∉ I) (hdJ : d ∉ J)
    (he : (∑ a ∈ I, a) + d = (∑ a ∈ J, a) + c) :
    (I = J ∧ c = d) ∨ d ∈ I ∨ c ∈ J := by
  classical
  by_cases hdI : d ∈ I
  · exact Or.inr (Or.inl hdI)
  by_cases hcJ : c ∈ J
  · exact Or.inr (Or.inr hcJ)
  have heq : insert d I = insert c J := by
    apply h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa using Set.insert_subset hdA hI
    · simpa using Set.insert_subset hcA hJ
    · simp [Finset.card_insert_of_notMem hdI, hIc]
    · simp [Finset.card_insert_of_notMem hcJ, hJc]
    · simpa [Finset.sum_insert hdI, Finset.sum_insert hcJ, add_comm] using he
  have hc : c ∈ insert d I := by rw [heq]; simp
  have hcd : c = d := (Finset.mem_insert.mp hc).resolve_right hcI
  subst d
  have hIJ := congrArg (fun K : Finset α => K.erase c) heq
  exact Or.inl ⟨by simpa [Finset.erase_insert hcI, Finset.erase_insert hcJ] using hIJ, rfl⟩

/-- There are at most three representations of a fixed signed triple sum in
which the subtracted element is larger than both added elements. -/
lemma NtupleCondition.signed_card_le_three {A : Set ℕ}
    (h : NtupleCondition A 3) (t : ℤ) (S : Finset (Finset ℕ × ℕ))
    (hs : ∀ p ∈ S, (p.1 : Set ℕ) ⊆ A ∧ p.1.card = 2 ∧ p.2 ∈ A ∧
      (∀ a ∈ p.1, a < p.2) ∧ ((∑ a ∈ p.1, a : ℕ) : ℤ) - p.2 = t) :
    S.card ≤ 3 := by
  classical
  by_cases hn : S.Nonempty
  · obtain ⟨p, hp, hmax⟩ := S.exists_max_image Prod.snd hn
    obtain ⟨hpA, hpcard, hpcA, hplt, hpsum⟩ := hs p hp
    have hpn : p.2 ∉ p.1 := fun hm => (lt_irrefl _ (hplt _ hm))
    have hbound : (S.erase p).card ≤ p.1.card := by
      apply Finset.card_le_card_of_injOn (fun q : Finset ℕ × ℕ => q.2)
      · intro q hq
        obtain ⟨hqp, hqS⟩ := Finset.mem_erase.mp hq
        obtain ⟨hqA, hqcard, hqcA, hqlt, hqsum⟩ := hs q hqS
        have hqn : q.2 ∉ q.1 := fun hm => (lt_irrefl _ (hqlt _ hm))
        have he : (∑ a ∈ q.1, a) + p.2 = (∑ a ∈ p.1, a) + q.2 := by
          have he' : ((∑ a ∈ q.1, a : ℕ) : ℤ) + p.2 =
              ((∑ a ∈ p.1, a : ℕ) : ℤ) + q.2 := by omega
          exact_mod_cast he'
        rcases h.signed_collision hqA hpA hqcard hpcard hqcA hpcA hqn hpn he with
            heq | hcross | hcross
        · exact (hqp (Prod.ext heq.1 heq.2)).elim
        · exact (not_lt_of_ge (hmax q hqS) (hqlt _ hcross)).elim
        · exact hcross
      · intro q hq r hr hqr
        obtain ⟨hqA, hqcard, hqcA, hqlt, hqsum⟩ := hs q (Finset.mem_of_mem_erase hq)
        obtain ⟨hrA, hrcard, hrcA, hrlt, hrsum⟩ := hs r (Finset.mem_of_mem_erase hr)
        have hqn : q.2 ∉ q.1 := fun hm => (lt_irrefl _ (hqlt _ hm))
        have hrn : r.2 ∉ r.1 := fun hm => (lt_irrefl _ (hrlt _ hm))
        have he : (∑ a ∈ q.1, a) + r.2 = (∑ a ∈ r.1, a) + q.2 := by
          have he' : ((∑ a ∈ q.1, a : ℕ) : ℤ) + r.2 =
              ((∑ a ∈ r.1, a : ℕ) : ℤ) + q.2 := by omega
          exact_mod_cast he'
        rcases h.signed_collision hqA hrA hqcard hrcard hqcA hrcA hqn hrn he with
            heq | hcross | hcross
        · exact Prod.ext heq.1 heq.2
        · exact (hqn (by simpa only [hqr] using hcross)).elim
        · exact (hrn (by simpa only [hqr] using hcross)).elim
    rw [hpcard, Finset.card_erase_of_mem hp] at hbound
    omega
  · have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [this]

/-- The analytic conclusion is equivalent to a discrete sparsity assertion. -/
lemma NtupleCondition.liminf_eq_zero_iff_cubic_sparsity {A : Set ℕ}
    (h : NtupleCondition A 3) :
    Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) = 0 ↔
      ∀ k M : ℕ, ∃ N ≥ M, k * (A ∩ Icc 1 N).ncard ^ 3 ≤ N := by
  refine ⟨?_, liminf_eq_zero_of_cubic_sparsity h⟩
  intro hz k M
  have hlo : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) :=
    Filter.isBoundedUnder_of ⟨0, fun N => by positivity⟩
  have hk : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hf := (Filter.liminf_le_iff
    (Filter.isCoboundedUnder_ge_of_le _ h.ratio_le_five) hlo).mp hz.le
      (1 / ((k + 1 : ℕ) : ℝ)) (by positivity)
  rw [Filter.frequently_atTop] at hf
  obtain ⟨N, hN, hratio⟩ := hf (max M 1)
  have hNM : M ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN1)
  refine ⟨N, hNM, ?_⟩
  have hr0 : 0 < (N : ℝ) ^ (1 / 3 : ℝ) := by positivity
  have hr3 : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = (N : ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
    norm_num
  have hc : ((A ∩ Icc 1 N).ncard : ℝ) <
      (N : ℝ) ^ (1 / 3 : ℝ) / ((k + 1 : ℕ) : ℝ) := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using (div_lt_iff₀ hr0).mp hratio
  have hm := (lt_div_iff₀ hk).mp hc
  have hc3 : (((A ∩ Icc 1 N).ncard : ℝ) * ((k + 1 : ℕ) : ℝ)) ^ 3 < N := by
    rw [← hr3]
    exact (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by decide : 3 ≠ 0)).mpr hm
  have hkn : k ≤ (k + 1) ^ 3 := by nlinarith [Nat.zero_le (k ^ 3), Nat.zero_le (k ^ 2)]
  have hkr : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 3 := by exact_mod_cast hkn
  have hresult : (k : ℝ) * ((A ∩ Icc 1 N).ncard : ℝ) ^ 3 < N := by
    calc
      (k : ℝ) * ((A ∩ Icc 1 N).ncard : ℝ) ^ 3 ≤
          ((k + 1 : ℕ) : ℝ) ^ 3 * ((A ∩ Icc 1 N).ncard : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hkr (by positivity)
      _ = (((A ∩ Icc 1 N).ncard : ℝ) * ((k + 1 : ℕ) : ℝ)) ^ 3 := by ring
      _ < N := hc3
  exact_mod_cast hresult.le

/-- Any counterexample must satisfy a uniform eventual cubic growth bound. -/
lemma NtupleCondition.liminf_ne_zero_iff_cubic_growth {A : Set ℕ}
    (h : NtupleCondition A 3) :
    Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) ≠ 0 ↔
      ∃ k M : ℕ, ∀ N ≥ M, N < k * (A ∩ Icc 1 N).ncard ^ 3 := by
  rw [ne_eq, h.liminf_eq_zero_iff_cubic_sparsity]
  push_neg
  rfl

/-- A uniform bound for a finite collection of signed sums in a prescribed set. -/
lemma NtupleCondition.signed_card_le_three_mul {A : Set ℕ}
    (h : NtupleCondition A 3) (S : Finset (Finset ℕ × ℕ)) (T : Finset ℤ)
    (hs : ∀ p ∈ S, (p.1 : Set ℕ) ⊆ A ∧ p.1.card = 2 ∧ p.2 ∈ A ∧
      (∀ a ∈ p.1, a < p.2) ∧ ((∑ a ∈ p.1, a : ℕ) : ℤ) - p.2 ∈ T) :
    S.card ≤ T.card * 3 := by
  classical
  rw [Nat.mul_comm T.card 3]
  apply Finset.card_le_mul_card_image_of_maps_to
    (f := fun p : Finset ℕ × ℕ => ((∑ a ∈ p.1, a : ℕ) : ℤ) - p.2)
    (fun p hp => (hs p hp).2.2.2.2) 3
  intro t ht
  apply h.signed_card_le_three t
  intro p hp
  obtain ⟨hpS, hpt⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpA, hpc, hpa, hplt, _⟩ := hs p hpS
  exact ⟨hpA, hpc, hpa, hplt, hpt⟩

/-- Only linearly many near-cancellations can fall in a fixed-width interval,
regardless of how large their summands are. -/
lemma NtupleCondition.signed_interval_card_le {A : Set ℕ}
    (h : NtupleCondition A 3) (S : Finset (Finset ℕ × ℕ)) (H : ℕ)
    (hs : ∀ p ∈ S, (p.1 : Set ℕ) ⊆ A ∧ p.1.card = 2 ∧ p.2 ∈ A ∧
      (∀ a ∈ p.1, a < p.2) ∧
      -(H : ℤ) ≤ ((∑ a ∈ p.1, a : ℕ) : ℤ) - p.2 ∧
      ((∑ a ∈ p.1, a : ℕ) : ℤ) - p.2 ≤ H) :
    S.card ≤ (2 * H + 1) * 3 := by
  classical
  have hb := h.signed_card_le_three_mul S (Finset.Icc (-(H : ℤ)) H) (by
    intro p hp
    obtain ⟨hpA, hpc, hpa, hplt, hlow, hupp⟩ := hs p hp
    exact ⟨hpA, hpc, hpa, hplt, Finset.mem_Icc.mpr ⟨hlow, hupp⟩⟩)
  have hc : (Finset.Icc (-(H : ℤ)) H).card = 2 * H + 1 := by
    rw [Int.card_Icc]
    omega
  simpa only [hc] using hb

/-- Ordered triples with bounded cancellation admit a bound independent of the
sizes of their entries. -/
lemma NtupleCondition.ordered_near_sum_card_le {A : Set ℕ}
    (h : NtupleCondition A 3) (S : Finset (ℕ × ℕ × ℕ)) (H : ℕ)
    (hs : ∀ p ∈ S, p.1 ∈ A ∧ p.2.1 ∈ A ∧ p.2.2 ∈ A ∧
      p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
      -(H : ℤ) ≤ (p.1 : ℤ) + p.2.1 - p.2.2 ∧
      (p.1 : ℤ) + p.2.1 - p.2.2 ≤ H) :
    S.card ≤ (2 * H + 1) * 3 := by
  classical
  let f : ℕ × ℕ × ℕ → Finset ℕ × ℕ := fun p => ({p.1, p.2.1}, p.2.2)
  have hinj : Set.InjOn f (S : Set (ℕ × ℕ × ℕ)) := by
    intro p hp q hq hpq
    obtain ⟨_, _, _, hpxy, _, _, _⟩ := hs p hp
    obtain ⟨_, _, _, hqxy, _, _, _⟩ := hs q hq
    have hec : p.2.2 = q.2.2 := congrArg (fun r : Finset ℕ × ℕ => r.2) hpq
    have heI : ({p.1, p.2.1} : Finset ℕ) = {q.1, q.2.1} := congrArg Prod.fst hpq
    have heS : ({p.1, p.2.1} : Set ℕ) = {q.1, q.2.1} := by
      simpa only [Finset.coe_pair] using congrArg (fun I : Finset ℕ => (I : Set ℕ)) heI
    rcases Set.pair_eq_pair_iff.mp heS with ⟨hpa, hpb⟩ | ⟨hpa, hpb⟩
    · exact Prod.ext hpa (Prod.ext hpb hec)
    · omega
  rw [← Finset.card_image_of_injOn hinj]
  apply h.signed_interval_card_le (S.image f) H
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hqa, hqb, hqc, hqab, hqbc, hlo, hup⟩ := hs q hq
  refine ⟨?_, ?_, hqc, ?_, ?_, ?_⟩
  · simpa only [f, Finset.coe_pair, Set.pair_subset_iff] using And.intro hqa hqb
  · exact Finset.card_pair hqab.ne
  · intro a ha
    simp only [f, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact lt_trans hqab hqbc
    · exact hqbc
  · simpa only [f, Finset.sum_pair hqab.ne, Nat.cast_add] using hlo
  · simpa only [f, Finset.sum_pair hqab.ne, Nat.cast_add] using hup

/-- A discrete convolution bound on the counts in equal-width blocks. The
index set can include blocks from many widely separated scales. -/
lemma NtupleCondition.block_convolution_bound {A : Set ℕ}
    (h : NtupleCondition A 3) (L : ℕ) (B : ℕ → Finset ℕ)
    (hA : ∀ i a, a ∈ B i → a ∈ A)
    (hB : ∀ i a, a ∈ B i → i * L < a ∧ a ≤ (i + 1) * L)
    (J : Finset (ℕ × ℕ)) (hJ : ∀ p ∈ J, 1 ≤ p.1 ∧ p.1 < p.2) :
    (∑ p ∈ J, (B p.1).card * (B p.2).card * (B (p.1 + p.2)).card) ≤
      (4 * L + 1) * 3 := by
  classical
  have hunique : ∀ i j a, a ∈ B i → a ∈ B j → i = j := by
    intro i j a hai haj
    obtain ⟨hil, hiu⟩ := hB i a hai
    obtain ⟨hjl, hju⟩ := hB j a haj
    rcases lt_trichotomy i j with hij | hij | hij
    · have hh := Nat.mul_le_mul_right L (show i + 1 ≤ j by omega)
      omega
    · exact hij
    · have hh := Nat.mul_le_mul_right L (show j + 1 ≤ i by omega)
      omega
  let T : ℕ × ℕ → Finset (ℕ × ℕ × ℕ) :=
    fun p => (B p.1).product ((B p.2).product (B (p.1 + p.2)))
  have hd : Set.PairwiseDisjoint (J : Set (ℕ × ℕ)) T := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro x hxp hxq
    obtain ⟨hpa, hpb, hpc⟩ :=
      show x.1 ∈ B p.1 ∧ x.2.1 ∈ B p.2 ∧ x.2.2 ∈ B (p.1 + p.2) by
        simpa only [T, Finset.product_eq_sprod, Finset.mem_product] using hxp
    obtain ⟨hqa, hqb, hqc⟩ :=
      show x.1 ∈ B q.1 ∧ x.2.1 ∈ B q.2 ∧ x.2.2 ∈ B (q.1 + q.2) by
        simpa only [T, Finset.product_eq_sprod, Finset.mem_product] using hxq
    exact hpq (Prod.ext (hunique _ _ _ hpa hqa) (hunique _ _ _ hpb hqb))
  have hu := h.ordered_near_sum_card_le (J.biUnion T) (2 * L) (by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hpa, hpb, hpc⟩ :=
      show x.1 ∈ B p.1 ∧ x.2.1 ∈ B p.2 ∧ x.2.2 ∈ B (p.1 + p.2) by
        simpa only [T, Finset.product_eq_sprod, Finset.mem_product] using hxp
    obtain ⟨hi, hij⟩ := hJ p hp
    obtain ⟨hal, hau⟩ := hB _ _ hpa
    obtain ⟨hbl, hbu⟩ := hB _ _ hpb
    obtain ⟨hcl, hcu⟩ := hB _ _ hpc
    have hxy : x.1 < x.2.1 := by
      have hh := Nat.mul_le_mul_right L (show p.1 + 1 ≤ p.2 by omega)
      omega
    have hyz : x.2.1 < x.2.2 := by
      have hh := Nat.mul_le_mul_right L (show p.2 + 1 ≤ p.1 + p.2 by omega)
      omega
    have hlo : x.2.2 ≤ x.1 + x.2.1 + 2 * L := by nlinarith
    have hup : x.1 + x.2.1 ≤ x.2.2 + 2 * L := by nlinarith
    have hlo' : (x.2.2 : ℤ) ≤ (x.1 : ℤ) + x.2.1 + 2 * L := by exact_mod_cast hlo
    have hup' : (x.1 : ℤ) + x.2.1 ≤ (x.2.2 : ℤ) + 2 * L := by exact_mod_cast hup
    exact ⟨hA _ _ hpa, hA _ _ hpb, hA _ _ hpc, hxy, hyz, by omega, by omega⟩)
  rw [Finset.card_biUnion hd] at hu
  have hwidth : 2 * (2 * L) = 4 * L := by ring
  simpa only [T, Finset.product_eq_sprod, Finset.card_product, hwidth, Nat.mul_assoc] using hu

noncomputable def intervalBlock (A : Set ℕ) (L i : ℕ) : Finset ℕ :=
  ((Set.finite_Ioc (i * L) ((i + 1) * L)).inter_of_right A).toFinset

@[simp] lemma mem_intervalBlock (A : Set ℕ) (L i a : ℕ) :
    a ∈ intervalBlock A L i ↔ a ∈ A ∧ i * L < a ∧ a ≤ (i + 1) * L := by
  simp only [intervalBlock, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_Ioc]

lemma card_intervalBlock_add (A : Set ℕ) (L i : ℕ) :
    (A ∩ Icc 1 (i * L)).ncard + (intervalBlock A L i).card =
      (A ∩ Icc 1 ((i + 1) * L)).ncard := by
  have hpart : A ∩ Icc 1 ((i + 1) * L) =
      (A ∩ Icc 1 (i * L)) ∪ (A ∩ Ioc (i * L) ((i + 1) * L)) := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_union, Set.mem_Ioc]
    have hm : i * L ≤ (i + 1) * L := Nat.mul_le_mul_right L (by omega)
    by_cases ha : a ∈ A
    · simp only [ha, true_and]
      omega
    · simp only [ha, false_and, false_or]
  have hd : Disjoint (A ∩ Icc 1 (i * L)) (A ∩ Ioc (i * L) ((i + 1) * L)) := by
    apply Set.disjoint_left.mpr
    intro a ha hb
    exact (not_lt_of_ge ha.2.2 hb.2.1)
  rw [hpart, Set.ncard_union_eq hd]
  congr 1
  exact (Set.ncard_eq_toFinset_card _
    ((Set.finite_Ioc (i * L) ((i + 1) * L)).inter_of_right A)).symm

lemma tendsto_scaled_count {A : Set ℕ} {c : ℝ}
    (hc : Tendsto (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds c)) (i : ℕ) (hi : 0 < i) :
    Tendsto (fun N => (A ∩ Icc 1 (i * N)).ncard / (N : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds (c * (i : ℝ) ^ (1 / 3 : ℝ))) := by
  have ht : Tendsto (fun N : ℕ => i * N) atTop atTop :=
    tendsto_atTop_mono (fun N => show N ≤ i * N by nlinarith) tendsto_id
  have hh := (hc.comp ht).mul_const ((i : ℝ) ^ (1 / 3 : ℝ))
  convert hh using 1
  funext N
  change ((A ∩ Icc 1 (i * N)).ncard : ℝ) / (N : ℝ) ^ (1 / 3 : ℝ) =
    ((A ∩ Icc 1 (i * N)).ncard : ℝ) / ((i * N : ℕ) : ℝ) ^ (1 / 3 : ℝ) *
      (i : ℝ) ^ (1 / 3 : ℝ)
  have hi0 : 0 < (i : ℝ) := by exact_mod_cast hi
  have hir : 0 < (i : ℝ) ^ (1 / 3 : ℝ) := by positivity
  by_cases hN : N = 0
  · simp [hN]
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hNr : 0 < (N : ℝ) ^ (1 / 3 : ℝ) := by positivity
  rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
  field_simp

lemma tendsto_intervalBlock {A : Set ℕ} {c : ℝ}
    (hc : Tendsto (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds c)) (i : ℕ) (hi : 0 < i) :
    Tendsto (fun L => ((intervalBlock A L i).card : ℝ) / (L : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds (c * (((i + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) -
        (i : ℝ) ^ (1 / 3 : ℝ)))) := by
  have ht := (tendsto_scaled_count hc (i + 1) (by omega)).sub
    (tendsto_scaled_count hc i hi)
  convert ht using 1
  · funext L
    rw [← sub_div]
    congr 1
    have hh : ((A ∩ Icc 1 (i * L)).ncard : ℝ) + (intervalBlock A L i).card =
        (A ∩ Icc 1 ((i + 1) * L)).ncard := by exact_mod_cast card_intervalBlock_add A L i
    linarith
  · rw [mul_sub]

noncomputable def cubeRootIncrement (i : ℕ) : ℝ :=
  ((i + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) - (i : ℝ) ^ (1 / 3 : ℝ)

lemma NtupleCondition.limit_block_convolution_bound {A : Set ℕ}
    (h : NtupleCondition A 3) {c : ℝ}
    (hc : Tendsto (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds c)) (J : Finset (ℕ × ℕ))
    (hJ : ∀ p ∈ J, 1 ≤ p.1 ∧ p.1 < p.2) :
    (∑ p ∈ J, (c * cubeRootIncrement p.1) * (c * cubeRootIncrement p.2) *
      (c * cubeRootIncrement (p.1 + p.2))) ≤ 12 := by
  classical
  let F : ℕ → ℝ := fun L => ∑ p ∈ J,
    ((intervalBlock A L p.1).card / (L : ℝ) ^ (1 / 3 : ℝ)) *
    ((intervalBlock A L p.2).card / (L : ℝ) ^ (1 / 3 : ℝ)) *
    ((intervalBlock A L (p.1 + p.2)).card / (L : ℝ) ^ (1 / 3 : ℝ))
  have ht : Tendsto F atTop (nhds (∑ p ∈ J,
      (c * cubeRootIncrement p.1) * (c * cubeRootIncrement p.2) *
        (c * cubeRootIncrement (p.1 + p.2)))) := by
    apply tendsto_finset_sum
    intro p hp
    obtain ⟨hi, hij⟩ := hJ p hp
    exact ((tendsto_intervalBlock hc p.1 (by omega)).mul
      (tendsto_intervalBlock hc p.2 (by omega))).mul
      (tendsto_intervalBlock hc (p.1 + p.2) (by omega))
  have hb : ∀ᶠ L : ℕ in atTop, F L ≤ 12 + 3 / (L : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with L hL
    have hL0 : 0 < (L : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hL)
    have hr0 : 0 < (L : ℝ) ^ (1 / 3 : ℝ) := by positivity
    have hr3 : ((L : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = (L : ℝ) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg L)]
      norm_num
    have hu := h.block_convolution_bound L (intervalBlock A L)
      (fun i a ha => (mem_intervalBlock A L i a).mp ha |>.1)
      (fun i a ha => (mem_intervalBlock A L i a).mp ha |>.2) J hJ
    have hur : (∑ p ∈ J, ((intervalBlock A L p.1).card : ℝ) *
        (intervalBlock A L p.2).card * (intervalBlock A L (p.1 + p.2)).card) ≤
        (4 * (L : ℝ) + 1) * 3 := by exact_mod_cast hu
    have heq : F L = (∑ p ∈ J, ((intervalBlock A L p.1).card : ℝ) *
        (intervalBlock A L p.2).card * (intervalBlock A L (p.1 + p.2)).card) / L := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      calc
        _ = (((intervalBlock A L p.1).card : ℝ) * (intervalBlock A L p.2).card *
            (intervalBlock A L (p.1 + p.2)).card) /
              ((L : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by
          field_simp
        _ = _ := by rw [hr3]
    rw [heq]
    calc
      _ ≤ ((4 * (L : ℝ) + 1) * 3) / L := div_le_div_of_nonneg_right hur hL0.le
      _ = 12 + 3 / (L : ℝ) := by field_simp; ring
  have hz : Tendsto (fun L : ℕ => (3 : ℝ) / L) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun L : ℕ => 12 + 3 / (L : ℝ)) atTop (nhds 12) := by
    simpa using (tendsto_const_nhds (x := (12 : ℝ))).add hz
  exact le_of_tendsto_of_tendsto ht hbound hb

lemma cubeRootIncrement_lower (i : ℕ) {R : ℝ} (hR : 0 < R)
    (hi : ((i + 1 : ℕ) : ℝ) ≤ R ^ (3 : ℕ)) :
    1 / (3 * R ^ (2 : ℕ)) ≤ cubeRootIncrement i := by
  let a : ℝ := (i : ℝ) ^ (1 / 3 : ℝ)
  let b : ℝ := ((i + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have ha3 : a ^ (3 : ℕ) = (i : ℝ) := by
    dsimp [a]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg i)]
    norm_num
  have hb3 : b ^ (3 : ℕ) = ((i + 1 : ℕ) : ℝ) := by
    dsimp [b]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg (i + 1))]
    norm_num
  have hab : a ≤ b := Real.rpow_le_rpow (by positivity)
    (by exact_mod_cast Nat.le_succ i) (by norm_num)
  have hbR : b ≤ R :=
    (pow_le_pow_iff_left₀ hb0 hR.le (by decide : 3 ≠ 0)).mp (by rwa [hb3])
  have haR : a ≤ R := le_trans hab hbR
  have hfac : (b - a) * (b ^ 2 + b * a + a ^ 2) = 1 := by
    push_cast at hb3
    nlinarith
  have hQ : b ^ 2 + b * a + a ^ 2 ≤ 3 * R ^ 2 := by
    have haa := mul_le_mul haR haR ha0 hR.le
    have hbb := mul_le_mul hbR hbR hb0 hR.le
    have hba := mul_le_mul hbR haR ha0 hR.le
    nlinarith
  change 1 / (3 * R ^ 2) ≤ b - a
  apply (div_le_iff₀ (by positivity : 0 < 3 * R ^ 2)).mpr
  calc
    1 = (b - a) * (b ^ 2 + b * a + a ^ 2) := hfac.symm
    _ ≤ (b - a) * (3 * R ^ 2) := mul_le_mul_of_nonneg_left hQ (sub_nonneg.mpr hab)

lemma cubeRootIncrement_lower_dyadic (i s : ℕ) (hi : i < 8 ^ (s + 1)) :
    1 / (12 * (4 : ℝ) ^ s) ≤ cubeRootIncrement i := by
  have hpow : ((2 : ℝ) ^ (s + 1)) ^ (3 : ℕ) = (8 : ℝ) ^ (s + 1) := by
    rw [← pow_mul, Nat.mul_comm (s + 1) 3, pow_mul]
    norm_num
  have hbound : ((i + 1 : ℕ) : ℝ) ≤ ((2 : ℝ) ^ (s + 1)) ^ (3 : ℕ) := by
    rw [hpow]
    exact_mod_cast (show i + 1 ≤ 8 ^ (s + 1) by omega)
  have hh := cubeRootIncrement_lower i (by positivity : 0 < (2 : ℝ) ^ (s + 1)) hbound
  have hdenom : 3 * ((2 : ℝ) ^ (s + 1)) ^ (2 : ℕ) = 12 * (4 : ℝ) ^ s := by
    rw [← pow_mul, Nat.mul_comm (s + 1) 2, pow_mul]
    norm_num
    rw [pow_succ]
    ring
  simpa only [hdenom] using hh

def dyadicPairBlock (s : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico (8 ^ s) (2 * 8 ^ s)).product (Finset.Ico (2 * 8 ^ s) (3 * 8 ^ s))

lemma mem_dyadicPairBlock (s : ℕ) (p : ℕ × ℕ) :
    p ∈ dyadicPairBlock s ↔
      (8 ^ s ≤ p.1 ∧ p.1 < 2 * 8 ^ s) ∧ (2 * 8 ^ s ≤ p.2 ∧ p.2 < 3 * 8 ^ s) := by
  simp only [dyadicPairBlock, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Ico]

lemma dyadicPairBlock_bounds {s : ℕ} {p : ℕ × ℕ} (hp : p ∈ dyadicPairBlock s) :
    (1 ≤ p.1 ∧ p.1 < p.2) ∧ p.1 < 8 ^ (s + 1) ∧ p.2 < 8 ^ (s + 1) ∧
      p.1 + p.2 < 8 ^ (s + 1) := by
  have hm : 0 < 8 ^ s := by positivity
  obtain ⟨⟨hil, hiu⟩, ⟨hjl, hju⟩⟩ := (mem_dyadicPairBlock s p).mp hp
  rw [pow_succ]
  omega

lemma dyadicPairBlock_disjoint {s t : ℕ} (hst : s ≠ t) :
    Disjoint (dyadicPairBlock s) (dyadicPairBlock t) := by
  apply Finset.disjoint_left.mpr
  intro p hps hpt
  obtain ⟨⟨hsl, hsu⟩, _⟩ := (mem_dyadicPairBlock s p).mp hps
  obtain ⟨⟨htl, htu⟩, _⟩ := (mem_dyadicPairBlock t p).mp hpt
  rcases lt_or_gt_of_ne hst with hst | hts
  · have hp := Nat.pow_le_pow_right (by decide : 0 < 8) (show s + 1 ≤ t by omega)
    rw [pow_succ] at hp
    omega
  · have hp := Nat.pow_le_pow_right (by decide : 0 < 8) (show t + 1 ≤ s by omega)
    rw [pow_succ] at hp
    omega

lemma card_dyadicPairBlock (s : ℕ) : (dyadicPairBlock s).card = (8 ^ s) ^ 2 := by
  rw [dyadicPairBlock, Finset.product_eq_sprod, Finset.card_product, Nat.card_Ico, Nat.card_Ico]
  have h₁ : 2 * 8 ^ s - 8 ^ s = 8 ^ s := by omega
  have h₂ : 3 * 8 ^ s - 2 * 8 ^ s = 8 ^ s := by omega
  rw [h₁, h₂, pow_two]

lemma cubeRootIncrement_block_lower (c : ℝ) (hc : 0 ≤ c) (s : ℕ) :
    c ^ 3 / 1728 ≤ ∑ p ∈ dyadicPairBlock s,
      (c * cubeRootIncrement p.1) * (c * cubeRootIncrement p.2) *
        (c * cubeRootIncrement (p.1 + p.2)) := by
  have hterm : ∀ p ∈ dyadicPairBlock s, (c / (12 * (4 : ℝ) ^ s)) ^ 3 ≤
      (c * cubeRootIncrement p.1) * (c * cubeRootIncrement p.2) *
        (c * cubeRootIncrement (p.1 + p.2)) := by
    intro p hp
    obtain ⟨_, hi, hj, hij⟩ := dyadicPairBlock_bounds hp
    have hi' : c / (12 * (4 : ℝ) ^ s) ≤ c * cubeRootIncrement p.1 := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
        (cubeRootIncrement_lower_dyadic p.1 s hi) hc
    have hj' : c / (12 * (4 : ℝ) ^ s) ≤ c * cubeRootIncrement p.2 := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
        (cubeRootIncrement_lower_dyadic p.2 s hj) hc
    have hij' : c / (12 * (4 : ℝ) ^ s) ≤ c * cubeRootIncrement (p.1 + p.2) := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
        (cubeRootIncrement_lower_dyadic (p.1 + p.2) s hij) hc
    have hqi : 0 ≤ c * cubeRootIncrement p.1 := le_trans (by positivity) hi'
    have hqj : 0 ≤ c * cubeRootIncrement p.2 := le_trans (by positivity) hj'
    have hh := mul_le_mul (mul_le_mul hi' hj' (by positivity) hqi) hij'
      (by positivity) (mul_nonneg hqi hqj)
    convert hh using 1
    ring
  have hsum := Finset.sum_le_sum hterm
  have heq : (∑ _p ∈ dyadicPairBlock s, (c / (12 * (4 : ℝ) ^ s)) ^ 3) = c ^ 3 / 1728 := by
    rw [Finset.sum_const, nsmul_eq_mul, card_dyadicPairBlock]
    push_cast
    have hp : ((8 : ℝ) ^ s) ^ (2 : ℕ) = ((4 : ℝ) ^ s) ^ (3 : ℕ) := by
      calc
        ((8 : ℝ) ^ s) ^ (2 : ℕ) = (64 : ℝ) ^ s := by
          rw [← pow_mul, Nat.mul_comm s 2, pow_mul]
          norm_num
        _ = ((4 : ℝ) ^ s) ^ (3 : ℕ) := by
          symm
          rw [← pow_mul, Nat.mul_comm s 3, pow_mul]
          norm_num
    rw [hp]
    field_simp
    ring
  rwa [heq] at hsum

/-- If the normalized counting function has a full limit, that limit is zero.
This does not assume or prove that a full limit exists. -/
lemma NtupleCondition.full_limit_eq_zero {A : Set ℕ}
    (h : NtupleCondition A 3) {c : ℝ}
    (hc : Tendsto (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds c)) : c = 0 := by
  classical
  have hc0 : 0 ≤ c := ge_of_tendsto hc (Filter.Eventually.of_forall fun N => by positivity)
  have hb : ∀ K : ℕ, (K : ℝ) * (c ^ 3 / 1728) ≤ 12 := by
    intro K
    have hd : Set.PairwiseDisjoint ((Finset.range K : Finset ℕ) : Set ℕ) dyadicPairBlock := by
      intro s hs t ht hst
      exact dyadicPairBlock_disjoint hst
    have hu := h.limit_block_convolution_bound hc ((Finset.range K).biUnion dyadicPairBlock) (by
      intro p hp
      obtain ⟨s, hs, hps⟩ := Finset.mem_biUnion.mp hp
      exact (dyadicPairBlock_bounds hps).1)
    rw [Finset.sum_biUnion hd] at hu
    calc
      (K : ℝ) * (c ^ 3 / 1728) = ∑ _s ∈ Finset.range K, c ^ 3 / 1728 := by simp
      _ ≤ ∑ s ∈ Finset.range K, ∑ p ∈ dyadicPairBlock s,
          (c * cubeRootIncrement p.1) * (c * cubeRootIncrement p.2) *
            (c * cubeRootIncrement (p.1 + p.2)) :=
        Finset.sum_le_sum fun s hs => cubeRootIncrement_block_lower c hc0 s
      _ ≤ 12 := hu
  by_contra hn
  have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hn)
  have htpos : 0 < c ^ 3 / 1728 := by positivity
  obtain ⟨K, hK⟩ := exists_nat_gt (12 / (c ^ 3 / 1728))
  have hgt : 12 < (K : ℝ) * (c ^ 3 / 1728) := (div_lt_iff₀ htpos).mp hK
  exact (not_lt_of_ge (hb K)) hgt

lemma NtupleCondition.subsequence_block_convolution_bound {A : Set ℕ}
    (h : NtupleCondition A 3) {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop) {b : ℕ → ℝ}
    (hb : ∀ i, 0 < i → Tendsto
      (fun n => ((intervalBlock A (L n) i).card : ℝ) / (L n : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds (b i))) (J : Finset (ℕ × ℕ))
    (hJ : ∀ p ∈ J, 1 ≤ p.1 ∧ p.1 < p.2) :
    (∑ p ∈ J, (b p.1) * (b p.2) *
      (b (p.1 + p.2))) ≤ 12 := by
  classical
  let F : ℕ → ℝ := fun L => ∑ p ∈ J,
    ((intervalBlock A L p.1).card / (L : ℝ) ^ (1 / 3 : ℝ)) *
    ((intervalBlock A L p.2).card / (L : ℝ) ^ (1 / 3 : ℝ)) *
    ((intervalBlock A L (p.1 + p.2)).card / (L : ℝ) ^ (1 / 3 : ℝ))
  have ht : Tendsto (fun n => F (L n)) atTop (nhds (∑ p ∈ J,
      (b p.1) * (b p.2) *
        (b (p.1 + p.2)))) := by
    apply tendsto_finset_sum
    intro p hp
    obtain ⟨hi, hij⟩ := hJ p hp
    exact ((hb p.1 (by omega)).mul
      (hb p.2 (by omega))).mul
      (hb (p.1 + p.2) (by omega))
  have hbound_nat : ∀ᶠ L : ℕ in atTop, F L ≤ 12 + 3 / (L : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with L hL
    have hL0 : 0 < (L : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hL)
    have hr0 : 0 < (L : ℝ) ^ (1 / 3 : ℝ) := by positivity
    have hr3 : ((L : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = (L : ℝ) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg L)]
      norm_num
    have hu := h.block_convolution_bound L (intervalBlock A L)
      (fun i a ha => (mem_intervalBlock A L i a).mp ha |>.1)
      (fun i a ha => (mem_intervalBlock A L i a).mp ha |>.2) J hJ
    have hur : (∑ p ∈ J, ((intervalBlock A L p.1).card : ℝ) *
        (intervalBlock A L p.2).card * (intervalBlock A L (p.1 + p.2)).card) ≤
        (4 * (L : ℝ) + 1) * 3 := by exact_mod_cast hu
    have heq : F L = (∑ p ∈ J, ((intervalBlock A L p.1).card : ℝ) *
        (intervalBlock A L p.2).card * (intervalBlock A L (p.1 + p.2)).card) / L := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      calc
        _ = (((intervalBlock A L p.1).card : ℝ) * (intervalBlock A L p.2).card *
            (intervalBlock A L (p.1 + p.2)).card) /
              ((L : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by
          field_simp
        _ = _ := by rw [hr3]
    rw [heq]
    calc
      _ ≤ ((4 * (L : ℝ) + 1) * 3) / L := div_le_div_of_nonneg_right hur hL0.le
      _ = 12 + 3 / (L : ℝ) := by field_simp; ring
  have hz : Tendsto (fun L : ℕ => (3 : ℝ) / L) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun L : ℕ => 12 + 3 / (L : ℝ)) atTop (nhds 12) := by
    simpa using (tendsto_const_nhds (x := (12 : ℝ))).add hz
  exact le_of_tendsto_of_tendsto ht (hbound.comp hL) (hL.eventually hbound_nat)

lemma NtupleCondition.subsequence_block_limit_eq_zero {A : Set ℕ}
    (h : NtupleCondition A 3) {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ i, 0 < i → Tendsto
      (fun n => ((intervalBlock A (L n) i).card : ℝ) / (L n : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds (c * cubeRootIncrement i))) : c = 0 := by
  classical
  have hb : ∀ K : ℕ, (K : ℝ) * (c ^ 3 / 1728) ≤ 12 := by
    intro K
    have hd : Set.PairwiseDisjoint ((Finset.range K : Finset ℕ) : Set ℕ) dyadicPairBlock := by
      intro s hs t ht hst
      exact dyadicPairBlock_disjoint hst
    have hu := h.subsequence_block_convolution_bound hL hc ((Finset.range K).biUnion dyadicPairBlock) (by
      intro p hp
      obtain ⟨s, hs, hps⟩ := Finset.mem_biUnion.mp hp
      exact (dyadicPairBlock_bounds hps).1)
    rw [Finset.sum_biUnion hd] at hu
    calc
      (K : ℝ) * (c ^ 3 / 1728) = ∑ _s ∈ Finset.range K, c ^ 3 / 1728 := by simp
      _ ≤ ∑ s ∈ Finset.range K, ∑ p ∈ dyadicPairBlock s,
          (c * cubeRootIncrement p.1) * (c * cubeRootIncrement p.2) *
            (c * cubeRootIncrement (p.1 + p.2)) :=
        Finset.sum_le_sum fun s hs => cubeRootIncrement_block_lower c hc0 s
      _ ≤ 12 := hu
  by_contra hn
  have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hn)
  have htpos : 0 < c ^ 3 / 1728 := by positivity
  obtain ⟨K, hK⟩ := exists_nat_gt (12 / (c ^ 3 / 1728))
  have hgt : 12 < (K : ℝ) * (c ^ 3 / 1728) := (div_lt_iff₀ htpos).mp hK
  exact (not_lt_of_ge (hb K)) hgt


/-- The full-limit conclusion still holds if convergence is only known along one
unbounded sequence, provided that the same limit holds at every fixed positive
integer dilation of that sequence. -/
lemma NtupleCondition.dilation_subsequence_limit_eq_zero {A : Set ℕ}
    (h : NtupleCondition A 3) {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop) {c : ℝ}
    (hc : ∀ i, 0 < i → Tendsto
      (fun n => (A ∩ Icc 1 (i * L n)).ncard /
        ((i * L n : ℕ) : ℝ) ^ (1 / 3 : ℝ)) atTop (nhds c)) : c = 0 := by
  have hc0 : 0 ≤ c := ge_of_tendsto (hc 1 (by omega))
    (Filter.Eventually.of_forall fun n => by positivity)
  have hscaled : ∀ i, 0 < i → Tendsto
      (fun n => (A ∩ Icc 1 (i * L n)).ncard / (L n : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds (c * (i : ℝ) ^ (1 / 3 : ℝ))) := by
    intro i hi
    have hh := (hc i hi).mul_const ((i : ℝ) ^ (1 / 3 : ℝ))
    convert hh using 1
    funext n
    have hi0 : 0 < (i : ℝ) := by exact_mod_cast hi
    have hir : 0 < (i : ℝ) ^ (1 / 3 : ℝ) := by positivity
    by_cases hn : L n = 0
    · simp [hn]
    have hn0 : 0 < (L n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnr : 0 < (L n : ℝ) ^ (1 / 3 : ℝ) := by positivity
    rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
    field_simp
  apply h.subsequence_block_limit_eq_zero hL hc0
  intro i hi
  have ht := (hscaled (i + 1) (by omega)).sub (hscaled i hi)
  convert ht using 1
  · funext n
    rw [← sub_div]
    congr 1
    have hh : ((A ∩ Icc 1 (i * L n)).ncard : ℝ) +
        (intervalBlock A (L n) i).card =
        (A ∩ Icc 1 ((i + 1) * L n)).ncard := by
      exact_mod_cast card_intervalBlock_add A (L n) i
    linarith
  · simp only [cubeRootIncrement, mul_sub]

lemma NtupleCondition.liminf_eq_zero_of_zero_subsequence {A : Set ℕ}
    (h : NtupleCondition A 3) {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop)
    (hc : Tendsto
      (fun n => (A ∩ Icc 1 (L n)).ncard / (L n : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds 0)) :
    Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) = 0 := by
  apply le_antisymm ?_ h.liminf_nonneg
  have hlo : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) :=
    Filter.isBoundedUnder_of ⟨0, fun N => by positivity⟩
  apply (Filter.liminf_le_iff
    (Filter.isCoboundedUnder_ge_of_le _ h.ratio_le_five) hlo).mpr
  intro ε hε
  rw [Filter.frequently_atTop]
  intro M
  obtain ⟨n, hn, hf⟩ := ((hL.eventually (Filter.eventually_ge_atTop M)).and
    (hc.eventually (eventually_lt_nhds hε))).exists
  exact ⟨L n, hn, hf⟩

/-- A fixed signed sum has bounded multiplicity even without any ordering
condition on the three distinct elements. -/
lemma NtupleCondition.signed_card_le_five {A : Set ℕ}
    (h : NtupleCondition A 3) (t : ℤ) (S : Finset (Finset ℕ × ℕ))
    (hs : ∀ p ∈ S, (p.1 : Set ℕ) ⊆ A ∧ p.1.card = 2 ∧ p.2 ∈ A ∧
      p.2 ∉ p.1 ∧ ((∑ a ∈ p.1, a : ℕ) : ℤ) - p.2 = t) :
    S.card ≤ 5 := by
  classical
  have hrel : ∀ p ∈ S, ∀ q ∈ S,
      p = q ∨ q.2 ∈ p.1 ∨ p.2 ∈ q.1 := by
    intro p hp q hq
    obtain ⟨hpA, hpc, hpa, hpn, hpt⟩ := hs p hp
    obtain ⟨hqA, hqc, hqa, hqn, hqt⟩ := hs q hq
    have he : (∑ a ∈ p.1, a) + q.2 = (∑ a ∈ q.1, a) + p.2 := by
      have he' : ((∑ a ∈ p.1, a : ℕ) : ℤ) + q.2 =
          ((∑ a ∈ q.1, a : ℕ) : ℤ) + p.2 := by omega
      exact_mod_cast he'
    rcases h.signed_collision hpA hqA hpc hqc hpa hqa hpn hqn he with heq | heq
    · exact Or.inl (Prod.ext heq.1 heq.2)
    · exact Or.inr heq
  have hinj : Set.InjOn (fun p : Finset ℕ × ℕ => p.2) (S : Set (Finset ℕ × ℕ)) := by
    intro p hp q hq he
    rcases hrel p hp q hq with hsame | hcross | hcross
    · exact hsame
    · exact ((hs p hp).2.2.2.1 (by simpa only [he] using hcross)).elim
    · exact ((hs q hq).2.2.2.1 (by simpa only [he] using hcross)).elim
  have hdeg : ∀ p ∈ S, ∑ q ∈ S, (if q.2 ∈ p.1 then (1 : ℕ) else 0) ≤ 2 := by
    intro p hp
    have hh : (S.filter fun q => q.2 ∈ p.1).card ≤ p.1.card := by
      apply Finset.card_le_card_of_injOn (fun q : Finset ℕ × ℕ => q.2)
      · intro q hq
        exact (Finset.mem_filter.mp hq).2
      · intro q hq r hr he
        exact hinj (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hr).1 he
    simpa [(hs p hp).2.1] using hh
  have hsum : (∑ p ∈ S, ∑ q ∈ S,
      (if q.2 ∈ p.1 then (1 : ℕ) else 0)) ≤ 2 * S.card := by
    calc
      _ ≤ ∑ _p ∈ S, (2 : ℕ) := Finset.sum_le_sum hdeg
      _ = 2 * S.card := by simp [Nat.mul_comm]
  have hpair : (∑ p ∈ S, ∑ q ∈ S, (1 : ℕ)) ≤ ∑ p ∈ S, ∑ q ∈ S,
      ((if p = q then 1 else 0) + (if q.2 ∈ p.1 then 1 else 0) +
        (if p.2 ∈ q.1 then 1 else 0)) := by
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.sum_le_sum
    intro q hq
    rcases hrel p hp q hq with he | he | he <;> simp [he] <;> omega
  have hswap : (∑ p ∈ S, ∑ q ∈ S, (if p.2 ∈ q.1 then (1 : ℕ) else 0)) =
      ∑ p ∈ S, ∑ q ∈ S, (if q.2 ∈ p.1 then (1 : ℕ) else 0) :=
    Finset.sum_comm
  simp only [Finset.sum_add_distrib] at hpair
  rw [hswap] at hpair
  have hdiag : (∑ p ∈ S, ∑ q ∈ S, (if p = q then (1 : ℕ) else 0)) = S.card := by
    simp
  rw [hdiag] at hpair
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.mul_one] at hpair
  nlinarith

/-- Uniform multiplicity for arbitrary signed sums whose values lie in a
prescribed finite set. No relative ordering of their entries is assumed. -/
lemma NtupleCondition.signed_card_le_five_mul {A : Set ℕ}
    (h : NtupleCondition A 3) (S : Finset (Finset ℕ × ℕ)) (T : Finset ℤ)
    (hs : ∀ p ∈ S, (p.1 : Set ℕ) ⊆ A ∧ p.1.card = 2 ∧ p.2 ∈ A ∧
      p.2 ∉ p.1 ∧ ((∑ a ∈ p.1, a : ℕ) : ℤ) - p.2 ∈ T) :
    S.card ≤ T.card * 5 := by
  classical
  rw [Nat.mul_comm T.card 5]
  apply Finset.card_le_mul_card_image_of_maps_to
    (f := fun p : Finset ℕ × ℕ => ((∑ a ∈ p.1, a : ℕ) : ℤ) - p.2)
    (fun p hp => (hs p hp).2.2.2.2) 5
  intro t ht
  apply h.signed_card_le_five t
  intro p hp
  obtain ⟨hpS, hpt⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpA, hpc, hpa, hpn, _⟩ := hs p hpS
  exact ⟨hpA, hpc, hpa, hpn, hpt⟩

/-- A signed-sum bound in an interval with an arbitrary integer center. -/
lemma NtupleCondition.signed_translated_interval_card_le {A : Set ℕ}
    (h : NtupleCondition A 3) (S : Finset (Finset ℕ × ℕ)) (t : ℤ) (H : ℕ)
    (hs : ∀ p ∈ S, (p.1 : Set ℕ) ⊆ A ∧ p.1.card = 2 ∧ p.2 ∈ A ∧
      p.2 ∉ p.1 ∧
      t - H ≤ ((∑ a ∈ p.1, a : ℕ) : ℤ) - p.2 ∧
      ((∑ a ∈ p.1, a : ℕ) : ℤ) - p.2 ≤ t + H) :
    S.card ≤ (2 * H + 1) * 5 := by
  classical
  have hb := h.signed_card_le_five_mul S (Finset.Icc (t - H) (t + H)) (by
    intro p hp
    obtain ⟨hpA, hpc, hpa, hpn, hlow, hupp⟩ := hs p hp
    exact ⟨hpA, hpc, hpa, hpn, Finset.mem_Icc.mpr ⟨hlow, hupp⟩⟩)
  have hc : (Finset.Icc (t - H) (t + H)).card = 2 * H + 1 := by
    rw [Int.card_Icc]
    omega
  simpa only [hc] using hb

/-- Triple uniqueness bounds counts in any interval by its width, independently
of the location of that interval. -/
lemma NtupleCondition.choose_card_le_interval {A : Set ℕ} {n : ℕ}
    (h : NtupleCondition A n) (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A)
    (L H : ℕ) (hI : ∀ a ∈ S, L ≤ a ∧ a ≤ L + H) :
    S.card.choose n ≤ n * H + 1 := by
  classical
  have hcard : (Finset.Icc (n * L) (n * (L + H))).card = n * H + 1 := by
    rw [Nat.card_Icc, Nat.mul_add]
    omega
  rw [← Finset.card_powersetCard n S, ← hcard]
  apply Finset.card_le_card_of_injOn (fun I : Finset ℕ => ∑ a ∈ I, a)
  · intro I hIS
    obtain ⟨hsub, hIc⟩ := Finset.mem_powersetCard.mp hIS
    simp only [Finset.mem_coe, Finset.mem_Icc]
    constructor
    · calc
        n * L = ∑ _a ∈ I, L := by simp [hIc]
        _ ≤ ∑ a ∈ I, a := Finset.sum_le_sum fun a ha => (hI a (hsub ha)).1
    · calc
        (∑ a ∈ I, a) ≤ ∑ _a ∈ I, (L + H) :=
          Finset.sum_le_sum fun a ha => (hI a (hsub ha)).2
        _ = n * (L + H) := by simp [hIc]
  · intro I hI J hJ heq
    obtain ⟨hIS, hIc⟩ := Finset.mem_powersetCard.mp hI
    obtain ⟨hJS, hJc⟩ := Finset.mem_powersetCard.mp hJ
    exact h I J ⟨fun a ha => hS (hIS ha), fun a ha => hS (hJS ha), hIc, hJc, heq⟩

lemma NtupleCondition.cube_bound_interval {A : Set ℕ}
    (h : NtupleCondition A 3) (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A)
    (L H : ℕ) (hI : ∀ a ∈ S, L ≤ a ∧ a ≤ L + H) :
    (((S.card + 1 - 3 : ℕ) : ℝ) ^ 3) ≤ 18 * (H : ℝ) + 6 := by
  have hb : ((S.card.choose 3 : ℕ) : ℝ) ≤ 3 * (H : ℝ) + 1 := by
    exact_mod_cast h.choose_card_le_interval S hS L H hI
  have hp := Nat.pow_le_choose (α := ℝ) 3 S.card
  norm_num at hp
  linarith

/-- Two equal sums with one more summand than the uniqueness hypothesis must
coincide if the corresponding sets have a common element. -/
lemma NtupleCondition.eq_of_common_mem_succ {A : Set ℕ} {n : ℕ}
    (h : NtupleCondition A n) {I J : Finset ℕ}
    (hI : (I : Set ℕ) ⊆ A) (hJ : (J : Set ℕ) ⊆ A)
    (hIc : I.card = n + 1) (hJc : J.card = n + 1)
    (he : ∑ a ∈ I, a = ∑ a ∈ J, a) {a : ℕ} (haI : a ∈ I) (haJ : a ∈ J) :
    I = J := by
  classical
  have he' : ∑ b ∈ I.erase a, b = ∑ b ∈ J.erase a, b := by
    have hi := Finset.sum_erase_add I (fun b : ℕ => b) haI
    have hj := Finset.sum_erase_add J (fun b : ℕ => b) haJ
    dsimp only at hi hj
    omega
  have herase : I.erase a = J.erase a := h _ _ ⟨
    fun b hb => hI (Finset.mem_of_mem_erase hb),
    fun b hb => hJ (Finset.mem_of_mem_erase hb),
    by simp [Finset.card_erase_of_mem haI, hIc],
    by simp [Finset.card_erase_of_mem haJ, hJc], he'⟩
  calc
    I = insert a (I.erase a) := (Finset.insert_erase haI).symm
    _ = insert a (J.erase a) := congrArg (insert a) herase
    _ = J := Finset.insert_erase haJ

/-- Equal sums of `n+1` distinct elements form a disjoint family when sums of
`n` distinct elements are unique. In particular, each four-sum fiber in a
triple-unique set occupies four fresh elements per representation. -/
lemma NtupleCondition.succ_sum_family_card_bound {A : Set ℕ} {n : ℕ}
    (h : NtupleCondition A n) (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A)
    (t : ℕ) (F : Finset (Finset ℕ))
    (hF : ∀ I ∈ F, I ⊆ S ∧ I.card = n + 1 ∧ ∑ a ∈ I, a = t) :
    (n + 1) * F.card ≤ S.card := by
  classical
  have hd : Set.PairwiseDisjoint (F : Set (Finset ℕ)) (fun I => I) := by
    intro I hIF J hJF hne
    apply Finset.disjoint_left.mpr
    intro a haI haJ
    obtain ⟨hIS, hIc, hIt⟩ := hF I hIF
    obtain ⟨hJS, hJc, hJt⟩ := hF J hJF
    exact hne (h.eq_of_common_mem_succ (fun b hb => hS (hIS hb))
      (fun b hb => hS (hJS hb)) hIc hJc (hIt.trans hJt.symm) haI haJ)
  have hsub : F.biUnion (fun I => I) ⊆ S := by
    intro a ha
    obtain ⟨I, hIF, haI⟩ := Finset.mem_biUnion.mp ha
    exact (hF I hIF).1 haI
  calc
    (n + 1) * F.card = ∑ I ∈ F, I.card := by
      rw [Finset.sum_congr rfl (fun I hIF => (hF I hIF).2.1)]
      simp [Nat.mul_comm]
    _ = (F.biUnion (fun I => I)).card := (Finset.card_biUnion hd).symm
    _ ≤ S.card := Finset.card_le_card hsub

lemma NtupleCondition.distinct_near_sum_card_le {A : Set ℕ}
    (h : NtupleCondition A 3) (S : Finset (ℕ × ℕ × ℕ)) (H : ℕ)
    (hs : ∀ p ∈ S, p.1 ∈ A ∧ p.2.1 ∈ A ∧ p.2.2 ∈ A ∧
      p.1 < p.2.1 ∧ p.2.2 ≠ p.1 ∧ p.2.2 ≠ p.2.1 ∧
      -(H : ℤ) ≤ (p.1 : ℤ) + p.2.1 - p.2.2 ∧
      (p.1 : ℤ) + p.2.1 - p.2.2 ≤ H) :
    S.card ≤ (2 * H + 1) * 5 := by
  classical
  let f : ℕ × ℕ × ℕ → Finset ℕ × ℕ := fun p => ({p.1, p.2.1}, p.2.2)
  have hinj : Set.InjOn f (S : Set (ℕ × ℕ × ℕ)) := by
    intro p hp q hq hpq
    have hpxy := (hs p hp).2.2.2.1
    have hqxy := (hs q hq).2.2.2.1
    have hec : p.2.2 = q.2.2 := congrArg (fun r : Finset ℕ × ℕ => r.2) hpq
    have heI : ({p.1, p.2.1} : Finset ℕ) = {q.1, q.2.1} := congrArg Prod.fst hpq
    have heS : ({p.1, p.2.1} : Set ℕ) = {q.1, q.2.1} := by
      simpa only [Finset.coe_pair] using congrArg (fun I : Finset ℕ => (I : Set ℕ)) heI
    rcases Set.pair_eq_pair_iff.mp heS with ⟨hpa, hpb⟩ | ⟨hpa, hpb⟩
    · exact Prod.ext hpa (Prod.ext hpb hec)
    · omega
  rw [← Finset.card_image_of_injOn hinj]
  apply h.signed_translated_interval_card_le (S.image f) 0 H
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hqa, hqb, hqc, hqab, hqca, hqcb, hlo, hup⟩ := hs q hq
  refine ⟨?_, ?_, hqc, ?_, ?_, ?_⟩
  · simpa only [f, Finset.coe_pair, Set.pair_subset_iff] using And.intro hqa hqb
  · exact Finset.card_pair hqab.ne
  · simpa only [f, Finset.mem_insert, Finset.mem_singleton, not_or] using And.intro hqca hqcb
  · simpa only [f, Finset.sum_pair hqab.ne, Nat.cast_add, zero_sub] using hlo
  · simpa only [f, Finset.sum_pair hqab.ne, Nat.cast_add, zero_add] using hup

/-- A small prefix amplifies the bound on close pairs in all later blocks.
The diagonal term is displayed explicitly so the bound has a polynomial form. -/
lemma NtupleCondition.tail_block_square_bound {A : Set ℕ}
    (h : NtupleCondition A 3) (L : ℕ) (P : Finset ℕ)
    (hP : (P : Set ℕ) ⊆ A) (hPL : ∀ a ∈ P, a ≤ L)
    (B : ℕ → Finset ℕ) (hBA : ∀ i a, a ∈ B i → a ∈ A)
    (hB : ∀ i a, a ∈ B i → i * L < a ∧ a ≤ (i + 1) * L)
    (J : Finset ℕ) (hJ : ∀ i ∈ J, 1 ≤ i) :
    P.card * (∑ i ∈ J, (B i).card ^ 2) ≤
      (4 * L + 1) * 5 + P.card * (∑ i ∈ J, (B i).card) := by
  classical
  let T : ℕ → Finset (ℕ × ℕ × ℕ) := fun i => P.product (B i).offDiag
  have hunique : ∀ i j a, a ∈ B i → a ∈ B j → i = j := by
    intro i j a hai haj
    obtain ⟨hil, hiu⟩ := hB i a hai
    obtain ⟨hjl, hju⟩ := hB j a haj
    rcases lt_trichotomy i j with hij | hij | hij
    · have hh := Nat.mul_le_mul_right L (show i + 1 ≤ j by omega)
      omega
    · exact hij
    · have hh := Nat.mul_le_mul_right L (show j + 1 ≤ i by omega)
      omega
  have hd : Set.PairwiseDisjoint (J : Set ℕ) T := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    have hbi : p.2.1 ∈ B i := by
      simpa only [T, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_offDiag] using
        ((show p.1 ∈ P ∧ p.2 ∈ (B i).offDiag by
          simpa only [T, Finset.product_eq_sprod, Finset.mem_product] using hpi).2 |>
          Finset.mem_offDiag.mp |>.1)
    have hbj : p.2.1 ∈ B j :=
      (Finset.mem_offDiag.mp (Finset.mem_product.mp hpj).2).1
    exact hij (hunique i j p.2.1 hbi hbj)
  have hu := h.distinct_near_sum_card_le (J.biUnion T) (2 * L) (by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
    have hp' : p.1 ∈ P ∧ p.2 ∈ (B i).offDiag := by
      simpa only [T, Finset.product_eq_sprod, Finset.mem_product] using hpi
    obtain ⟨hpb, hpc, hbc⟩ := Finset.mem_offDiag.mp hp'.2
    obtain ⟨hbl, hbu⟩ := hB i p.2.1 hpb
    obtain ⟨hcl, hcu⟩ := hB i p.2.2 hpc
    have ha := hPL p.1 hp'.1
    have hiL : L ≤ i * L := by nlinarith [hJ i hi]
    have hab : p.1 < p.2.1 := by omega
    have hca : p.2.2 ≠ p.1 := by omega
    have hlo : p.2.2 ≤ p.1 + p.2.1 + 2 * L := by nlinarith
    have hup : p.1 + p.2.1 ≤ p.2.2 + 2 * L := by nlinarith
    have hlo' : (p.2.2 : ℤ) ≤ (p.1 : ℤ) + p.2.1 + 2 * L := by exact_mod_cast hlo
    have hup' : (p.1 : ℤ) + p.2.1 ≤ (p.2.2 : ℤ) + 2 * L := by exact_mod_cast hup
    exact ⟨hP hp'.1, hBA i _ hpb, hBA i _ hpc, hab, hca, hbc.symm, by omega, by omega⟩)
  rw [Finset.card_biUnion hd] at hu
  simp only [T, Finset.product_eq_sprod, Finset.card_product, Finset.offDiag_card] at hu
  rw [← Finset.mul_sum] at hu
  have hdecomp : (∑ i ∈ J, ((B i).card * (B i).card - (B i).card)) +
      (∑ i ∈ J, (B i).card) = ∑ i ∈ J, (B i).card ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hn : (B i).card ≤ (B i).card * (B i).card := by nlinarith
    rw [Nat.sub_add_cancel hn, pow_two]
  nlinarith


/-- Every block scaling profile obeys a global square bound on its tail. -/
lemma NtupleCondition.subsequence_tail_square_bound {A : Set ℕ}
    (h : NtupleCondition A 3) {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop) {b : ℕ → ℝ}
    (hb : ∀ i, Tendsto
      (fun n => ((intervalBlock A (L n) i).card : ℝ) / (L n : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds (b i))) (J : Finset ℕ) (hJ : ∀ i ∈ J, 1 ≤ i) :
    b 0 * (∑ i ∈ J, (b i) ^ 2) ≤ 20 := by
  classical
  let R : ℕ → ℝ := fun n => (L n : ℝ) ^ (1 / 3 : ℝ)
  let C : ℕ → ℕ → ℝ := fun n i => (intervalBlock A (L n) i).card
  let f : ℕ → ℕ → ℝ := fun n i => C n i / R n
  have hf : ∀ i, Tendsto (fun n => f n i) atTop (nhds (b i)) := hb
  have hR : Tendsto R atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      (tendsto_natCast_atTop_atTop.comp hL)
  have hsmall : Tendsto (fun n => f n 0 * (∑ i ∈ J, f n i) / R n)
      atTop (nhds 0) :=
    ((hf 0).mul (tendsto_finset_sum _ (fun i _ => hf i))).div_atTop hR
  have hz : Tendsto (fun n => (5 : ℝ) / L n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hL)
  have hbound : Tendsto
      (fun n => 20 + 5 / (L n : ℝ) + f n 0 * (∑ i ∈ J, f n i) / R n)
      atTop (nhds 20) := by
    simpa using ((tendsto_const_nhds (x := (20 : ℝ))).add hz).add hsmall
  have ht : Tendsto (fun n => f n 0 * (∑ i ∈ J, (f n i) ^ 2))
      atTop (nhds (b 0 * (∑ i ∈ J, (b i) ^ 2))) :=
    (hf 0).mul (tendsto_finset_sum _ (fun i _ => (hf i).pow 2))
  apply le_of_tendsto_of_tendsto ht hbound
  filter_upwards [hL.eventually (eventually_ge_atTop 1)] with n hn
  have hLn : 0 < (L n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hRn : 0 < R n := by dsimp [R]; positivity
  have hR3 : (R n) ^ (3 : ℕ) = (L n : ℝ) := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg (L n))]
    norm_num
  have hu := h.tail_block_square_bound (L n) (intervalBlock A (L n) 0)
    (fun a ha => (mem_intervalBlock A (L n) 0 a).mp ha |>.1)
    (fun a ha => by simpa using ((mem_intervalBlock A (L n) 0 a).mp ha).2.2)
    (intervalBlock A (L n))
    (fun i a ha => (mem_intervalBlock A (L n) i a).mp ha |>.1)
    (fun i a ha => (mem_intervalBlock A (L n) i a).mp ha |>.2) J hJ
  have hur : C n 0 * (∑ i ∈ J, (C n i) ^ 2) ≤
      (4 * (L n : ℝ) + 1) * 5 + C n 0 * (∑ i ∈ J, C n i) := by
    dsimp only [C]
    exact_mod_cast hu
  have heq : f n 0 * (∑ i ∈ J, (f n i) ^ 2) =
      C n 0 * (∑ i ∈ J, (C n i) ^ 2) / L n := by
    simp only [f, div_pow, ← Finset.sum_div]
    rw [← hR3]
    field_simp
  have hdiag : C n 0 * (∑ i ∈ J, C n i) / L n =
      f n 0 * (∑ i ∈ J, f n i) / R n := by
    simp only [f, ← Finset.sum_div]
    rw [← hR3]
    field_simp
  rw [heq]
  calc
    _ ≤ ((4 * (L n : ℝ) + 1) * 5 + C n 0 * (∑ i ∈ J, C n i)) / L n :=
      div_le_div_of_nonneg_right hur hLn.le
    _ = 20 + 5 / (L n : ℝ) + C n 0 * (∑ i ∈ J, C n i) / L n := by
      field_simp
      ring
    _ = _ := by rw [hdiag]

/-- If the first block of a scaling profile has positive mass, the later
block masses are square summable. -/
lemma NtupleCondition.summable_sq_subsequence_blocks {A : Set ℕ}
    (h : NtupleCondition A 3) {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop) {b : ℕ → ℝ}
    (hb : ∀ i, Tendsto
      (fun n => ((intervalBlock A (L n) i).card : ℝ) / (L n : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds (b i))) (hb0 : 0 < b 0) :
    Summable (fun i : ℕ => (b (i + 1)) ^ 2) := by
  classical
  apply summable_of_sum_le (c := 20 / b 0) (fun i => sq_nonneg _)
  intro s
  have hh := h.subsequence_tail_square_bound hL hb (s.image Nat.succ) (by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    omega)
  rw [Finset.sum_image (fun _ _ _ _ h => Nat.succ_injective h)] at hh
  apply (le_div_iff₀ hb0).mpr
  simpa only [Nat.succ_eq_add_one, mul_comm] using hh


/-- The normalized count in an interval has a location-independent bound. -/
lemma NtupleCondition.interval_ratio_le_five {A : Set ℕ}
    (h : NtupleCondition A 3) (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A)
    (x L : ℕ) (hI : ∀ a ∈ S, x ≤ a ∧ a ≤ x + L) :
    (S.card : ℝ) / (L : ℝ) ^ (1 / 3 : ℝ) ≤ 5 := by
  by_cases hL : L = 0
  · simp [hL]
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hL
  have hr : 1 ≤ (L : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hr3 : ((L : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = (L : ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg L)]
    norm_num
  have hcube := h.cube_bound_interval S hS x L hI
  have hsmall : (((S.card + 1 - 3 : ℕ) : ℝ)) ≤ 3 * (L : ℝ) ^ (1 / 3 : ℝ) := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 3 ≠ 0)).mp
    rw [mul_pow, hr3]
    norm_num
    linarith
  have hcard : (S.card : ℝ) ≤ (((S.card + 1 - 3 : ℕ) : ℝ)) + 2 := by
    exact_mod_cast (show S.card ≤ S.card + 1 - 3 + 2 by omega)
  apply (div_le_iff₀ (by positivity : 0 < (L : ℝ) ^ (1 / 3 : ℝ))).mpr
  linarith

/-- Compactness gives simultaneous block limits. The limits are not asserted
 to be equal, or to have a homogeneous dependence on the block index. -/
lemma NtupleCondition.exists_block_profile {A : Set ℕ}
    (h : NtupleCondition A 3) :
    ∃ (L : ℕ → ℕ) (b : ℕ → ℝ), StrictMono L ∧
      (∀ i, b i ∈ Icc 0 5) ∧ ∀ i, Tendsto
        (fun n => ((intervalBlock A (L n) i).card : ℝ) /
          (L n : ℝ) ^ (1 / 3 : ℝ)) atTop (nhds (b i)) := by
  let f : ℕ → ℕ → ℝ := fun N i =>
    ((intervalBlock A N i).card : ℝ) / (N : ℝ) ^ (1 / 3 : ℝ)
  have hcompact : IsCompact {b : ℕ → ℝ | ∀ i, b i ∈ Icc 0 5} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  have hmem : ∀ N, f N ∈ {b : ℕ → ℝ | ∀ i, b i ∈ Icc 0 5} := by
    intro N i
    refine ⟨by dsimp [f]; positivity, ?_⟩
    apply h.interval_ratio_le_five (intervalBlock A N i)
      (fun a ha => ((mem_intervalBlock A N i a).mp ha).1) (i * N) N
    intro a ha
    obtain ⟨_, hlo, hup⟩ := (mem_intervalBlock A N i a).mp ha
    exact ⟨hlo.le, by nlinarith⟩
  obtain ⟨b, hb, L, hL, ht⟩ := hcompact.tendsto_subseq hmem
  exact ⟨L, b, hL, hb, tendsto_pi_nhds.mp ht⟩

lemma card_intervalBlock_zero (A : Set ℕ) (N : ℕ) :
    (intervalBlock A N 0).card = (A ∩ Icc 1 N).ncard := by
  simpa using card_intervalBlock_add A N 0

lemma sum_card_intervalBlock (A : Set ℕ) (L k : ℕ) :
    ∑ i ∈ Finset.range k, (intervalBlock A L i).card =
      (A ∩ Icc 1 (k * L)).ncard := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    exact card_intervalBlock_add A L k

/-- Every subsequential limit of the normalized counts lies above the liminf. -/
lemma liminf_le_count_subsequence_limit {A : Set ℕ} {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop) {c : ℝ}
    (hc : Tendsto
      (fun n => (A ∩ Icc 1 (L n)).ncard / (L n : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds c)) :
    Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) ≤ c := by
  apply Filter.liminf_le_of_le (Filter.isBoundedUnder_of ⟨0, fun N => by positivity⟩)
  intro x hx
  exact ge_of_tendsto hc (hL.eventually hx)

/-- Block limits determine the scaled cumulative counting limits by telescoping. -/
lemma tendsto_count_of_block_profile {A : Set ℕ} {L : ℕ → ℕ} {b : ℕ → ℝ}
    (hb : ∀ i, Tendsto
      (fun n => ((intervalBlock A (L n) i).card : ℝ) / (L n : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds (b i))) (k : ℕ) :
    Tendsto (fun n => (A ∩ Icc 1 (k * L n)).ncard / (L n : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds (∑ i ∈ Finset.range k, b i)) := by
  have ht := tendsto_finset_sum (Finset.range k) (fun i _ => hb i)
  convert ht using 1
  funext n
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_card_intervalBlock]

lemma tendsto_dilation_of_block_profile {A : Set ℕ} {L : ℕ → ℕ} {b : ℕ → ℝ}
    (hb : ∀ i, Tendsto
      (fun n => ((intervalBlock A (L n) i).card : ℝ) / (L n : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds (b i))) (k : ℕ) :
    Tendsto
      (fun n => (A ∩ Icc 1 (k * L n)).ncard /
        ((k * L n : ℕ) : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds ((∑ i ∈ Finset.range k, b i) / (k : ℝ) ^ (1 / 3 : ℝ))) := by
  have ht := (tendsto_count_of_block_profile hb k).div_const ((k : ℝ) ^ (1 / 3 : ℝ))
  convert ht using 1
  funext n
  rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity), div_div]
  congr 1
  exact mul_comm _ _

lemma NtupleCondition.block_profile_cumulative_bounds {A : Set ℕ}
    (h : NtupleCondition A 3) {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    {b : ℕ → ℝ} (hb : ∀ i, Tendsto
      (fun n => ((intervalBlock A (L n) i).card : ℝ) / (L n : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds (b i))) (k : ℕ) :
    Filter.atTop.liminf
        (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) *
          (k : ℝ) ^ (1 / 3 : ℝ) ≤ (∑ i ∈ Finset.range k, b i) ∧
      (∑ i ∈ Finset.range k, b i) ≤ 5 * (k : ℝ) ^ (1 / 3 : ℝ) := by
  by_cases hk : k = 0
  · simp [hk]
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hrpos : 0 < (k : ℝ) ^ (1 / 3 : ℝ) := by positivity
  have hd : Tendsto (fun n => k * L n) atTop atTop :=
    tendsto_atTop_mono (fun n => show L n ≤ k * L n by nlinarith [Nat.pos_of_ne_zero hk]) hL
  have ht := tendsto_dilation_of_block_profile hb k
  refine ⟨(le_div_iff₀ hrpos).mp (liminf_le_count_subsequence_limit hd ht), ?_⟩
  apply (div_le_iff₀ hrpos).mp
  exact le_of_tendsto ht (Filter.Eventually.of_forall (fun n => h.ratio_le_five _))

/-- A nonzero conjectured liminf gives an actual nonnegative block profile
with positive first mass, cubic-root cumulative growth, and square-summable tail.
This is a necessary condition, not a contradiction. -/
lemma NtupleCondition.exists_positive_block_profile {A : Set ℕ}
    (h : NtupleCondition A 3)
    (hne : Filter.atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) ≠ 0) :
    ∃ (L : ℕ → ℕ) (b : ℕ → ℝ), StrictMono L ∧
      (∀ i, b i ∈ Icc 0 5) ∧
      (∀ i, Tendsto
        (fun n => ((intervalBlock A (L n) i).card : ℝ) /
          (L n : ℝ) ^ (1 / 3 : ℝ)) atTop (nhds (b i))) ∧
      0 < b 0 ∧ Summable (fun i : ℕ => (b (i + 1)) ^ 2) ∧
      ∀ k : ℕ, Filter.atTop.liminf
          (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) *
            (k : ℝ) ^ (1 / 3 : ℝ) ≤ (∑ i ∈ Finset.range k, b i) ∧
        (∑ i ∈ Finset.range k, b i) ≤ 5 * (k : ℝ) ^ (1 / 3 : ℝ) := by
  obtain ⟨L, b, hL, hb, ht⟩ := h.exists_block_profile
  have hbounds := h.block_profile_cumulative_bounds hL.tendsto_atTop ht
  have h0 : 0 < b 0 := by
    have hlo := (hbounds 1).1
    norm_num at hlo
    exact lt_of_lt_of_le (lt_of_le_of_ne h.liminf_nonneg (Ne.symm hne)) hlo
  exact ⟨L, b, hL, hb, ht, h0,
    h.summable_sq_subsequence_blocks hL.tendsto_atTop ht h0, hbounds⟩


/-- The unordered positive pair has two orderings, giving a bound for fully
ordered triples whose three entries are distinct. -/
lemma NtupleCondition.distinct_translated_triples_card_le {A : Set ℕ}
    (h : NtupleCondition A 3) (S : Finset (ℕ × ℕ × ℕ)) (t : ℤ) (H : ℕ)
    (hs : ∀ p ∈ S, p.1 ∈ A ∧ p.2.1 ∈ A ∧ p.2.2 ∈ A ∧
      p.1 ≠ p.2.1 ∧ p.2.2 ≠ p.1 ∧ p.2.2 ≠ p.2.1 ∧
      t - H ≤ (p.1 : ℤ) + p.2.1 - p.2.2 ∧
      (p.1 : ℤ) + p.2.1 - p.2.2 ≤ t + H) :
    S.card ≤ (2 * H + 1) * 10 := by
  classical
  let f : ℕ × ℕ × ℕ → Finset ℕ × ℕ := fun p => ({p.1, p.2.1}, p.2.2)
  have hb : (S.image f).card ≤ (2 * H + 1) * 5 := by
    apply h.signed_translated_interval_card_le (S.image f) t H
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨ha, hb, hc, hab, hca, hcb, hlo, hup⟩ := hs p hp
    refine ⟨?_, Finset.card_pair hab, hc, ?_, ?_, ?_⟩
    · simpa only [f, Finset.coe_pair, Set.pair_subset_iff] using And.intro ha hb
    · simpa only [f, Finset.mem_insert, Finset.mem_singleton, not_or] using And.intro hca hcb
    · simpa only [f, Finset.sum_pair hab, Nat.cast_add] using hlo
    · simpa only [f, Finset.sum_pair hab, Nat.cast_add] using hup
  have hfib : S.card ≤ 2 * (S.image f).card := by
    apply Finset.card_le_mul_card_image_of_maps_to (f := f)
      (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) 2
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hcard : (f p).1.card = 2 := Finset.card_pair (hs p hp).2.2.2.1
    rw [← hcard]
    apply Finset.card_le_card_of_injOn (fun r : ℕ × ℕ × ℕ => r.1)
    · intro r hr
      have he := (Finset.mem_filter.mp hr).2
      rw [← he]
      simp [f]
    · intro r hr s hs' hrs
      obtain ⟨hrS, hrq⟩ := Finset.mem_filter.mp hr
      obtain ⟨hsS, hsq⟩ := Finset.mem_filter.mp hs'
      have he : f r = f s := hrq.trans hsq.symm
      have hec : r.2.2 = s.2.2 := congrArg (fun q : Finset ℕ × ℕ => q.2) he
      have heI : ({r.1, r.2.1} : Finset ℕ) = {s.1, s.2.1} := congrArg Prod.fst he
      have heS : ({r.1, r.2.1} : Set ℕ) = {s.1, s.2.1} := by
        simpa only [Finset.coe_pair] using congrArg (fun I : Finset ℕ => (I : Set ℕ)) heI
      rcases Set.pair_eq_pair_iff.mp heS with ⟨hea, heb⟩ | ⟨hea, heb⟩
      · exact Prod.ext hea (Prod.ext heb hec)
      · exact ((hs r hrS).2.2.2.1 (hrs.trans heb.symm)).elim
  omega

/-- Repeated entries contribute only a quadratic error to the count of all
signed triples in a translated interval. -/
lemma NtupleCondition.translated_triples_card_le {A : Set ℕ}
    (h : NtupleCondition A 3) (P : Finset ℕ) (hP : (P : Set ℕ) ⊆ A)
    (S : Finset (ℕ × ℕ × ℕ)) (t : ℤ) (H : ℕ)
    (hs : ∀ p ∈ S, p.1 ∈ P ∧ p.2.1 ∈ P ∧ p.2.2 ∈ P ∧
      t - H ≤ (p.1 : ℤ) + p.2.1 - p.2.2 ∧
      (p.1 : ℤ) + p.2.1 - p.2.2 ≤ t + H) :
    S.card ≤ (2 * H + 1) * 10 + 3 * P.card ^ 2 := by
  classical
  let G := S.filter (fun p => p.1 ≠ p.2.1 ∧ p.2.2 ≠ p.1 ∧ p.2.2 ≠ p.2.1)
  let D₁ := (P.product P).image (fun p : ℕ × ℕ => (p.1, p.1, p.2))
  let D₂ := (P.product P).image (fun p : ℕ × ℕ => (p.1, p.2, p.1))
  let D₃ := (P.product P).image (fun p : ℕ × ℕ => (p.1, p.2, p.2))
  have hg : G.card ≤ (2 * H + 1) * 10 := by
    apply h.distinct_translated_triples_card_le G t H
    intro p hp
    obtain ⟨hpS, hdist⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb, hc, hlo, hup⟩ := hs p hpS
    exact ⟨hP ha, hP hb, hP hc, hdist.1, hdist.2.1, hdist.2.2, hlo, hup⟩
  have h₁ : D₁.card ≤ P.card ^ 2 := by
    calc
      _ ≤ (P.product P).card := Finset.card_image_le
      _ = _ := by simp [Finset.product_eq_sprod, pow_two]
  have h₂ : D₂.card ≤ P.card ^ 2 := by
    calc
      _ ≤ (P.product P).card := Finset.card_image_le
      _ = _ := by simp [Finset.product_eq_sprod, pow_two]
  have h₃ : D₃.card ≤ P.card ^ 2 := by
    calc
      _ ≤ (P.product P).card := Finset.card_image_le
      _ = _ := by simp [Finset.product_eq_sprod, pow_two]
  have hsub : S ⊆ ((G ∪ D₁) ∪ D₂) ∪ D₃ := by
    intro p hp
    obtain ⟨ha, hb, hc, _, _⟩ := hs p hp
    by_cases hab : p.1 = p.2.1
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(p.1, p.2.2), Finset.mem_product.mpr ⟨ha, hc⟩,
        Prod.ext rfl (Prod.ext hab rfl)⟩
    by_cases hca : p.2.2 = p.1
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(p.1, p.2.1), Finset.mem_product.mpr ⟨ha, hb⟩,
        Prod.ext rfl (Prod.ext rfl hca.symm)⟩
    by_cases hcb : p.2.2 = p.2.1
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(p.1, p.2.1), Finset.mem_product.mpr ⟨ha, hb⟩,
        Prod.ext rfl (Prod.ext rfl hcb.symm)⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hp, hab, hca, hcb⟩)))
  have hh := Finset.card_le_card hsub
  have hu₁ := Finset.card_union_le G D₁
  have hu₂ := Finset.card_union_le (G ∪ D₁) D₂
  have hu₃ := Finset.card_union_le ((G ∪ D₁) ∪ D₂) D₃
  omega


lemma intervalBlock_index_eq {A : Set ℕ} {L i j a : ℕ}
    (hi : a ∈ intervalBlock A L i) (hj : a ∈ intervalBlock A L j) : i = j := by
  obtain ⟨_, hil, hiu⟩ := (mem_intervalBlock A L i a).mp hi
  obtain ⟨_, hjl, hju⟩ := (mem_intervalBlock A L j a).mp hj
  rcases lt_trichotomy i j with hij | hij | hij
  · have hh := Nat.mul_le_mul_right L (show i + 1 ≤ j by omega)
    omega
  · exact hij
  · have hh := Nat.mul_le_mul_right L (show j + 1 ≤ i by omega)
    omega

/-- A translated block convolution bound that allows coincidences between
block indices. Coincidences between actual elements are a quadratic error. -/
lemma NtupleCondition.translated_block_convolution_bound {A : Set ℕ}
    (h : NtupleCondition A 3) (L K : ℕ) (J : Finset (ℕ × ℕ × ℕ))
    (hJ : ∀ p ∈ J, p.1 < K ∧ p.2.1 < K ∧ p.2.2 < K)
    (t : ℤ) (ht : ∀ p ∈ J, (p.1 : ℤ) + p.2.1 - p.2.2 = t) :
    (∑ p ∈ J, (intervalBlock A L p.1).card * (intervalBlock A L p.2.1).card *
      (intervalBlock A L p.2.2).card) ≤
      (4 * L + 1) * 10 + 3 * (A ∩ Icc 1 (K * L)).ncard ^ 2 := by
  classical
  let P : Finset ℕ := ((Set.finite_Icc 1 (K * L)).inter_of_right A).toFinset
  have hPc : P.card = (A ∩ Icc 1 (K * L)).ncard :=
    (Set.ncard_eq_toFinset_card _ _).symm
  have hP : (P : Set ℕ) ⊆ A := by
    intro a ha
    have ha' : a ∈ A ∩ Icc 1 (K * L) := by
      simpa only [Finset.mem_coe, P, Set.Finite.mem_toFinset] using ha
    exact ha'.1
  have hBP : ∀ i < K, ∀ a ∈ intervalBlock A L i, a ∈ P := by
    intro i hi a ha
    obtain ⟨haA, hal, hau⟩ := (mem_intervalBlock A L i a).mp ha
    change a ∈ ((Set.finite_Icc 1 (K * L)).inter_of_right A).toFinset
    rw [Set.Finite.mem_toFinset]
    refine ⟨haA, ?_, ?_⟩
    · omega
    · have hh := Nat.mul_le_mul_right L (show i + 1 ≤ K by omega)
      omega
  let T : ℕ × ℕ × ℕ → Finset (ℕ × ℕ × ℕ) := fun p =>
    (intervalBlock A L p.1).product
      ((intervalBlock A L p.2.1).product (intervalBlock A L p.2.2))
  have hd : Set.PairwiseDisjoint (J : Set (ℕ × ℕ × ℕ)) T := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro a hap haq
    obtain ⟨ha₁, ha₂, ha₃⟩ :=
      show a.1 ∈ intervalBlock A L p.1 ∧ a.2.1 ∈ intervalBlock A L p.2.1 ∧
        a.2.2 ∈ intervalBlock A L p.2.2 by
        simpa only [T, Finset.product_eq_sprod, Finset.mem_product] using hap
    obtain ⟨hb₁, hb₂, hb₃⟩ :=
      show a.1 ∈ intervalBlock A L q.1 ∧ a.2.1 ∈ intervalBlock A L q.2.1 ∧
        a.2.2 ∈ intervalBlock A L q.2.2 by
        simpa only [T, Finset.product_eq_sprod, Finset.mem_product] using haq
    exact hpq (Prod.ext (intervalBlock_index_eq ha₁ hb₁)
      (Prod.ext (intervalBlock_index_eq ha₂ hb₂) (intervalBlock_index_eq ha₃ hb₃)))
  have hh := h.translated_triples_card_le P hP (J.biUnion T) (t * L) (2 * L) (by
    intro a ha
    obtain ⟨p, hp, hap⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨ha₁, ha₂, ha₃⟩ :=
      show a.1 ∈ intervalBlock A L p.1 ∧ a.2.1 ∈ intervalBlock A L p.2.1 ∧
        a.2.2 ∈ intervalBlock A L p.2.2 by
        simpa only [T, Finset.product_eq_sprod, Finset.mem_product] using hap
    obtain ⟨hp₁, hp₂, hp₃⟩ := hJ p hp
    refine ⟨hBP _ hp₁ _ ha₁, hBP _ hp₂ _ ha₂, hBP _ hp₃ _ ha₃, ?_, ?_⟩
    all_goals
      have ha₁' : (p.1 : ℤ) * L < a.1 ∧ (a.1 : ℤ) ≤ (p.1 + 1 : ℤ) * L := by
        exact_mod_cast ((mem_intervalBlock A L p.1 a.1).mp ha₁).2
      have ha₂' : (p.2.1 : ℤ) * L < a.2.1 ∧ (a.2.1 : ℤ) ≤ (p.2.1 + 1 : ℤ) * L := by
        exact_mod_cast ((mem_intervalBlock A L p.2.1 a.2.1).mp ha₂).2
      have ha₃' : (p.2.2 : ℤ) * L < a.2.2 ∧ (a.2.2 : ℤ) ≤ (p.2.2 + 1 : ℤ) * L := by
        exact_mod_cast ((mem_intervalBlock A L p.2.2 a.2.2).mp ha₃).2
      have htmul := congrArg (fun z : ℤ => z * L) (ht p hp)
      push_cast
      nlinarith)
  rw [Finset.card_biUnion hd] at hh
  have hw : 2 * (2 * L) = 4 * L := by ring
  simpa only [T, Finset.product_eq_sprod, Finset.card_product, Nat.mul_assoc, hw, hPc] using hh


/-- Every finite signed triple convolution of a scaling profile is uniformly
bounded, at any translated target. Repeated block indices are allowed. -/
lemma NtupleCondition.block_profile_translated_convolution_bound {A : Set ℕ}
    (h : NtupleCondition A 3) {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    {b : ℕ → ℝ} (hb : ∀ i, Tendsto
      (fun n => ((intervalBlock A (L n) i).card : ℝ) / (L n : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds (b i))) (J : Finset (ℕ × ℕ × ℕ))
    (t : ℤ) (ht : ∀ p ∈ J, (p.1 : ℤ) + p.2.1 - p.2.2 = t) :
    (∑ p ∈ J, b p.1 * b p.2.1 * b p.2.2) ≤ 40 := by
  classical
  let K : ℕ := J.sup (fun p => p.1 + p.2.1 + p.2.2) + 1
  have hJ : ∀ p ∈ J, p.1 < K ∧ p.2.1 < K ∧ p.2.2 < K := by
    intro p hp
    have hh : p.1 + p.2.1 + p.2.2 ≤ J.sup (fun p => p.1 + p.2.1 + p.2.2) :=
      Finset.le_sup (f := fun p : ℕ × ℕ × ℕ => p.1 + p.2.1 + p.2.2) hp
    dsimp [K]
    omega
  let R : ℕ → ℝ := fun n => (L n : ℝ) ^ (1 / 3 : ℝ)
  let C : ℕ → ℝ := fun n => (A ∩ Icc 1 (K * L n)).ncard
  let f : ℕ → ℕ → ℝ := fun n i => (intervalBlock A (L n) i).card / R n
  have hf : ∀ i, Tendsto (fun n => f n i) atTop (nhds (b i)) := hb
  have hC : Tendsto (fun n => C n / R n) atTop
      (nhds (∑ i ∈ Finset.range K, b i)) := tendsto_count_of_block_profile hb K
  have hR : Tendsto R atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      (tendsto_natCast_atTop_atTop.comp hL)
  have hsmall : Tendsto (fun n => 3 * (C n / R n) ^ 2 / R n) atTop (nhds 0) :=
    ((tendsto_const_nhds (x := (3 : ℝ))).mul (hC.pow 2)).div_atTop hR
  have hz : Tendsto (fun n => (10 : ℝ) / L n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hL)
  have hbound : Tendsto
      (fun n => 40 + 10 / (L n : ℝ) + 3 * (C n / R n) ^ 2 / R n)
      atTop (nhds 40) := by
    simpa using ((tendsto_const_nhds (x := (40 : ℝ))).add hz).add hsmall
  have hsum : Tendsto (fun n => ∑ p ∈ J, f n p.1 * f n p.2.1 * f n p.2.2)
      atTop (nhds (∑ p ∈ J, b p.1 * b p.2.1 * b p.2.2)) :=
    tendsto_finset_sum _ (fun p _ => ((hf p.1).mul (hf p.2.1)).mul (hf p.2.2))
  apply le_of_tendsto_of_tendsto hsum hbound
  filter_upwards [hL.eventually (eventually_ge_atTop 1)] with n hn
  have hLn : 0 < (L n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hR3 : (R n) ^ (3 : ℕ) = (L n : ℝ) := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg (L n))]
    norm_num
  have hu := h.translated_block_convolution_bound (L n) K J hJ t ht
  have hur : (∑ p ∈ J, ((intervalBlock A (L n) p.1).card : ℝ) *
        (intervalBlock A (L n) p.2.1).card * (intervalBlock A (L n) p.2.2).card) ≤
      (4 * (L n : ℝ) + 1) * 10 + 3 * (C n) ^ 2 := by
    dsimp only [C]
    exact_mod_cast hu
  have heq : (∑ p ∈ J, f n p.1 * f n p.2.1 * f n p.2.2) =
      (∑ p ∈ J, ((intervalBlock A (L n) p.1).card : ℝ) *
        (intervalBlock A (L n) p.2.1).card * (intervalBlock A (L n) p.2.2).card) / L n := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only [f]
    rw [← hR3]
    field_simp
  have hdiag : 3 * C n ^ 2 / L n = 3 * (C n / R n) ^ 2 / R n := by
    rw [← hR3]
    field_simp
  rw [heq]
  calc
    _ ≤ ((4 * (L n : ℝ) + 1) * 10 + 3 * C n ^ 2) / L n :=
      div_le_div_of_nonneg_right hur hLn.le
    _ = 40 + 10 / (L n : ℝ) + 3 * C n ^ 2 / L n := by
      field_simp
      ring
    _ = _ := by rw [hdiag]

/-- Any positive block in a profile forces square summability of the entire
profile, by taking the other two block indices equal. -/
lemma NtupleCondition.summable_sq_block_profile {A : Set ℕ}
    (h : NtupleCondition A 3) {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    {b : ℕ → ℝ} (hb : ∀ i, Tendsto
      (fun n => ((intervalBlock A (L n) i).card : ℝ) / (L n : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds (b i))) {m : ℕ} (hm : 0 < b m) :
    Summable (fun i : ℕ => (b i) ^ 2) := by
  classical
  apply summable_of_sum_le (c := 40 / b m) (fun i => sq_nonneg _)
  intro s
  have hh := h.block_profile_translated_convolution_bound hL hb
    (s.image (fun i => (m, i, i))) m (by
      intro p hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      simp)
  rw [Finset.sum_image (fun i _ j _ he => congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) he)] at hh
  apply (le_div_iff₀ hm).mpr
  have heq : (∑ i ∈ s, b m * b i * b i) = (∑ i ∈ s, (b i) ^ 2) * b m := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simpa only [heq] using hh


/-- Only finitely many triples with distinct entries can have signed sum in
any fixed bounded interval. -/
lemma NtupleCondition.finite_signed_triples_in_interval {A : Set ℕ}
    (h : NtupleCondition A 3) (t : ℤ) (H : ℕ) :
    {p : ℕ × ℕ × ℕ | p.1 ∈ A ∧ p.2.1 ∈ A ∧ p.2.2 ∈ A ∧
      p.1 ≠ p.2.1 ∧ p.2.2 ≠ p.1 ∧ p.2.2 ≠ p.2.1 ∧
      t - H ≤ (p.1 : ℤ) + p.2.1 - p.2.2 ∧
      (p.1 : ℤ) + p.2.1 - p.2.2 ≤ t + H}.Finite := by
  classical
  by_contra hinf
  obtain ⟨S, hS, hSc⟩ := Set.Infinite.exists_subset_card_eq hinf ((2 * H + 1) * 10 + 1)
  have hh := h.distinct_translated_triples_card_le S t H (fun p hp => hS hp)
  omega

/-- The exceptional triples in a bounded signed interval are confined to a
finite initial segment of A. No quantitative estimate for this segment is asserted. -/
lemma NtupleCondition.signed_triples_bounded_height {A : Set ℕ}
    (h : NtupleCondition A 3) (t : ℤ) (H : ℕ) :
    ∃ M : ℕ, ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
      a ≠ b → c ≠ a → c ≠ b →
      t - H ≤ (a : ℤ) + b - c → (a : ℤ) + b - c ≤ t + H →
      a < M ∧ b < M ∧ c < M := by
  let S : Set (ℕ × ℕ × ℕ) := {p | p.1 ∈ A ∧ p.2.1 ∈ A ∧ p.2.2 ∈ A ∧
    p.1 ≠ p.2.1 ∧ p.2.2 ≠ p.1 ∧ p.2.2 ≠ p.2.1 ∧
    t - H ≤ (p.1 : ℤ) + p.2.1 - p.2.2 ∧
    (p.1 : ℤ) + p.2.1 - p.2.2 ≤ t + H}
  have hS : S.Finite := h.finite_signed_triples_in_interval t H
  let f : ℕ × ℕ × ℕ → ℕ := fun p => max p.1 (max p.2.1 p.2.2)
  obtain ⟨M, hM⟩ := (hS.image f).exists_le
  refine ⟨M + 1, ?_⟩
  intro a ha b hb c hc hab hca hcb hlo hup
  have hp : (a, b, c) ∈ S := ⟨ha, hb, hc, hab, hca, hcb, hlo, hup⟩
  have hh := hM _ (Set.mem_image_of_mem f hp)
  dsimp only [f] at hh
  omega

/-- Eventually, every distinct signed triple avoids a prescribed bounded
interval, even if only one of its entries is in the tail. -/
lemma NtupleCondition.eventually_avoids_signed_interval {A : Set ℕ}
    (h : NtupleCondition A 3) (t : ℤ) (H : ℕ) :
    ∃ M : ℕ, ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
      a ≠ b → c ≠ a → c ≠ b → M ≤ max a (max b c) →
      (a : ℤ) + b - c < t - H ∨ t + H < (a : ℤ) + b - c := by
  obtain ⟨M, hM⟩ := h.signed_triples_bounded_height t H
  refine ⟨M, ?_⟩
  intro a ha b hb c hc hab hca hcb hmax
  by_contra hn
  push_neg at hn
  obtain ⟨haM, hbM, hcM⟩ := hM a ha b hb c hc hab hca hcb hn.1 hn.2
  omega

/-- Fixed-width intervals sufficiently far out contain at most one element
of A. This qualitative spacing conclusion does not give cubic sparsity. -/
lemma NtupleCondition.eventually_separated {A : Set ℕ}
    (h : NtupleCondition A 3) (H : ℕ) :
    ∃ M : ℕ, ∀ a ∈ A, ∀ b ∈ A, M ≤ a → a < b → a + H < b := by
  rcases A.eq_empty_or_nonempty with hA | ⟨p, hp⟩
  · simp [hA]
  obtain ⟨M, hM⟩ := h.signed_triples_bounded_height p H
  refine ⟨max M (p + 1), ?_⟩
  intro a ha b hb hMa hab
  have hpa : p < a := by omega
  have hpb : p < b := by omega
  by_contra hclose
  have hclose' : b ≤ a + H := by omega
  have hlo : (p : ℤ) - H ≤ (p : ℤ) + a - b := by omega
  have hup : (p : ℤ) + a - b ≤ (p : ℤ) + H := by omega
  obtain ⟨_, haM, _⟩ := hM p hp a ha b hb hpa.ne hpb.ne.symm hab.ne.symm hlo hup
  omega

/-- Packing with both the prefix and the differences in translated intervals. -/
lemma NtupleCondition.difference_packing_bound_intervals {A : Set ℕ}
    (h : NtupleCondition A 3) (P D : Finset ℕ) (x t H : ℕ)
    (hP : (P : Set ℕ) ⊆ A)
    (hPH : ∀ a ∈ P, x ≤ a ∧ a ≤ x + H)
    (hD : ∀ d ∈ D, 0 < d ∧ t ≤ d ∧ d ≤ t + H ∧ ∃ b ∈ A, b + d ∈ A) :
    P.card * D.card ≤ (2 * H + 1) * 10 + 2 * D.card := by
  classical
  let b : ℕ → ℕ := fun d => if hd : d ∈ D then
    Classical.choose (hD d hd).2.2.2 else 0
  have hb : ∀ d ∈ D, b d ∈ A ∧ b d + d ∈ A := by
    intro d hd
    simp only [b, dif_pos hd]
    exact Classical.choose_spec (hD d hd).2.2.2
  let T := P ×ˢ D
  let good : ℕ × ℕ → Prop := fun p => p.1 ≠ b p.2 ∧ p.1 ≠ b p.2 + p.2
  let G := T.filter good
  let B := T.filter (fun p => ¬ good p)
  let f : ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (p.1, b p.2, b p.2 + p.2)
  have hf : Function.Injective f := by
    intro p q hpq
    have h1 : p.1 = q.1 := congrArg (fun r : ℕ × ℕ × ℕ => r.1) hpq
    have h2 : b p.2 = b q.2 := congrArg (fun r : ℕ × ℕ × ℕ => r.2.1) hpq
    have h3 : b p.2 + p.2 = b q.2 + q.2 :=
      congrArg (fun r : ℕ × ℕ × ℕ => r.2.2) hpq
    exact Prod.ext h1 (by omega)
  have hG : G.card ≤ (2 * H + 1) * 10 := by
    rw [← Finset.card_image_of_injective G hf]
    apply h.distinct_translated_triples_card_le (G.image f) ((x : ℤ) - t) H
    intro r hr
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hpT, hpG⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpP, hpD⟩ := Finset.mem_product.mp hpT
    have hd := hD p.2 hpD
    have hpb := hb p.2 hpD
    have haH := hPH p.1 hpP
    change p.1 ≠ b p.2 ∧ p.1 ≠ b p.2 + p.2 at hpG
    dsimp only [f]
    refine ⟨hP hpP, hpb.1, hpb.2, hpG.1, hpG.2.symm, ?_, ?_, ?_⟩ <;>
      push_cast <;> omega
  have hB : B.card ≤ 2 * D.card := by
    let U := D.image (fun d => (b d, d))
    let V := D.image (fun d => (b d + d, d))
    have hsub : B ⊆ U ∪ V := by
      intro p hp
      obtain ⟨hpT, hpB⟩ := Finset.mem_filter.mp hp
      have hpD := (Finset.mem_product.mp hpT).2
      change ¬ (p.1 ≠ b p.2 ∧ p.1 ≠ b p.2 + p.2) at hpB
      have hpB' : p.1 = b p.2 ∨ p.1 = b p.2 + p.2 := by tauto
      rcases hpB' with hpB' | hpB'
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨p.2, hpD, Prod.ext hpB'.symm rfl⟩
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨p.2, hpD, Prod.ext hpB'.symm rfl⟩
    calc
      B.card ≤ (U ∪ V).card := Finset.card_le_card hsub
      _ ≤ U.card + V.card := Finset.card_union_le U V
      _ ≤ D.card + D.card := Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
      _ = 2 * D.card := by omega
  have hpartition : G.card + B.card = P.card * D.card := by
    simpa only [G, B, T, Finset.card_product] using
      Finset.card_filter_add_card_filter_not (s := T) good
  omega




/-- The prefix-at-zero specialization of translated difference packing. -/
lemma NtupleCondition.difference_packing_bound_translated {A : Set ℕ}
    (h : NtupleCondition A 3) (P D : Finset ℕ) (t H : ℕ)
    (hP : (P : Set ℕ) ⊆ A)
    (hPH : ∀ a ∈ P, a ≤ H)
    (hD : ∀ d ∈ D, 0 < d ∧ t ≤ d ∧ d ≤ t + H ∧ ∃ b ∈ A, b + d ∈ A) :
    P.card * D.card ≤ (2 * H + 1) * 10 + 2 * D.card := by
  apply h.difference_packing_bound_intervals P D 0 t H hP ?_ hD
  intro a ha
  exact ⟨Nat.zero_le a, by simpa using hPH a ha⟩

/-- The initial-interval specialization of difference packing. -/
lemma NtupleCondition.difference_packing_bound {A : Set ℕ}
    (h : NtupleCondition A 3) (P D : Finset ℕ) (H : ℕ)
    (hP : (P : Set ℕ) ⊆ A)
    (hPH : ∀ a ∈ P, a ≤ H)
    (hD : ∀ d ∈ D, 0 < d ∧ d ≤ H ∧ ∃ b ∈ A, b + d ∈ A) :
    P.card * D.card ≤ (2 * H + 1) * 10 + 2 * D.card := by
  apply h.difference_packing_bound_translated P D 0 H hP hPH
  intro d hd
  obtain ⟨hd0, hdH, hb⟩ := hD d hd
  exact ⟨hd0, Nat.zero_le d, by simpa using hdH, hb⟩

/-- Uniform sparsity of the full difference set over translated intervals. -/
lemma NtupleCondition.difference_sparsity_uniform {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite) (k : ℕ) :
    ∃ M : ℕ, ∀ H ≥ M, ∀ t : ℕ, ∀ D : Finset ℕ,
      (∀ d ∈ D, 0 < d ∧ t ≤ d ∧ d ≤ t + H ∧ ∃ b ∈ A, b + d ∈ A) →
      k * D.card ≤ H := by
  classical
  obtain ⟨P, hP, hPc⟩ := hA.exists_subset_card_eq (30 * k + 2)
  refine ⟨max 1 (P.sup id), ?_⟩
  intro H hH t D hD
  have hPH : ∀ a ∈ P, a ≤ H := by
    intro a ha
    exact (Finset.le_sup (f := id) ha).trans ((le_max_right _ _).trans hH)
  have hp := h.difference_packing_bound_translated P D t H hP hPH hD
  rw [hPc] at hp
  have hHpos : 1 ≤ H := (le_max_left _ _).trans hH
  nlinarith

/-- Positive differences at most H, including those realized above H. -/
noncomputable def positiveDifferences (A : Set ℕ) (H : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 H).filter (fun d => ∃ b ∈ A, b + d ∈ A)

@[simp] lemma mem_positiveDifferences {A : Set ℕ} {H d : ℕ} :
    d ∈ positiveDifferences A H ↔ 0 < d ∧ d ≤ H ∧ ∃ b ∈ A, b + d ∈ A := by
  classical
  simp only [positiveDifferences, Finset.mem_filter, Finset.mem_Icc,
    Nat.succ_le_iff, and_assoc]

/-- The full difference set has density zero, in an integer formulation. -/
lemma NtupleCondition.difference_sparsity {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite) (k : ℕ) :
    ∃ M : ℕ, ∀ H ≥ M, k * (positiveDifferences A H).card ≤ H := by
  classical
  obtain ⟨P, hP, hPc⟩ := hA.exists_subset_card_eq (30 * k + 2)
  refine ⟨max 1 (P.sup id), ?_⟩
  intro H hH
  have hPH : ∀ a ∈ P, a ≤ H := by
    intro a ha
    exact (Finset.le_sup (f := id) ha).trans ((le_max_right _ _).trans hH)
  have hp := h.difference_packing_bound P (positiveDifferences A H) H hP hPH
    (fun d hd => mem_positiveDifferences.mp hd)
  rw [hPc] at hp
  have hHpos : 1 ≤ H := (le_max_left _ _).trans hH
  nlinarith

lemma NtupleCondition.difference_density_eq_zero {A : Set ℕ}
    (h : NtupleCondition A 3) (hA : A.Infinite) :
    Tendsto (fun H => ((positiveDifferences A H).card : ℝ) / H)
      atTop (nhds 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun H => lt_of_lt_of_le ha (by positivity)
  · intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨M, hM⟩ := h.difference_sparsity hA (k + 1)
    filter_upwards [eventually_ge_atTop (max M 1)] with H hH
    have hHM : M ≤ H := (le_max_left _ _).trans hH
    have hHpos : (0 : ℝ) < H := by
      have : 1 ≤ H := (le_max_right _ _).trans hH
      exact_mod_cast this
    have hb : ((k : ℝ) + 1) * (positiveDifferences A H).card ≤ H := by
      exact_mod_cast hM H hHM
    apply lt_of_le_of_lt ?_ hk
    apply (div_le_div_iff₀ hHpos (by positivity : (0 : ℝ) < k + 1)).2
    nlinarith


/-- Under eventual cubic growth, the full difference set has a uniform local
cubic bound, including intervals situated arbitrarily far from the origin. -/
lemma NtupleCondition.difference_cube_bound_of_growth {A : Set ℕ}
    (h : NtupleCondition A 3) (k M : ℕ)
    (hg : ∀ N ≥ M, N < k * (A ∩ Icc 1 N).ncard ^ 3) :
    ∀ H ≥ max M (64 * k + 1), ∀ t : ℕ, ∀ D : Finset ℕ,
      (∀ d ∈ D, 0 < d ∧ t ≤ d ∧ d ≤ t + H ∧ ∃ b ∈ A, b + d ∈ A) →
      D.card ^ 3 ≤ 216000 * k * H ^ 2 := by
  classical
  intro H hH t D hD
  have hHM : M ≤ H := (le_max_left _ _).trans hH
  have hHk : 64 * k + 1 ≤ H := (le_max_right _ _).trans hH
  have hHpos : 0 < H := by omega
  have hgH := hg H hHM
  have hfin : (A ∩ Icc 1 H).Finite := (finite_Icc 1 H).inter_of_right A
  let P := hfin.toFinset
  have hPc : P.card = (A ∩ Icc 1 H).ncard := (Set.ncard_eq_toFinset_card _ hfin).symm
  have hm : 4 ≤ P.card := by
    by_contra hn
    have hn' : P.card ≤ 3 := by omega
    have hn3 : P.card ^ 3 ≤ 27 := by simpa using Nat.pow_le_pow_left hn' 3
    rw [← hPc] at hgH
    nlinarith
  have hp := h.difference_packing_bound_translated P D t H
    (fun a ha => (hfin.mem_toFinset.mp ha).1)
    (fun a ha => (hfin.mem_toFinset.mp ha).2.2) hD
  have hprod : P.card * D.card ≤ 60 * H := by
    have hh : 4 * D.card ≤ P.card * D.card := Nat.mul_le_mul_right D.card hm
    nlinarith
  have hprod3 := Nat.pow_le_pow_left hprod 3
  have hg' : H ≤ k * P.card ^ 3 := by simpa only [hPc] using hgH.le
  have hcancel : H * D.card ^ 3 ≤ H * (216000 * k * H ^ 2) := by
    calc
      H * D.card ^ 3 ≤ (k * P.card ^ 3) * D.card ^ 3 :=
        Nat.mul_le_mul_right _ hg'
      _ = k * (P.card * D.card) ^ 3 := by ring
      _ ≤ k * (60 * H) ^ 3 := Nat.mul_le_mul_left k hprod3
      _ = H * (216000 * k * H ^ 2) := by ring
  exact Nat.le_of_mul_le_mul_left hcancel hHpos

/-- Three positively oriented disjoint edges cannot have labels d+e=f. -/
lemma NtupleCondition.difference_relation_overlap {A : Set ℕ}
    (h : NtupleCondition A 3) {a b c d e f : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hd : d ∈ A) (he : e ∈ A) (hf : f ∈ A)
    (hab : a < b) (_hcd : c < d) (_hef : e < f)
    (hs : b + d + e = a + c + f) :
    ¬ Disjoint ({a,b} : Finset ℕ) {c,d} ∨
    ¬ Disjoint ({a,b} : Finset ℕ) {e,f} ∨
    ¬ Disjoint ({c,d} : Finset ℕ) {e,f} := by
  classical
  by_contra hn
  push_neg at hn
  obtain ⟨h1, h2, h3⟩ := hn
  simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
    Finset.mem_insert, Finset.mem_singleton, not_or] at h1 h2 h3
  have hbd : b ≠ d := h1.2.2
  have hbe : b ≠ e := h2.2.1
  have hde : d ≠ e := h3.2.1
  have hac : a ≠ c := h1.1.1
  have haf : a ≠ f := h2.1.2
  have hcf : c ≠ f := h3.1.2
  have hEq : ({b,d,e} : Finset ℕ) = {a,c,f} := by
    apply h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Finset.coe_insert, Finset.coe_singleton,
        Set.insert_subset_iff, Set.singleton_subset_iff] using ⟨hb, hd, he⟩
    · simpa only [Finset.coe_insert, Finset.coe_singleton,
        Set.insert_subset_iff, Set.singleton_subset_iff] using ⟨ha, hc, hf⟩
    · simp [hbd, hbe, hde]
    · simp [hac, haf, hcf]
    · simpa [hbd, hbe, hde, hac, haf, hcf, add_assoc] using hs
  have hm : b ∈ ({a,c,f} : Finset ℕ) := by rw [← hEq]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm | hm
  · omega
  · exact h1.2.1 hm
  · exact h2.2.2 hm


/-- A bound on the number of selected difference edges incident to one vertex. -/
lemma NtupleCondition.difference_incidence_packing {A : Set ℕ}
    (h : NtupleCondition A 3) (D : Finset ℕ) (b : ℕ → ℕ) (H x : ℕ)
    (hD : ∀ d ∈ D, 0 < d ∧ d ≤ H ∧ b d ∈ A ∧ b d + d ∈ A) :
    (D.filter (fun d => x = b d ∨ x = b d + d)).card * D.card ≤
      (4 * H + 1) * 10 + 2 * D.card := by
  classical
  let I := D.filter (fun d => x = b d ∨ x = b d + d)
  let other : ℕ → ℕ := fun d => if x = b d then b d + d else b d
  let P := I.image other
  have hP : (P : Set ℕ) ⊆ A := by
    intro a ha
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ha
    have hdD := (Finset.mem_filter.mp hd).1
    dsimp [other]
    split_ifs
    · exact (hD d hdD).2.2.2
    · exact (hD d hdD).2.2.1
  have hPH : ∀ a ∈ P, x - H ≤ a ∧ a ≤ (x - H) + 2 * H := by
    intro a ha
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hdD, hdx⟩ := Finset.mem_filter.mp hd
    have hdH := (hD d hdD).2.1
    dsimp [other]
    split_ifs <;> omega
  have hinj : (I : Set ℕ).InjOn other := by
    intro d hd e he hde
    obtain ⟨hdD, hdx⟩ := Finset.mem_filter.mp hd
    obtain ⟨heD, hex⟩ := Finset.mem_filter.mp he
    have hd0 := (hD d hdD).1
    have he0 := (hD e heD).1
    dsimp [other] at hde
    split_ifs at hde <;> omega
  have hPc : P.card = I.card := Finset.card_image_of_injOn hinj
  have hp := h.difference_packing_bound_intervals P D (x - H) 0 (2 * H) hP hPH
    (by
      intro d hd
      obtain ⟨hd0, hdH, hbd, hbdd⟩ := hD d hd
      exact ⟨hd0, Nat.zero_le d, by omega, b d, hbd, hbdd⟩)
  rw [hPc] at hp
  simpa only [show 2 * (2 * H) = 4 * H by omega] using hp


/-- There are only linearly many pairs of selected small-difference edges
which meet at an endpoint. -/
lemma NtupleCondition.difference_overlapping_pairs_card_le {A : Set ℕ}
    (h : NtupleCondition A 3) (D : Finset ℕ) (b : ℕ → ℕ) (H : ℕ)
    (hD : ∀ d ∈ D, 0 < d ∧ d ≤ H ∧ b d ∈ A ∧ b d + d ∈ A) :
    ((D ×ˢ D).filter (fun p =>
      ¬ Disjoint ({b p.1, b p.1 + p.1} : Finset ℕ)
        {b p.2, b p.2 + p.2})).card ≤
      2 * ((4 * H + 1) * 10 + 2 * D.card) := by
  classical
  let I := fun x => D.filter (fun d => x = b d ∨ x = b d + d)
  let F := fun d => (I (b d)).card + (I (b d + d)).card
  let E := (D ×ˢ D).filter (fun p =>
    ¬ Disjoint ({b p.1, b p.1 + p.1} : Finset ℕ) {b p.2, b p.2 + p.2})
  change E.card ≤ _
  by_cases hn : D.Nonempty
  · obtain ⟨d₀, hd₀, hmax⟩ := D.exists_max_image F hn
    have hcount : E.card ≤ F d₀ * D.card := by
      apply Finset.card_le_mul_card_image_of_maps_to (f := Prod.fst)
        (fun p hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1) (F d₀)
      intro d hd
      apply le_trans ?_ (hmax d hd)
      calc
        (E.filter (fun p => p.1 = d)).card ≤ (I (b d) ∪ I (b d + d)).card := by
          apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.2)
          · intro p hp
            obtain ⟨hpE, hpd⟩ := Finset.mem_filter.mp hp
            obtain ⟨hpD, hpO⟩ := Finset.mem_filter.mp hpE
            have hp2D := (Finset.mem_product.mp hpD).2
            obtain ⟨z, hz1, hz2⟩ := Finset.not_disjoint_iff.mp hpO
            simp only [Finset.mem_insert, Finset.mem_singleton, hpd] at hz1 hz2
            rcases hz1 with hz1 | hz1
            · apply Finset.mem_union_left
              exact Finset.mem_filter.mpr ⟨hp2D, by simpa only [hz1] using hz2⟩
            · apply Finset.mem_union_right
              exact Finset.mem_filter.mpr ⟨hp2D, by simpa only [hz1] using hz2⟩
          · intro p hp q hq hpq
            have hpd := (Finset.mem_filter.mp hp).2
            have hqd := (Finset.mem_filter.mp hq).2
            exact Prod.ext (hpd.trans hqd.symm) hpq
        _ ≤ F d := Finset.card_union_le _ _
    have h1 := h.difference_incidence_packing D b H (b d₀) hD
    have h2 := h.difference_incidence_packing D b H (b d₀ + d₀) hD
    change (I (b d₀)).card * D.card ≤ _ at h1
    change (I (b d₀ + d₀)).card * D.card ≤ _ at h2
    dsimp only [F] at hcount
    nlinarith
  · have hD0 : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [E, hD0]


/-- The full positive difference set has at most linearly many additive
relations with all three differences at most H. Realizing pairs may have
unbounded heights. -/
lemma NtupleCondition.difference_additive_pairs_card_le {A : Set ℕ}
    (h : NtupleCondition A 3) (D : Finset ℕ) (H : ℕ)
    (hD : ∀ d ∈ D, 0 < d ∧ d ≤ H ∧ ∃ b ∈ A, b + d ∈ A) :
    ((D ×ˢ D).filter (fun p => p.1 + p.2 ∈ D)).card ≤ 252 * H + 60 := by
  classical
  let b : ℕ → ℕ := fun d => if hd : d ∈ D then
    Classical.choose (hD d hd).2.2 else 0
  have hb : ∀ d ∈ D, 0 < d ∧ d ≤ H ∧ b d ∈ A ∧ b d + d ∈ A := by
    intro d hd
    refine ⟨(hD d hd).1, (hD d hd).2.1, ?_⟩
    simp only [b, dif_pos hd]
    exact Classical.choose_spec (hD d hd).2.2
  let R := (D ×ˢ D).filter (fun p => p.1 + p.2 ∈ D)
  let E := (D ×ˢ D).filter (fun p =>
    ¬ Disjoint ({b p.1, b p.1 + p.1} : Finset ℕ) {b p.2, b p.2 + p.2})
  let f₁ : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.1 + p.2)
  let f₂ : ℕ × ℕ → ℕ × ℕ := fun p => (p.2, p.1 + p.2)
  have hf₁ : Function.Injective f₁ := by
    intro p q hpq
    have h1 := congrArg Prod.fst hpq
    have h2 := congrArg Prod.snd hpq
    change p.1 = q.1 at h1
    change p.1 + p.2 = q.1 + q.2 at h2
    exact Prod.ext h1 (by omega)
  have hf₂ : Function.Injective f₂ := by
    intro p q hpq
    have h1 := congrArg Prod.fst hpq
    have h2 := congrArg Prod.snd hpq
    change p.2 = q.2 at h1
    change p.1 + p.2 = q.1 + q.2 at h2
    exact Prod.ext (by omega) h1
  have hsub : R ⊆ (R.filter (fun p => p ∈ E)) ∪
      (R.filter (fun p => f₁ p ∈ E)) ∪ (R.filter (fun p => f₂ p ∈ E)) := by
    intro p hp
    obtain ⟨hpD, hsum⟩ := Finset.mem_filter.mp hp
    obtain ⟨h1D, h2D⟩ := Finset.mem_product.mp hpD
    obtain ⟨h10, _, h1a, h1b⟩ := hb p.1 h1D
    obtain ⟨h20, _, h2a, h2b⟩ := hb p.2 h2D
    obtain ⟨h30, _, h3a, h3b⟩ := hb (p.1 + p.2) hsum
    have hov := h.difference_relation_overlap h1a h1b h2a h2b h3a h3b
      (by omega) (by omega) (by omega) (by omega)
    rcases hov with h0 | h1 | h2
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hp, Finset.mem_filter.mpr ⟨hpD, h0⟩⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨hp, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1D, hsum⟩, h1⟩⟩
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨hp, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2D, hsum⟩, h2⟩⟩
  have hfilter (f : ℕ × ℕ → ℕ × ℕ) (hf : Function.Injective f) :
      (R.filter (fun p => f p ∈ E)).card ≤ E.card := by
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
    · exact hf.injOn
  have hR : R.card ≤ 3 * E.card := by
    have hU := Finset.card_le_card hsub
    have hU1 := Finset.card_union_le (R.filter (fun p => p ∈ E))
      (R.filter (fun p => f₁ p ∈ E))
    have hU2 := Finset.card_union_le ((R.filter (fun p => p ∈ E)) ∪
      (R.filter (fun p => f₁ p ∈ E))) (R.filter (fun p => f₂ p ∈ E))
    have h0 := hfilter id Function.injective_id
    have h1 := hfilter f₁ hf₁
    have h2 := hfilter f₂ hf₂
    change (R.filter (fun p => p ∈ E)).card ≤ E.card at h0
    omega
  have hE := h.difference_overlapping_pairs_card_le D b H hb
  change E.card ≤ _ at hE
  have hDc : D.card ≤ H := by
    calc
      D.card ≤ (Finset.Icc 1 H).card := Finset.card_le_card (by
        intro d hd
        exact Finset.mem_Icc.mpr ⟨(hD d hd).1, (hD d hd).2.1⟩)
      _ = H := by simp
  change R.card ≤ _
  omega


namespace MinimizingProfiles

/-- A bounded real sequence has a strictly increasing subsequence converging
exactly to its liminf. This is only a subsequence assertion. -/
lemma exists_liminf_subsequence {u : ℕ → ℝ}
    (hlo : IsBoundedUnder (· ≥ ·) atTop u)
    (hhi : IsCoboundedUnder (· ≥ ·) atTop u) :
    ∃ L : ℕ → ℕ, StrictMono L ∧ Tendsto (u ∘ L) atTop (nhds (atTop.liminf u)) := by
  have hfreq (n : ℕ) : ∃ᶠ k in atTop, u k < atTop.liminf u + 1 / ((n : ℝ)+1) := by
    apply frequently_lt_of_liminf_lt hhi
    have hp : 0 < 1 / ((n : ℝ)+1) := by positivity
    linarith
  obtain ⟨L,hL,hnear⟩ := extraction_forall_of_frequently hfreq
  refine ⟨L,hL,tendsto_order.mpr ⟨?_,?_⟩⟩
  · intro x hx
    exact hL.tendsto_atTop.eventually (eventually_lt_of_lt_liminf hx hlo)
  · intro x hx
    have ht : Tendsto (fun n : ℕ => atTop.liminf u + 1 / ((n : ℝ)+1))
        atTop (nhds (atTop.liminf u)) := by
      simpa using tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    filter_upwards [ht.eventually (gt_mem_nhds hx)] with n hn
    exact (hnear n).trans hn

/-- Simultaneous block compactness can be applied along a prescribed increasing
subsequence, without losing a previously obtained limit of the first block. -/
lemma exists_block_profile_along {A : Set ℕ} (h : NtupleCondition A 3)
    (L₀ : ℕ → ℕ) :
    ∃ (K : ℕ → ℕ) (b : ℕ → ℝ), StrictMono K ∧
      (∀ i, b i ∈ Icc 0 5) ∧ ∀ i, Tendsto
        (fun n => ((intervalBlock A (L₀ (K n)) i).card : ℝ) /
          (L₀ (K n) : ℝ) ^ (1 / 3 : ℝ)) atTop (nhds (b i)) := by
  let f : ℕ → ℕ → ℝ := fun n i =>
    ((intervalBlock A (L₀ n) i).card : ℝ) / (L₀ n : ℝ) ^ (1 / 3 : ℝ)
  have hcompact : IsCompact {b : ℕ → ℝ | ∀ i, b i ∈ Icc 0 5} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  have hmem : ∀ n, f n ∈ {b : ℕ → ℝ | ∀ i, b i ∈ Icc 0 5} := by
    intro n i
    refine ⟨by dsimp [f]; positivity, ?_⟩
    apply h.interval_ratio_le_five (intervalBlock A (L₀ n) i)
      (fun a ha => ((mem_intervalBlock A (L₀ n) i a).mp ha).1) (i * L₀ n) (L₀ n)
    intro a ha
    obtain ⟨_,hlo,hup⟩ := (mem_intervalBlock A (L₀ n) i a).mp ha
    exact ⟨hlo.le,by nlinarith⟩
  obtain ⟨b,hb,K,hK,ht⟩ := hcompact.tendsto_subseq hmem
  exact ⟨K,b,hK,hb,tendsto_pi_nhds.mp ht⟩

/-- The first mass can equal the original liminf, not merely lie above it.
This does not assert that the other dilation limits are equal to it. -/
theorem exists_minimizing_block_profile {A : Set ℕ} (h : NtupleCondition A 3) :
    ∃ (L : ℕ → ℕ) (b : ℕ → ℝ), StrictMono L ∧
      (∀ i, b i ∈ Icc 0 5) ∧
      (∀ i, Tendsto
        (fun n => ((intervalBlock A (L n) i).card : ℝ) /
          (L n : ℝ) ^ (1 / 3 : ℝ)) atTop (nhds (b i))) ∧
      b 0 = atTop.liminf
        (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) := by
  let u : ℕ → ℝ := fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)
  have hlo : IsBoundedUnder (· ≥ ·) atTop u :=
    isBoundedUnder_of ⟨0,fun _ => by dsimp [u]; positivity⟩
  have hhi : IsCoboundedUnder (· ≥ ·) atTop u :=
    isCoboundedUnder_ge_of_le _ h.ratio_le_five
  obtain ⟨L₀,hL₀,ht₀⟩ := exists_liminf_subsequence hlo hhi
  obtain ⟨K,b,hK,hb,ht⟩ := exists_block_profile_along h L₀
  refine ⟨L₀ ∘ K,b,hL₀.comp hK,hb,ht,?_⟩
  have ht₁ : Tendsto (u ∘ L₀ ∘ K) atTop (nhds (b 0)) := by
    simpa only [Function.comp_def,u,card_intervalBlock_zero] using ht 0
  exact tendsto_nhds_unique ht₁ (ht₀.comp hK.tendsto_atTop)

/-- At every integral dilation, the minimizing profile lies above the
cubic-root barrier determined by its first mass. Contact at the first block
is genuine, but gives no lower bound on individual later block increments. -/
theorem exists_positive_minimizing_profile {A : Set ℕ} (h : NtupleCondition A 3)
    (hne : atTop.liminf
      (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) ≠ 0) :
    ∃ (L : ℕ → ℕ) (b : ℕ → ℝ), StrictMono L ∧
      (∀ i, b i ∈ Icc 0 5) ∧
      (∀ i, Tendsto
        (fun n => ((intervalBlock A (L n) i).card : ℝ) /
          (L n : ℝ) ^ (1 / 3 : ℝ)) atTop (nhds (b i))) ∧
      b 0 = atTop.liminf
        (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) ∧
      0 < b 0 ∧ Summable (fun i : ℕ => (b i)^2) ∧
      ∀ k : ℕ, b 0 * (k : ℝ) ^ (1 / 3 : ℝ) ≤ ∑ i ∈ Finset.range k, b i := by
  obtain ⟨L,b,hL,hb,ht,he⟩ := exists_minimizing_block_profile h
  have hb0 : 0 < b 0 := by
    rw [he]
    exact lt_of_le_of_ne h.liminf_nonneg (Ne.symm hne)
  refine ⟨L,b,hL,hb,ht,he,hb0,
    h.summable_sq_block_profile hL.tendsto_atTop ht hb0,?_⟩
  intro k
  rw [he]
  exact (h.block_profile_cumulative_bounds hL.tendsto_atTop ht k).1

end MinimizingProfiles

/--
Let `A ⊆ ℕ` be an infinite set such that the triple sums `a + b + c` are all distinct for
`a, b, c` in `A` (aside from the trivial coincidences). Is it true that
`liminf n → ∞ |A ∩ {1, …, N}| / N^(1/3) = 0`?
-/
theorem erdos_41 (A : Set ℕ) (h_triple : NtupleCondition A 3) (h_infinite : A.Infinite) :
    Filter.atTop.liminf (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) = 0 := by
  by_cases hconv : ∃ (L : ℕ → ℕ) (c : ℝ), Tendsto L atTop atTop ∧
      ∀ i, 0 < i → Tendsto
        (fun n => (A ∩ Icc 1 (i * L n)).ncard /
          ((i * L n : ℕ) : ℝ) ^ (1 / 3 : ℝ)) atTop (nhds c)
  · obtain ⟨L, c, hL, hc⟩ := hconv
    have hzero := h_triple.dilation_subsequence_limit_eq_zero hL hc
    apply h_triple.liminf_eq_zero_of_zero_subsequence hL
    simpa only [one_mul, hzero] using hc 1 (by omega)
  · by_contra hne
    obtain ⟨k, M, hgrowth⟩ := h_triple.liminf_ne_zero_iff_cubic_growth.mp hne
    obtain ⟨L, b, hL, hb_bounds, hb, hmin, hb0, hsq, hcum⟩ :=
      MinimizingProfiles.exists_positive_minimizing_profile h_triple hne
    have htranslated := h_triple.block_profile_translated_convolution_bound hL.tendsto_atTop hb
    have hsq_all := h_triple.summable_sq_block_profile hL.tendsto_atTop hb hb0
    sorry

end Erdos41
