import Submission.GreedyConfigurationTails

/-!
Packing intersecting witnesses before applying inclusion bounds. The conclusion
continues to concern the stopped process, not a guarantee of its running time.
-/
namespace Erdos773.GreedyWitnessPacking
open Finset GreedyHypergraphState StoppedGreedyMoments GreedyConfigurationTails
set_option maxHeartbeats 2000000
noncomputable section

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- A largest disjoint subfamily intersects every nonempty support. -/
theorem exists_disjoint_cover (T : Finset β) (C : β → Finset α)
    (hne : ∀ i ∈ T, (C i).Nonempty) :
    ∃ U ⊆ T, (U : Set β).PairwiseDisjoint C ∧
      ∀ i ∈ T, ∃ j ∈ U, ¬Disjoint (C i) (C j) := by
  classical
  let F := T.powerset.filter (fun U : Finset β => (U : Set β).PairwiseDisjoint C)
  have hf : (∅ : Finset β) ∈ F := by simp [F, Set.PairwiseDisjoint]
  obtain ⟨U, hUF, hmax⟩ := exists_max_image F Finset.card ⟨∅, hf⟩
  obtain ⟨hUT, hd⟩ := mem_filter.mp hUF
  have hUT : U ⊆ T := mem_powerset.mp hUT
  refine ⟨U, hUT, hd, ?_⟩
  intro i hi
  by_contra! hdis
  have hin : i ∉ U := by
    intro hiU
    obtain ⟨a, ha⟩ := hne i hi
    exact disjoint_left.mp (hdis i hiU) ha ha
  have hins : ((insert i U : Finset β) : Set β).PairwiseDisjoint C := by
    rw [coe_insert]
    exact hd.insert (fun j hj _ => hdis j hj)
  have hh := hmax (insert i U) (mem_filter.mpr
    ⟨mem_powerset.mpr (insert_subset hi hUT), hins⟩)
  rw [card_insert_of_notMem hin] at hh
  omega

/-- Bounded support size and incidence imply a large disjoint subfamily.
    Repeated supports with distinct indices are permitted. -/
theorem packing_bound (T : Finset β) (C : β → Finset α) (r M : ℕ)
    (hne : ∀ i ∈ T, (C i).Nonempty)
    (hsize : ∀ i ∈ T, (C i).card ≤ r)
    (hinc : ∀ a, (T.filter (fun i => a ∈ C i)).card ≤ M) :
    ∃ U ⊆ T, (U : Set β).PairwiseDisjoint C ∧ T.card ≤ r*M*U.card := by
  classical
  obtain ⟨U, hUT, hd, hcover⟩ := exists_disjoint_cover T C hne
  refine ⟨U, hUT, hd, ?_⟩
  have hc : T ⊆ (U.biUnion C).biUnion (fun a => T.filter (fun i => a ∈ C i)) := by
    intro i hi
    obtain ⟨j, hj, hij⟩ := hcover i hi
    obtain ⟨a, ha⟩ := not_disjoint_iff_nonempty_inter.mp hij
    obtain ⟨hai, haj⟩ := mem_inter.mp ha
    exact mem_biUnion.mpr ⟨a, mem_biUnion.mpr ⟨j, hj, haj⟩,
      mem_filter.mpr ⟨hi, hai⟩⟩
  have hu : (U.biUnion C).card ≤ r*U.card := by
    calc
      _ ≤ ∑ i ∈ U, (C i).card := card_biUnion_le
      _ ≤ ∑ _i ∈ U, r := sum_le_sum (fun i hi => hsize i (hUT hi))
      _ = _ := by simp [mul_comm]
  calc
    T.card ≤ ((U.biUnion C).biUnion (fun a => T.filter (fun i => a ∈ C i))).card :=
      card_le_card hc
    _ ≤ ∑ a ∈ U.biUnion C, (T.filter (fun i => a ∈ C i)).card := card_biUnion_le
    _ ≤ ∑ _a ∈ U.biUnion C, M := sum_le_sum (fun a _ => hinc a)
    _ = M*(U.biUnion C).card := by simp [mul_comm]
    _ ≤ M*(r*U.card) := Nat.mul_le_mul_left M hu
    _ = r*M*U.card := by ring

/-- A crowded selected family contains a disjoint selected k+1-subfamily. -/
theorem selected_packing_witness (T : Finset β) (C : β → Finset α) (r M k : ℕ)
    (hne : ∀ i ∈ T, (C i).Nonempty)
    (hsize : ∀ i ∈ T, (C i).card ≤ r)
    (hinc : ∀ a, (T.filter (fun i => a ∈ C i)).card ≤ M)
    (I : Finset α) (hI : r*M*k < (T.filter (fun i => C i ⊆ I)).card) :
    ∃ U ∈ T.powersetCard (k+1), (U : Set β).PairwiseDisjoint C ∧ U.biUnion C ⊆ I := by
  classical
  let S := T.filter (fun i => C i ⊆ I)
  have hST : S ⊆ T := filter_subset _ _
  obtain ⟨V, hVS, hd, hc⟩ := packing_bound S C r M
    (fun i hi => hne i (hST hi)) (fun i hi => hsize i (hST hi))
    (fun a => (card_le_card (filter_subset_filter _ hST)).trans (hinc a))
  have hkV : k+1 ≤ V.card := by
    by_contra! hh
    have hle := Nat.mul_le_mul_left (r*M) (show V.card ≤ k by omega)
    exact (not_lt_of_ge (hc.trans hle)) hI
  obtain ⟨U, hUV, hUk⟩ := exists_subset_card_eq hkV
  refine ⟨U, mem_powersetCard.mpr ⟨hUV.trans (hVS.trans hST), hUk⟩,
    fun i hi j hj hij => hd (hUV hi) (hUV hj) hij, ?_⟩
  exact biUnion_subset.mpr (fun i hi => (mem_filter.mp (hVS (hUV hi))).2)

omit [DecidableEq α] [DecidableEq β] in
/-- A convenient exponential bound retaining the factorial in the binomial
    coefficient. -/
lemma choose_mul_pow_le (m j s : ℕ) (hj : 0 < j) (p : ℝ) (hp : 0 ≤ p) :
    (m.choose j : ℝ)*p^(s*j) ≤ (3*m*p^s/j)^j := by
  have hjR : (0:ℝ) < j := by exact_mod_cast hj
  have hfact : (0:ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hpow := Real.pow_div_factorial_le_exp (j:ℝ) hjR.le j
  have hexp : Real.exp (j:ℝ) ≤ (3:ℝ)^j := by
    calc
      _ = (Real.exp 1)^j := by simpa only [mul_one] using Real.exp_nat_mul 1 j
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_d9]) j
  have hbase : ((j:ℝ)/3)^j ≤ (j.factorial:ℝ) := by
    rw [div_pow]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 3^j)).mpr
    simpa only [mul_comm] using (div_le_iff₀ hfact).mp (hpow.trans hexp)
  calc
    _ ≤ ((m:ℝ)^j / (j.factorial:ℝ))*p^(s*j) :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div j m) (by positivity)
    _ ≤ ((m:ℝ)^j / ((j:ℝ)/3)^j)*p^(s*j) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity)
        (by positivity) hbase) (by positivity)
    _ = _ := by rw [← div_pow, pow_mul, ← mul_pow]; congr 1; field_simp

variable [Fintype α]

/-- Packing tail: overlapping witnesses are reduced to disjoint subfamilies.
    This is a stopped-process estimate, and uses no independence assertion. -/
theorem packing_tail (H : Finset (Finset α)) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hn : n ≤ L) (T : Finset β) (C : β → Finset α) (r M s k : ℕ)
    (hne : ∀ i ∈ T, (C i).Nonempty)
    (hsize : ∀ i ∈ T, (C i).card ≤ r)
    (hlower : ∀ i ∈ T, s ≤ (C i).card)
    (hinc : ∀ a, (T.filter (fun i => a ∈ C i)).card ≤ M) :
    expectation H L n (event (fun I => r*M*k < (T.filter (fun i => C i ⊆ I)).card)) ≤
      (T.card.choose (k+1) : ℝ)*((n:ℝ)/L)^(s*(k+1)) := by
  classical
  let F := (T.powersetCard (k+1)).filter (fun U : Finset β => (U : Set β).PairwiseDisjoint C)
  have hw (I : Finset α) (hI : r*M*k < (T.filter (fun i => C i ⊆ I)).card) :
      ∃ U ∈ F, U.biUnion C ⊆ I := by
    obtain ⟨U, hU, hd, hUI⟩ := selected_packing_witness T C r M k hne hsize hinc I hI
    exact ⟨U, mem_filter.mpr ⟨hU, hd⟩, hUI⟩
  have hcard (U : Finset β) (hU : U ∈ F) : s*(k+1) ≤ (U.biUnion C).card := by
    obtain ⟨hU, hd⟩ := mem_filter.mp hU
    obtain ⟨hUT, hUk⟩ := mem_powersetCard.mp hU
    rw [card_biUnion hd]
    calc
      s*(k+1) = ∑ _i ∈ U, s := by simp [hUk, mul_comm]
      _ ≤ _ := sum_le_sum (fun i hi => hlower i (hUT hi))
  have hp0 : (0:ℝ) ≤ (n:ℝ)/L := by positivity
  have hp1 : (n:ℝ)/L ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hL : (0:ℝ) < L)).mpr
    exact_mod_cast hn
  calc
    _ ≤ ∑ U ∈ F, ((n:ℝ)/L)^(U.biUnion C).card := witness_bound H L hL n F _ _ hw
    _ ≤ ∑ _U ∈ F, ((n:ℝ)/L)^(s*(k+1)) :=
      sum_le_sum (fun U hU => pow_le_pow_of_le_one hp0 hp1 (hcard U hU))
    _ = (F.card : ℝ)*((n:ℝ)/L)^(s*(k+1)) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hh := card_filter_le (s := T.powersetCard (k+1))
        (p := fun U : Finset β => (U : Set β).PairwiseDisjoint C)
      rw [card_powersetCard] at hh
      exact_mod_cast hh

/-- Exponential version of the packing tail. -/
theorem packing_exponential_tail (H : Finset (Finset α)) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hn : n ≤ L) (T : Finset β) (C : β → Finset α) (r M s k : ℕ)
    (hne : ∀ i ∈ T, (C i).Nonempty)
    (hsize : ∀ i ∈ T, (C i).card ≤ r)
    (hlower : ∀ i ∈ T, s ≤ (C i).card)
    (hinc : ∀ a, (T.filter (fun i => a ∈ C i)).card ≤ M) :
    expectation H L n (event (fun I => r*M*k < (T.filter (fun i => C i ⊆ I)).card)) ≤
      (3*T.card*((n:ℝ)/L)^s/(k+1))^(k+1) := by
  have hh := (packing_tail H L hL n hn T C r M s k hne hsize hlower hinc).trans
    (choose_mul_pow_le T.card (k+1) s (by omega) ((n:ℝ)/L) (by positivity))
  simpa only [Nat.cast_add, Nat.cast_one] using hh

#print axioms choose_mul_pow_le
#print axioms packing_exponential_tail
#print axioms exists_disjoint_cover
#print axioms packing_bound
#print axioms selected_packing_witness
#print axioms packing_tail
end
end Erdos773.GreedyWitnessPacking
