import FormalConjecturesUtil

/-! An unconditional additive consequence of reciprocal divergence.
This file does not prove or disprove the arithmetic-progression conjecture. -/

namespace Erdos3ParallelogramCheck

set_option maxHeartbeats 1000000

def HasProperParallelogram (A : Set ℕ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, ∃ d ∈ A,
    a < b ∧ b < c ∧ c < d ∧ a + d = b + c

theorem ordered_pair_unique {A : Set ℕ} (h : ¬ HasProperParallelogram A)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a < b) (hcd : c < d) (heq : a + b = c + d) : a = c ∧ b = d := by
  rcases lt_trichotomy a c with hac | hac | hac
  · exact (h ⟨a, ha, c, hc, d, hd, b, hb, hac, hcd, by omega, heq⟩).elim
  · omega
  · exact (h ⟨c, hc, a, ha, b, hb, d, hd, hac, hab, by omega, heq.symm⟩).elim

theorem finite_card_bound {A : Set ℕ} (h : ¬ HasProperParallelogram A)
    {S : Finset ℕ} {N : ℕ} (hS : (S : Set ℕ) ⊆ A) (hN : ∀ n ∈ S, n ≤ N) :
    S.card * (S.card - 1) ≤ 2 * (2 * N + 1) := by
  classical
  let e : S.offDiag → Fin (2 * N + 1) × Bool := fun p ↦
    (⟨p.1.1 + p.1.2, by
      have hp := Finset.mem_offDiag.mp p.2
      have := hN p.1.1 hp.1
      have := hN p.1.2 hp.2.1
      omega⟩, decide (p.1.1 ≤ p.1.2))
  have he : Function.Injective e := by
    intro p q hpq
    have hp := Finset.mem_offDiag.mp p.2
    have hq := Finset.mem_offDiag.mp q.2
    have hsum : p.1.1 + p.1.2 = q.1.1 + q.1.2 := congrArg (fun x ↦ x.1.val) hpq
    have hflag : decide (p.1.1 ≤ p.1.2) = decide (q.1.1 ≤ q.1.2) := congrArg Prod.snd hpq
    apply Subtype.ext
    by_cases hple : p.1.1 ≤ p.1.2
    · have hqle : q.1.1 ≤ q.1.2 := by simpa [hple] using hflag.symm
      obtain ⟨h₁, h₂⟩ := ordered_pair_unique h (hS hp.1) (hS hp.2.1)
        (hS hq.1) (hS hq.2.1) (by omega) (by omega) hsum
      exact Prod.ext h₁ h₂
    · have hqle : ¬ q.1.1 ≤ q.1.2 := by simpa [hple] using hflag.symm
      obtain ⟨h₁, h₂⟩ := ordered_pair_unique h (hS hp.2.1) (hS hp.1)
        (hS hq.2.1) (hS hq.1) (by omega) (by omega) (by omega)
      exact Prod.ext h₂ h₁
  have hc := Fintype.card_le_of_injective e he
  simpa [Fintype.card_coe, Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_comm] using hc

theorem finite_card_geometric_bound {A : Set ℕ} (h : ¬ HasProperParallelogram A)
    {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ A) (j : ℕ)
    (hN : ∀ n ∈ S, n ≤ 4 ^ (j + 1)) : S.card ≤ 6 * 2 ^ j := by
  have hb := finite_card_bound h hS hN
  have hfour : 4 ^ j = (2 ^ j) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
    norm_num
  rw [pow_succ', hfour] at hb
  have hpos : 1 ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  by_cases hm : S.card = 0
  · simp [hm]
  · have hpred : S.card - 1 + 1 = S.card := Nat.sub_add_cancel (by omega)
    nlinarith

/-- A uniform reciprocal-sum bound for finite sets with no proper additive parallelogram. -/
theorem finite_recip_sum_bound {A : Set ℕ} (h : ¬ HasProperParallelogram A)
    (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ A) :
    (∑ n ∈ S, 1 / (n : ℝ)) ≤ ∑' j : ℕ, (6 : ℝ) * (1 / 2) ^ j := by
  classical
  have hgeo : Summable (fun j : ℕ ↦ (6 : ℝ) * (1 / 2) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left 6
  let S' := S.erase 0
  let J := S'.image (Nat.log 4)
  have hfiber (j : ℕ) :
      (∑ n ∈ S'.filter (fun n ↦ Nat.log 4 n = j), 1 / (n : ℝ)) ≤
        (6 : ℝ) * (1 / 2) ^ j := by
    let T := S'.filter (fun n ↦ Nat.log 4 n = j)
    have hTsub : (T : Set ℕ) ⊆ A := by
      intro n hn
      exact hS ((Finset.erase_subset _ _) ((Finset.filter_subset _ _) hn))
    have hTb : ∀ n ∈ T, n ≤ 4 ^ (j + 1) := by
      intro n hn
      obtain ⟨_, hnj⟩ := Finset.mem_filter.mp hn
      simpa [hnj] using (Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) n).le
    have hTc := finite_card_geometric_bound h hTsub j hTb
    calc
      (∑ n ∈ T, 1 / (n : ℝ)) ≤ ∑ n ∈ T, 1 / ((4 ^ j : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hnS, hnj⟩ := Finset.mem_filter.mp hn
        have hn0 := (Finset.mem_erase.mp hnS).1
        have hpow : 4 ^ j ≤ n := by simpa [hnj] using Nat.pow_log_le_self 4 hn0
        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hpow)
      _ = (T.card : ℝ) / ((4 ^ j : ℕ) : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ ((6 * 2 ^ j : ℕ) : ℝ) / ((4 ^ j : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast hTc
      _ = (6 : ℝ) * (1 / 2) ^ j := by
        push_cast
        rw [mul_div_assoc, ← div_pow]
        norm_num
  calc
    (∑ n ∈ S, 1 / (n : ℝ)) = ∑ n ∈ S', 1 / (n : ℝ) :=
      (Finset.sum_erase S (by simp : (1 : ℝ) / (0 : ℕ) = 0)).symm
    _ = ∑ j ∈ J, ∑ n ∈ S'.filter (fun n ↦ Nat.log 4 n = j), 1 / (n : ℝ) :=
      (Finset.sum_fiberwise_of_maps_to
        (fun n hn ↦ Finset.mem_image_of_mem (Nat.log 4) hn) (fun n : ℕ ↦ 1 / (n : ℝ))).symm
    _ ≤ ∑ j ∈ J, (6 : ℝ) * (1 / 2) ^ j := Finset.sum_le_sum (fun j _ ↦ hfiber j)
    _ ≤ ∑' j : ℕ, (6 : ℝ) * (1 / 2) ^ j :=
      Summable.sum_le_tsum _ (fun _ _ ↦ by positivity) hgeo

theorem summable_of_no_proper_parallelogram {A : Set ℕ}
    (h : ¬ HasProperParallelogram A) : Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  apply summable_of_sum_le (c := ∑' j : ℕ, (6 : ℝ) * (1 / 2) ^ j)
    (fun _ ↦ by positivity)
  intro F
  let e : A ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hsub : (F.map e : Set ℕ) ⊆ A := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hn
    exact a.property
  simpa [e] using finite_recip_sum_bound h (F.map e) hsub

/-- This is an unconditional consequence of the conjecture's hypothesis. Its conclusion is
strictly weaker than a four-term arithmetic progression: the three gaps need not be equal. -/
theorem divergence_has_proper_parallelogram (A : Set ℕ)
    (h : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) : HasProperParallelogram A := by
  by_contra hno
  exact h (summable_of_no_proper_parallelogram hno)

#print axioms divergence_has_proper_parallelogram

/-- The new intermediate conclusion alone does not even force a three-term AP. -/
theorem proper_parallelogram_does_not_force_threeAP :
    ∃ A : Set ℕ, HasProperParallelogram A ∧ ThreeAPFree A := by
  refine ⟨↑({0, 1, 3, 4} : Finset ℕ), ?_, ?_⟩
  · exact ⟨0, by simp, 1, by simp, 3, by simp, 4, by simp, by norm_num⟩
  · decide

#print axioms proper_parallelogram_does_not_force_threeAP

end Erdos3ParallelogramCheck
