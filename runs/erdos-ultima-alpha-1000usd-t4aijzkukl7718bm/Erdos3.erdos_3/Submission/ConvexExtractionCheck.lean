import FormalConjecturesUtil

/-! Nondecreasing-gap extraction cannot preserve reciprocal divergence in general.
This is an obstruction to a proposed strategy, not a disproof of the conjecture. -/

namespace Erdos3ConvexExtractionCheck

/-- Long intervals separated by gaps that are larger than the following interval. -/
def blocks : Set ℕ := {n | ∃ j : ℕ, 4 * 4 ^ j ≤ n ∧ n < 5 * 4 ^ j}

lemma block_power_separation {i j : ℕ} (hij : i < j) :
    5 * 4 ^ i ≤ 2 * 4 ^ j := by
  have h : 4 * 4 ^ i ≤ 4 ^ j := by
    rw [← pow_succ']
    exact Nat.pow_le_pow_right (by omega) hij
  omega

lemma block_order {i j x y : ℕ} (hij : i < j)
    (hx : x < 5 * 4 ^ i) (hy : 4 * 4 ^ j ≤ y) : x < y := by
  have := block_power_separation hij
  omega

def blockValue (v : Σ j : ℕ, Fin (4 ^ j)) : ℕ := 4 * 4 ^ v.1 + v.2

lemma blockValue_mem (v : Σ j : ℕ, Fin (4 ^ j)) : blockValue v ∈ blocks := by
  refine ⟨v.1, ?_, ?_⟩ <;> dsimp [blockValue]
  · omega
  · have := v.2.isLt
    omega

lemma blockValue_injective : Function.Injective blockValue := by
  rintro ⟨i, x⟩ ⟨j, y⟩ heq
  have hx := x.isLt
  have hy := y.isLt
  have hij : i = j := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hij | hji
    · have hp := block_power_separation hij
      dsimp [blockValue] at heq
      omega
    · have hp := block_power_separation hji
      dsimp [blockValue] at heq
      omega
  subst j
  have hxy : x = y := Fin.ext (by simpa [blockValue] using heq)
  cases hxy
  rfl

lemma block_reciprocal_lower_bound (j : ℕ) :
    (1 : ℝ) / 5 ≤ ∑' m : Fin (4 ^ j), 1 / ((4 * 4 ^ j + m : ℕ) : ℝ) := by
  rw [tsum_fintype]
  calc
    (1 : ℝ) / 5 = ∑ _m : Fin (4 ^ j), 1 / ((5 * 4 ^ j : ℕ) : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp
    _ ≤ _ := Finset.sum_le_sum (fun m _ ↦ by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast (show 4 * 4 ^ j + m.val ≤ 5 * 4 ^ j by have := m.isLt; omega))

theorem blocks_divergent : ¬ Summable (fun a : blocks ↦ 1 / (a : ℝ)) := by
  intro hs
  let e : (Σ j : ℕ, Fin (4 ^ j)) → blocks := fun v ↦ ⟨blockValue v, blockValue_mem v⟩
  have he : Function.Injective e := by
    intro x y hxy
    exact blockValue_injective (congrArg Subtype.val hxy)
  have hp : Summable (fun v : Σ j : ℕ, Fin (4 ^ j) ↦ 1 / (blockValue v : ℝ)) :=
    hs.comp_injective (i := e) he
  have ht := (summable_sigma_of_nonneg (fun v ↦ by positivity)).mp hp |>.2
  have hv := ht.tendsto_atTop_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 5)
  obtain ⟨j, hj⟩ := hv.exists
  exact (not_lt_of_ge (block_reciprocal_lower_bound j)) hj

/-- Every infinite increasing sequence in these blocks with nondecreasing gaps has
summable reciprocals, even though the whole set has divergent reciprocal sum. -/
theorem convex_sequence_summable (f : ℕ → ℕ) (hmono : StrictMono f)
    (hconvex : ∀ n : ℕ, f (n + 1) - f n ≤ f (n + 2) - f (n + 1))
    (hmem : ∀ n : ℕ, f n ∈ blocks) :
    Summable (fun n : ℕ ↦ 1 / (f n : ℝ)) := by
  classical
  choose b hb using hmem
  have hbm : Monotone b := by
    intro m n hmn
    by_contra hnot
    have hlt := block_order (show b n < b m by omega) (hb n).2 (hb m).1
    have := hmono.monotone hmn
    omega
  have hprop (n : ℕ) (hn : b n < b (n + 1)) : b (n + 1) < b (n + 2) := by
    by_contra hnot
    have heq : b (n + 2) = b (n + 1) := by
      have := hbm (show n + 1 ≤ n + 2 by omega)
      omega
    have hp := block_power_separation hn
    have hx := (hb n).2
    have hy := (hb (n + 1)).1
    have hz := (hb (n + 2)).2
    rw [heq] at hz
    have hc := hconvex n
    have hxy := hmono (show n < n + 1 by omega)
    have hyz := hmono (show n + 1 < n + 2 by omega)
    omega
  obtain ⟨N, hN⟩ : ∃ N : ℕ, b N < b (N + 1) := by
    by_contra! hn
    have heq (n : ℕ) : b n = b 0 := by
      induction n with
      | zero => rfl
      | succ n ih =>
        have := hn n
        have := hbm (show n ≤ n + 1 by omega)
        omega
    have hl := hmono.id_le (5 * 4 ^ b 0)
    have hu := (hb (5 * 4 ^ b 0)).2
    rw [heq (5 * 4 ^ b 0)] at hu
    exact (not_lt_of_ge hl) hu
  have htail (n : ℕ) : b (n + N) < b (n + N + 1) := by
    induction n with
    | zero => simpa using hN
    | succ n ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hprop (n + N) ih
  have hstrict : StrictMono (fun n : ℕ ↦ b (n + N)) := by
    apply strictMono_nat_of_lt_succ
    intro n
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail n
  have hf (n : ℕ) : 4 ^ n ≤ f (n + N) := by
    have hp : 4 ^ n ≤ 4 ^ b (n + N) :=
      Nat.pow_le_pow_right (by omega) (hstrict.id_le n)
    have := (hb (n + N)).1
    omega
  have hg : Summable (fun n : ℕ ↦ 1 / ((4 ^ n : ℕ) : ℝ)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, one_div, inv_pow] using
      summable_geometric_of_abs_lt_one (by norm_num : |(4 : ℝ)⁻¹| < 1)
  apply (summable_nat_add_iff N).mp
  apply hg.of_nonneg_of_le (fun _ ↦ by positivity)
  intro n
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hf n)

/-- This explicitly refutes the divergence-preserving convex extraction step. -/
theorem convex_extraction_fails :
    ¬ (∀ A : Set ℕ, (¬ Summable (fun a : A ↦ 1 / (a : ℝ))) →
      ∃ f : ℕ → ℕ, StrictMono f ∧
        (∀ n : ℕ, f (n + 1) - f n ≤ f (n + 2) - f (n + 1)) ∧
        (∀ n : ℕ, f n ∈ A) ∧ ¬ Summable (fun n : ℕ ↦ 1 / (f n : ℝ))) := by
  intro h
  obtain ⟨f, hf, hc, hm, hs⟩ := h blocks blocks_divergent
  exact hs (convex_sequence_summable f hf hc hm)

/-- The witness has progressions of every length, so it is not a counterexample
to the conjecture itself. -/
theorem blocks_contains_ap (k : ℕ) : ∃ S ⊆ blocks, S.IsAPOfLength k := by
  let a := 4 * 4 ^ k
  let f : ℕ → ℕ := fun i ↦ a + i
  have hi : Function.Injective f := by
    intro i j hij
    exact Nat.add_left_cancel hij
  refine ⟨f '' Set.Iio k, ?_, a, 1, ?_, ?_⟩
  · rintro x ⟨i, hik, rfl⟩
    have hik' : i < 4 ^ k :=
      (lt_trans hik Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left (by norm_num) k)
    exact ⟨k, by dsimp [f, a]; omega, by dsimp [f, a]; omega⟩
  · change (f '' Set.Iio k).encard = (k : ℕ∞)
    rw [hi.encard_image]
    exact Set.Nat.encard_range k
  · ext x
    simp [f]

#print axioms blocks_contains_ap

#print axioms blocks_divergent
#print axioms convex_sequence_summable
#print axioms convex_extraction_fails

end Erdos3ConvexExtractionCheck
