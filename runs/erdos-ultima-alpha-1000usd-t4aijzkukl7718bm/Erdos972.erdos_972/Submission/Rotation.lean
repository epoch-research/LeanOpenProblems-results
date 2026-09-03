import FormalConjecturesUtil
/-! Auxiliary irrational-rotation lemmas for investigating modular obstructions. -/
namespace Erdos972Aux

lemma irrational_mod_interval {α : ℝ} (hI : Irrational α)
    (β a b : ℝ) (hab : a < b) :
    ∃ n : ℕ, ∃ m : ℤ, a < α * n + β - m ∧ α * n + β - m < b := by
  have hz : DenseRange (fun n : ℤ => n • (α : AddCircle (1 : ℝ))) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using hI)
  have hn : DenseRange (fun n : ℕ => n • (α : AddCircle (1 : ℝ))) :=
    denseRange_zsmul_iff_nsmul.mp hz
  have hd : DenseRange (fun n : ℕ => n • (α : AddCircle (1 : ℝ)) +
      (β : AddCircle (1 : ℝ))) :=
    (Homeomorph.addRight (β : AddCircle (1 : ℝ))).surjective.denseRange.comp hn
      (Homeomorph.addRight (β : AddCircle (1 : ℝ))).continuous
  obtain ⟨n, x, hx, heq⟩ := hd.exists_mem_open
    (QuotientAddGroup.isOpenMap_coe (Set.Ioo a b) isOpen_Ioo)
    ((Set.nonempty_Ioo.mpr hab).image (fun x : ℝ => (x : AddCircle (1 : ℝ))))
  have heq' : ((α * n + β - x : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, AddCircle.coe_add]
    have hn' : ((α * n : ℝ) : AddCircle (1 : ℝ)) =
        n • (α : AddCircle (1 : ℝ)) := by
      rw [mul_comm, ← nsmul_eq_mul, AddCircle.coe_nsmul]
    rw [hn', heq, sub_self]
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp heq'
  simp only [zsmul_eq_mul, mul_one] at hm
  exact ⟨n, m, by linarith [hx.1], by linarith [hx.2]⟩

lemma exists_large_coprime_pair {α : ℝ} (hα : 0 ≤ α) (hI : Irrational α)
    (M : ℕ) (hM : 0 < M) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ n.Coprime M ∧ (⌊α * n⌋₊).Coprime M := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  obtain ⟨k, m, hlo, hhi⟩ := irrational_mod_interval hI
    (α * (M * (N + 1) + 1) / M) (1 / M) (2 / M)
    (div_lt_div_of_pos_right (by norm_num) hMr)
  let n := M * (k + N + 1) + 1
  have heq : α * n = (M : ℝ) * (α * k + α * (M * (N + 1) + 1) / M) := by
    dsimp [n]
    push_cast
    field_simp
    <;> ring
  have hlo' : 1 < α * n - (M : ℝ) * m := by
    have h := (div_lt_iff₀ hMr).mp hlo
    rw [heq]
    nlinarith [h]
  have hhi' : α * n - (M : ℝ) * m < 2 := by
    have h := (lt_div_iff₀ hMr).mp hhi
    rw [heq]
    nlinarith [h]
  have hf : ⌊α * n⌋ = (M : ℤ) * m + 1 := by
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith
  refine ⟨n, ?_, ?_, ?_⟩
  · dsimp [n]
    nlinarith
  · dsimp [n]
    simp [Nat.coprime_mul_left_add_left]
  · change Nat.gcd ⌊α * n⌋₊ M = 1
    rw [← Int.gcd_natCast_natCast,
      Int.natCast_floor_eq_floor (mul_nonneg hα (Nat.cast_nonneg n)), hf]
    rw [add_comm, Int.gcd_add_mul_left_left]
    simp

lemma infinite_coprime_pairs {α : ℝ} (hα : 0 ≤ α) (hI : Irrational α)
    (M : ℕ) (hM : 0 < M) :
    {n : ℕ | n.Coprime M ∧ (⌊α * n⌋₊).Coprime M}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hn, hc, hfc⟩ := exists_large_coprime_pair hα hI M hM N
  exact ⟨n, ⟨hc, hfc⟩, hn⟩

#print axioms infinite_coprime_pairs
#print axioms exists_large_coprime_pair
#print axioms irrational_mod_interval
end Erdos972Aux
