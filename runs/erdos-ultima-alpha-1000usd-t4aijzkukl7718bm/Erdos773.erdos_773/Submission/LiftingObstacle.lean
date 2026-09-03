import FormalConjecturesUtil

/-!
A check of the naive block-enlargement proposal. This is not a disproof of Erdős 773.
-/

namespace Erdos773

lemma block_collision_identity (a b L : ℤ) :
    (2 * a * L + 2 * a + b) ^ 2 + (2 * b * L + 2 * b - a) ^ 2 =
      (2 * a * L + 2 * a - b) ^ 2 + (2 * b * L + 2 * b + a) ^ 2 := by
  ring

lemma two_label_squares_sidon : IsSidon ({8 ^ 2, 10 ^ 2} : Set ℕ) := by
  intro a ha b hb c hc d hd he
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc hd
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> norm_num at *

private def blockLift : Set ℕ :=
  {n | ∃ a ∈ ({8, 10} : Set ℕ), ∃ b < 20, n = 20 * a + b}

lemma naive_block_lift_not_sidon :
    ¬ IsSidon ((fun n : ℕ => n ^ 2) '' blockLift) := by
  intro h
  have hm {a b : ℕ} (ha : a ∈ ({8, 10} : Set ℕ)) (hb : b < 20) :
      (20 * a + b) ^ 2 ∈ ((fun n : ℕ => n ^ 2) '' blockLift) := by
    exact ⟨20 * a + b, ⟨a, ha, b, hb, rfl⟩, rfl⟩
  have h173 := hm (a := 8) (b := 13) (by simp) (by omega)
  have h163 := hm (a := 8) (b := 3) (by simp) (by omega)
  have h206 := hm (a := 10) (b := 6) (by simp) (by omega)
  have h214 := hm (a := 10) (b := 14) (by simp) (by omega)
  have he := h _ h173 _ h163 _ h206 _ h214 (by norm_num)
  norm_num at he

#print axioms naive_block_lift_not_sidon

end Erdos773
