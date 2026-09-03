import FormalConjecturesUtil

/-! Auxiliary results only: this file does not settle the conjecture. -/

namespace Erdos1206

private lemma cube_sum_lt_of_offset_sum_lt (L M x y z w : ℕ)
    (hM : M = 2 * L ^ 2 + 2 * L ^ 3 + 1)
    (hx : x ≤ L) (hy : y ≤ L) (hs : x + y < z + w) :
    (M + x) ^ 3 + (M + y) ^ 3 < (M + z) ^ 3 + (M + w) ^ 3 := by
  have hx2 : x ^ 2 ≤ L ^ 2 := Nat.pow_le_pow_left hx 2
  have hy2 : y ^ 2 ≤ L ^ 2 := Nat.pow_le_pow_left hy 2
  have hx3 : x ^ 3 ≤ L ^ 3 := Nat.pow_le_pow_left hx 3
  have hy3 : y ^ 3 ≤ L ^ 3 := Nat.pow_le_pow_left hy 3
  have hM2 : 2 * L ^ 2 + 1 ≤ M := by omega
  have hM3 : 2 * L ^ 3 < M := by omega
  have hmul := Nat.mul_le_mul_left (3 * M) hM2
  have hbound : 6 * M * L ^ 2 + 2 * L ^ 3 < 3 * M ^ 2 := by
    nlinarith
  have hquad : x ^ 2 + y ^ 2 ≤ 2 * L ^ 2 := by omega
  have hquad' := Nat.mul_le_mul_left (3 * M) hquad
  have htail : 3 * M * (x ^ 2 + y ^ 2) + (x ^ 3 + y ^ 3) < 3 * M ^ 2 := by
    nlinarith
  have hsum : x + y + 1 ≤ z + w := hs
  have hsum' := Nat.mul_le_mul_left (3 * M ^ 2) hsum
  have hother := Nat.zero_le (3 * M * (z ^ 2 + w ^ 2) + (z ^ 3 + w ^ 3))
  nlinarith only [htail, hsum', hother]

lemma cubes_sidon_on_far_interval (L : ℕ) :
    let M := 2 * L ^ 2 + 2 * L ^ 3 + 1
    IsSidon ((fun a : ℕ => a ^ 3) '' Set.Icc M (M + L)) := by
  dsimp only
  let M := 2 * L ^ 2 + 2 * L ^ 3 + 1
  rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩ heq
  change M ≤ a ∧ a ≤ M + L at ha
  change M ≤ b ∧ b ≤ M + L at hb
  change M ≤ c ∧ c ≤ M + L at hc
  change M ≤ d ∧ d ≤ M + L at hd
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le ha.1
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hb.1
  obtain ⟨z, rfl⟩ := Nat.exists_eq_add_of_le hc.1
  obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hd.1
  have hx : x ≤ L := by omega
  have hy : y ≤ L := by omega
  have hz : z ≤ L := by omega
  have hw : w ≤ L := by omega
  have hs : x + y = z + w := by
    rcases lt_trichotomy (x + y) (z + w) with h | h | h
    · exact False.elim ((ne_of_lt (cube_sum_lt_of_offset_sum_lt L M x y z w rfl hx hy h)) heq)
    · exact h
    · exact False.elim ((ne_of_lt (cube_sum_lt_of_offset_sum_lt L M z w x y rfl hz hw h)) heq.symm)
  have hsum : M + x + (M + y) = M + z + (M + w) := by omega
  have hM : 0 < M := by dsimp [M]; omega
  have hp : (M + x) * (M + y) = (M + z) * (M + w) := by
    have hid :
        3 * (M + x + (M + y)) * ((M + x) * (M + y)) +
          ((M + x) ^ 3 + (M + y) ^ 3) = (M + x + (M + y)) ^ 3 := by ring
    have hid' :
        3 * (M + z + (M + w)) * ((M + z) * (M + w)) +
          ((M + z) ^ 3 + (M + w) ^ 3) = (M + z + (M + w)) ^ 3 := by ring
    rw [hsum, heq] at hid
    have hm : 3 * (M + z + (M + w)) * ((M + x) * (M + y)) =
        3 * (M + z + (M + w)) * ((M + z) * (M + w)) :=
      Nat.add_right_cancel (hid.trans hid'.symm)
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 3 * (M + z + (M + w))) hm
  have hp' : (x : ℤ) * y = (z : ℤ) * w := by
    have hpZ : ((M : ℤ) + x) * (M + y) = (M + z) * (M + w) := by exact_mod_cast hp
    have hsZ : (x : ℤ) + y = z + w := by exact_mod_cast hs
    nlinarith
  have hz0 : ((x : ℤ) - z) * (x - w) = 0 := by
    have hsZ : (x : ℤ) + y = z + w := by exact_mod_cast hs
    nlinarith
  rcases mul_eq_zero.mp hz0 with h | h
  · have hxz : x = z := by omega
    have hyw : y = w := by omega
    subst z
    subst w
    exact Or.inl ⟨rfl, rfl⟩
  · have hxw : x = w := by omega
    have hyz : y = z := by omega
    subst w
    subst z
    exact Or.inr ⟨rfl, rfl⟩

lemma arbitrarily_long_intervals_with_sidon_cubes (L : ℕ) :
    ∃ M : ℕ, IsSidon ((fun a : ℕ => a ^ 3) '' Set.Icc M (M + L)) :=
  ⟨_, cubes_sidon_on_far_interval L⟩

end Erdos1206
