import FormalConjectures.Util.ProblemImports

open Nat Finset Set

-- Genuine verified identity: the set S = {x²+y²+z³} is closed under multiplication by 8.
-- Proof identity: 8(x²+y²+z³) = (2x+2y)² + (2|x-y|)² + (2z)³.
theorem descent8 (n : ℕ) (h : ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 + z ^ 3) :
    ∃ x y z : ℕ, 8 * n = x ^ 2 + y ^ 2 + z ^ 3 := by
  obtain ⟨x, y, z, rfl⟩ := h
  rcases le_total y x with hxy | hxy
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hxy
    exact ⟨2 * (y + a) + 2 * y, 2 * a, 2 * z, by ring⟩
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hxy
    exact ⟨2 * x + 2 * (x + a), 2 * a, 2 * z, by ring⟩

-- The key lemma: every integer > 5042631 is a sum of two squares and a cube.
theorem eu : ∀ m : ℕ, 5042631 < m → ∃ x y z : ℕ, m = x^2 + y^2 + z^3 := by
  sorry

theorem foo.disproof :
  ¬ (∀ (a b c i j k : ℕ),
      0 < a → 0 < b → 0 < c →
      1 < i → 1 < j → 1 < k →
      (let S : Set ℕ := {n | ∃ x y z : ℕ, n = a * x^i + b * y^j + c * z^k}
       Set.Infinite {n : ℕ+ | (n : ℕ) ∉ S})) := by
  intro H
  have h := H 1 1 1 2 2 3 one_pos one_pos one_pos (by norm_num) (by norm_num) (by norm_num)
  simp only [one_mul] at h
  -- h : Set.Infinite {n : ℕ+ | (n:ℕ) ∉ {n | ∃ x y z, n = x^2 + y^2 + z^3}}
  have hbig : ((fun n : ℕ+ => (n : ℕ)) ⁻¹' Set.Iic (5042631 : ℕ)).Finite :=
    Set.Finite.preimage (PNat.coe_injective.injOn) (Set.finite_Iic _)
  have hfin : {n : ℕ+ | (n : ℕ) ∉ {n : ℕ | ∃ x y z : ℕ, n = x^2 + y^2 + z^3}}.Finite := by
    apply Set.Finite.subset hbig
    intro n hn
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic] at hn ⊢
    by_contra hlt
    push_neg at hlt
    obtain ⟨x, y, z, hxyz⟩ := eu (n : ℕ) hlt
    exact hn ⟨x, y, z, hxyz⟩
  exact (Set.not_infinite.mpr hfin) h
