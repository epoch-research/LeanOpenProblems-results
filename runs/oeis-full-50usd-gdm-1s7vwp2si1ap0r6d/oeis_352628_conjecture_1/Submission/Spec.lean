import FormalConjectures.Util.ProblemImports

open Nat Finset

lemma same_parity_sum_sq_helper (u v : ℕ) (h_le : v ≤ u) (hp : u % 2 = v % 2) :
    ∃ z w, 2 * z^2 + 2 * w^2 = u^2 + v^2 := by
  have h1 : (u + v) % 2 = 0 := by
    omega
  have h2 : (u - v) % 2 = 0 := by
    omega
  obtain ⟨z, hz⟩ : ∃ k, u + v = 2 * k := by
    exact dvd_iff_mod_eq_zero.mpr h1
  obtain ⟨w, hw⟩ : ∃ k, u - v = 2 * k := by
    exact dvd_iff_mod_eq_zero.mpr h2
  use z, w
  have hz2 : 2 * z = u + v := by omega
  have hw2 : 2 * w = u - v := by omega
  have h_eq : 4 * (2 * z^2 + 2 * w^2) = 4 * (u^2 + v^2) := by
    calc
      4 * (2 * z^2 + 2 * w^2) = 2 * ((2 * z)^2 + (2 * w)^2) := by ring
      _ = 2 * ((u + v)^2 + (u - v)^2) := by rw [hz2, hw2]
      _ = 4 * (u^2 + v^2) := by
        rcases Nat.exists_eq_add_of_le h_le with ⟨d, rfl⟩
        have h_sub : v + d - v = d := by omega
        rw [h_sub]
        ring
  omega

lemma same_parity_sum_sq (u v : ℕ) (hp : u % 2 = v % 2) :
    ∃ z w, 2 * z^2 + 2 * w^2 = u^2 + v^2 := by
  by_cases h : v ≤ u
  · exact same_parity_sum_sq_helper u v h hp
  · have h_le : u ≤ v := by omega
    have hp2 : v % 2 = u % 2 := hp.symm
    rcases same_parity_sum_sq_helper v u h_le hp2 with ⟨z, w, hzw⟩
    use z, w
    rw [add_comm (u^2) (v^2)]
    exact hzw

lemma parity_pigeonhole (A B C D : ℕ) :
    A % 2 = B % 2 ∨ A % 2 = C % 2 ∨ A % 2 = D % 2 ∨
    B % 2 = C % 2 ∨ B % 2 = D % 2 ∨
    C % 2 = D % 2 := by
  omega

lemma sum_four_squares_to_form (n : ℕ) : ∃ x y z w, x^2 + y^2 + 2*z^2 + 2*w^2 = n := by
  rcases Nat.sum_four_squares n with ⟨A, B, C, D, h⟩
  rcases parity_pigeonhole A B C D with hAB | hAC | hAD | hBC | hBD | hCD
  · rcases same_parity_sum_sq A B hAB with ⟨z, w, hzw⟩
    use C, D, z, w
    omega
  · rcases same_parity_sum_sq A C hAC with ⟨z, w, hzw⟩
    use B, D, z, w
    omega
  · rcases same_parity_sum_sq A D hAD with ⟨z, w, hzw⟩
    use B, C, z, w
    omega
  · rcases same_parity_sum_sq B C hBC with ⟨z, w, hzw⟩
    use A, D, z, w
    omega
  · rcases same_parity_sum_sq B D hBD with ⟨z, w, hzw⟩
    use A, C, z, w
    omega
  · rcases same_parity_sum_sq C D hCD with ⟨z, w, hzw⟩
    use A, B, z, w
    omega

/--
A352628: Number of ways to write $n$ as $a^2 + 2b^2 + c^4 + 2d^4 + 3c^2d^2$,
where $a,b,c,d$ are nonnegative integers.
-/
def A352628 (n : ℕ) : ℕ :=
  let S : Finset ℕ := range (n + 1)
  let Q := S.product (S.product (S.product S))
  Q.sum fun p =>
    let a := p.fst
    let p_bcd := p.snd
    let b := p_bcd.fst
    let p_cd := p_bcd.snd
    let c := p_cd.fst
    let d := p_cd.snd
    let E := (a^2) + (2 * b^2) + (c^4) + (2 * d^4) + (3 * c^2 * d^2)
    if E = n then 1 else 0

lemma nat_le_sq (a : ℕ) : a ≤ a^2 := by
  cases a with
  | zero => simp
  | succ a =>
    rw [sq]
    have : a + 1 ≤ (a + 1) * (a + 1) := by nlinarith
    exact this

lemma representable_le {a b c d n : ℕ} (h : a^2 + 2*b^2 + c^4 + 2*d^4 + 3*c^2*d^2 = n) :
    a ≤ n ∧ b ≤ n ∧ c ≤ n ∧ d ≤ n := by
  have h1 : a^2 ≤ n := by omega
  have h2 : b^2 ≤ n := by omega
  have h3 : c^2 ≤ n := by
    have hc : (c^2)^2 = c^4 := by ring
    have h_c4 : c^4 ≤ n := by omega
    rw [← hc] at h_c4
    have : c^2 ≤ (c^2)^2 := nat_le_sq (c^2)
    exact this.trans h_c4
  have h4 : d^2 ≤ n := by
    have hd : (d^2)^2 = d^4 := by ring
    have h_d4 : d^4 ≤ n := by omega
    rw [← hd] at h_d4
    have : d^2 ≤ (d^2)^2 := nat_le_sq (d^2)
    exact this.trans h_d4
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (nat_le_sq a).trans h1
  · exact (nat_le_sq b).trans h2
  · exact (nat_le_sq c).trans h3
  · exact (nat_le_sq d).trans h4

lemma representable (n : ℕ) : ∃ a b c d, a^2 + 2*b^2 + c^4 + 2*d^4 + 3*c^2*d^2 = n := by
  sorry

theorem oeis_352628_conjecture_1 (n : ℕ) : A352628 n > 0 := by
  unfold A352628
  apply Finset.sum_pos'
  · intro p hp
    dsimp only
    split_ifs
    · exact zero_le_one
    · rfl
  · dsimp only
    rcases representable n with ⟨a, b, c, d, h⟩
    have h_le := representable_le h
    have ha : a ∈ range (n + 1) := mem_range.mpr (by omega)
    have hb : b ∈ range (n + 1) := mem_range.mpr (by omega)
    have hc : c ∈ range (n + 1) := mem_range.mpr (by omega)
    have hd : d ∈ range (n + 1) := mem_range.mpr (by omega)
    use (a, (b, (c, d)))
    refine ⟨?_, ?_⟩
    · simp [ha, hb, hc, hd]
    · simp only [h, ↓reduceIte]
      exact zero_lt_one
