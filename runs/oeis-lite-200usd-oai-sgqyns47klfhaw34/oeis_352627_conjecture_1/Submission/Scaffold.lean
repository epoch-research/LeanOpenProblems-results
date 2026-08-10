import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  let R : Finset ℕ := Finset.range (sqrt n + 1)
  let S_quadruples := R.product (R.product (R.product R))
  (S_quadruples.filter (fun p =>
    let a := p.1
    let b := p.2.1
    let c := p.2.2.1
    let d := p.2.2.2
    a^2 + 2 * b^2 + c^4 + 4 * d^4 + c^2 * d^2 = n
  )).card

lemma pos_a_of_exists {n A B C D : ℕ}
    (h : A^2 + 2 * B^2 + C^4 + 4 * D^4 + C^2 * D^2 = n) : 0 < a n := by
  dsimp [a]
  rw [Finset.card_pos]
  refine ⟨(A,(B,(C,D))), ?_⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  have hA : A * A ≤ n := by
    rw [← h]
    nlinarith [Nat.zero_le (2 * B^2), Nat.zero_le (C^4), Nat.zero_le (4 * D^4), Nat.zero_le (C^2 * D^2)]
  have hB : B * B ≤ n := by
    rw [← h]
    nlinarith [Nat.zero_le (A^2), Nat.zero_le (B^2), Nat.zero_le (C^4), Nat.zero_le (4 * D^4), Nat.zero_le (C^2 * D^2)]
  have hC : C * C ≤ n := by
    rw [← h]
    have hc : C * C ≤ C ^ 4 := by
      by_cases hc0 : C = 0
      · simp [hc0]
      · have : 1 ≤ C * C := Nat.succ_le_of_lt (Nat.mul_pos (Nat.pos_of_ne_zero hc0) (Nat.pos_of_ne_zero hc0))
        calc C * C = C * C * 1 := by rw [mul_one]
          _ ≤ C * C * (C * C) := Nat.mul_le_mul_left _ this
          _ = C ^ 4 := by ring
    nlinarith [hc, Nat.zero_le (A^2), Nat.zero_le (2 * B^2), Nat.zero_le (4 * D^4), Nat.zero_le (C^2 * D^2)]
  have hD : D * D ≤ n := by
    rw [← h]
    have hd : D * D ≤ 4 * D ^ 4 := by
      by_cases hd0 : D = 0
      · simp [hd0]
      · have : 1 ≤ D * D := Nat.succ_le_of_lt (Nat.mul_pos (Nat.pos_of_ne_zero hd0) (Nat.pos_of_ne_zero hd0))
        calc D * D = 1 * (D * D) := by rw [one_mul]
          _ ≤ 4 * (D * D * (D * D)) := by nlinarith
          _ = 4 * D ^ 4 := by ring
    nlinarith [hd, Nat.zero_le (A^2), Nat.zero_le (2 * B^2), Nat.zero_le (C^4), Nat.zero_le (C^2 * D^2)]
  exact ⟨⟨Nat.lt_succ_of_le (Nat.le_sqrt.mpr hA),
      ⟨Nat.lt_succ_of_le (Nat.le_sqrt.mpr hB),
       ⟨Nat.lt_succ_of_le (Nat.le_sqrt.mpr hC), Nat.lt_succ_of_le (Nat.le_sqrt.mpr hD)⟩⟩⟩,
    by simpa using h⟩

lemma sq_add_sq_same_parity {x y : ℕ} (h : x % 2 = y % 2) :
    ∃ u v : ℕ, x ^ 2 + y ^ 2 = 2 * u ^ 2 + 2 * v ^ 2 := by
  wlog hxy : x ≤ y generalizing x y with H
  · obtain ⟨u,v,huv⟩ := H h.symm (le_of_not_ge hxy)
    exact ⟨u,v, by simpa [add_comm] using huv⟩
  have hEvenDiff : Even (y - x) := by rw [Nat.even_iff]; omega
  have hEvenSum : Even (x + y) := by rw [Nat.even_iff]; omega
  obtain ⟨v,hv⟩ := hEvenDiff
  obtain ⟨u,hu⟩ := hEvenSum
  refine ⟨u,v,?_⟩
  have hy : y = x + 2*v := by omega
  have hu' : u = x + v := by omega
  subst y; subst u; ring

lemma four_sq_to_1122 (n : ℕ) :
    ∃ x z y w : ℕ, x ^ 2 + z ^ 2 + 2 * y ^ 2 + 2 * w ^ 2 = n := by
  obtain ⟨a,b,c,d,h⟩ := Nat.sum_four_squares n
  have hab : a % 2 = b % 2 ∨ a % 2 = c % 2 ∨ a % 2 = d % 2 ∨
             b % 2 = c % 2 ∨ b % 2 = d % 2 ∨ c % 2 = d % 2 := by
    omega
  rcases hab with hab | hac | had | hbc | hbd | hcd
  · obtain ⟨u,v,huv⟩ := sq_add_sq_same_parity hab
    refine ⟨c,d,u,v,?_⟩; nlinarith
  · obtain ⟨u,v,huv⟩ := sq_add_sq_same_parity hac
    refine ⟨b,d,u,v,?_⟩; nlinarith
  · obtain ⟨u,v,huv⟩ := sq_add_sq_same_parity had
    refine ⟨b,c,u,v,?_⟩; nlinarith
  · obtain ⟨u,v,huv⟩ := sq_add_sq_same_parity hbc
    refine ⟨a,d,u,v,?_⟩; nlinarith
  · obtain ⟨u,v,huv⟩ := sq_add_sq_same_parity hbd
    refine ⟨a,c,u,v,?_⟩; nlinarith
  · obtain ⟨u,v,huv⟩ := sq_add_sq_same_parity hcd
    refine ⟨a,b,u,v,?_⟩; nlinarith
