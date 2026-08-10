with open("/workspace/leanproject/Submission/Spec.lean", "r") as f:
    content = f.read()

helper_code = """
theorem coprime_of_distinct_primes {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) : p.Coprime q := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have h_eq : q = p := by
    have hp1 : p ≠ 1 := hp.ne_one
    rwa [Nat.Prime.dvd_iff_eq hq hp1] at hdvd
  exact hne h_eq.symm

theorem A319524_eq_cond (y : ℕ) (hy : 1 ≤ y) (h_eq : A319524 y = A319524 (y + 1)) :
  let p (k : ℕ) : ℕ := Nat.nth Nat.Prime k
  let P1 := p (y - 1)
  let P2 := p y
  let P3 := p (y + 1)
  let P4 := p (y + 2)
  ∃ (m m' k' : ℕ),
    1 ≤ m ∧ 1 ≤ m' ∧ 1 ≤ k' ∧
    P1 + m * P2 = P2 + m' * P3 ∧
    P2 + m' * P3 = P3 + k' * P4 ∧
    m' < P2 := by
  intro p P1 P2 P3 P4
  have h_inf : {x : ℕ | Nat.Prime x}.Infinite := Nat.infinite_setOf_prime
  have hP1_lt_P2 : P1 < P2 := (nth_strictMono h_inf) (Nat.sub_lt hy (by decide))
  have hP2_lt_P3 : P2 < P3 := (nth_strictMono h_inf) (Nat.lt_succ_self y)
  have hP3_lt_P4 : P3 < P4 := (nth_strictMono h_inf) (Nat.lt_succ_self (y + 1))
  have h_prime2 : Nat.Prime P2 := nth_mem_of_infinite h_inf y
  have h_prime3 : Nat.Prime P3 := nth_mem_of_infinite h_inf (y + 1)
  have h_prime4 : Nat.Prime P4 := nth_mem_of_infinite h_inf (y + 2)
  have h_ne23 : P2 ≠ P3 := (nth_strictMono h_inf).injective.ne (by omega)
  have h_ne34 : P3 ≠ P4 := (nth_strictMono h_inf).injective.ne (by omega)
  have h_coprime23 : P2.Coprime P3 := coprime_of_distinct_primes h_prime2 h_prime3 h_ne23
  have h_coprime34 : P3.Coprime P4 := coprime_of_distinct_primes h_prime3 h_prime4 h_ne34

  let S1 := { x : ℕ | ∃ m m', 1 ≤ m ∧ 1 ≤ m' ∧ x = P1 + m * P2 ∧ x = P2 + m' * P3 }
  let S2 := { x : ℕ | ∃ m m', 1 ≤ m ∧ 1 ≤ m' ∧ x = P2 + m * P3 ∧ x = P3 + m' * P4 }
  have hS1 : S1.Nonempty := S_nonempty P1 P2 P3 hP1_lt_P2 hP2_lt_P3 h_coprime23
  have hS2 : S2.Nonempty := S_nonempty P2 P3 P4 hP2_lt_P3 hP3_lt_P4 h_coprime34

  have h_isLeast1 : IsLeast S1 (A319524 y) := by
    change IsLeast S1 (sInf S1)
    exact sInf_least hS1
  have h_isLeast2 : IsLeast S2 (A319524 (y+1)) := by
    change IsLeast S2 (sInf S2)
    exact sInf_least hS2

  let X := A319524 y
  have hX_eq2 : A319524 (y + 1) = X := h_eq.symm
  have hX_S1 : X ∈ S1 := h_isLeast1.1
  have hX_S2 : X ∈ S2 := hX_eq2 ▸ h_isLeast2.1

  rcases hX_S1 with ⟨m, m', hm, hm', hX_eq1_1, hX_eq1_2⟩
  rcases hX_S2 with ⟨n, n', hn, hn', hX_eq2_1, hX_eq2_2⟩

  have h_m'_eq_n : m' = n := by
    have h_eq_parts : P2 + m' * P3 = P2 + n * P3 := by rw [← hX_eq1_2, hX_eq2_1]
    have h_eq_mul : m' * P3 = n * P3 := Nat.add_left_cancel h_eq_parts
    have hP3_pos : 0 < P3 := h_prime3.pos
    exact Nat.eq_of_mul_eq_mul_right hP3_pos h_eq_mul

  have hm'_lt_P2 : m' < P2 := by
    have hP1_pos : 0 < P1 := by
      have : 2 ≤ P1 := by
        have h_p0 : nth Nat.Prime 0 = 2 := by
          have h_2 : Nat.Prime 2 := by decide
          have hc_2 : count Nat.Prime 2 = 0 := by decide
          have := nth_count h_2
          rw [hc_2] at this
          exact this
        rw [← h_p0]
        exact (nth_strictMono h_inf).monotone (by omega)
      omega
    have hP2_pos : 0 < P2 := h_prime2.pos
    have hP3_pos : 0 < P3 := h_prime3.pos
    exact m'_lt_P2 P1 P2 P3 m m' X hP1_pos hP2_pos hP3_pos hP1_lt_P2 h_isLeast1 hm hm' hX_eq1_1 hX_eq1_2

  use m, m', n'
  refine ⟨hm, hm', hn', hX_eq1_1.symm.trans hX_eq1_2, ?_, hm'_lt_P2⟩
  calc P2 + m' * P3 = X := hX_eq1_2.symm
  _ = P3 + n' * P4 := hX_eq2_2
"""

target = "theorem oeis_a319524_conjecture_1.disproof"
new_content = content.replace(target, helper_code + "\n" + target)

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write(new_content)

print("Inserted helper theorems successfully!")
