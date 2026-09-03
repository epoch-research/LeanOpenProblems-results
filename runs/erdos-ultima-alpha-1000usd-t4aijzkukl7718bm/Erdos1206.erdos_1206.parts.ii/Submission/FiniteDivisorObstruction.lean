import FormalConjecturesUtil

/-! A finite forbidden-divisor set, unless it contains `1`, cannot eliminate all
nontrivial cubic collisions. This does not rule out infinite divisor covers. -/

namespace Erdos1206
open Finset

/-- Every finite collection of forbidden divisors other than `1` leaves an
explicit nontrivial positive cubic collision uncovered. -/
lemma finite_divisors_leave_cube_collision (B : Finset ℕ) (h1 : 1 ∉ B) :
    ∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3 ∧ a ≠ c ∧ a ≠ d ∧
      ∀ p ∈ B, ¬ p ∣ a ∧ ¬ p ∣ b ∧ ¬ p ∣ c ∧ ¬ p ∣ d := by
  let M := ∏ p ∈ B, p.factorial
  have hM : 0 < M := prod_pos fun p hp => Nat.factorial_pos p
  have hav (k : ℕ) (p : ℕ) (hp : p ∈ B) : ¬ p ∣ 1 + M * k := by
    intro hdiv
    have hp0 : 0 < p := Nat.pos_of_dvd_of_pos hdiv (by omega)
    have hpM : p ∣ M :=
      (Nat.dvd_factorial hp0 (le_refl p)).trans (dvd_prod_of_mem Nat.factorial hp)
    have hpk : p ∣ M * k := dvd_mul_of_dvd_left hpM k
    have hp1 : p ∣ 1 := (Nat.dvd_add_iff_left hpk).mpr hdiv
    exact h1 ((Nat.dvd_one.mp hp1) ▸ hp)
  let a := 1 + M * (1296 * M ^ 4 + 864 * M ^ 3 + 312 * M ^ 2 + 84 * M + 13)
  let b := 1 + M * (7776 * M ^ 5 + 9072 * M ^ 4 + 4608 * M ^ 3 +
    1272 * M ^ 2 + 222 * M + 23)
  let c := 1 + M * (1296 * M ^ 4 + 1728 * M ^ 3 + 744 * M ^ 2 + 156 * M + 17)
  let d := 1 + M * (7776 * M ^ 5 + 9072 * M ^ 4 + 4608 * M ^ 3 +
    1272 * M ^ 2 + 198 * M + 19)
  refine ⟨a, b, c, d, by dsimp [a]; omega, by dsimp [b]; omega,
    by dsimp [c]; omega, by dsimp [d]; omega, ?_, ?_, ?_, ?_⟩
  · dsimp [a, b, c, d]
    ring
  · apply ne_of_lt
    dsimp [a, c]
    apply Nat.add_lt_add_left
    apply Nat.mul_lt_mul_of_pos_left _ hM
    omega
  · apply ne_of_lt
    dsimp [a, d]
    apply Nat.add_lt_add_left
    apply Nat.mul_lt_mul_of_pos_left _ hM
    omega
  · intro p hp
    exact ⟨hav _ p hp, hav _ p hp, hav _ p hp, hav _ p hp⟩

/-- A finite divisor cover of all nontrivial cubic collisions must contain `1`. -/
lemma finite_cube_divisor_cover_contains_one (B : Finset ℕ)
    (hcover : ∀ a b c d : ℕ, 0 < a → 0 < b → 0 < c → 0 < d →
      a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3 → a ≠ c → a ≠ d →
      ∃ p ∈ B, p ∣ a ∨ p ∣ b ∨ p ∣ c ∨ p ∣ d) :
    1 ∈ B := by
  by_contra h1
  obtain ⟨a, b, c, d, ha, hb, hc, hd, heq, hac, had, havoid⟩ :=
    finite_divisors_leave_cube_collision B h1
  obtain ⟨p, hp, hpa | hpb | hpc | hpd⟩ := hcover a b c d ha hb hc hd heq hac had
  · exact (havoid p hp).1 hpa
  · exact (havoid p hp).2.1 hpb
  · exact (havoid p hp).2.2.1 hpc
  · exact (havoid p hp).2.2.2 hpd

end Erdos1206
