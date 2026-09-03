import FormalConjecturesUtil

/-!
Uniform local restrictions on cubic collisions at primes congruent to `2 mod 3`.
These are structural lemmas, not a density theorem or a settlement of Erdős 1206.
-/

namespace Erdos1206

lemma cube_injective_zmod_of_mod_three_eq_two {p : ℕ} (hp : p.Prime)
    (hp3 : p % 3 = 2) : Function.Injective (fun x : ZMod p => x ^ 3) := by
  letI : Fact p.Prime := ⟨hp⟩
  have he : 3 * (2 * (p / 3) + 1) = (p - 1) * 2 + 1 := by omega
  have hinv (x : ZMod p) : (x ^ 3) ^ (2 * (p / 3) + 1) = x := by
    rw [← pow_mul, he, pow_add, pow_mul]
    by_cases hx : x = 0
    · simp [hx]
    · simp [ZMod.pow_card_sub_one_eq_one hx]
  intro x y h
  change x ^ 3 = y ^ 3 at h
  rw [← hinv x, h, hinv y]

private lemma inert_prime_not_dvd_three {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 2) :
    ¬ p ∣ 3 := by
  intro hd
  have hle := Nat.le_of_dvd (by decide : 0 < 3) hd
  have := hp.two_le
  have hp2 : p = 2 := by omega
  norm_num [hp2] at hd

/-- The quadratic cofactor of a difference of cubes is a unit at an inert prime
whenever the first root is a unit at that prime. -/
lemma inert_prime_not_dvd_cube_cofactor {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 2)
    {a b : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    ¬ (p : ℤ) ∣ a ^ 2 + a * b + b ^ 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  intro hd
  have hQ : (a : ZMod p) ^ 2 + (a : ZMod p) * (b : ZMod p) + (b : ZMod p) ^ 2 = 0 := by
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
  have hcube : (a : ZMod p) ^ 3 = (b : ZMod p) ^ 3 := by
    apply sub_eq_zero.mp
    calc
      _ = ((a : ZMod p) - b) * ((a : ZMod p) ^ 2 + (a : ZMod p) * b + (b : ZMod p) ^ 2) := by ring
      _ = 0 := by rw [hQ]; ring
  have hab := cube_injective_zmod_of_mod_three_eq_two hp hp3 hcube
  have h3 : (3 : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 3 p).not.mpr (inert_prime_not_dvd_three hp hp3)
  have hmul : (3 : ZMod p) * (a : ZMod p) ^ 2 = 0 := by
    rw [← hab] at hQ
    linear_combination hQ
  have ha0 : (a : ZMod p) = 0 :=
    eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hmul).resolve_left h3)
  exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha0)

/-- At an inert prime, a unit root allows the cube exponent to be removed from
congruences modulo every prime power, not just modulo the prime. -/
lemma inert_prime_pow_dvd_cube_sub_iff {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 2)
    {a b : ℤ} (ha : ¬ (p : ℤ) ∣ a) (e : ℕ) :
    (p : ℤ) ^ e ∣ a ^ 3 - b ^ 3 ↔ (p : ℤ) ^ e ∣ a - b := by
  let Q : ℤ := a ^ 2 + a * b + b ^ 2
  have hQ : ¬ (p : ℤ) ∣ Q := inert_prime_not_dvd_cube_cofactor hp hp3 ha
  have hcop : IsCoprime (p : ℤ) Q := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast]
    exact (hp.coprime_iff_not_dvd.mpr (by simpa [← Int.natCast_dvd] using hQ)).gcd_eq_one
  have heq : a ^ 3 - b ^ 3 = (a - b) * Q := by dsimp [Q]; ring
  rw [heq]
  constructor
  · exact hcop.pow_left.dvd_of_dvd_mul_right
  · exact fun h => dvd_mul_of_dvd_left h Q

lemma inert_prime_pow_dvd_cube_add_iff {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 2)
    {a b : ℤ} (ha : ¬ (p : ℤ) ∣ a) (e : ℕ) :
    (p : ℤ) ^ e ∣ a ^ 3 + b ^ 3 ↔ (p : ℤ) ^ e ∣ a + b := by
  simpa only [show (-b) ^ 3 = -(b ^ 3) by ring, sub_neg_eq_add] using
    inert_prime_pow_dvd_cube_sub_iff hp hp3 (b := -b) ha e

/-- A prime `2 mod 3` dividing both roots on one side either divides the
opposite root as well, or its cube is bounded by the sum of the opposite roots. -/
lemma inert_prime_pair_sum_bound {p a b c d : ℕ} (hp : p.Prime) (hp3 : p % 3 = 2)
    (hpa : p ∣ a) (hpb : p ∣ b) (hpc : ¬ p ∣ c) (hcd : 0 < c + d)
    (he : a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3) :
    p ^ 3 ≤ c + d := by
  have hsum : p ^ 3 ∣ c ^ 3 + d ^ 3 := by
    rw [← he]
    exact dvd_add (pow_dvd_pow_of_dvd hpa 3) (pow_dvd_pow_of_dvd hpb 3)
  have hsumZ : (p : ℤ) ^ 3 ∣ (c : ℤ) ^ 3 + (d : ℤ) ^ 3 := by exact_mod_cast hsum
  have hcZ : ¬ (p : ℤ) ∣ (c : ℤ) := by exact_mod_cast hpc
  have hlin := (inert_prime_pow_dvd_cube_add_iff hp hp3 hcZ 3).mp hsumZ
  have hnat : p ^ 3 ∣ c + d := by exact_mod_cast hlin
  exact Nat.le_of_dvd hcd hnat

/-- In a collision whose roots have no common prime divisor, a prime `2 mod 3`
shared by the two roots on one side has cube at most twice the root cutoff. -/
lemma primitive_collision_same_side_inert_prime_bound {p a b c d N : ℕ}
    (hp : p.Prime) (hp3 : p % 3 = 2) (hpa : p ∣ a) (hpb : p ∣ b)
    (hprim : Nat.Coprime (Nat.gcd a b) (Nat.gcd c d))
    (hc : 0 < c) (hcN : c ≤ N) (hdN : d ≤ N)
    (he : a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3) : p ^ 3 ≤ 2 * N := by
  have hpc : ¬ p ∣ c := by
    intro hpc
    have hsum : p ∣ c ^ 3 + d ^ 3 := by
      rw [← he]
      exact dvd_add (hpa.trans (dvd_pow_self a (by decide)))
        (hpb.trans (dvd_pow_self b (by decide)))
    have hpd : p ∣ d := hp.dvd_of_dvd_pow
      ((Nat.dvd_add_iff_right (hpc.trans (dvd_pow_self c (by decide)))).mpr hsum)
    have hh := Nat.dvd_gcd (Nat.dvd_gcd hpa hpb) (Nat.dvd_gcd hpc hpd)
    rw [hprim.gcd_eq_one] at hh
    exact hp.not_dvd_one hh
  have hbound := inert_prime_pair_sum_bound hp hp3 hpa hpb hpc (by omega) he
  omega

/-- For a nontrivial primitive collision, a prime `2 mod 3` dividing two roots
on opposite sides has cube at most the root cutoff. -/
lemma primitive_collision_cross_inert_prime_bound {p a b c d N : ℕ}
    (hp : p.Prime) (hp3 : p % 3 = 2) (hpa : p ∣ a) (hpc : p ∣ c)
    (hprim : Nat.Coprime (Nat.gcd a b) (Nat.gcd c d))
    (hbd : b ≠ d) (hbN : b ≤ N) (hdN : d ≤ N)
    (he : a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3) : p ^ 3 ≤ N := by
  have hpb : ¬ p ∣ b := by
    intro hpb
    have hsum : p ∣ c ^ 3 + d ^ 3 := by
      rw [← he]
      exact dvd_add (hpa.trans (dvd_pow_self a (by decide)))
        (hpb.trans (dvd_pow_self b (by decide)))
    have hpd : p ∣ d := hp.dvd_of_dvd_pow
      ((Nat.dvd_add_iff_right (hpc.trans (dvd_pow_self c (by decide)))).mpr hsum)
    have hh := Nat.dvd_gcd (Nat.dvd_gcd hpa hpb) (Nat.dvd_gcd hpc hpd)
    rw [hprim.gcd_eq_one] at hh
    exact hp.not_dvd_one hh
  have hpaZ : (p : ℤ) ^ 3 ∣ (a : ℤ) ^ 3 := by
    exact_mod_cast pow_dvd_pow_of_dvd hpa 3
  have hpcZ : (p : ℤ) ^ 3 ∣ (c : ℤ) ^ 3 := by
    exact_mod_cast pow_dvd_pow_of_dvd hpc 3
  have heZ : (a : ℤ) ^ 3 + (b : ℤ) ^ 3 = (c : ℤ) ^ 3 + (d : ℤ) ^ 3 := by
    exact_mod_cast he
  have hsub : (p : ℤ) ^ 3 ∣ (b : ℤ) ^ 3 - (d : ℤ) ^ 3 := by
    have heq : (b : ℤ) ^ 3 - (d : ℤ) ^ 3 = (c : ℤ) ^ 3 - (a : ℤ) ^ 3 := by omega
    rw [heq]
    exact dvd_sub hpcZ hpaZ
  have hbZ : ¬ (p : ℤ) ∣ (b : ℤ) := by exact_mod_cast hpb
  have hlin := (inert_prime_pow_dvd_cube_sub_iff hp hp3 hbZ 3).mp hsub
  have hmod : Nat.ModEq (p ^ 3) b d := by
    apply Nat.modEq_iff_dvd.mpr
    have hlin' : (p : ℤ) ^ 3 ∣ (d : ℤ) - (b : ℤ) := by
      simpa only [neg_sub] using dvd_neg.mpr hlin
    exact_mod_cast hlin'
  by_contra hN
  have hb : b < p ^ 3 := by omega
  have hd : d < p ^ 3 := by omega
  apply hbd
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hd] using hmod

/-- Above the cubic-root scale, an inert prime cannot be shared by any two
roots of a nontrivial primitive collision. -/
lemma large_inert_prime_divides_at_most_one_root {p a b c d N : ℕ}
    (hp : p.Prime) (hp3 : p % 3 = 2) (hpN : 2 * N < p ^ 3)
    (hprim : Nat.Coprime (Nat.gcd a b) (Nat.gcd c d))
    (ha : 0 < a) (hc : 0 < c)
    (haN : a ≤ N) (hbN : b ≤ N) (hcN : c ≤ N) (hdN : d ≤ N)
    (hac : a ≠ c) (had : a ≠ d)
    (he : a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3) :
    ¬ (p ∣ a ∧ p ∣ b) ∧ ¬ (p ∣ a ∧ p ∣ c) ∧ ¬ (p ∣ a ∧ p ∣ d) ∧
      ¬ (p ∣ b ∧ p ∣ c) ∧ ¬ (p ∣ b ∧ p ∣ d) ∧ ¬ (p ∣ c ∧ p ∣ d) := by
  have hbd : b ≠ d := by
    intro hh
    apply hac
    apply Nat.pow_left_injective (by decide : 3 ≠ 0)
    dsimp only
    subst d
    omega
  have hbc : b ≠ c := by
    intro hh
    apply had
    apply Nat.pow_left_injective (by decide : 3 ≠ 0)
    dsimp only
    subst c
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hpa, hpb⟩
    have := primitive_collision_same_side_inert_prime_bound hp hp3 hpa hpb
      hprim hc hcN hdN he
    omega
  · rintro ⟨hpa, hpc⟩
    have := primitive_collision_cross_inert_prime_bound hp hp3 hpa hpc
      hprim hbd hbN hdN he
    omega
  · rintro ⟨hpa, hpd⟩
    have := primitive_collision_cross_inert_prime_bound hp hp3 hpa hpd
      (by simpa only [Nat.gcd_comm d c] using hprim) hbc hbN hcN
      (show a ^ 3 + b ^ 3 = d ^ 3 + c ^ 3 by omega)
    omega
  · rintro ⟨hpb, hpc⟩
    have := primitive_collision_cross_inert_prime_bound hp hp3 hpb hpc
      (by simpa only [Nat.gcd_comm b a] using hprim) had haN hdN
      (show b ^ 3 + a ^ 3 = c ^ 3 + d ^ 3 by omega)
    omega
  · rintro ⟨hpb, hpd⟩
    have := primitive_collision_cross_inert_prime_bound hp hp3 hpb hpd
      (by simpa only [Nat.gcd_comm b a, Nat.gcd_comm d c] using hprim) hac haN hcN
      (show b ^ 3 + a ^ 3 = d ^ 3 + c ^ 3 by omega)
    omega
  · rintro ⟨hpc, hpd⟩
    have := primitive_collision_same_side_inert_prime_bound hp hp3 hpc hpd
      hprim.symm ha haN hbN he.symm
    omega

end Erdos1206

#print axioms Erdos1206.inert_prime_pow_dvd_cube_sub_iff
#print axioms Erdos1206.primitive_collision_same_side_inert_prime_bound
#print axioms Erdos1206.primitive_collision_cross_inert_prime_bound

#print axioms Erdos1206.large_inert_prime_divides_at_most_one_root
