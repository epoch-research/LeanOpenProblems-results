import FormalConjectures.Util.ProblemImports

set_option warn.sorry false

open Nat Set

/--
A053000: $a(n) = (\text{smallest prime} > n^2) - n^2$.
-/
noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

/--
Conjecture: a(n) <= 1+phi(n) = 1+A000010(n), for n>0. This improves on Oppermann's conjecture, which says a(n) < n.
-/
@[category research open]
theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n := answer(sorry)


#print axioms oeis_53000_conjecture_1

lemma prime_set_nonempty (n : ℕ) : {p | Nat.Prime p ∧ p > n ^ 2}.Nonempty := by
  rcases Nat.exists_infinite_primes (n ^ 2 + 1) with ⟨p, hp1, hp2⟩
  refine ⟨p, hp2, ?_⟩
  omega

lemma find_congr_classical {P : ℕ → Prop} [d1 : DecidablePred P] [d2 : DecidablePred P] (h1 : ∃ x, P x) (h2 : ∃ x, P x) :
    @Nat.find P d1 h1 = @Nat.find P d2 h2 := by
  have h_spec1 := @Nat.find_spec P d1 h1
  have h_spec2 := @Nat.find_spec P d2 h2
  have h_min1 := @Nat.find_min P d1 h1
  have h_min2 := @Nat.find_min P d2 h2
  have h_le1 : @Nat.find P d1 h1 ≤ @Nat.find P d2 h2 := by
    by_contra h_lt
    have h_lt' : @Nat.find P d2 h2 < @Nat.find P d1 h1 := by omega
    have := h_min1 h_lt'
    exact this h_spec2
  have h_le2 : @Nat.find P d2 h2 ≤ @Nat.find P d1 h1 := by
    by_contra h_lt
    have h_lt' : @Nat.find P d1 h1 < @Nat.find P d2 h2 := by omega
    have := h_min2 h_lt'
    exact this h_spec1
  omega

lemma composite_in_interval_has_small_prime_factor (n x : ℕ) (hn : n ≥ 2) (hx1 : x > n^2) (hx2 : x ≤ n^2 + 1 + Nat.totient n) (h_comp : ¬ Nat.Prime x) :
    ∃ q, Nat.Prime q ∧ q ∣ x ∧ q ≤ n := by
  have hn2_ge : n^2 ≥ 4 := by
    have : 2 * 2 ≤ n * n := Nat.mul_le_mul hn hn
    have hn2_eq : n^2 = n * n := by ring
    omega
  have hx_pos : 0 < x := by omega
  have hx_ne1 : x ≠ 1 := by omega
  let q := minFac x
  have hq_prime : Nat.Prime q := minFac_prime hx_ne1
  have hq_dvd : q ∣ x := minFac_dvd x
  have hq_sq : q ^ 2 ≤ x := minFac_sq_le_self hx_pos h_comp
  have h1 : 1 < n := by omega
  have h_phi_lt : Nat.totient n < n := Nat.totient_lt n h1
  have h_x_lt : x < (n + 1) ^ 2 := by
    calc
      x ≤ n^2 + 1 + Nat.totient n := hx2
      _ < n^2 + 1 + n := by omega
      _ ≤ n^2 + 2 * n + 1 := by omega
      _ = (n + 1) ^ 2 := by ring
  have hq_lt : q < n + 1 := by
    rw [← Nat.mul_self_lt_mul_self_iff]
    have hq2 : q * q = q ^ 2 := by ring
    have hn2 : (n + 1) * (n + 1) = (n + 1) ^ 2 := by ring
    rw [hq2, hn2]
    omega
  refine ⟨q, hq_prime, hq_dvd, by omega⟩


lemma A053000_le_iff (n : ℕ) : A053000 n ≤ 1 + Nat.totient n ↔ sInf {p | Nat.Prime p ∧ p > n ^ 2} ≤ 1 + Nat.totient n + n ^ 2 := by

  dsimp [A053000]
  have hS := prime_set_nonempty n
  have h_mem := Nat.sInf_mem hS
  have h_gt : sInf {p | Nat.Prime p ∧ p > n ^ 2} > n ^ 2 := h_mem.2
  omega

lemma exists_prime_in_interval (n : ℕ) (hn : n > 0) :
    (∃ p, Nat.Prime p ∧ p > n ^ 2 ∧ p ≤ n ^ 2 + 1 + Nat.totient n) → A053000 n ≤ 1 + Nat.totient n := by
  intro h
  rcases h with ⟨p, hp_prime, hp_gt, hp_le⟩
  rw [A053000_le_iff]
  have hS : {p | Nat.Prime p ∧ p > n ^ 2}.Nonempty := ⟨p, hp_prime, hp_gt⟩
  have h_le := Nat.sInf_le (show p ∈ {p | Nat.Prime p ∧ p > n ^ 2} from ⟨hp_prime, hp_gt⟩)
  omega













