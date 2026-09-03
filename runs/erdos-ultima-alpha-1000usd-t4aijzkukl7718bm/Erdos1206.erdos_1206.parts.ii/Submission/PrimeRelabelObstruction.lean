import Submission.Compactness

/-!
A restricted obstruction: relabelling the prime factors while preserving their
exponents cannot define a positive-density set with Sidon cubes. This does not
settle the unrestricted conjecture.
-/

namespace Erdos1206
open Finset
open scoped Classical

/-- Membership is unchanged by injectively relabelling the prime factors.
For positive integers this is precisely the relevant exponent-pattern
invariance; no invariance is imposed at zero. -/
def PrimeRelabelInvariant (A : Set ℕ) : Prop :=
  ∀ f : ℕ → ℕ, Function.Injective f → (∀ p, Nat.Prime p → Nat.Prime (f p)) →
    ∀ n : ℕ, 0 < n → (n ∈ A ↔ n.factorization.prod (fun p e => f p ^ e) ∈ A)

private lemma relabel_collision_from_exponent_one {A : Set ℕ}
    (hA : PrimeRelabelInvariant A) {n p : ℕ} (hn : n ∈ A) (hn0 : 0 < n)
    (hep : n.factorization p = 1) :
    ¬ IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  classical
  let q : ℕ → ℕ := fun j => Nat.nth Nat.Prime (j + 35544)
  have hqprime (j : ℕ) : Nat.Prime (q j) :=
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _
  have hqbig (j : ℕ) : 35543 < q j := by
    have hle := (Nat.nth_strictMono Nat.infinite_setOf_prime).id_le (j + 35544)
    change j + 35544 ≤ q j at hle
    omega
  have hqinj : Function.Injective q := by
    intro j k hjk
    have hh := Nat.nth_injective Nat.infinite_setOf_prime hjk
    omega
  have hpS : p ∈ n.primeFactors := by
    change p ∈ n.factorization.support
    exact Finsupp.mem_support_iff.mpr (by omega)
  let m := ∏ r ∈ n.primeFactors.erase p, q r ^ n.factorization r
  have hm : 0 < m := prod_pos fun r hr => pow_pos (hqprime r).pos _
  have hmem (r : ℕ) (hr : Nat.Prime r) (hrb : r ≤ 35543) : r * m ∈ A := by
    let f : ℕ → ℕ := fun j => if j = p then r else q j
    have hfi : Function.Injective f := by
      intro i j hij
      by_cases hi : i = p
      · subst i
        by_cases hj : j = p
        · exact hj.symm
        · simp only [f, if_pos rfl, if_neg hj] at hij
          have := hqbig j
          omega
      · by_cases hj : j = p
        · subst j
          simp only [f, if_neg hi, if_pos rfl] at hij
          have := hqbig i
          omega
        · simp only [f, if_neg hi, if_neg hj] at hij
          exact hqinj hij
    have hfp : ∀ j, Nat.Prime j → Nat.Prime (f j) := by
      intro j hj
      dsimp only [f]
      split_ifs
      · exact hr
      · exact hqprime j
    have hh := (hA f hfi hfp n hn0).mp hn
    have heq : n.factorization.prod (fun j e => f j ^ e) = r * m := by
      rw [Nat.prod_factorization_eq_prod_primeFactors,
        ← mul_prod_erase n.primeFactors (fun j => f j ^ n.factorization j) hpS]
      simp only [f, if_pos rfl, hep, pow_one]
      congr 1
      apply prod_congr rfl
      intro j hj
      rw [if_neg (mem_erase.mp hj).1]
    rwa [heq] at hh
  have h1 := hmem 26711 (by norm_num) (by omega)
  have h2 := hmem 31469 (by norm_num) (by omega)
  have h3 := hmem 32009 (by norm_num) (by omega)
  have h4 := hmem 35543 (by norm_num) (by omega)
  intro hs
  have he : (26711 * m)^3 + (35543 * m)^3 =
      (31469 * m)^3 + (32009 * m)^3 := by ring
  have hh := hs _ ⟨_, h1, rfl⟩ _ ⟨_, h2, rfl⟩
    _ ⟨_, h4, rfl⟩ _ ⟨_, h3, rfl⟩ he
  rcases hh with hh | hh
  · have heq := Nat.pow_left_injective (by decide : 3 ≠ 0) hh.1
    nlinarith
  · have heq := Nat.pow_left_injective (by decide : 3 ≠ 0) hh.1
    nlinarith

lemma prime_relabel_cube_sidon_powerful {A : Set ℕ}
    (hA : PrimeRelabelInvariant A)
    (hs : IsSidon ((fun n : ℕ => n ^ 3) '' A)) :
    ∀ n ∈ A, Nat.Powerful n := by
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    exact Nat.Full.zero_right 2
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hep : 0 < n.factorization p := by
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  have hne : n.factorization p ≠ 1 := by
    intro he
    exact relabel_collision_from_exponent_one hA hn (Nat.pos_of_ne_zero hn0) he hs
  exact (hpprime.pow_dvd_iff_le_factorization hn0).mpr (by omega)

/-- Every powerful integer is a square times a cube. -/
lemma powerful_eq_square_mul_cube {n : ℕ} (hn : Nat.Powerful n) :
    ∃ a b : ℕ, n = a ^ 2 * b ^ 3 := by
  classical
  by_cases hn0 : n = 0
  · exact ⟨0, 0, by simp [hn0]⟩
  let e := n.factorization
  let a := ∏ p ∈ n.primeFactors, p ^ ((e p - 3 * (e p % 2)) / 2)
  let b := ∏ p ∈ n.primeFactors, p ^ (e p % 2)
  refine ⟨a, b, ?_⟩
  have he (p : ℕ) (hp : p ∈ n.primeFactors) :
      (e p - 3 * (e p % 2)) / 2 * 2 + (e p % 2) * 3 = e p := by
    have h2 : 2 ≤ e p :=
      (Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization hn0 |>.mp (hn p hp)
    have hm : e p % 2 < 2 := Nat.mod_lt _ (by omega)
    omega
  calc
    n = ∏ p ∈ n.primeFactors, p ^ e p := by
      simpa only [Nat.prod_factorization_eq_prod_primeFactors] using
        (Nat.factorization_prod_pow_eq_self hn0).symm
    _ = ∏ p ∈ n.primeFactors,
        (p ^ ((e p - 3 * (e p % 2)) / 2)) ^ 2 * (p ^ (e p % 2)) ^ 3 := by
      apply prod_congr rfl
      intro p hp
      rw [← pow_mul, ← pow_mul, ← pow_add, he p hp]
    _ = a ^ 2 * b ^ 3 := by
      rw [prod_mul_distrib, prod_pow, prod_pow]

/-- A simple power-saving bound along sixth-power cutoffs. -/
lemma powerful_prefix_count (t : ℕ) :
    ({n : ℕ | Nat.Powerful n} ∩ Set.Iio (t ^ 6)).ncard ≤ t ^ 5 := by
  classical
  let S := (range (t ^ 3)) ×ˢ (range (t ^ 2))
  let F := S.image (fun x => x.1 ^ 2 * x.2 ^ 3)
  have hsub : {n : ℕ | Nat.Powerful n} ∩ Set.Iio (t ^ 6) ⊆ (F : Set ℕ) := by
    intro n hn
    have hnN : n < t ^ 6 := hn.2
    have ht : 0 < t := by
      by_contra hh
      have he : t = 0 := by omega
      simp [he] at hnN
    by_cases hn0 : n = 0
    · apply mem_image.mpr
      refine ⟨(0, 0), ?_, by simp [hn0]⟩
      exact mem_product.mpr ⟨mem_range.mpr (pow_pos ht _), mem_range.mpr (pow_pos ht _)⟩
    · obtain ⟨a, b, he⟩ := powerful_eq_square_mul_cube hn.1
      have ha : 0 < a := by
        by_contra hh
        have ha0 : a = 0 := by omega
        simp [ha0] at he
        exact hn0 he
      have hb : 0 < b := by
        by_contra hh
        have hb0 : b = 0 := by omega
        simp [hb0] at he
        exact hn0 he
      have haN : a ^ 2 < (t ^ 3) ^ 2 := by
        rw [← pow_mul]
        norm_num
        exact (Nat.le_mul_of_pos_right (a ^ 2) (pow_pos hb _)).trans_lt (he ▸ hnN)
      have hbN : b ^ 3 < (t ^ 2) ^ 3 := by
        rw [← pow_mul]
        norm_num
        exact (Nat.le_mul_of_pos_left (b ^ 3) (pow_pos ha _)).trans_lt (he ▸ hnN)
      exact mem_image.mpr ⟨(a, b), mem_product.mpr
        ⟨mem_range.mpr ((Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp haN),
          mem_range.mpr ((Nat.pow_lt_pow_iff_left (by decide : 3 ≠ 0)).mp hbN)⟩, he.symm⟩
  have hh := Set.ncard_le_ncard hsub F.finite_toSet
  have hcard : F.card ≤ t ^ 5 := by
    calc
      F.card ≤ S.card := card_image_le
      _ = t ^ 3 * t ^ 2 := by simp [S]
      _ = t ^ 5 := by rw [← pow_add]
  simp only [Set.ncard_coe_finset] at hh
  exact hh.trans hcard

lemma lowerDensity_zero_of_powerful_support {A : Set ℕ}
    (hA : ∀ n ∈ A, Nat.Powerful n) : A.lowerDensity = 0 := by
  apply le_antisymm _ (Set.lowerDensity_nonneg A)
  by_contra! hpos
  obtain ⟨δ, hδ, C, hpref⟩ := prefix_bound_of_positive_lowerDensity hpos
  have hC : 0 ≤ C := by simpa using hpref 0
  obtain ⟨t, ht⟩ := exists_nat_gt ((C + 1) / δ + 1)
  have htpos : 0 < t := by
    have : (0 : ℝ) ≤ (C + 1) / δ := by positivity
    have : (0 : ℝ) < t := by linarith
    exact_mod_cast this
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast htpos
  have hlarge : C + 1 < δ * t := by
    have : (C + 1) / δ < t := by linarith
    have := (div_lt_iff₀ hδ).mp this
    nlinarith
  have hcount : (A ∩ Set.Iio (t ^ 6)).ncard ≤ t ^ 5 := by
    apply le_trans (Set.ncard_le_ncard (t := {n : ℕ | Nat.Powerful n} ∩ Set.Iio (t ^ 6))
      (fun n hn => ⟨hA n hn.1, hn.2⟩))
    exact powerful_prefix_count t
  have hcR : ((A ∩ Set.Iio (t ^ 6)).ncard : ℝ) ≤ (t : ℝ) ^ 5 := by exact_mod_cast hcount
  have hp := hpref (t ^ 6)
  push_cast at hp
  have ht5 : (1 : ℝ) ≤ (t : ℝ) ^ 5 := one_le_pow₀ htR
  have hmul := mul_lt_mul_of_pos_right hlarge (by positivity : (0 : ℝ) < (t : ℝ) ^ 5)
  have hCm := mul_le_mul_of_nonneg_left ht5 hC
  have he : (t : ℝ) ^ 6 = t * (t : ℝ) ^ 5 := by ring
  rw [he] at hp
  nlinarith

lemma prime_relabel_cube_sidon_lowerDensity_zero {A : Set ℕ}
    (hA : PrimeRelabelInvariant A)
    (hs : IsSidon ((fun n : ℕ => n ^ 3) '' A)) : A.lowerDensity = 0 :=
  lowerDensity_zero_of_powerful_support (prime_relabel_cube_sidon_powerful hA hs)

#print axioms prime_relabel_cube_sidon_powerful
#print axioms powerful_eq_square_mul_cube
#print axioms lowerDensity_zero_of_powerful_support
#print axioms prime_relabel_cube_sidon_lowerDensity_zero

end Erdos1206
