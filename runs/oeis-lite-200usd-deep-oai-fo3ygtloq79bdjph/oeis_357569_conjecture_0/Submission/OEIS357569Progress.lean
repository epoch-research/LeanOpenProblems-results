import FormalConjectures.Util.ProblemImports
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Cast

open scoped BigOperators
open Finset Nat

lemma choose_add_eq_prod (n k : ℕ) :
    (((n + k).choose k : ℚ)) =
      ∏ i ∈ Finset.range k, (((n + (i + 1) : ℕ) : ℚ) / ((i + 1 : ℕ) : ℚ)) := by
  classical
  have hchoose_nat : (n + 1).ascFactorial k = k ! * (n + k).choose k := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.ascFactorial_eq_factorial_mul_choose' (n + 1) k)
  have hchoose_q : (((n + k).choose k : ℕ) : ℚ) = ((n + 1).ascFactorial k : ℚ) / (k ! : ℚ) := by
    have hfac : ((k ! : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero k)
    rw [eq_div_iff_mul_eq hfac]
    rw [← Nat.cast_mul, Nat.mul_comm, ← hchoose_nat]
  have hasc_prod : (((n + 1).ascFactorial k : ℕ) : ℚ) =
      ∏ i ∈ Finset.range k, (((n + 1 + i : ℕ) : ℚ)) := by
    exact_mod_cast (Nat.ascFactorial_eq_prod_range (n + 1) k)
  have hfac_prod : (((k ! : ℕ) : ℚ)) =
      ∏ i ∈ Finset.range k, (((i + 1 : ℕ) : ℚ)) := by
    exact_mod_cast (Nat.factorial_eq_prod_range_add_one k)
  rw [hchoose_q, hasc_prod, hfac_prod]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hn : n + 1 + i = n + (i + 1) := by omega
  simp [hn]

lemma choose_mul_eq_prod (q m : ℕ) :
    ((Nat.choose ((m+1)*q) q : ℚ)) =
      ∏ i ∈ Finset.range q, (((m*q + (i+1) : ℕ) : ℚ) / ((i+1 : ℕ) : ℚ)) := by
  have h := choose_add_eq_prod (m*q) q
  have harg : m * q + q = (m + 1) * q := by ring
  rw [← harg]
  exact h

lemma choose_mul_eq_prod_Icc (q m : ℕ) :
    ((Nat.choose ((m+1)*q) q : ℚ)) =
      ∏ i ∈ Finset.Icc 1 q, (((m*q + i : ℕ) : ℚ) / (i : ℚ)) := by
  rw [choose_mul_eq_prod]
  rw [← Nat.Ico_zero_eq_range]
  rw [Finset.prod_Ico_add' (fun i : ℕ => (((m*q + i : ℕ) : ℚ) / (i : ℚ))) 0 q 1]
  rw [zero_add, Finset.Ico_add_one_right_eq_Icc]

lemma divisible_part_product (p n m q : ℕ) (hp : p ≠ 0) (hq : q = p * n) :
    (∏ i ∈ Finset.Icc 1 n, (((m*n + i : ℕ) : ℚ) / (i : ℚ))) =
      ∏ i ∈ (Finset.Icc 1 q).filter (fun i => p ∣ i),
        (((m*q + i : ℕ) : ℚ) / (i : ℚ)) := by
  classical
  let Fq : ℕ → ℚ := fun i => (((m*q + i : ℕ) : ℚ) / (i : ℚ))
  let Fn : ℕ → ℚ := fun i => (((m*n + i : ℕ) : ℚ) / (i : ℚ))
  refine Finset.prod_bij (fun i _ => p * i) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_Icc]
    rw [Finset.mem_Icc] at hi
    rcases hi with ⟨h1, h2⟩
    constructor
    · constructor
      · exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.pos_of_ne_zero hp) (Nat.succ_le_iff.mp h1))
      · rw [hq]
        exact Nat.mul_le_mul_left p h2
    · exact ⟨i, rfl⟩
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) hab
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    rcases hb with ⟨⟨hb1, hb2⟩, ⟨a, ha⟩⟩
    refine ⟨a, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      constructor
      · by_contra hzero
        have : a = 0 := Nat.eq_zero_of_not_pos (by simpa [Nat.succ_le_iff] using hzero)
        subst a
        simp at ha
        omega
      · rw [hq] at hb2
        rw [ha] at hb2
        exact Nat.le_of_mul_le_mul_left hb2 (Nat.pos_of_ne_zero hp)
    · exact ha.symm
  · intro i hi
    dsimp [Fn, Fq]
    rw [hq]
    have hpq : ((p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hp
    have hnum : ((m * (p * n) + p * i : ℕ) : ℚ) = (p : ℚ) * ((m * n + i : ℕ) : ℚ) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    have hden : ((p * i : ℕ) : ℚ) = (p : ℚ) * (i : ℚ) := by norm_num [Nat.cast_mul]
    rw [hnum, hden]
    field_simp [hpq]

lemma binomial_ratio_product (p n m q : ℕ) (hp : p ≠ 0) (hn : n ≠ 0) (hq : q = p * n) :
    ((Nat.choose ((m+1)*q) q : ℚ) / (Nat.choose ((m+1)*n) n : ℚ)) =
      ∏ i ∈ (Finset.Icc 1 q).filter (fun i => ¬ p ∣ i),
        (((m*q + i : ℕ) : ℚ) / (i : ℚ)) := by
  classical
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let F : ℕ → ℚ := fun i => (((m*q + i : ℕ) : ℚ) / (i : ℚ))
  have hbig : ((Nat.choose ((m+1)*q) q : ℚ)) = ∏ i ∈ Finset.Icc 1 q, F i := by
    simpa [F] using choose_mul_eq_prod_Icc q m
  have hsmall_choose : ((Nat.choose ((m+1)*n) n : ℚ)) =
      ∏ i ∈ Finset.Icc 1 n, (((m*n + i : ℕ) : ℚ) / (i : ℚ)) := by
    simpa using choose_mul_eq_prod_Icc n m
  have hdiv : ((Nat.choose ((m+1)*n) n : ℚ)) =
      ∏ i ∈ (Finset.Icc 1 q).filter (fun i => p ∣ i), F i := by
    rw [hsmall_choose]
    simpa [F] using divisible_part_product p n m q hp hq
  have hsplit :
      (∏ i ∈ (Finset.Icc 1 q).filter (fun i => p ∣ i), F i) *
        (∏ i ∈ (Finset.Icc 1 q).filter (fun i => ¬ p ∣ i), F i) =
          ∏ i ∈ Finset.Icc 1 q, F i := by
    simpa using (Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 q) (fun i => p ∣ i) F)
  have hden_ne : ((Nat.choose ((m+1)*n) n : ℚ)) ≠ 0 := by
    exact_mod_cast (Nat.choose_ne_zero (by nlinarith [hnpos, Nat.mul_le_mul_right n (Nat.le_add_left m 1)] : n ≤ (m + 1) * n))
  have hdiv_ne : (∏ i ∈ (Finset.Icc 1 q).filter (fun i => p ∣ i), F i) ≠ 0 := by
    simpa [hdiv] using hden_ne
  have hsplit' : ∏ i ∈ Finset.Icc 1 q, F i =
      (∏ i ∈ (Finset.Icc 1 q).filter (fun i => ¬ p ∣ i), F i) *
        (∏ i ∈ (Finset.Icc 1 q).filter (fun i => p ∣ i), F i) := by
    rw [mul_comm]
    exact hsplit.symm
  rw [hbig, hdiv]
  exact (div_eq_of_eq_mul hdiv_ne hsplit')



lemma binomial_ratio_product_clear_denoms_nat (p n m q : ℕ)
    (hp : p ≠ 0) (hn : n ≠ 0) (hq : q = p * n) :
    Nat.choose ((m+1)*q) q *
        (∏ i ∈ (Finset.Icc 1 q).filter (fun i => ¬ p ∣ i), i)
      = Nat.choose ((m+1)*n) n *
        (∏ i ∈ (Finset.Icc 1 q).filter (fun i => ¬ p ∣ i), (m*q + i)) := by
  classical
  let S := (Finset.Icc 1 q).filter (fun i => ¬ p ∣ i)
  let A := Nat.choose ((m+1)*q) q
  let B := Nat.choose ((m+1)*n) n
  let C := ∏ i ∈ S, (m*q + i)
  let D := ∏ i ∈ S, i
  have hrat := binomial_ratio_product p n m q hp hn hq
  have hprod :
      (∏ i ∈ S, ((((m*q + i : ℕ) : ℚ) / (i : ℚ))))
        = ((C : ℕ) : ℚ) / ((D : ℕ) : ℚ) := by
    dsimp [C, D]
    rw [Finset.prod_div_distrib]
    simp [S]
  have hrat' : ((A : ℕ) : ℚ) / ((B : ℕ) : ℚ) = ((C : ℕ) : ℚ) / ((D : ℕ) : ℚ) := by
    dsimp [A, B]
    rw [hrat]
    exact hprod
  have hB_ne : ((B : ℕ) : ℚ) ≠ 0 := by
    dsimp [B]
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    exact_mod_cast (Nat.choose_ne_zero (by
      nlinarith [hnpos, Nat.mul_le_mul_right n (Nat.le_add_left m 1)] :
        n ≤ (m + 1) * n))
  have hD_pos : 0 < D := by
    dsimp [D]
    refine Finset.prod_pos ?_
    intro i hi
    have hiIcc : i ∈ Finset.Icc 1 q := (Finset.mem_filter.mp hi).1
    have : 1 ≤ i := (Finset.mem_Icc.mp hiIcc).1
    exact Nat.succ_le_iff.mp this
  have hD_ne_Q : ((D : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD_pos)
  have hmainQ : ((A : ℕ) : ℚ) * ((D : ℕ) : ℚ) = ((B : ℕ) : ℚ) * ((C : ℕ) : ℚ) := by
    rw [div_eq_div_iff hB_ne hD_ne_Q] at hrat'
    simpa [mul_comm, mul_left_comm, mul_assoc] using hrat'
  have hnat : A * D = B * C := by exact_mod_cast hmainQ
  simpa [A, B, C, D, S, mul_comm, mul_left_comm, mul_assoc] using hnat

lemma zmod_prod_nat_inv_eq_inv_prod {N : ℕ} (s : Finset ℕ)
    (hcop : ∀ i ∈ s, Nat.Coprime i N) :
    (∏ i ∈ s, (i : ZMod N)) * (∏ i ∈ s, (i : ZMod N)⁻¹) = 1 := by
  classical
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one (by
    intro i hi
    exact ZMod.coe_mul_inv_eq_one i (hcop i hi))

lemma binomial_product_zmod (N p n m q : ℕ)
    (hp : p ≠ 0) (hn : n ≠ 0) (hq : q = p * n)
    (hcop : ∀ i ∈ (Finset.Icc 1 q).filter (fun i => ¬ p ∣ i), Nat.Coprime i N) :
    ((Nat.choose ((m+1)*q) q : ℕ) : ZMod N)
      = ((Nat.choose ((m+1)*n) n : ℕ) : ZMod N) *
          ∏ i ∈ (Finset.Icc 1 q).filter (fun i => ¬ p ∣ i),
            (((m*q + i : ℕ) : ZMod N) * ((i : ℕ) : ZMod N)⁻¹) := by
  classical
  let S := (Finset.Icc 1 q).filter (fun i => ¬ p ∣ i)
  let A := Nat.choose ((m+1)*q) q
  let B := Nat.choose ((m+1)*n) n
  let C := ∏ i ∈ S, (m*q + i)
  let D := ∏ i ∈ S, i
  have hnat := binomial_ratio_product_clear_denoms_nat p n m q hp hn hq
  have hnat' : A * D = B * C := by
    simpa [A, B, C, D, S, mul_comm, mul_left_comm, mul_assoc] using hnat
  have hcast : (A : ZMod N) * (D : ZMod N) = (B : ZMod N) * (C : ZMod N) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul]
    exact congrArg (fun x : ℕ => (x : ZMod N)) hnat'
  have hcopS : ∀ i ∈ S, Nat.Coprime i N := by
    intro i hi
    exact hcop i hi
  have hDinv : (D : ZMod N) * (∏ i ∈ S, ((i : ℕ) : ZMod N)⁻¹) = 1 := by
    dsimp [D]
    rw [Nat.cast_prod]
    exact zmod_prod_nat_inv_eq_inv_prod S hcopS
  have hA : (A : ZMod N) = (B : ZMod N) * (C : ZMod N) * (∏ i ∈ S, ((i : ℕ) : ZMod N)⁻¹) := by
    calc
      (A : ZMod N) = (A : ZMod N) * 1 := by rw [mul_one]
      _ = (A : ZMod N) * ((D : ZMod N) * (∏ i ∈ S, ((i : ℕ) : ZMod N)⁻¹)) := by rw [hDinv]
      _ = ((A : ZMod N) * (D : ZMod N)) * (∏ i ∈ S, ((i : ℕ) : ZMod N)⁻¹) := by ring
      _ = ((B : ZMod N) * (C : ZMod N)) * (∏ i ∈ S, ((i : ℕ) : ZMod N)⁻¹) := by rw [hcast]
      _ = (B : ZMod N) * (C : ZMod N) * (∏ i ∈ S, ((i : ℕ) : ZMod N)⁻¹) := by ring
  have hprod_rhs :
      (C : ZMod N) * (∏ i ∈ S, ((i : ℕ) : ZMod N)⁻¹)
        = ∏ i ∈ S, (((m*q + i : ℕ) : ZMod N) * ((i : ℕ) : ZMod N)⁻¹) := by
    dsimp [C]
    rw [Nat.cast_prod]
    rw [← Finset.prod_mul_distrib]
  dsimp [A, B, S] at hA ⊢
  rw [hA]
  calc
    ↑(((m + 1) * n).choose n) * ↑C * (∏ i ∈ Finset.Icc 1 q with ¬p ∣ i, (↑i)⁻¹ : ZMod N)
        = ↑(((m + 1) * n).choose n) * (↑C * (∏ i ∈ S, ((i : ℕ) : ZMod N)⁻¹)) := by
          simp [S, mul_assoc]
    _ = ↑(((m + 1) * n).choose n) *
          (∏ i ∈ S, (((m*q + i : ℕ) : ZMod N) * ((i : ℕ) : ZMod N)⁻¹)) := by
          rw [hprod_rhs]
    _ = ↑(((m + 1) * n).choose n) *
          ∏ i ∈ Finset.Icc 1 q with ¬p ∣ i,
            (((m*q + i : ℕ) : ZMod N) * ((i : ℕ) : ZMod N)⁻¹) := by
          simp [S]

/-- Specialization of `binomial_product_zmod` to one prime-power step, with the
exact modulus appearing in `oeis_357569_conjecture_0`.  This is the product
identity used to compare `choose ((m+1)*p^r) (p^r)` with the previous level after
removing the factors divisible by `p`. -/
lemma binomial_product_prime_power_step_zmod
    (p r m : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r) :
    ((Nat.choose ((m + 1) * (p ^ r)) (p ^ r) : ℕ) : ZMod (p ^ (3 * r + 3))) =
      ((Nat.choose ((m + 1) * (p ^ (r - 1))) (p ^ (r - 1)) : ℕ) : ZMod (p ^ (3 * r + 3))) *
        ∏ i ∈ (Finset.Icc 1 (p ^ r)).filter (fun i => ¬ p ∣ i),
          (((m * (p ^ r) + i : ℕ) : ZMod (p ^ (3 * r + 3))) *
            ((i : ℕ) : ZMod (p ^ (3 * r + 3)))⁻¹) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : p ≠ 0 := hp.ne_zero
  have hn0 : p ^ (r - 1) ≠ 0 := pow_ne_zero (r - 1) hp0
  have hq : p ^ r = p * p ^ (r - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hcop : ∀ i ∈ (Finset.Icc 1 (p ^ r)).filter (fun i => ¬ p ∣ i),
      Nat.Coprime i (p ^ (3 * r + 3)) := by
    intro i hi
    have hnot : ¬ p ∣ i := (Finset.mem_filter.mp hi).2
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr hnot
  simpa using
    (binomial_product_zmod (N := p ^ (3 * r + 3)) (p := p) (n := p ^ (r - 1))
      (m := m) (q := p ^ r) hp0 hn0 hq hcop)

/-- The `m = 1` instance: product formula for the central binomial coefficient
`choose (2*p^r) (p^r)` modulo the target modulus. -/
lemma choose_two_prime_power_step_product_zmod
    (p r : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r) :
    ((Nat.choose (2 * (p ^ r)) (p ^ r) : ℕ) : ZMod (p ^ (3 * r + 3))) =
      ((Nat.choose (2 * (p ^ (r - 1))) (p ^ (r - 1)) : ℕ) : ZMod (p ^ (3 * r + 3))) *
        ∏ i ∈ (Finset.Icc 1 (p ^ r)).filter (fun i => ¬ p ∣ i),
          ((((p ^ r) + i : ℕ) : ZMod (p ^ (3 * r + 3))) *
            ((i : ℕ) : ZMod (p ^ (3 * r + 3)))⁻¹) := by
  simpa [one_add_one_eq_two, two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using (binomial_product_prime_power_step_zmod (p := p) (r := r) (m := 1) hp hr)

/-- The `m = 2` instance: product formula for `choose (3*p^r) (p^r)` modulo
the target modulus. -/
lemma choose_three_prime_power_step_product_zmod
    (p r : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r) :
    ((Nat.choose (3 * (p ^ r)) (p ^ r) : ℕ) : ZMod (p ^ (3 * r + 3))) =
      ((Nat.choose (3 * (p ^ (r - 1))) (p ^ (r - 1)) : ℕ) : ZMod (p ^ (3 * r + 3))) *
        ∏ i ∈ (Finset.Icc 1 (p ^ r)).filter (fun i => ¬ p ∣ i),
          (((2 * (p ^ r) + i : ℕ) : ZMod (p ^ (3 * r + 3))) *
            ((i : ℕ) : ZMod (p ^ (3 * r + 3)))⁻¹) := by
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.succ_eq_add_one]
    using (binomial_product_prime_power_step_zmod (p := p) (r := r) (m := 2) hp hr)
