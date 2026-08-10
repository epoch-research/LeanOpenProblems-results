import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

-- Copied definitions and lemmas from Spec.lean to make Sandbox self-contained

def A_seq : ℕ → ℤ
  | 0 => 0
  | k + 1 => (k.factorial : ℤ) + (k + 1 : ℤ) * A_seq k

def A_sum (k : ℕ) : ℤ :=
  ∑ j ∈ range k, (((k.factorial / (j + 1) : ℕ) : ℤ))

lemma A_seq_eq_A_sum (k : ℕ) :
    A_seq k = A_sum k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [A_seq, ih]
    have h_sum_succ : A_sum (k + 1) = ∑ j ∈ range k, (((k + 1).factorial / (j + 1) : ℕ) : ℤ) + (((k + 1).factorial / (k + 1) : ℕ) : ℤ) := by
      exact sum_range_succ (fun j => (((k + 1).factorial / (j + 1) : ℕ) : ℤ)) k
    rw [h_sum_succ]
    have h_last : (((k + 1).factorial / (k + 1) : ℕ) : ℤ) = (k.factorial : ℤ) := by
      have h_div : (k + 1).factorial / (k + 1) = k.factorial := by
        rw [factorial_succ]
        exact Nat.mul_div_cancel_left _ (by omega)
      rw [h_div]
    rw [h_last]
    have h_eq : (k + 1 : ℤ) * A_sum k = ∑ j ∈ range k, (((k + 1).factorial / (j + 1) : ℕ) : ℤ) := by
      rw [A_sum, mul_sum]
      apply sum_congr rfl
      intro x hx
      have hx_lt : x < k := by rwa [mem_range] at hx
      have h_dvd : x + 1 ∣ k.factorial := Nat.dvd_factorial (by omega) (by omega)
      have h_div_assoc : (k + 1).factorial / (x + 1) = (k + 1) * (k.factorial / (x + 1)) := by
        rw [factorial_succ]
        exact Nat.mul_div_assoc _ h_dvd
      rw [h_div_assoc]
      push_cast
      ring
    rw [h_eq, add_comm]

lemma nat_div_cast_zmod (p : ℕ) [Fact p.Prime] (a b : ℕ) (h_dvd : b ∣ a) (hb : (b : ZMod p) ≠ 0) :
    ((a / b : ℕ) : ZMod p) = (a : ZMod p) / (b : ZMod p) := by
  have h_eq : a = b * (a / b) := (Nat.mul_div_cancel' h_dvd).symm
  have h_cast : (a : ZMod p) = (b : ZMod p) * ((a / b : ℕ) : ZMod p) := by
    have h_c : ((a : ℕ) : ZMod p) = ((b * (a / b) : ℕ) : ZMod p) := congr_arg (fun (x : ℕ) => (x : ZMod p)) h_eq
    push_cast at h_c
    exact h_c
  rw [h_cast, mul_div_cancel_left₀ _ hb]

lemma coprime_of_sum_eq_prime (p a b : ℕ) (hp : p.Prime) (hsum : a + b = p) (ha : a < p) (ha_pos : a > 0) :
    Nat.Coprime a b := by
  have h_gcd : Nat.gcd a b ∣ p := by
    have h1 : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
    have h2 : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
    have h3 : Nat.gcd a b ∣ a + b := dvd_add h1 h2
    rwa [hsum] at h3
  rcases hp.eq_one_or_self_of_dvd _ h_gcd with h_one | h_self
  · exact h_one
  · have h_le : Nat.gcd a b ≤ a := by
      rcases a with rfl | a
      · omega
      · exact Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
    omega

lemma product_dvd_factorial (p j : ℕ) (hp : p.Prime) (hj : j < p - 1) :
    (j + 1) * (p - 1 - j) ∣ (p - 1).factorial := by
  have h_sum : (j + 1) + (p - 1 - j) = p := by omega
  have h_lt1 : j + 1 < p := by omega
  have h_lt2 : p - 1 - j < p := by omega
  have h_cop : Nat.Coprime (j + 1) (p - 1 - j) := coprime_of_sum_eq_prime p (j + 1) (p - 1 - j) hp h_sum h_lt1 (by omega)
  have hdvd1 : j + 1 ∣ (p - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
  have hdvd2 : p - 1 - j ∣ (p - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h_cop hdvd1 hdvd2

lemma two_ne_zero_zmod (p : ℕ) [Fact p.Prime] (hp5 : p ≥ 5) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hp : p.Prime := Fact.out
  have h_div : (p : ℤ) ∣ (2 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) p).mp (by exact_mod_cast h)
  have h_div_nat : p ∣ 2 := by exact_mod_cast h_div
  have h_le : p ≤ 2 := Nat.le_of_dvd (by decide) h_div_nat
  omega

def equiv_mul_two (p : ℕ) [Fact p.Prime] (hp5 : p ≥ 5) : ZMod p ≃ ZMod p where
  toFun x := 2 * x
  invFun x := (2 : ZMod p)⁻¹ * x
  left_inv x := by
    dsimp
    have h2 := two_ne_zero_zmod p hp5
    rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  right_inv x := by
    dsimp
    have h2 := two_ne_zero_zmod p hp5
    rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul]

lemma sum_inv_square_zero (p : ℕ) [Fact p.Prime] (hp5 : p ≥ 5) :
    ∑ x : ZMod p, (x⁻¹ ^ 2) = 0 := by
  let h_equiv := equiv_mul_two p hp5
  have h_sum_rew : ∑ x : ZMod p, ((2 * x)⁻¹ ^ 2) = ∑ x : ZMod p, (x⁻¹ ^ 2) :=
    Fintype.sum_equiv h_equiv (fun x => (2 * x)⁻¹ ^ 2) (fun x => x⁻¹ ^ 2) (by intro x; dsimp [h_equiv, equiv_mul_two])
  have h_term : ∀ x : ZMod p, ((2 * x)⁻¹ ^ 2) = (2 : ZMod p)⁻¹ ^ 2 * (x⁻¹ ^ 2) := by
    intro x
    rw [mul_inv, mul_pow]
  have h_sum_mul : ∑ x : ZMod p, ((2 * x)⁻¹ ^ 2) = (2 : ZMod p)⁻¹ ^ 2 * ∑ x : ZMod p, (x⁻¹ ^ 2) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x _
    exact h_term x
  have h_alg_eq : (1 - (2 : ZMod p)⁻¹ ^ 2) * ∑ x : ZMod p, (x⁻¹ ^ 2) = 0 := by
    calc
      (1 - (2 : ZMod p)⁻¹ ^ 2) * ∑ x : ZMod p, (x⁻¹ ^ 2) = ∑ x : ZMod p, (x⁻¹ ^ 2) - (2 : ZMod p)⁻¹ ^ 2 * ∑ x : ZMod p, (x⁻¹ ^ 2) := by ring
      _ = ∑ x : ZMod p, (x⁻¹ ^ 2) - ∑ x : ZMod p, ((2 * x)⁻¹ ^ 2) := by rw [h_sum_mul]
      _ = 0 := by rw [h_sum_rew, sub_self]
  have h_ne : 1 - (2 : ZMod p)⁻¹ ^ 2 ≠ 0 := by
    intro h_zero
    have h_eq1 : (1 : ZMod p) = (2 : ZMod p)⁻¹ ^ 2 := by
      exact sub_eq_zero.mp h_zero
    have h_eq2 : (2 : ZMod p)⁻¹ ^ 2 = (4 : ZMod p)⁻¹ := by
      have h_rew : (2 : ZMod p) ^ 2 = 4 := by ring
      rw [inv_pow, h_rew]
    rw [h_eq2] at h_eq1
    have h_eq3 : (1 : ZMod p) = 4 := by
      have h_inv := congr_arg (fun x => x⁻¹) h_eq1
      simp only [inv_one, inv_inv] at h_inv
      exact h_inv
    have h_eq4 : (3 : ZMod p) = 0 := by
      calc
        (3 : ZMod p) = 4 - 1 := by ring
        _ = 1 - 1 := by rw [← h_eq3]
        _ = 0 := by ring
    have h_div : (p : ℤ) ∣ 3 := (ZMod.intCast_zmod_eq_zero_iff_dvd 3 p).mp (by exact_mod_cast h_eq4)
    have h_div_nat : p ∣ 3 := by exact_mod_cast h_div
    have h_le : p ≤ 3 := Nat.le_of_dvd (by decide) h_div_nat
    omega
  rcases mul_eq_zero.mp h_alg_eq with h_one | h_two
  · contradiction
  · exact h_two

lemma sum_zmod_range (p : ℕ) [Fact p.Prime] (g_func : ZMod p → ZMod p) :
    ∑ x : ZMod p, g_func x = ∑ i ∈ range p, g_func i := by
  rcases p with _ | n
  · have hp : Nat.Prime 0 := Fact.out
    exfalso
    exact Nat.not_prime_zero hp
  · let h_equiv := (ZMod.finEquiv (n + 1)).toEquiv
    have h_sum := Fintype.sum_equiv h_equiv (fun (i : Fin (n + 1)) => g_func (h_equiv i)) g_func (fun (i : Fin (n + 1)) => rfl)
    rw [h_sum.symm]
    have h_def : (fun (i : Fin (n + 1)) => g_func (h_equiv i)) = (fun (i : Fin (n + 1)) => g_func i) := rfl
    rw [h_def]
    have h_val : (fun i : Fin (n + 1) => g_func i) = (fun i : Fin (n + 1) => g_func ((i : ℕ) : ZMod (n + 1))) := by
      ext i
      congr 1
      apply Fin.ext
      change i.val = i.val % (n + 1)
      exact (Nat.mod_eq_of_lt i.isLt).symm
    rw [h_val]
    exact Fin.sum_univ_eq_sum_range (n := n + 1) (fun (i : ℕ) => g_func (i : ZMod (n + 1)))

lemma fact_div_cast_zmod (p : ℕ) [Fact p.Prime] (i : ℕ) (hi : i < p - 1) :
    (((p - 1).factorial / (i + 1) : ℕ) : ZMod p) = - (1 + i : ZMod p)⁻¹ := by
  have hdvd : i + 1 ∣ (p - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
  have h_ne : ((i + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro hdvd2
    have h_div : (p : ℤ) ∣ (i + 1 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (i + 1 : ℤ) p).mp (by exact_mod_cast hdvd2)
    have h_div_nat : p ∣ i + 1 := by exact_mod_cast h_div
    have h_lt : i + 1 < p := by omega
    have h_le := Nat.le_of_dvd (by omega) h_div_nat
    omega
  have h_rew : ((i + 1 : ℕ) : ZMod p) = ((1 + i : ℕ) : ZMod p) := by
    congr 1
    omega
  rw [nat_div_cast_zmod p (p - 1).factorial (i + 1) hdvd h_ne]
  have h_wilson := ZMod.wilsons_lemma p
  rw [h_wilson, h_rew]
  push_cast
  ring

def S2_sum (k : ℕ) : ℤ := ∑ i ∈ range k, (((k.factorial / (i + 1) : ℕ) : ℤ))^2

lemma S2_sum_cast_zmod (p : ℕ) [Fact p.Prime] (hp5 : p ≥ 5) :
    ((S2_sum (p - 1) : ℤ) : ZMod p) = ∑ i ∈ range (p - 1), ((1 + i : ZMod p)⁻¹ ^ 2) := by
  unfold S2_sum
  have h_hom : ((∑ i ∈ range (p - 1), (((p - 1).factorial / (i + 1) : ℕ) : ℤ)^2 : ℤ) : ZMod p) =
               (Int.castRingHom (ZMod p)) (∑ i ∈ range (p - 1), (((p - 1).factorial / (i + 1) : ℕ) : ℤ)^2) := rfl
  rw [h_hom, map_sum]
  apply sum_congr rfl
  intro i hi
  have hi_lt : i < p - 1 := by rwa [mem_range] at hi
  have h_fact := fact_div_cast_zmod p i hi_lt
  have h_goal : (Int.castRingHom (ZMod p)) ((((p - 1).factorial / (i + 1) : ℕ) : ℤ) ^ 2) =
                ((((p - 1).factorial / (i + 1) : ℕ) : ZMod p) ^ 2) := by
    rw [map_pow]
    simp only [Int.coe_castRingHom]
    norm_cast
  rw [h_goal, h_fact]
  ring

lemma hS2_proof (p : ℕ) [Fact p.Prime] (hp5 : p ≥ 5) :
    (p : ℤ) ∣ S2_sum (p - 1) := by
  rcases p with _ | n
  · have hp : Nat.Prime 0 := Fact.out
    exfalso
    exact Nat.not_prime_zero hp
  · have h_sum_zero := sum_inv_square_zero (n + 1) hp5
    have h_range := sum_zmod_range (n + 1) (fun x => x⁻¹ ^ 2)
    have h_range2 : ∑ i ∈ range (n + 1), (i : ZMod (n + 1))⁻¹ ^ 2 = 0 := by
      trans ∑ x : ZMod (n + 1), x⁻¹ ^ 2
      · exact h_range.symm
      · exact h_sum_zero
    rw [sum_range_succ'] at h_range2
    have h_zero : ((0 : ℕ) : ZMod (n + 1))⁻¹ ^ 2 = 0 := by simp
    rw [h_zero, add_zero] at h_range2
    -- Now we have ∑ i ∈ range n, ((i + 1 : ZMod (n + 1))⁻¹ ^ 2) = 0
    have h_congr : ∑ i ∈ range n, ((i + 1 : ZMod (n + 1))⁻¹ ^ 2) = ∑ i ∈ range n, ((1 + i : ZMod (n + 1))⁻¹ ^ 2) := by
      apply sum_congr rfl
      intro i _
      congr 1
      ring
    push_cast at h_range2
    rw [h_congr] at h_range2
    have h_cast := S2_sum_cast_zmod (n + 1) hp5
    have h_sub_one : n + 1 - 1 = n := by omega
    rw [h_sub_one] at h_cast
    rw [h_range2] at h_cast
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (S2_sum n) (n + 1)).mp h_cast

def S_prime (p : ℕ) : ℤ := ∑ j ∈ range (p - 1), (((p - 1).factorial / ((j + 1) * (p - 1 - j)) : ℕ) : ℤ)

lemma S_prime_cast_zmod (p : ℕ) [Fact p.Prime] (hp5 : p ≥ 5) :
    ((S_prime p : ℤ) : ZMod p) = ∑ j ∈ range (p - 1), ((1 + j : ZMod p)⁻¹ ^ 2) := by
  unfold S_prime
  have h_hom : ((∑ j ∈ range (p - 1), (((p - 1).factorial / ((j + 1) * (p - 1 - j)) : ℕ) : ℤ) : ℤ) : ZMod p) =
               (Int.castRingHom (ZMod p)) (∑ j ∈ range (p - 1), (((p - 1).factorial / ((j + 1) * (p - 1 - j)) : ℕ) : ℤ)) := rfl
  rw [h_hom, map_sum]
  apply sum_congr rfl
  intro j hj
  have hj_lt : j < p - 1 := by rwa [mem_range] at hj
  have hdvd := product_dvd_factorial p j Fact.out hj_lt
  have h_ne : (((j + 1) * (p - 1 - j) : ℕ) : ZMod p) ≠ 0 := by
    intro h_zero
    have h_div : (p : ℤ) ∣ (((j + 1) * (p - 1 - j) : ℕ) : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (((j + 1) * (p - 1 - j) : ℕ) : ℤ) p).mp (by exact_mod_cast h_zero)
    have h_div_nat : p ∣ (j + 1) * (p - 1 - j) := by exact_mod_cast h_div
    rcases (Nat.Prime.dvd_mul (Fact.out : Nat.Prime p)).mp h_div_nat with h1 | h2
    · have h_lt : j + 1 < p := by omega
      have h_le := Nat.le_of_dvd (by omega) h1
      omega
    · have h_lt : p - 1 - j < p := by omega
      have h_le := Nat.le_of_dvd (by omega) h2
      omega
  have h_goal : (Int.castRingHom (ZMod p)) ((((p - 1).factorial / ((j + 1) * (p - 1 - j)) : ℕ) : ℤ)) =
                ((((p - 1).factorial / ((j + 1) * (p - 1 - j)) : ℕ) : ZMod p)) := by
    simp only [Int.coe_castRingHom]
    norm_cast
  rw [h_goal]
  rw [nat_div_cast_zmod p (p - 1).factorial ((j + 1) * (p - 1 - j)) hdvd h_ne]
  have h_wilson := ZMod.wilsons_lemma p
  rw [h_wilson]
  have h_sub_eq : (((p - 1 - j : ℕ) : ZMod p)) = - (1 + j : ZMod p) := by
    have hp_zero : (p : ZMod p) = 0 := by exact CharP.cast_eq_zero (ZMod p) p
    have h_omega : p - 1 - j = p - (1 + j) := by omega
    have h_le : 1 + j ≤ p := by omega
    rw [h_omega, Nat.cast_sub h_le]
    push_cast
    rw [hp_zero, zero_sub]
  push_cast
  rw [h_sub_eq]
  have h_mul_ne : (1 + j : ZMod p) ≠ 0 := by
    intro hj0
    have h_div : (p : ℤ) ∣ (1 + j : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (1 + j : ℤ) p).mp (by exact_mod_cast hj0)
    have h_div_nat : p ∣ 1 + j := by exact_mod_cast h_div
    have h_lt : 1 + j < p := by omega
    have h_le := Nat.le_of_dvd (by omega) h_div_nat
    omega
  have h_mul_neg : (j + 1 : ZMod p) * - (1 + j : ZMod p) = - (1 + j : ZMod p)^2 := by
    have h_eq : (j + 1 : ZMod p) = (1 + j : ZMod p) := by ring
    rw [h_eq]
    ring
  rw [h_mul_neg]
  have h_div_neg : -1 / (- (1 + j : ZMod p)^2) = (1 + j : ZMod p)⁻¹ ^ 2 := by
    rw [neg_div_neg_eq]
    have h_inv_eq : (1 + j : ZMod p)^2 = ((1 + j : ZMod p)^2) := rfl
    rw [one_div, inv_pow]
  exact h_div_neg

lemma S_prime_div_p (p : ℕ) [Fact p.Prime] (hp5 : p ≥ 5) :
    (p : ℤ) ∣ S_prime p := by
  rcases p with _ | n
  · have hp : Nat.Prime 0 := Fact.out
    exfalso
    exact Nat.not_prime_zero hp
  · have h_sum_zero := sum_inv_square_zero (n + 1) hp5
    have h_range := sum_zmod_range (n + 1) (fun x => x⁻¹ ^ 2)
    have h_range2 : ∑ i ∈ range (n + 1), (i : ZMod (n + 1))⁻¹ ^ 2 = 0 := by
      trans ∑ x : ZMod (n + 1), x⁻¹ ^ 2
      · exact h_range.symm
      · exact h_sum_zero
    rw [sum_range_succ'] at h_range2
    have h_zero : ((0 : ℕ) : ZMod (n + 1))⁻¹ ^ 2 = 0 := by simp
    rw [h_zero, add_zero] at h_range2
    have h_congr : ∑ i ∈ range n, ((i + 1 : ZMod (n + 1))⁻¹ ^ 2) = ∑ i ∈ range n, ((1 + i : ZMod (n + 1))⁻¹ ^ 2) := by
      apply sum_congr rfl
      intro i _
      congr 1
      ring
    push_cast at h_range2
    rw [h_congr] at h_range2
    have h_cast := S_prime_cast_zmod (n + 1) hp5
    have h_sub_one : n + 1 - 1 = n := by omega
    rw [h_sub_one] at h_cast
    rw [h_range2] at h_cast
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (S_prime (n + 1)) (n + 1)).mp h_cast

lemma sum_factorial_div_reflect (p : ℕ) (hp3 : p ≥ 3) :
    ∑ j ∈ range (p - 1), (((p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) =
    ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) : ℕ) : ℤ) := by
  have h_ref := Finset.sum_range_reflect (fun j => (((p - 1).factorial / (j + 1) : ℕ) : ℤ)) (p - 1)
  have h_congr : ∑ i ∈ range (p - 1), (((p - 1).factorial / (p - 1 - 1 - i + 1) : ℕ) : ℤ) =
                 ∑ i ∈ range (p - 1), (((p - 1).factorial / (p - 1 - i) : ℕ) : ℤ) := by
    apply sum_congr rfl
    intro i hi
    have hi_lt : i < p - 1 := by rwa [mem_range] at hi
    congr 2
    omega
  rw [h_congr] at h_ref
  exact h_ref

lemma div_add_div_eq_mul_div (F A B p : ℕ) (h_dvd : A * B ∣ F) (h_sum : A + B = p) (hA : A > 0) (hB : B > 0) :
    F / A + F / B = p * (F / (A * B)) := by
  rcases h_dvd with ⟨K, rfl⟩
  have h_div1 : (A * B * K) / A = B * K := by
    have h_assoc : A * B * K = A * (B * K) := by ring
    rw [h_assoc]
    exact Nat.mul_div_cancel_left (B * K) hA
  have h_div2 : (A * B * K) / B = A * K := by
    have h_assoc : A * B * K = B * (A * K) := by ring
    rw [h_assoc]
    exact Nat.mul_div_cancel_left (A * K) hB
  have h_div3 : (A * B * K) / (A * B) = K := by
    exact Nat.mul_div_cancel_left K (Nat.mul_pos hA hB)
  rw [h_div1, h_div2, h_div3]
  rw [← add_mul, ← h_sum]
  ring

lemma A_seq_div_p2 (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    (p : ℤ)^2 ∣ A_seq (p - 1) := by
  rw [A_seq_eq_A_sum]
  have h_reflect := sum_factorial_div_reflect p (by omega)
  have h_add : 2 * A_sum (p - 1) = ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) + (p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) := by
    have h_two : 2 * A_sum (p - 1) = A_sum (p - 1) + A_sum (p - 1) := by ring
    rw [h_two]
    have h_sum1 : A_sum (p - 1) = ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) : ℕ) : ℤ) := rfl
    have h_sum2 : A_sum (p - 1) = ∑ j ∈ range (p - 1), (((p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) := by
      rw [A_sum, sum_factorial_div_reflect p (by omega)]
    nth_rw 1 [h_sum1]
    nth_rw 1 [h_sum2]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    push_cast
    rfl
  have h_rew_reflect : ∑ j ∈ range (p - 1), (((p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) =
                       ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) : ℕ) : ℤ) := h_reflect
  have h_sum_add : ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) : ℕ) : ℤ) + ∑ j ∈ range (p - 1), (((p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) =
                   2 * A_sum (p - 1) := by
    rw [h_rew_reflect, ← two_mul]
    rfl
  have h_dvd_sum : ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) + (p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) =
                   (p : ℤ) * S_prime p := by
    unfold S_prime
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    have hj_lt : j < p - 1 := by rwa [mem_range] at hj
    have hdvd := product_dvd_factorial p j hp hj_lt
    have h_sum : (j + 1) + (p - 1 - j) = p := by omega
    have h_div := div_add_div_eq_mul_div (p - 1).factorial (j + 1) (p - 1 - j) p hdvd h_sum (by omega) (by omega)
    push_cast [h_div]
    ring
  have h_mul_eq : 2 * A_sum (p - 1) = (p : ℤ) * S_prime p := h_add.trans h_dvd_sum
  -- So we have 2 * A_sum (p - 1) = p * S_prime p.
  -- And we know p ∣ S_prime p (since [Fact p.Prime] holds).
  have hp_fact : Fact p.Prime := ⟨hp⟩
  have h_div_S := S_prime_div_p p hp5
  rcases h_div_S with ⟨k, hk⟩
  have h_mul : 2 * A_sum (p - 1) = (p : ℤ)^2 * k := by
    calc
      2 * A_sum (p - 1) = (p : ℤ) * S_prime p := h_mul_eq
      _ = (p : ℤ) * ((p : ℤ) * k) := by rw [hk]
      _ = (p : ℤ)^2 * k := by ring
  -- So (p : ℤ)^2 ∣ 2 * A_sum (p - 1)
  have h_div_2A : (p : ℤ)^2 ∣ 2 * A_sum (p - 1) := by
    rw [h_mul]
    exact dvd_mul_right _ _
  -- Since p ≥ 5, p is not 2, so (p^2) is coprime to 2.
  -- Thus (p : ℤ)^2 ∣ A_sum (p - 1).
  have h_pow_cast : (p : ℤ)^2 = ((p^2 : ℕ) : ℤ) := by push_cast; rfl
  rw [h_pow_cast] at h_div_2A
  rw [Int.natCast_dvd] at h_div_2A
  have h_abs : (2 * A_sum (p - 1)).natAbs = 2 * (A_sum (p - 1)).natAbs := by
    rw [Int.natAbs_mul]
    rfl
  rw [h_abs] at h_div_2A
  rw [mul_comm] at h_div_2A
  have h_cop : Nat.Coprime (p^2) 2 := by
    have h_cop_p : Nat.Coprime p 2 := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hdvd
      have h_le := Nat.le_of_dvd (by omega) hdvd
      omega
    exact Nat.Coprime.pow_left 2 h_cop_p
  have h_div_abs : p^2 ∣ (A_sum (p - 1)).natAbs := (Nat.Coprime.dvd_mul_right h_cop).mp h_div_2A
  rwa [← Int.natCast_dvd] at h_div_abs

