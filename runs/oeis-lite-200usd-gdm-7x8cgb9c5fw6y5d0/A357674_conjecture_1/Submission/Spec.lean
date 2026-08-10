import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

/--
A357674: $a(n) = \left( \sum_{k = 0}^{2n} \binom{n+k-1}{k} \right)^4 \cdot \left( \sum_{k = 0}^{2n} \binom{n+k-1}{k}^2 \right)^3$.

The terms $\sum_{k = 0}^{2n} \binom{n+k-1}{k}$ and $\sum_{k = 0}^{2n} \binom{n+k-1}{k}^2$ are the summations required.
For $n \ge 1$, the first sum is equal to $\binom{3n}{n}$. We keep the summation structure for fidelity to the OEIS definition, using Finset.sum and Nat.choose.
-/
def A357674 (n : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ 4 * S2 ^ 3

/--
The general sequence $u(n, m)$ from conjecture 3.
$u(n, m) = \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k} \right)^{2m} \cdot \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k}^2 \right)^{m+1}$.
Note that `A357674 n = u_A357674 n 2`.
-/
def u_A357674 (n m : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (m * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (m * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ (2 * m) * S2 ^ (m + 1)



namespace List

def sum_prod_excl {R : Type*} [CommRing R] : List R → R
  | [] => 0
  | a :: L => L.prod + a * sum_prod_excl L

theorem prod_add_y_eq {R : Type*} [CommRing R] (y : R) (hy2 : y ^ 2 = 0) (L : List R) :
    (L.map (fun x ↦ y + x)).prod = L.prod + y * sum_prod_excl L := by
  induction L with
  | nil =>
    simp [sum_prod_excl]
  | cons a L ih =>
    simp [sum_prod_excl, ih]
    linear_combination (y + a) * (L.prod + y * sum_prod_excl L) - (L.prod * a + y * (L.prod + a * sum_prod_excl L)) + (sum_prod_excl L) * hy2


def sum_pairs {R : Type*} [CommRing R] : List R → R
  | [] => 0
  | a :: L => sum_pairs L + a * L.sum

lemma map_list_sum {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) (L : List A) :
    f L.sum = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp [ih]

lemma ringHom_sum_pairs {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (L : List A) :
    f (sum_pairs L) = sum_pairs (L.map f) := by
  induction L with
  | nil => simp [sum_pairs]
  | cons a L ih =>
    simp [sum_pairs, ih, map_list_sum]

theorem list_sum_sq_eq {R : Type*} [CommRing R] (L : List R) :
    L.sum ^ 2 = (L.map (fun x => x ^ 2)).sum + 2 * sum_pairs L := by
  induction L with
  | nil => simp [sum_pairs]
  | cons a L ih =>
    simp [sum_pairs]
    linear_combination ih

theorem prod_one_add_y_mul_eq3 {R : Type*} [CommRing R] (y : R) (hy3 : y ^ 3 = 0) (L : List R) :
    (L.map (fun x ↦ 1 + y * x)).prod = 1 + y * L.sum + y ^ 2 * sum_pairs L := by
  induction L with
  | nil => simp [sum_pairs]
  | cons a L ih =>
    simp [sum_pairs, ih]
    linear_combination (1 + y * a) * (1 + y * L.sum + y ^ 2 * sum_pairs L) -
                       (1 + y * (a + L.sum) + y ^ 2 * (sum_pairs L + a * L.sum)) +
                       (a * sum_pairs L) * hy3

end List

theorem S1_eq_choose (p : ℕ) (hp3 : p ≥ 3) :
    (∑ k ∈ range (2 * p + 1), (p + k - 1).choose k) = (3 * p).choose p := by
  have h1 : ∀ k ∈ range (2 * p + 1), (p + k - 1).choose k = (p + k - 1).choose (p - 1) := by
    intro k hk
    rw [← Nat.choose_symm]
    · congr 1; omega
    · omega
  rw [sum_congr rfl h1]
  rw [range_eq_Ico]
  have h2 : ∀ k ∈ Ico 0 (2 * p + 1), (p + k - 1).choose (p - 1) = ((p - 1) + k).choose (p - 1) := by
    intro k hk
    congr 1; omega
  rw [sum_congr rfl h2]
  have h3 : (∑ x ∈ Ico 0 (2 * p + 1), (p - 1 + x).choose (p - 1)) = (∑ x ∈ Ico 0 (2 * p + 1), (fun y ↦ y.choose (p - 1)) (p - 1 + x)) := rfl
  rw [h3]
  rw [sum_Ico_add (fun y ↦ y.choose (p - 1)) 0 (2 * p + 1) (p - 1)]
  have h4 : (∑ x ∈ Ico (0 + (p - 1)) (2 * p + 1 + (p - 1)), x.choose (p - 1)) = ∑ x ∈ Icc (p - 1) (3 * p - 1), x.choose (p - 1) := by
    congr 1
    ext x
    simp only [mem_Ico, mem_Icc]
    omega
  rw [h4]
  rw [sum_Icc_choose]
  congr 1 <;> omega

lemma dvd_choose_of_lt (p k : ℕ) (hp : p.Prime) (hk1 : k ≥ 1) (hk2 : k < p) : p ∣ (p + k - 1).choose k := by
  have h1 : (p + k - 1).choose k * (p + k - 1 + 1) = (p + k - 1 + 1).choose k * (p + k - 1 + 1 - k) := by
    rw [choose_mul_succ_eq]
  have h2 : p + k - 1 + 1 = p + k := by omega
  rw [h2] at h1
  have h3 : p + k - k = p := by omega
  rw [h3] at h1
  have h4 : p ∣ (p + k).choose k * p := dvd_mul_left _ _
  rw [← h1] at h4
  have hp_dvd := hp.dvd_or_dvd h4
  rcases hp_dvd with h_left | h_right
  · exact h_left
  · have h5 : p ∣ k := (Nat.dvd_add_right (dvd_refl p)).mp h_right
    have h6 := Nat.le_of_dvd hk1 h5
    omega


lemma S1_mod_p (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) : (3 * p).choose p ≡ 3 [MOD p] := by
  have h : (3 * p).choose p ≡ ((3 * p) % p).choose (p % p) * ((3 * p) / p).choose (p / p) [MOD p] := by
    have : Fact p.Prime := ⟨hp⟩
    exact Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have hp0 : p > 0 := by omega
  have h1 : (3 * p) % p = 0 := by
    rw [Nat.mul_comm 3 p]
    exact Nat.mul_mod_right p 3
  have h2 : p % p = 0 := Nat.mod_self p
  have h3 : (3 * p) / p = 3 := by
    rw [Nat.mul_comm 3 p]
    exact Nat.mul_div_cancel_left 3 hp0
  have h4 : p / p = 1 := Nat.div_self hp0
  rw [h1, h2, h3, h4] at h
  exact h

lemma choose_3p_p (p : ℕ) (hp3 : p ≥ 3) :
    (3 * p).choose p = 3 * (3 * p - 1).choose (p - 1) := by
  have h1 : (3 * p - 1 + 1) * (3 * p - 1).choose (p - 1) = (3 * p - 1 + 1).choose (p - 1 + 1) * (p - 1 + 1) := by
    rw [add_one_mul_choose_eq]
  have h2 : 3 * p - 1 + 1 = 3 * p := by omega
  have h3 : p - 1 + 1 = p := by omega
  rw [h2, h3] at h1
  have h4 : 3 * p * (3 * p - 1).choose (p - 1) = p * (3 * (3 * p - 1).choose (p - 1)) := by
    ring
  rw [h4] at h1
  have h5 : p * (3 * (3 * p - 1).choose (p - 1)) = p * (3 * p).choose p := by
    rw [h1, Nat.mul_comm]
  have hp0 : p > 0 := by omega
  exact Nat.eq_of_mul_eq_mul_left hp0 h5.symm

lemma choose_3p_minus_1_p_minus_1_mod_p (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    (3 * p - 1).choose (p - 1) ≡ 1 [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have h : (3 * p - 1).choose (p - 1) ≡
    ((3 * p - 1) % p).choose ((p - 1) % p) * ((3 * p - 1) / p).choose ((p - 1) / p) [MOD p] := by
    have : Fact p.Prime := ⟨hp⟩
    exact Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have h1 : (3 * p - 1) % p = p - 1 := by
    have h2 : 3 * p - 1 = (p - 1) + p * 2 := by omega
    rw [h2, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have h3 : (3 * p - 1) / p = 2 := by
    have h2 : 3 * p - 1 = (p - 1) + p * 2 := by omega
    rw [h2]
    rw [Nat.add_mul_div_left (p - 1) 2 (by omega)]
    have h4 : (p - 1) / p = 0 := Nat.div_eq_of_lt (by omega)
    rw [h4, Nat.zero_add]
  have h5 : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
  have h6 : (p - 1) / p = 0 := Nat.div_eq_of_lt (by omega)
  rw [h1, h3, h5, h6] at h
  have h7 : (p - 1).choose (p - 1) = 1 := Nat.choose_self (p - 1)
  have h8 : Nat.choose 2 0 = 1 := Nat.choose_zero_right 2
  rw [h7, h8] at h
  simp only [Nat.mul_one] at h
  exact h


lemma choose_2p_minus_1_p_minus_1_mod_p (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have h : (2 * p - 1).choose (p - 1) ≡
    ((2 * p - 1) % p).choose ((p - 1) % p) * ((2 * p - 1) / p).choose ((p - 1) / p) [MOD p] := by
    have : Fact p.Prime := ⟨hp⟩
    exact Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have h1 : (2 * p - 1) % p = p - 1 := by
    have h2 : 2 * p - 1 = (p - 1) + p * 1 := by omega
    rw [h2, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have h3 : (2 * p - 1) / p = 1 := by
    have h2 : 2 * p - 1 = (p - 1) + p * 1 := by omega
    rw [h2]
    rw [Nat.add_mul_div_left (p - 1) 1 (by omega)]
    have h4 : (p - 1) / p = 0 := Nat.div_eq_of_lt (by omega)
    rw [h4, Nat.zero_add]
  have h5 : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
  have h6 : (p - 1) / p = 0 := Nat.div_eq_of_lt (by omega)
  rw [h1, h3, h5, h6] at h
  have h7 : (p - 1).choose (p - 1) = 1 := Nat.choose_self (p - 1)
  have h8 : Nat.choose 1 0 = 1 := Nat.choose_zero_right 1
  rw [h7, h8] at h
  simp only [Nat.mul_one] at h
  exact h

lemma dvd_choose_of_gt_p (p j : ℕ) (hp : p.Prime) (hj1 : j ≥ 1) (hj2 : j < p) : p ∣ (2 * p + j - 1).choose (p + j) := by
  have h1 : (2 * p + j - 1).choose (p + j) * (2 * p + j - 1 + 1) = (2 * p + j - 1 + 1).choose (p + j) * (2 * p + j - 1 + 1 - (p + j)) := by
    rw [choose_mul_succ_eq]
  have h2 : 2 * p + j - 1 + 1 = 2 * p + j := by omega
  rw [h2] at h1
  have h3 : 2 * p + j - (p + j) = p := by omega
  rw [h3] at h1
  have h4 : p ∣ (2 * p + j).choose (p + j) * p := dvd_mul_left _ _
  rw [← h1] at h4
  have hp_dvd := hp.dvd_or_dvd h4
  rcases hp_dvd with h_left | h_right
  · exact h_left
  · have h5 : p ∣ 2 * p + j := h_right
    have hd : p ∣ 2 * p := ⟨2, by ring⟩
    have h6 : p ∣ j := (Nat.dvd_add_right hd).mp h5
    have h7 := Nat.le_of_dvd hj1 h6
    omega


theorem sum_inv_sq_zero (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    letI : NeZero p := ⟨by omega⟩
    (∑ k : ZMod p, (k ^ 2)⁻¹) = 0 := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h_dvd : p ∣ 2 := by
      exact (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    have h_le : p ≤ 2 := Nat.le_of_dvd (by decide) h_dvd
    omega
  let E : ZMod p ≃ ZMod p := Equiv.mulLeft₀ (2 : ZMod p) h2
  have h_comp : (∑ k : ZMod p, ((2 * k) ^ 2)⁻¹) = ∑ k : ZMod p, (k ^ 2)⁻¹ := by
    have hE := Equiv.sum_comp E (fun x => (x ^ 2)⁻¹)
    have h_rw : ∀ x, E x = 2 * x := fun x => rfl
    simp_rw [h_rw] at hE
    exact hE
  have h_mul : ∀ x : ZMod p, ((2 * x) ^ 2)⁻¹ = 4⁻¹ * (x ^ 2)⁻¹ := by
    intro x
    have : (2 * x) ^ 2 = 4 * x ^ 2 := by ring
    rw [this, mul_inv]
  have h_sum_rw : (∑ k : ZMod p, ((2 * k) ^ 2)⁻¹) = 4⁻¹ * ∑ k : ZMod p, (k ^ 2)⁻¹ := by
    rw [sum_congr rfl (fun x _ => h_mul x), ← mul_sum]
  have h_eq : (∑ k : ZMod p, (k ^ 2)⁻¹) = 4⁻¹ * ∑ k : ZMod p, (k ^ 2)⁻¹ := by
    calc (∑ k : ZMod p, (k ^ 2)⁻¹)
      _ = ∑ k : ZMod p, ((2 * k) ^ 2)⁻¹ := h_comp.symm
      _ = 4⁻¹ * ∑ k : ZMod p, (k ^ 2)⁻¹ := h_sum_rw
  have h_4 : (4 : ZMod p) * (∑ k : ZMod p, (k ^ 2)⁻¹) = (4 : ZMod p) * (4⁻¹ * ∑ k : ZMod p, (k ^ 2)⁻¹) :=
    congr_arg (fun x => (4 : ZMod p) * x) h_eq
  have h_4_inv : (4 : ZMod p) * 4⁻¹ = 1 := by
    apply mul_inv_cancel₀
    intro h4
    have h_dvd4 : p ∣ 4 := by
      exact (CharP.cast_eq_zero_iff (ZMod p) p 4).mp h4
    have h_le4 : p ≤ 4 := Nat.le_of_dvd (by decide) h_dvd4
    omega
  rw [← mul_assoc] at h_4
  rw [h_4_inv] at h_4
  rw [one_mul] at h_4
  have h_sub : (3 : ZMod p) * (∑ k : ZMod p, (k ^ 2)⁻¹) = 0 := by
    linear_combination h_4
  have h_3_ne_zero : (3 : ZMod p) ≠ 0 := by
    intro h3
    have h_dvd3 : p ∣ 3 := by
      exact (CharP.cast_eq_zero_iff (ZMod p) p 3).mp h3
    have h_le3 : p ≤ 3 := Nat.le_of_dvd (by decide) h_dvd3
    omega
  have h_goal : (3 : ZMod p)⁻¹ * ((3 : ZMod p) * (∑ k : ZMod p, (k ^ 2)⁻¹)) = 0 := by
    rw [h_sub, mul_zero]
  rw [← mul_assoc, inv_mul_cancel₀ h_3_ne_zero, one_mul] at h_goal
  exact h_goal

lemma algebraic_reduction (S1 S2 : ℕ) (p : ℕ) (hp3 : p ≥ 3)
    (h1 : (S1 : ℤ) ≡ 3 [ZMOD (p : ℤ)^3])
    (h2 : (S2 : ℤ) ≡ 3 [ZMOD (p : ℤ)^3])
    (h3 : 3 * (S2 : ℤ) + 4 * (S1 : ℤ) ≡ 21 [ZMOD (p : ℤ)^5]) :
    (S1 : ℤ)^4 * (S2 : ℤ)^3 ≡ 2187 [ZMOD (p : ℤ)^5] := by
  have hd1 : (p : ℤ)^3 ∣ (S1 : ℤ) - 3 := by
    have h1_symm : 3 ≡ (S1 : ℤ) [ZMOD (p : ℤ)^3] := Int.ModEq.symm h1
    exact Int.ModEq.dvd h1_symm
  have hd2 : (p : ℤ)^3 ∣ (S2 : ℤ) - 3 := by
    have h2_symm : 3 ≡ (S2 : ℤ) [ZMOD (p : ℤ)^3] := Int.ModEq.symm h2
    exact Int.ModEq.dvd h2_symm
  rcases hd1 with ⟨a, ha⟩
  rcases hd2 with ⟨b, hb⟩
  have hS1 : (S1 : ℤ) = 3 + a * (p : ℤ)^3 := by
    linear_combination ha
  have hS2 : (S2 : ℤ) = 3 + b * (p : ℤ)^3 := by
    linear_combination hb
  have hd3 : (p : ℤ)^5 ∣ 3 * (S2 : ℤ) + 4 * (S1 : ℤ) - 21 := by
    have h3_symm : 21 ≡ 3 * (S2 : ℤ) + 4 * (S1 : ℤ) [ZMOD (p : ℤ)^5] := Int.ModEq.symm h3
    exact Int.ModEq.dvd h3_symm
  rcases hd3 with ⟨c, hc⟩
  have h_linear : 3 * (S2 : ℤ) + 4 * (S1 : ℤ) - 21 = c * (p : ℤ)^5 := by
    linear_combination hc
  have h_diff_eq : (S1 : ℤ)^4 * (S2 : ℤ)^3 - 2187 = 729 * (3 * (S2 : ℤ) + 4 * (S1 : ℤ) - 21) + (p : ℤ)^5 * ((p : ℤ) * (
    a^4*b^3*(p : ℤ)^15 + 9*a^4*b^2*(p : ℤ)^12 + 27*a^4*b*(p : ℤ)^9 + 27*a^4*(p : ℤ)^6 + 12*a^3*b^3*(p : ℤ)^12 + 108*a^3*b^2*(p : ℤ)^9 +
    324*a^3*b*(p : ℤ)^6 + 324*a^3*(p : ℤ)^3 + 54*a^2*b^3*(p : ℤ)^9 + 486*a^2*b^2*(p : ℤ)^6 + 1458*a^2*b*(p : ℤ)^3 + 1458*a^2 +
    108*a*b^3*(p : ℤ)^6 + 972*a*b^2*(p : ℤ)^3 + 2916*a*b + 81*b^3*(p : ℤ)^3 + 729*b^2
  )) := by
    rw [hS1, hS2]
    ring
  have h_diff_div : (p : ℤ)^5 ∣ (S1 : ℤ)^4 * (S2 : ℤ)^3 - 2187 := by
    rw [h_diff_eq, h_linear]
    use 729 * c + (p : ℤ) * (
      a^4*b^3*(p : ℤ)^15 + 9*a^4*b^2*(p : ℤ)^12 + 27*a^4*b*(p : ℤ)^9 + 27*a^4*(p : ℤ)^6 + 12*a^3*b^3*(p : ℤ)^12 + 108*a^3*b^2*(p : ℤ)^9 +
      324*a^3*b*(p : ℤ)^6 + 324*a^3*(p : ℤ)^3 + 54*a^2*b^3*(p : ℤ)^9 + 486*a^2*b^2*(p : ℤ)^6 + 1458*a^2*b*(p : ℤ)^3 + 1458*a^2 +
      108*a*b^3*(p : ℤ)^6 + 972*a*b^2*(p : ℤ)^3 + 2916*a*b + 81*b^3*(p : ℤ)^3 + 729*b^2
    )
    ring
  have h_goal_symm : 2187 ≡ (S1 : ℤ)^4 * (S2 : ℤ)^3 [ZMOD (p : ℤ)^5] := Int.modEq_of_dvd h_diff_div
  exact Int.ModEq.symm h_goal_symm

theorem list_prod_range_eq_finset_prod_range {R : Type*} [CommRing R] (f : ℕ → R) (n : ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    simp [Finset.prod_range_succ]

theorem range_prod_eq_factorial {R : Type*} [CommRing R] (n : ℕ) :
    ((List.range n).map (fun (i : ℕ) => ((i + 1 : ℕ) : R))).prod = (n.factorial : R) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    simp [Nat.factorial_succ]
    ring

theorem choose_mul_factorial_eq_prod {R : Type*} [CommRing R] (p : ℕ) :
    (((3 * p - 1).choose (p - 1) : R) * ((p - 1).factorial : R)) =
    ((List.range (p - 1)).map (fun (i : ℕ) => ((3 * p - 1 - i : ℕ) : R))).prod := by
  have h1 : (3 * p - 1).choose (p - 1) * (p - 1).factorial = (3 * p - 1).descFactorial (p - 1) := by
    rw [mul_comm, descFactorial_eq_factorial_mul_choose]
  have h2 : (3 * p - 1).descFactorial (p - 1) = ∏ i ∈ Finset.range (p - 1), (3 * p - 1 - i) := by
    rw [descFactorial_eq_prod_range]
  have h3 : (((3 * p - 1).choose (p - 1) : R) * ((p - 1).factorial : R)) = (((3 * p - 1).choose (p - 1) * (p - 1).factorial : ℕ) : R) := by
    push_cast; rfl
  rw [h3, h1, h2]
  push_cast
  rw [list_prod_range_eq_finset_prod_range]


theorem choose_mul_factorial_eq_prod_2p {R : Type*} [CommRing R] (p : ℕ) :
    (((2 * p - 1).choose (p - 1) : R) * ((p - 1).factorial : R)) =
    ((List.range (p - 1)).map (fun (i : ℕ) => ((2 * p - 1 - i : ℕ) : R))).prod := by
  have h1 : (2 * p - 1).choose (p - 1) * (p - 1).factorial = (2 * p - 1).descFactorial (p - 1) := by
    rw [mul_comm, descFactorial_eq_factorial_mul_choose]
  have h2 : (2 * p - 1).descFactorial (p - 1) = ∏ i ∈ Finset.range (p - 1), (2 * p - 1 - i) := by
    rw [descFactorial_eq_prod_range]
  have h3 : (((2 * p - 1).choose (p - 1) : R) * ((p - 1).factorial : R)) = (((2 * p - 1).choose (p - 1) * (p - 1).factorial : ℕ) : R) := by
    push_cast; rfl
  rw [h3, h1, h2]
  push_cast
  rw [list_prod_range_eq_finset_prod_range]

lemma coprime_p_pow (p k : ℕ) (hp : p.Prime) (hk1 : k ≥ 1) (hk2 : k < p) (a : ℕ) : k.Coprime (p ^ a) := by
  have h_coprime : k.Coprime p := by
    rw [Nat.coprime_comm]
    apply hp.coprime_iff_not_dvd.mpr
    apply Nat.not_dvd_of_pos_of_lt hk1 hk2
  exact h_coprime.pow_right a

lemma unit_mul_inv {n : ℕ} {a : ZMod n} (ha : IsUnit a) : a * a⁻¹ = 1 := by
  rw [mul_comm]
  exact (ZMod.inv_mul_eq_one_of_isUnit ha a).mpr rfl

lemma ringHom_map_inv {n m : ℕ} (f : ZMod n →+* ZMod m) (x : ZMod n) (hx : IsUnit x) :
    f x⁻¹ = (f x)⁻¹ := by
  have h1 : x * x⁻¹ = 1 := unit_mul_inv hx
  have h2 : f x * f x⁻¹ = 1 := by
    calc f x * f x⁻¹
      _ = f (x * x⁻¹) := by rw [← f.map_mul]
      _ = f 1 := by rw [h1]
      _ = 1 := f.map_one
  have h_unit : IsUnit (f x) := hx.map f
  have h3 : f x * (f x)⁻¹ = 1 := unit_mul_inv h_unit
  calc f x⁻¹
    _ = 1 * f x⁻¹ := by rw [one_mul]
    _ = ((f x)⁻¹ * f x) * f x⁻¹ := by rw [mul_comm (f x)⁻¹, h3]
    _ = (f x)⁻¹ * (f x * f x⁻¹) := by ring
    _ = (f x)⁻¹ * 1 := by rw [h2]
    _ = (f x)⁻¹ := by rw [mul_one]

lemma isUnit_of_lt (p i a : ℕ) (hp : p.Prime) (hi : i < p - 1) :
    IsUnit ((i + 1 : ℕ) : ZMod (p ^ a)) := by
  have hk1 : i + 1 ≥ 1 := by omega
  have hk2 : i + 1 < p := by omega
  have h_coprime := coprime_p_pow p (i + 1) hp hk1 hk2 a
  rw [ZMod.isUnit_iff_coprime]
  exact h_coprime

lemma factorial_unit (p n a : ℕ) (hp : p.Prime) (hn : n < p) : IsUnit (n.factorial : ZMod (p ^ a)) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Nat.factorial_succ]
    have hn_lt : n < p := by omega
    have ih_unit := ih hn_lt
    have h_succ : IsUnit ((n + 1 : ℕ) : ZMod (p ^ a)) := by
      have hk1 : n + 1 ≥ 1 := by omega
      have hk2 : n + 1 < p := by omega
      have h_coprime := coprime_p_pow p (n + 1) hp hk1 hk2 a
      rw [ZMod.isUnit_iff_coprime]
      exact h_coprime
    push_cast
    push_cast at h_succ
    exact IsUnit.mul h_succ ih_unit

lemma pointwise_eq (p i : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hi : i < p - 1) :
    ((3 * p - 1 - i : ℕ) : ZMod (p ^ 3)) = -( (i + 1 : ℕ) : ZMod (p ^ 3) ) * (1 - (3 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹) := by
  have h_unit : IsUnit ((i + 1 : ℕ) : ZMod (p ^ 3)) := isUnit_of_lt p i 3 hp hi
  have h_inv : ((i + 1 : ℕ) : ZMod (p ^ 3)) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ = 1 := unit_mul_inv h_unit
  have h_sub : 3 * p - 1 - i = 3 * p - (i + 1) := by omega
  have h_cast : ((3 * p - 1 - i : ℕ) : ZMod (p ^ 3)) = (3 * p : ZMod (p ^ 3)) - ((i + 1 : ℕ) : ZMod (p ^ 3)) := by
    rw [h_sub]
    have h_le : i + 1 ≤ 3 * p := by omega
    rw [Nat.cast_sub h_le]
    push_cast
    rfl
  rw [h_cast]
  have h_eq : -( (i + 1 : ℕ) : ZMod (p ^ 3) ) * (1 - (3 * p : ZMod (p ^ 3)) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹) = (3 * p : ZMod (p ^ 3)) - ((i + 1 : ℕ) : ZMod (p ^ 3)) := by
    calc -( (i + 1 : ℕ) : ZMod (p ^ 3) ) * (1 - (3 * p : ZMod (p ^ 3)) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)
      _ = -( (i + 1 : ℕ) : ZMod (p ^ 3) ) + (3 * p : ZMod (p ^ 3)) * ( ((i + 1 : ℕ) : ZMod (p ^ 3)) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ ) := by ring
      _ = -( (i + 1 : ℕ) : ZMod (p ^ 3) ) + (3 * p : ZMod (p ^ 3)) * 1 := by rw [h_inv]
      _ = (3 * p : ZMod (p ^ 3)) - ((i + 1 : ℕ) : ZMod (p ^ 3)) := by ring
  exact h_eq.symm

lemma pointwise_eq_2p (p i : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hi : i < p - 1) :
    ((2 * p - 1 - i : ℕ) : ZMod (p ^ 3)) = -( (i + 1 : ℕ) : ZMod (p ^ 3) ) * (1 - (2 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹) := by
  have h_unit : IsUnit ((i + 1 : ℕ) : ZMod (p ^ 3)) := isUnit_of_lt p i 3 hp hi
  have h_inv : ((i + 1 : ℕ) : ZMod (p ^ 3)) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ = 1 := unit_mul_inv h_unit
  have h_sub : 2 * p - 1 - i = 2 * p - (i + 1) := by omega
  have h_cast : ((2 * p - 1 - i : ℕ) : ZMod (p ^ 3)) = (2 * p : ZMod (p ^ 3)) - ((i + 1 : ℕ) : ZMod (p ^ 3)) := by
    rw [h_sub]
    have h_le : i + 1 ≤ 2 * p := by omega
    rw [Nat.cast_sub h_le]
    push_cast
    rfl
  rw [h_cast]
  have h_eq : -( (i + 1 : ℕ) : ZMod (p ^ 3) ) * (1 - (2 * p : ZMod (p ^ 3)) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹) = (2 * p : ZMod (p ^ 3)) - ((i + 1 : ℕ) : ZMod (p ^ 3)) := by
    calc -( (i + 1 : ℕ) : ZMod (p ^ 3) ) * (1 - (2 * p : ZMod (p ^ 3)) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)
      _ = -( (i + 1 : ℕ) : ZMod (p ^ 3) ) + (2 * p : ZMod (p ^ 3)) * ( ((i + 1 : ℕ) : ZMod (p ^ 3)) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ ) := by ring
      _ = -( (i + 1 : ℕ) : ZMod (p ^ 3) ) + (2 * p : ZMod (p ^ 3)) * 1 := by rw [h_inv]
      _ = (2 * p : ZMod (p ^ 3)) - ((i + 1 : ℕ) : ZMod (p ^ 3)) := by ring
  exact h_eq.symm


theorem list_prod_mul {α : Type*} {R : Type*} [CommRing R] (L : List α) (f g : α → R) :
    (L.map (fun x => f x * g x)).prod = (L.map f).prod * (L.map g).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp [ih]
    ring

theorem list_prod_const {R : Type*} [CommRing R] (n : ℕ) (c : R) :
    ((List.range n).map (fun _ => c)).prod = c ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    simp [pow_succ]

lemma p_minus_one_even (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) : (p - 1) % 2 = 0 := by
  have hp_odd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr (by omega)
  omega

lemma neg_one_pow_p_minus_one (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    (-1 : ZMod (p ^ 3)) ^ (p - 1) = 1 := by
  have h_even := p_minus_one_even p hp hp3
  obtain ⟨k, hk⟩ : ∃ k, p - 1 = 2 * k := by
    use (p - 1) / 2
    omega
  rw [hk, pow_mul]
  have : (-1 : ZMod (p ^ 3)) ^ 2 = 1 := by ring
  rw [this, one_pow]

lemma neg_range_prod (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    ((List.range (p - 1)).map (fun (i : ℕ) => -( (i + 1 : ℕ) : ZMod (p ^ 3) ))).prod =
    ((List.range (p - 1)).map (fun (i : ℕ) => ( (i + 1 : ℕ) : ZMod (p ^ 3) ))).prod := by
  have h_eq : (fun (i : ℕ) => -( (i + 1 : ℕ) : ZMod (p ^ 3) )) = (fun (i : ℕ) => (-1 : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )) := by
    ext i
    ring
  rw [h_eq]
  rw [list_prod_mul]
  rw [list_prod_const]
  rw [neg_one_pow_p_minus_one p hp hp3]
  ring

lemma product_congr_pointwise (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    ((List.range (p - 1)).map (fun (i : ℕ) => ((3 * p - 1 - i : ℕ) : ZMod (p ^ 3)))).prod =
    ((List.range (p - 1)).map (fun (i : ℕ) => -( (i + 1 : ℕ) : ZMod (p ^ 3) ) * (1 - (3 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹))).prod := by
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < p - 1 := List.mem_range.mp hi
  exact pointwise_eq p i hp hp3 hi_lt

theorem choose_3p_minus_1_p_minus_1_mod_p3 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    ((3 * p - 1).choose (p - 1) : ZMod (p ^ 3)) =
    ((List.range (p - 1)).map (fun (i : ℕ) => (1 - (3 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹))).prod := by
  have h_fact := choose_mul_factorial_eq_prod p (R := ZMod (p ^ 3))
  have h_congr := product_congr_pointwise p hp hp3
  have h_mul := list_prod_mul (List.range (p - 1)) (fun (i : ℕ) => -( (i + 1 : ℕ) : ZMod (p ^ 3) )) (fun (i : ℕ) => (1 - (3 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹))
  have h_neg := neg_range_prod p hp hp3
  have h_prod_fact := range_prod_eq_factorial (R := ZMod (p ^ 3)) (p - 1)
  have h_combined : ((p - 1).factorial : ZMod (p ^ 3)) * ((3 * p - 1).choose (p - 1) : ZMod (p ^ 3)) =
      ((p - 1).factorial : ZMod (p ^ 3)) * ((List.range (p - 1)).map (fun (i : ℕ) => (1 - (3 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹))).prod := by
    calc ((p - 1).factorial : ZMod (p ^ 3)) * ((3 * p - 1).choose (p - 1) : ZMod (p ^ 3))
      _ = ((3 * p - 1).choose (p - 1) : ZMod (p ^ 3)) * ((p - 1).factorial : ZMod (p ^ 3)) := by ring
      _ = ((List.range (p - 1)).map (fun (i : ℕ) => ((3 * p - 1 - i : ℕ) : ZMod (p ^ 3)))).prod := h_fact
      _ = ((List.range (p - 1)).map (fun (i : ℕ) => -( (i + 1 : ℕ) : ZMod (p ^ 3) ) * (1 - (3 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹))).prod := h_congr
      _ = ((List.range (p - 1)).map (fun (i : ℕ) => -( (i + 1 : ℕ) : ZMod (p ^ 3) ))).prod * ((List.range (p - 1)).map (fun (i : ℕ) => (1 - (3 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹))).prod := h_mul
      _ = ((List.range (p - 1)).map (fun (i : ℕ) => ( (i + 1 : ℕ) : ZMod (p ^ 3) ))).prod * ((List.range (p - 1)).map (fun (i : ℕ) => (1 - (3 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹))).prod := by rw [h_neg]
      _ = ((p - 1).factorial : ZMod (p ^ 3)) * ((List.range (p - 1)).map (fun (i : ℕ) => (1 - (3 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹))).prod := by rw [h_prod_fact]
  have h_unit : IsUnit ((p - 1).factorial : ZMod (p ^ 3)) := factorial_unit p (p - 1) 3 hp (by omega)
  rwa [h_unit.mul_right_inj] at h_combined

lemma product_congr_pointwise_2p (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    ((List.range (p - 1)).map (fun (i : ℕ) => ((2 * p - 1 - i : ℕ) : ZMod (p ^ 3)))).prod =
    ((List.range (p - 1)).map (fun (i : ℕ) => -( (i + 1 : ℕ) : ZMod (p ^ 3) ) * (1 - (2 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹))).prod := by
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < p - 1 := List.mem_range.mp hi
  exact pointwise_eq_2p p i hp hp3 hi_lt

theorem choose_2p_minus_1_p_minus_1_mod_p3 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    ((2 * p - 1).choose (p - 1) : ZMod (p ^ 3)) =
    ((List.range (p - 1)).map (fun (i : ℕ) => (1 - (2 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹))).prod := by
  have h_fact := choose_mul_factorial_eq_prod_2p p (R := ZMod (p ^ 3))
  have h_congr := product_congr_pointwise_2p p hp hp3
  have h_mul := list_prod_mul (List.range (p - 1)) (fun (i : ℕ) => -( (i + 1 : ℕ) : ZMod (p ^ 3) )) (fun (i : ℕ) => (1 - (2 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹))
  have h_neg := neg_range_prod p hp hp3
  have h_prod_fact := range_prod_eq_factorial (R := ZMod (p ^ 3)) (p - 1)
  have h_combined : ((p - 1).factorial : ZMod (p ^ 3)) * ((2 * p - 1).choose (p - 1) : ZMod (p ^ 3)) =
      ((p - 1).factorial : ZMod (p ^ 3)) * ((List.range (p - 1)).map (fun (i : ℕ) => (1 - (2 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹))).prod := by
    calc ((p - 1).factorial : ZMod (p ^ 3)) * ((2 * p - 1).choose (p - 1) : ZMod (p ^ 3))
      _ = ((2 * p - 1).choose (p - 1) : ZMod (p ^ 3)) * ((p - 1).factorial : ZMod (p ^ 3)) := by ring
      _ = ((List.range (p - 1)).map (fun (i : ℕ) => ((2 * p - 1 - i : ℕ) : ZMod (p ^ 3)))).prod := h_fact
      _ = ((List.range (p - 1)).map (fun (i : ℕ) => -( (i + 1 : ℕ) : ZMod (p ^ 3) ) * (1 - (2 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹))).prod := h_congr
      _ = ((List.range (p - 1)).map (fun (i : ℕ) => -( (i + 1 : ℕ) : ZMod (p ^ 3) ))).prod * ((List.range (p - 1)).map (fun (i : ℕ) => (1 - (2 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹))).prod := h_mul
      _ = ((List.range (p - 1)).map (fun (i : ℕ) => ( (i + 1 : ℕ) : ZMod (p ^ 3) ))).prod * ((List.range (p - 1)).map (fun (i : ℕ) => (1 - (2 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹))).prod := by rw [h_neg]
      _ = ((p - 1).factorial : ZMod (p ^ 3)) * ((List.range (p - 1)).map (fun (i : ℕ) => (1 - (2 * p : ZMod (p ^ 3)) * ( (i + 1 : ℕ) : ZMod (p ^ 3) )⁻¹))).prod := by rw [h_prod_fact]
  have h_unit : IsUnit ((p - 1).factorial : ZMod (p ^ 3)) := factorial_unit p (p - 1) 3 hp (by omega)
  rwa [h_unit.mul_right_inj] at h_combined


lemma y_pow_3_eq_zero (p : ℕ) : (-3 * (p : ZMod (p ^ 3))) ^ 3 = 0 := by
  have : (-3 * (p : ZMod (p ^ 3))) ^ 3 = -27 * (p ^ 3 : ZMod (p ^ 3)) := by ring
  rw [this]
  have h_mod : (p ^ 3 : ZMod (p ^ 3)) = 0 := by
    have h_eq : (p ^ 3 : ZMod (p ^ 3)) = ((p ^ 3 : ℕ) : ZMod (p ^ 3)) := by push_cast; rfl
    rw [h_eq, ZMod.natCast_self]
  rw [h_mod, mul_zero]

lemma p_sq_inv_eq (p : ℕ) (j : ZMod (p ^ 3)) (hj1 : IsUnit j) (hj2 : IsUnit ((p : ZMod (p ^ 3)) - j)) :
    (p : ZMod (p ^ 3)) ^ 2 * ((p : ZMod (p ^ 3)) - j)⁻¹ + (p : ZMod (p ^ 3)) ^ 2 * j⁻¹ = 0 := by
  have h1 : j * j⁻¹ = 1 := unit_mul_inv hj1
  have h2 : ((p : ZMod (p ^ 3)) - j) * ((p : ZMod (p ^ 3)) - j)⁻¹ = 1 := unit_mul_inv hj2
  have h_mod : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
    have h_eq : ((p ^ 3 : ℕ) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) ^ 3 := by push_cast; rfl
    rw [← h_eq, ZMod.natCast_self]
  linear_combination
    - ((p : ZMod (p ^ 3)) ^ 2 * ((p : ZMod (p ^ 3)) - j)⁻¹) * (h1 - 1) -
    ((p : ZMod (p ^ 3)) ^ 2 * j⁻¹) * (h2 - 1) +
    (((p : ZMod (p ^ 3)) - j)⁻¹ * j⁻¹) * h_mod

lemma inv_add_inv_eq_mul (p : ℕ) (j : ZMod (p ^ 3)) (hj1 : IsUnit j) (hj2 : IsUnit ((p : ZMod (p ^ 3)) - j)) :
    j⁻¹ + ((p : ZMod (p ^ 3)) - j)⁻¹ = (p : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) - j)⁻¹ * j⁻¹ := by
  have h1 : j * j⁻¹ = 1 := unit_mul_inv hj1
  have h2 : ((p : ZMod (p ^ 3)) - j) * ((p : ZMod (p ^ 3)) - j)⁻¹ = 1 := unit_mul_inv hj2
  linear_combination
    - (((p : ZMod (p ^ 3)) - j)⁻¹ * (h1 - 1) + j⁻¹ * (h2 - 1))

theorem List.list_sum_range_eq_finset_sum_range {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp [Finset.sum_range_succ]

lemma sum_inv_sq_zero_ico (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    letI : NeZero p := ⟨by omega⟩
    (∑ j ∈ Finset.Ico 1 p, ((j : ZMod p)⁻¹ ^ 2)) = 0 := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have h_univ : (∑ k : ZMod p, (k⁻¹ ^ 2)) = 0 := by
    have h_eq : (∑ k : ZMod p, (k⁻¹ ^ 2)) = ∑ k : ZMod p, (k ^ 2)⁻¹ := by
      congr 1; ext k
      exact inv_pow k 2
    rw [h_eq]
    exact sum_inv_sq_zero p hp hp5
  have h_erase : (∑ k : ZMod p, k⁻¹ ^ 2) = ∑ k ∈ Finset.erase Finset.univ 0, k⁻¹ ^ 2 := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ 0)]
    simp
  rw [h_erase] at h_univ
  have h_bij : (∑ j ∈ Finset.Ico 1 p, ((j : ZMod p)⁻¹ ^ 2)) = ∑ k ∈ Finset.erase Finset.univ 0, k⁻¹ ^ 2 := by
    apply Finset.sum_bij (fun (j : ℕ) _ => (j : ZMod p))
    · intro j hj
      rw [Finset.mem_Ico] at hj
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro hj_zero
      have h_dvd : p ∣ j := (CharP.cast_eq_zero_iff (ZMod p) p j).mp hj_zero
      have h_le : p ≤ j := Nat.le_of_dvd (by omega) h_dvd
      omega
    · intro j1 hj1 j2 hj2 h_eq
      rw [Finset.mem_Ico] at hj1 hj2
      rw [ZMod.natCast_eq_natCast_iff j1 j2 p] at h_eq
      have h_mod1 : j1 % p = j1 := Nat.mod_eq_of_lt hj1.2
      have h_mod2 : j2 % p = j2 := Nat.mod_eq_of_lt hj2.2
      have h_eq_mod : j1 % p = j2 % p := h_eq
      rw [h_mod1, h_mod2] at h_eq_mod
      exact h_eq_mod
    · intro b hb
      rw [Finset.mem_erase] at hb
      have hb0 : b ≠ 0 := hb.1
      use b.val
      have hb_val_lt : b.val < p := b.val_lt
      have hb_val_ge : b.val ≥ 1 := by
        by_contra h_contra
        have : b.val = 0 := by omega
        apply hb0
        have h_val : b.val = (0 : ZMod p).val := by
          rw [this, ZMod.val_zero]
        exact ZMod.val_injective p h_val
      refine ⟨by rw [Finset.mem_Ico]; omega, by rw [ZMod.natCast_val, ZMod.cast_id]⟩
    · intro j hj
      rfl
  rw [h_bij]
  exact h_univ

def invEquiv (α : Type*) [DivisionRing α] : α ≃ α where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv x := inv_inv x
  right_inv x := inv_inv x

theorem sum_zmod_zero (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    letI : NeZero p := ⟨by omega⟩
    (∑ k : ZMod p, k) = 0 := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h_dvd : p ∣ 2 := by
      exact (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    have h_le : p ≤ 2 := Nat.le_of_dvd (by decide) h_dvd
    omega
  let E : ZMod p ≃ ZMod p := Equiv.mulLeft₀ (2 : ZMod p) h2
  have h_comp : (∑ k : ZMod p, (2 * k)) = ∑ k : ZMod p, k := by
    have hE := Equiv.sum_comp E (fun x => x)
    have h_rw : ∀ x, E x = 2 * x := fun x => rfl
    simp_rw [h_rw] at hE
    exact hE
  have h_sum_rw : (∑ k : ZMod p, (2 * k)) = 2 * ∑ k : ZMod p, k := by
    rw [← mul_sum]
  have h_eq : (∑ k : ZMod p, k) = 2 * ∑ k : ZMod p, k := by
    calc (∑ k : ZMod p, k)
      _ = ∑ k : ZMod p, (2 * k) := h_comp.symm
      _ = 2 * ∑ k : ZMod p, k := h_sum_rw
  linear_combination -h_eq

theorem sum_inv_zero (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    letI : NeZero p := ⟨by omega⟩
    (∑ k : ZMod p, k⁻¹) = 0 := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have h_comp : (∑ k : ZMod p, k⁻¹) = ∑ k : ZMod p, k := by
    have hE := Equiv.sum_comp (invEquiv (ZMod p)) (fun x => x)
    exact hE
  rw [h_comp]
  exact sum_zmod_zero p hp hp3

lemma sum_inv_zero_ico (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    letI : NeZero p := ⟨by omega⟩
    (∑ j ∈ Finset.Ico 1 p, (j : ZMod p)⁻¹) = 0 := by
  haveI : NeZero p := ⟨by omega⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have h_univ : (∑ k : ZMod p, k⁻¹) = 0 := sum_inv_zero p hp hp3
  have h_erase : (∑ k : ZMod p, k⁻¹) = ∑ k ∈ Finset.erase Finset.univ 0, k⁻¹ := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ 0)]
    simp
  rw [h_erase] at h_univ
  have h_bij : (∑ j ∈ Finset.Ico 1 p, (j : ZMod p)⁻¹) = ∑ k ∈ Finset.erase Finset.univ 0, k⁻¹ := by
    apply Finset.sum_bij (fun (j : ℕ) _ => (j : ZMod p))
    · intro j hj
      rw [Finset.mem_Ico] at hj
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro hj_zero
      have h_dvd : p ∣ j := (CharP.cast_eq_zero_iff (ZMod p) p j).mp hj_zero
      have h_le : p ≤ j := Nat.le_of_dvd (by omega) h_dvd
      omega
    · intro j1 hj1 j2 hj2 h_eq
      rw [Finset.mem_Ico] at hj1 hj2
      rw [ZMod.natCast_eq_natCast_iff j1 j2 p] at h_eq
      have h_mod1 : j1 % p = j1 := Nat.mod_eq_of_lt hj1.2
      have h_mod2 : j2 % p = j2 := Nat.mod_eq_of_lt hj2.2
      have h_eq_mod : j1 % p = j2 % p := h_eq
      rw [h_mod1, h_mod2] at h_eq_mod
      exact h_eq_mod
    · intro b hb
      rw [Finset.mem_erase] at hb
      have hb0 : b ≠ 0 := hb.1
      use b.val
      have hb_val_lt : b.val < p := b.val_lt
      have hb_val_ge : b.val ≥ 1 := by
        by_contra h_contra
        have : b.val = 0 := by omega
        apply hb0
        have h_val : b.val = (0 : ZMod p).val := by
          rw [this, ZMod.val_zero]
        exact ZMod.val_injective p h_val
      refine ⟨by rw [Finset.mem_Ico]; omega, by rw [ZMod.natCast_val, ZMod.cast_id]⟩
    · intro j hj
      rfl
  rw [h_bij]
  exact h_univ

lemma p_sq_mul_zero_of_cast_zero (p : ℕ) (hp : p.Prime) (X : ZMod (p ^ 3))
    (h_cast : (X.cast : ZMod p) = 0) :
    (p : ZMod (p ^ 3)) ^ 2 * X = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 3) := ⟨by
    have : p > 0 := hp.pos
    positivity⟩
  have h_val : ((X.val : ℕ) : ZMod p) = 0 := by
    rw [← ZMod.natCast_val X] at h_cast
    exact h_cast
  have h_dvd : p ∣ X.val := by
    exact (CharP.cast_eq_zero_iff (ZMod p) p X.val).mp h_val
  obtain ⟨k, hk⟩ := h_dvd
  have h_X_eq : X = ((X.val : ℕ) : ZMod (p ^ 3)) := by
    rw [ZMod.natCast_val X, ZMod.cast_id]
  rw [h_X_eq, hk]
  push_cast
  have h_p3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
    have h_eq : ((p ^ 3 : ℕ) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) ^ 3 := by push_cast; rfl
    rw [← h_eq, ZMod.natCast_self]
  calc (p : ZMod (p ^ 3)) ^ 2 * ((p : ZMod (p ^ 3)) * (k : ZMod (p ^ 3)))
    _ = (p : ZMod (p ^ 3)) ^ 3 * (k : ZMod (p ^ 3)) := by ring
    _ = 0 * (k : ZMod (p ^ 3)) := by rw [h_p3]
    _ = 0 := by ring

lemma sum_reflect_ico (p : ℕ) (hp3 : p ≥ 3) :
    (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹) = ∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ := by
  apply Finset.sum_bij (fun j _ => p - j)
  · intro j hj
    rw [Finset.mem_Ico] at hj ⊢
    omega
  · intro j1 hj1 j2 hj2 h_eq
    rw [Finset.mem_Ico] at hj1 hj2
    omega
  · intro b hb
    use p - b
    rw [Finset.mem_Ico] at hb ⊢
    have h_le : p - b ≤ p := by omega
    have h_sub : p - (p - b) = b := by omega
    refine ⟨by omega, h_sub⟩
  · intro j hj
    rw [Finset.mem_Ico] at hj
    have h_le : p - j ≤ p := by omega
    have h_sub : (p : ZMod (p ^ 3)) - ((p - j : ℕ) : ZMod (p ^ 3)) = (j : ZMod (p ^ 3)) := by
      rw [← Nat.cast_sub h_le]
      congr 1
      omega
    rw [h_sub]

lemma sum_inv_p_mul_zero (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    (p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹) = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 3) := ⟨by
    have : p > 0 := hp.pos
    positivity⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have h_reflect := sum_reflect_ico p (by omega)
  have h_twice : 2 * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹) =
      (∑ j ∈ Finset.Ico 1 p, ((j : ZMod (p ^ 3))⁻¹ + ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹)) := by
    rw [sum_add_distrib, ← h_reflect]
    ring
  have h_twice_mul : (p : ZMod (p ^ 3)) * (2 * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹)) = (p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, ((j : ZMod (p ^ 3))⁻¹ + ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹)) := by
    rw [h_twice]
  have h_simp : (∑ j ∈ Finset.Ico 1 p, ((j : ZMod (p ^ 3))⁻¹ + ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹)) =
      (p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹) := by
    have h_congr : (∑ j ∈ Finset.Ico 1 p, ((j : ZMod (p ^ 3))⁻¹ + ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹)) =
        ∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹) := by
      apply sum_congr rfl
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj1 : IsUnit (j : ZMod (p ^ 3)) := by
        have hk1 : j ≥ 1 := hj.1
        have hk2 : j < p := hj.2
        have h_coprime := coprime_p_pow p j hp hk1 hk2 3
        rw [ZMod.isUnit_iff_coprime]
        exact h_coprime
      have hj2 : IsUnit ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3))) := by
        have h_sub : (p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)) = ((p - j : ℕ) : ZMod (p ^ 3)) := by
          have h_le : j ≤ p := by omega
          rw [Nat.cast_sub h_le]
        rw [h_sub]
        have hk1 : p - j ≥ 1 := by omega
        have hk2 : p - j < p := by omega
        have h_coprime := coprime_p_pow p (p - j) hp hk1 hk2 3
        rw [ZMod.isUnit_iff_coprime]
        exact h_coprime
      exact inv_add_inv_eq_mul p (j : ZMod (p ^ 3)) hj1 hj2
    rw [h_congr, mul_sum]
    simp_rw [mul_assoc]
  have h_p_twice : 2 * ((p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹)) =
      (p : ZMod (p ^ 3)) ^ 2 * (∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹) := by
    calc 2 * ((p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹))
      _ = (p : ZMod (p ^ 3)) * (2 * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹)) := by ring
      _ = (p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, ((j : ZMod (p ^ 3))⁻¹ + ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹)) := h_twice_mul
      _ = (p : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹)) := by rw [h_simp]
      _ = (p : ZMod (p ^ 3)) ^ 2 * (∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹) := by ring
  have h_cast_eq : (((∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹).cast : ZMod p) = 0) := by
    let f : ZMod (p ^ 3) →+* ZMod p := ZMod.castHom (by
      have : p > 0 := hp.pos
      exact dvd_pow_self p (by omega)) (ZMod p)
    have h_map_eq : ((∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹).cast : ZMod p) =
        f (∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹) := by
      rw [ZMod.castHom_apply]
    rw [h_map_eq, map_sum]
    have h_simp_term : ∀ j ∈ Finset.Ico 1 p, f (((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹) = -((j : ZMod p)⁻¹ ^ 2) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj1 : IsUnit (j : ZMod (p ^ 3)) := by
        have hk1 : j ≥ 1 := hj.1
        have hk2 : j < p := hj.2
        have h_coprime := coprime_p_pow p j hp hk1 hk2 3
        rw [ZMod.isUnit_iff_coprime]
        exact h_coprime
      have hj2 : IsUnit ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3))) := by
        have h_sub : (p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)) = ((p - j : ℕ) : ZMod (p ^ 3)) := by
          have h_le : j ≤ p := by omega
          rw [Nat.cast_sub h_le]
        rw [h_sub]
        have hk1 : p - j ≥ 1 := by omega
        have hk2 : p - j < p := by omega
        have h_coprime := coprime_p_pow p (p - j) hp hk1 hk2 3
        rw [ZMod.isUnit_iff_coprime]
        exact h_coprime
      rw [f.map_mul, ringHom_map_inv f ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3))) hj2, ringHom_map_inv f (j : ZMod (p ^ 3)) hj1]
      have h_cast_j : f (j : ZMod (p ^ 3)) = (j : ZMod p) := map_natCast f j
      have h_cast_pj : f ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3))) = f (p : ZMod (p ^ 3)) - f (j : ZMod (p ^ 3)) := f.map_sub (p : ZMod (p ^ 3)) (j : ZMod (p ^ 3))
      have h_cast_p : f (p : ZMod (p ^ 3)) = 0 := by
        have h_eq : (p : ZMod (p ^ 3)) = ((p : ℕ) : ZMod (p ^ 3)) := by push_cast; rfl
        rw [h_eq, map_natCast, ZMod.natCast_self]
      have h_inv_neg : (- (j : ZMod p))⁻¹ = - (j : ZMod p)⁻¹ := inv_neg (a := (j : ZMod p))
      rw [h_cast_pj, h_cast_p, h_cast_j, zero_sub, h_inv_neg]
      ring
    rw [sum_congr rfl h_simp_term]
    rw [sum_neg_distrib]
    rw [sum_inv_sq_zero_ico p hp hp5]
    ring
  have h_p2_zero := p_sq_mul_zero_of_cast_zero p hp (∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹) h_cast_eq
  have h_goal : 2 * ((p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹)) = 2 * 0 := by
    rw [mul_zero]
    calc 2 * ((p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹))
      _ = (p : ZMod (p ^ 3)) ^ 2 * (∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3)))⁻¹ * (j : ZMod (p ^ 3))⁻¹) := h_p_twice
      _ = 0 := h_p2_zero
  have h2_unit : IsUnit (2 : ZMod (p ^ 3)) := isUnit_of_lt p 1 3 hp (by omega)
  rwa [h2_unit.mul_right_inj] at h_goal

lemma sum_pairs_p_sq_mul_zero (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : NeZero (p ^ 3) := ⟨by
      have : p > 0 := hp.pos
      positivity⟩
    (p : ZMod (p ^ 3)) ^ 2 * List.sum_pairs ((List.range (p - 1)).map (fun i => ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)) = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 3) := ⟨by
    have : p > 0 := hp.pos
    positivity⟩
  haveI : Fact p.Prime := ⟨hp⟩
  let L : List (ZMod (p ^ 3)) := (List.range (p - 1)).map (fun i => ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)
  have h_cast_eq : ((List.sum_pairs L).cast : ZMod p) = 0 := by
    let f : ZMod (p ^ 3) →+* ZMod p := ZMod.castHom (by
      have : p > 0 := hp.pos
      exact dvd_pow_self p (by omega)) (ZMod p)
    have h_map_eq : ((List.sum_pairs L).cast : ZMod p) = f (List.sum_pairs L) := by
      rw [ZMod.castHom_apply]
    rw [h_map_eq, List.ringHom_sum_pairs f L]
    have h_L_map : L.map f = (List.range (p - 1)).map (fun i => ((i + 1 : ℕ) : ZMod p)⁻¹) := by
      change ((List.range (p - 1)).map (fun i => ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)).map f = _
      simp only [List.map_map]
      apply List.map_congr_left
      intro i hi
      have hi_lt : i < p - 1 := List.mem_range.mp hi
      have hi_unit : IsUnit ((i + 1 : ℕ) : ZMod (p ^ 3)) := isUnit_of_lt p i 3 hp hi_lt
      simp only [Function.comp_apply]
      rw [ringHom_map_inv f ((i + 1 : ℕ) : ZMod (p ^ 3)) hi_unit, map_natCast f (i + 1)]
    rw [h_L_map]
    let L_p : List (ZMod p) := (List.range (p - 1)).map (fun i => ((i + 1 : ℕ) : ZMod p)⁻¹)
    have h_sum_sq := List.list_sum_sq_eq L_p
    have h_L_p_sum : L_p.sum = 0 := by
      rw [List.list_sum_range_eq_finset_sum_range]
      have h_sum_Ico : (∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod p)⁻¹) = ∑ j ∈ Ico 1 p, (j : ZMod p)⁻¹ := by
        rw [range_eq_Ico]
        apply Finset.sum_bij (fun i _ => i + 1)
        · intro i hi
          rw [Finset.mem_Ico] at hi ⊢
          omega
        · intro i1 hi1 i2 hi2 h_eq
          omega
        · intro j hj
          rw [Finset.mem_Ico] at hj
          refine ⟨j - 1, by rw [Finset.mem_Ico]; omega, by omega⟩
        · intro i hi
          rfl
      rw [h_sum_Ico]
      exact sum_inv_zero_ico p hp (by omega)
    have h_L_p_map_sum : (L_p.map (fun x => x ^ 2)).sum = 0 := by
      rw [List.map_map, List.list_sum_range_eq_finset_sum_range]
      simp only [Function.comp_apply]
      have h_sum_Ico : (∑ i ∈ range (p - 1), ((i + 1 : ℕ) : ZMod p)⁻¹ ^ 2) = ∑ j ∈ Ico 1 p, ((j : ZMod p)⁻¹ ^ 2) := by
        rw [range_eq_Ico]
        apply Finset.sum_bij (fun i _ => i + 1)
        · intro i hi
          rw [Finset.mem_Ico] at hi ⊢
          omega
        · intro i1 hi1 i2 hi2 h_eq
          omega
        · intro j hj
          rw [Finset.mem_Ico] at hj
          refine ⟨j - 1, by rw [Finset.mem_Ico]; omega, by omega⟩
        · intro i hi
          rfl
      rw [h_sum_Ico]
      exact sum_inv_sq_zero_ico p hp hp5
    rw [h_L_p_sum, h_L_p_map_sum] at h_sum_sq
    have h_2_unit : IsUnit (2 : ZMod p) := by
      have h2 : (2 : ZMod p) ≠ 0 := by
        intro h
        have h_dvd : p ∣ 2 := by
          exact (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
        have h_le : p ≤ 2 := Nat.le_of_dvd (by decide) h_dvd
        omega
      exact h2.isUnit
    have h_eq : 2 * List.sum_pairs L_p = 2 * 0 := by
      rw [mul_zero]
      have h_simp_sq : 0 = 2 * List.sum_pairs L_p := by
        calc 0
          _ = (0 : ZMod p) ^ 2 := by ring
          _ = 0 + 2 * List.sum_pairs L_p := h_sum_sq
          _ = 2 * List.sum_pairs L_p := by ring
      exact h_simp_sq.symm
    rwa [h_2_unit.mul_right_inj] at h_eq
  exact p_sq_mul_zero_of_cast_zero p hp (List.sum_pairs L) h_cast_eq

lemma choose_relation (p i : ℕ) :
    (p + i).choose (i + 1) * (i + 1) = p * (p + i).choose i := by
  have h1 : (p + i).choose (i + 1) * (p + i + 1) = (p + i + 1).choose (i + 1) * p := by
    have h := choose_mul_succ_eq (p + i) (i + 1)
    have : p + i + 1 - (i + 1) = p := by omega
    rwa [this] at h
  have h2 : (p + i + 1) * (p + i).choose i = (p + i + 1).choose (i + 1) * (i + 1) := by
    exact succ_mul_choose_eq (p + i) i
  have h5 : (p + i).choose (i + 1) * (i + 1) * (p + i + 1) = p * (p + i).choose i * (p + i + 1) := by
    calc (p + i).choose (i + 1) * (i + 1) * (p + i + 1)
      _ = (p + i).choose (i + 1) * (p + i + 1) * (i + 1) := by ring
      _ = (p + i + 1).choose (i + 1) * p * (i + 1) := by rw [h1]
      _ = (p + i + 1).choose (i + 1) * (i + 1) * p := by ring
      _ = (p + i + 1) * (p + i).choose i * p := by rw [← h2]
      _ = p * (p + i).choose i * (p + i + 1) := by ring
  have h_pos : p + i + 1 > 0 := by omega
  exact Nat.eq_of_mul_eq_mul_right h_pos h5

lemma choose_relation_gt (p j : ℕ) (hp : p ≥ 1) (hj : j ≥ 1) :
    (2 * p + j - 1).choose (p + j) * (2 * p + j) = p * (2 * p + j).choose (p + j) := by
  have h := choose_mul_succ_eq (2 * p + j - 1) (p + j)
  have h_comm : 2 * p = p * 2 := mul_comm 2 p
  rw [h_comm] at h
  rw [h_comm]
  have h1 : p * 2 + j - 1 + 1 = p * 2 + j := by omega
  have h3 : p * 2 + j - (p + j) = p := by omega
  rw [h1] at h
  rw [h3] at h
  rw [mul_comm _ p] at h
  exact h

lemma choose_pi_i_mod_p (p i : ℕ) (hp : p.Prime) (hi : i < p - 1) :
    (p + i).choose i ≡ 1 [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have h : (p + i).choose i ≡ ((p + i) % p).choose (i % p) * ((p + i) / p).choose (i / p) [MOD p] := Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have h1 : (p + i) % p = i := by
    rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have h2 : i % p = i := Nat.mod_eq_of_lt (by omega)
  have h3 : (p + i) / p = 1 := by
    have hp_pos : p > 0 := hp.pos
    rw [Nat.add_div hp_pos]
    have h_mod : i % p = i := Nat.mod_eq_of_lt (by omega)
    have h_div : i / p = 0 := Nat.div_eq_of_lt (by omega)
    rw [h_mod, h_div]
    have : ¬ (p ≤ i) := by omega
    simp [this]
    exact Nat.div_self hp_pos
  have h4 : i / p = 0 := Nat.div_eq_of_lt (by omega)
  rw [h1, h2, h3, h4] at h
  have h5 : i.choose i = 1 := Nat.choose_self i
  have h6 : Nat.choose 1 0 = 1 := Nat.choose_zero_right 1
  rw [h5, h6] at h
  simp only [mul_one] at h
  exact h

lemma term_sq_eq (p i : ℕ) (hp : p.Prime) (hi : i < p - 1) :
    letI : NeZero (p ^ 3) := ⟨by
      have : p > 0 := hp.pos
      positivity⟩
    (((p + i : ℕ).choose (i + 1) : ZMod (p ^ 3)) ^ 2) = (p : ZMod (p ^ 3)) ^ 2 * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 := by
  have h_unit : IsUnit ((i + 1 : ℕ) : ZMod (p ^ 3)) := isUnit_of_lt p i 3 hp hi
  have h_relation := choose_relation p i
  have h_cast : (((p + i).choose (i + 1) * (i + 1) : ℕ) : ZMod (p ^ 3)) = (((p * (p + i).choose i) : ℕ) : ZMod (p ^ 3)) := by
    congr 1
  push_cast at h_cast
  have h_mul : ((p + i).choose (i + 1) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) * ((p + i).choose i : ZMod (p ^ 3)) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ := by
    have h_cast_succ : ((i + 1 : ℕ) : ZMod (p ^ 3)) = (i : ZMod (p ^ 3)) + 1 := by push_cast; rfl
    calc ((p + i).choose (i + 1) : ZMod (p ^ 3))
      _ = ((p + i).choose (i + 1) : ZMod (p ^ 3)) * (((i + 1 : ℕ) : ZMod (p ^ 3)) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹) := by rw [unit_mul_inv h_unit, mul_one]
      _ = (((p + i).choose (i + 1) : ZMod (p ^ 3)) * ((i + 1 : ℕ) : ZMod (p ^ 3))) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ := by ring
      _ = (((p + i).choose (i + 1) : ZMod (p ^ 3)) * ((i : ZMod (p ^ 3)) + 1)) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ := by rw [h_cast_succ]
      _ = (p : ZMod (p ^ 3)) * ((p + i).choose i : ZMod (p ^ 3)) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ := by rw [h_cast]
  have h_sq : ((p + i).choose (i + 1) : ZMod (p ^ 3)) ^ 2 = (p : ZMod (p ^ 3)) ^ 2 * ((p + i).choose i : ZMod (p ^ 3)) ^ 2 * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 := by
    rw [h_mul]
    ring
  rw [h_sq]
  have h_mod_p : (p + i).choose i ≡ 1 [MOD p] := choose_pi_i_mod_p p i hp hi
  let f : ZMod (p ^ 3) →+* ZMod p := ZMod.castHom (by
    have : p > 0 := hp.pos
    exact dvd_pow_self p (by omega)) (ZMod p)
  have h_cast_p : f ((p + i).choose i : ZMod (p ^ 3)) = 1 := by
    have h_eq : (((p + i).choose i : ℕ) : ZMod p) = 1 := by
      have h_eq2 : (((p + i).choose i : ℕ) : ZMod p) = (((1 : ℕ) : ZMod p)) := by
        rwa [ZMod.natCast_eq_natCast_iff]
      rw [h_eq2]
      exact Nat.cast_one
    calc f ((p + i).choose i : ZMod (p ^ 3))
      _ = (((p + i).choose i : ℕ) : ZMod p) := map_natCast f ((p + i).choose i)
      _ = 1 := h_eq
  have h_cast_sq : f (((p + i).choose i : ZMod (p ^ 3)) ^ 2) = 1 := by
    rw [f.map_pow, h_cast_p]
    ring
  have h_sub_cast : f (((p + i).choose i : ZMod (p ^ 3)) ^ 2 - 1) = 0 := by
    rw [f.map_sub, h_cast_sq]
    simp
  have h_cast_eq : (((((p + i).choose i : ZMod (p ^ 3)) ^ 2 - 1).cast : ZMod p) = 0) := by
    have h_eq : (((((p + i).choose i : ZMod (p ^ 3)) ^ 2 - 1).cast : ZMod p) = f (((p + i).choose i : ZMod (p ^ 3)) ^ 2 - 1)) := rfl
    rw [h_eq, h_sub_cast]
  have h_mul_zero := p_sq_mul_zero_of_cast_zero p hp (((p + i).choose i : ZMod (p ^ 3)) ^ 2 - 1) h_cast_eq
  have h_final : (p : ZMod (p ^ 3)) ^ 2 * ((p + i).choose i : ZMod (p ^ 3)) ^ 2 = (p : ZMod (p ^ 3)) ^ 2 := by
    linear_combination h_mul_zero
  rw [h_final]

lemma sum_term_sq_zero (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    letI : NeZero (p ^ 3) := ⟨by
      have : p > 0 := hp.pos
      positivity⟩
    (∑ k ∈ Finset.Ico 1 p, (((p + k - 1).choose k : ZMod (p ^ 3)) ^ 2)) = 0 := by
  have h_sum : (∑ k ∈ Finset.Ico 1 p, (((p + k - 1).choose k : ZMod (p ^ 3)) ^ 2)) =
      ∑ i ∈ Finset.range (p - 1), (((p + i).choose (i + 1) : ZMod (p ^ 3)) ^ 2) := by
    rw [range_eq_Ico]
    apply Finset.sum_bij (fun k _ => k - 1)
    · intro k hk
      rw [Finset.mem_Ico] at hk ⊢
      omega
    · intro k1 hk1 k2 hk2 h_eq
      rw [Finset.mem_Ico] at hk1 hk2
      omega
    · intro j hj
      rw [Finset.mem_Ico] at hj
      refine ⟨j + 1, by rw [Finset.mem_Ico]; omega, by omega⟩
    · intro k hk
      rw [Finset.mem_Ico] at hk
      congr 1
      congr 1
      congr 1
      · omega
      · omega
  rw [h_sum]
  have h_congr : (∑ i ∈ Finset.range (p - 1), (((p + i).choose (i + 1) : ZMod (p ^ 3)) ^ 2)) =
      ∑ i ∈ Finset.range (p - 1), ((p : ZMod (p ^ 3)) ^ 2 * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi_lt : i < p - 1 := Finset.mem_range.mp hi
    exact term_sq_eq p i hp hi_lt
  rw [h_congr, ← mul_sum]
  have h_cast_eq : (((∑ i ∈ Finset.range (p - 1), (((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2)).cast : ZMod p) = 0) := by
    let f : ZMod (p ^ 3) →+* ZMod p := ZMod.castHom (by
      have : p > 0 := hp.pos
      exact dvd_pow_self p (by omega)) (ZMod p)
    have h_map_eq : (((∑ i ∈ Finset.range (p - 1), (((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2)).cast : ZMod p) = f (∑ i ∈ Finset.range (p - 1), (((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2))) := by
      rw [ZMod.castHom_apply]
    rw [h_map_eq, map_sum]
    have h_simp_term : ∀ i ∈ Finset.range (p - 1), f (((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2) = ((i + 1 : ℕ) : ZMod p)⁻¹ ^ 2 := by
      intro i hi
      have hi_lt : i < p - 1 := Finset.mem_range.mp hi
      have hi_unit : IsUnit ((i + 1 : ℕ) : ZMod (p ^ 3)) := isUnit_of_lt p i 3 hp hi_lt
      rw [f.map_pow, ringHom_map_inv f ((i + 1 : ℕ) : ZMod (p ^ 3)) hi_unit, map_natCast f (i + 1)]
    rw [sum_congr rfl h_simp_term]
    have h_sum_Ico : (∑ i ∈ Finset.range (p - 1), (((i + 1 : ℕ) : ZMod p)⁻¹ ^ 2)) = ∑ j ∈ Finset.Ico 1 p, ((j : ZMod p)⁻¹ ^ 2) := by
      rw [range_eq_Ico]
      apply Finset.sum_bij (fun i _ => i + 1)
      · intro i hi
        rw [Finset.mem_Ico] at hi ⊢
        omega
      · intro i1 hi1 i2 hi2 h_eq
        omega
      · intro j hj
        rw [Finset.mem_Ico] at hj
        refine ⟨j - 1, by rw [Finset.mem_Ico]; omega, by omega⟩
      · intro i hi
        rfl
    rw [h_sum_Ico]
    exact sum_inv_sq_zero_ico p hp hp5
  have h_zero := p_sq_mul_zero_of_cast_zero p hp (∑ i ∈ Finset.range (p - 1), (((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2)) h_cast_eq
  rw [h_zero]

lemma choose_3p_minus_1_p_minus_1_eq_one (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : NeZero (p ^ 3) := ⟨by
      have : p > 0 := hp.pos
      positivity⟩
    ((3 * p - 1).choose (p - 1) : ZMod (p ^ 3)) = 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 3) := ⟨by
    have : p > 0 := hp.pos
    positivity⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have h_prod_eq : ((3 * p - 1).choose (p - 1) : ZMod (p ^ 3)) =
      ((List.range (p - 1)).map (fun i => 1 + (-3 * (p : ZMod (p ^ 3))) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)).prod := by
    rw [choose_3p_minus_1_p_minus_1_mod_p3 p hp (by omega)]
    congr 1
    ext i
    ring
  rw [h_prod_eq]
  let y : ZMod (p ^ 3) := -3 * (p : ZMod (p ^ 3))
  have hy3 : y ^ 3 = 0 := by
    have : y ^ 3 = -27 * (p : ZMod (p ^ 3)) ^ 3 := by ring
    rw [this]
    have h_p3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
      have h_eq : ((p ^ 3 : ℕ) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) ^ 3 := by push_cast; rfl
      rw [← h_eq, ZMod.natCast_self]
    rw [h_p3, mul_zero]
  let L : List (ZMod (p ^ 3)) := (List.range (p - 1)).map (fun i => ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)
  have h_comp : ((List.range (p - 1)).map (fun i => 1 + (-3 * (p : ZMod (p ^ 3))) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)) = L.map (fun x => 1 + y * x) := by
    change ((List.range (p - 1)).map (fun i => 1 + (-3 * (p : ZMod (p ^ 3))) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)) = ((List.range (p - 1)).map (fun i => ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)).map (fun x => 1 + y * x)
    simp only [List.map_map]
    rfl
  rw [h_comp]
  rw [List.prod_one_add_y_mul_eq3 y hy3 L]
  have h_L_sum : L.sum = ∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹ := by
    rw [List.list_sum_range_eq_finset_sum_range]
    rw [range_eq_Ico]
    apply Finset.sum_bij (fun i _ => i + 1)
    · intro i hi
      rw [Finset.mem_Ico] at hi ⊢
      omega
    · intro i1 hi1 i2 hi2 h_eq
      omega
    · intro j hj
      rw [Finset.mem_Ico] at hj
      refine ⟨j - 1, by rw [Finset.mem_Ico]; omega, by omega⟩
    · intro i hi
      rfl
  have h_y_L_sum : y * L.sum = 0 := by
    rw [h_L_sum]
    have h_p_sum : (p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹) = 0 := sum_inv_p_mul_zero p hp hp5
    calc y * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹)
      _ = -3 * ((p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹)) := by ring
      _ = -3 * 0 := by rw [h_p_sum]
      _ = 0 := mul_zero _
  have h_y2_sum_pairs : y ^ 2 * List.sum_pairs L = 0 := by
    have h_p2_sum_pairs : (p : ZMod (p ^ 3)) ^ 2 * List.sum_pairs L = 0 := sum_pairs_p_sq_mul_zero p hp hp5
    calc y ^ 2 * List.sum_pairs L
      _ = 9 * ((p : ZMod (p ^ 3)) ^ 2 * List.sum_pairs L) := by ring
      _ = 9 * 0 := by rw [h_p2_sum_pairs]
      _ = 0 := mul_zero _
  rw [h_y_L_sum, h_y2_sum_pairs, add_zero, add_zero]


lemma choose_2p_minus_1_p_minus_1_eq_one (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : NeZero (p ^ 3) := ⟨by
      have : p > 0 := hp.pos
      positivity⟩
    ((2 * p - 1).choose (p - 1) : ZMod (p ^ 3)) = 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 3) := ⟨by
    have : p > 0 := hp.pos
    positivity⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have h_prod_eq : ((2 * p - 1).choose (p - 1) : ZMod (p ^ 3)) =
      ((List.range (p - 1)).map (fun i => 1 + (-2 * (p : ZMod (p ^ 3))) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)).prod := by
    rw [choose_2p_minus_1_p_minus_1_mod_p3 p hp (by omega)]
    congr 1
    ext i
    ring
  rw [h_prod_eq]
  let y : ZMod (p ^ 3) := -2 * (p : ZMod (p ^ 3))
  have hy3 : y ^ 3 = 0 := by
    have : y ^ 3 = -8 * (p : ZMod (p ^ 3)) ^ 3 := by ring
    rw [this]
    have h_p3 : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
      have h_eq : ((p ^ 3 : ℕ) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) ^ 3 := by push_cast; rfl
      rw [← h_eq, ZMod.natCast_self]
    rw [h_p3, mul_zero]
  let L : List (ZMod (p ^ 3)) := (List.range (p - 1)).map (fun i => ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)
  have h_comp : ((List.range (p - 1)).map (fun i => 1 + (-2 * (p : ZMod (p ^ 3))) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)) = L.map (fun x => 1 + y * x) := by
    change ((List.range (p - 1)).map (fun i => 1 + (-2 * (p : ZMod (p ^ 3))) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)) = ((List.range (p - 1)).map (fun i => ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹)).map (fun x => 1 + y * x)
    simp only [List.map_map]
    rfl
  rw [h_comp]
  rw [List.prod_one_add_y_mul_eq3 y hy3 L]
  have h_L_sum : L.sum = ∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹ := by
    rw [List.list_sum_range_eq_finset_sum_range]
    rw [range_eq_Ico]
    apply Finset.sum_bij (fun i _ => i + 1)
    · intro i hi
      rw [Finset.mem_Ico] at hi ⊢
      omega
    · intro i1 hi1 i2 hi2 h_eq
      omega
    · intro j hj
      rw [Finset.mem_Ico] at hj
      refine ⟨j - 1, by rw [Finset.mem_Ico]; omega, by omega⟩
    · intro i hi
      rfl
  have h_y_L_sum : y * L.sum = 0 := by
    rw [h_L_sum]
    have h_p_sum : (p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹) = 0 := sum_inv_p_mul_zero p hp hp5
    calc y * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹)
      _ = -2 * ((p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Ico 1 p, (j : ZMod (p ^ 3))⁻¹)) := by ring
      _ = -2 * 0 := by rw [h_p_sum]
      _ = 0 := mul_zero _
  have h_y2_sum_pairs : y ^ 2 * List.sum_pairs L = 0 := by
    have h_p2_sum_pairs : (p : ZMod (p ^ 3)) ^ 2 * List.sum_pairs L = 0 := sum_pairs_p_sq_mul_zero p hp hp5
    calc y ^ 2 * List.sum_pairs L
      _ = 4 * ((p : ZMod (p ^ 3)) ^ 2 * List.sum_pairs L) := by ring
      _ = 4 * 0 := by rw [h_p2_sum_pairs]
      _ = 0 := mul_zero _
  rw [h_y_L_sum, h_y2_sum_pairs, add_zero, add_zero]



lemma choose_gt_mod_p (p j : ℕ) (hp : p.Prime) (hj1 : j ≥ 1) (hj2 : j < p) :
    (2 * p + j).choose (p + j) ≡ 2 [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have h : (2 * p + j).choose (p + j) ≡
    ((2 * p + j) % p).choose ((p + j) % p) * ((2 * p + j) / p).choose ((p + j) / p) [MOD p] := Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have h1 : (2 * p + j) % p = j := by
    have h_eq : 2 * p + j = j + p * 2 := by ring
    rw [h_eq, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hj2
  have h2 : (p + j) % p = j := by
    have h_eq : p + j = j + p * 1 := by ring
    rw [h_eq, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hj2
  have h3 : (2 * p + j) / p = 2 := by
    have h_eq : 2 * p + j = j + p * 2 := by ring
    rw [h_eq]
    rw [Nat.add_mul_div_left j 2 (by omega)]
    have : j / p = 0 := Nat.div_eq_of_lt hj2
    rw [this, Nat.zero_add]
  have h4 : (p + j) / p = 1 := by
    have h_eq : p + j = j + p * 1 := by ring
    rw [h_eq]
    rw [Nat.add_mul_div_left j 1 (by omega)]
    have : j / p = 0 := Nat.div_eq_of_lt hj2
    rw [this, Nat.zero_add]
  have h5 : j.choose j = 1 := Nat.choose_self j
  have h6 : Nat.choose 2 1 = 2 := rfl
  rw [h1, h2, h3, h4, h5, h6] at h
  have h_mul : 1 * 2 = 2 := rfl
  rw [h_mul] at h
  exact h

lemma term_sq_eq_gt (p j : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (hj1 : j ≥ 1) (hj2 : j < p) :
    letI : NeZero (p ^ 3) := ⟨by
      have : p > 0 := hp.pos
      positivity⟩
    (((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) ^ 2) = (p : ZMod (p ^ 3)) ^ 2 * 4 * (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2) := by
  have h_unit : IsUnit ((2 * p + j : ℕ) : ZMod (p ^ 3)) := by
    rw [ZMod.isUnit_iff_coprime]
    have h_coprime : (2 * p + j).Coprime (p ^ 3) := by
      have h_cop : (2 * p + j).Coprime p := by
        rw [Nat.coprime_comm]
        apply hp.coprime_iff_not_dvd.mpr
        intro h_dvd
        have h_dvd_j : p ∣ j := by
          obtain ⟨k, hk⟩ := h_dvd
          use k - 2
          have hk2 : k ≥ 2 := by
            by_contra! hc
            interval_cases k
            · omega
            · omega
          have h_sub : p * (k - 2) = p * k - p * 2 := Nat.mul_sub_left_distrib p k 2
          rw [h_sub]
          omega
        have : p ≤ j := Nat.le_of_dvd hj1 h_dvd_j
        omega
      exact h_cop.pow_right 3
    exact h_coprime
  have h_relation := choose_relation_gt p j (by omega) hj1
  have h_cast : (((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) * ((2 * p + j : ℕ) : ZMod (p ^ 3))) = (p : ZMod (p ^ 3)) * ((2 * p + j).choose (p + j) : ZMod (p ^ 3)) := by
    have h_cast_mul : (((2 * p + j - 1).choose (p + j) * (2 * p + j) : ℕ) : ZMod (p ^ 3)) = (((p * (2 * p + j).choose (p + j)) : ℕ) : ZMod (p ^ 3)) := by
      congr 1
    rw [Nat.cast_mul, Nat.cast_mul] at h_cast_mul
    exact h_cast_mul
  have h_mul : ((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) * ((2 * p + j).choose (p + j) : ZMod (p ^ 3)) * ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ := by
    calc ((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3))
      _ = ((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) * (((2 * p + j : ℕ) : ZMod (p ^ 3)) * ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹) := by rw [unit_mul_inv h_unit, mul_one]
      _ = (((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) * ((2 * p + j : ℕ) : ZMod (p ^ 3))) * ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ := by ring
      _ = (p : ZMod (p ^ 3)) * ((2 * p + j).choose (p + j) : ZMod (p ^ 3)) * ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ := by rw [h_cast]
  have h_sq : ((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) ^ 2 = (p : ZMod (p ^ 3)) ^ 2 * ((2 * p + j).choose (p + j) : ZMod (p ^ 3)) ^ 2 * ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 := by
    rw [h_mul]
    ring
  have h_mod_p := choose_gt_mod_p p j hp hj1 hj2
  let f : ZMod (p ^ 3) →+* ZMod p := ZMod.castHom (by
    have : p > 0 := hp.pos
    exact dvd_pow_self p (by omega)) (ZMod p)
  have h_cast_p : f ((2 * p + j).choose (p + j) : ZMod (p ^ 3)) = 2 := by
    have h_eq : (((2 * p + j).choose (p + j) : ℕ) : ZMod p) = 2 := by
      have h_eq2 : (((2 * p + j).choose (p + j) : ℕ) : ZMod p) = (((2 : ℕ) : ZMod p)) := by
        rwa [ZMod.natCast_eq_natCast_iff]
      rw [h_eq2]
      rfl
    calc f ((2 * p + j).choose (p + j) : ZMod (p ^ 3))
      _ = (((2 * p + j).choose (p + j) : ℕ) : ZMod p) := map_natCast f ((2 * p + j).choose (p + j))
      _ = 2 := h_eq
  have h_cast_sq : f (((2 * p + j).choose (p + j) : ZMod (p ^ 3)) ^ 2) = 4 := by
    rw [f.map_pow, h_cast_p]
    ring
  have h_sub_cast : f (((2 * p + j).choose (p + j) : ZMod (p ^ 3)) ^ 2 - 4) = 0 := by
    rw [f.map_sub, h_cast_sq, map_ofNat f 4, sub_self]
  have h_cast_eq : (((((2 * p + j).choose (p + j) : ZMod (p ^ 3)) ^ 2 - 4).cast : ZMod p) = 0) := by
    have h_eq : (((((2 * p + j).choose (p + j) : ZMod (p ^ 3)) ^ 2 - 4).cast : ZMod p) = f (((2 * p + j).choose (p + j) : ZMod (p ^ 3)) ^ 2 - 4)) := rfl
    rw [h_eq, h_sub_cast]
  have h_mul_zero := p_sq_mul_zero_of_cast_zero p hp (((2 * p + j).choose (p + j) : ZMod (p ^ 3)) ^ 2 - 4) h_cast_eq
  have h_final : (p : ZMod (p ^ 3)) ^ 2 * ((2 * p + j).choose (p + j) : ZMod (p ^ 3)) ^ 2 = (p : ZMod (p ^ 3)) ^ 2 * 4 := by
    linear_combination h_mul_zero
  have h_unit_j : IsUnit ((j : ℕ) : ZMod (p ^ 3)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact coprime_p_pow p j hp hj1 hj2 3
  have h_inv_cast : f ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ = f ((j : ℕ) : ZMod (p ^ 3))⁻¹ := by
    have h_cast_pj : f ((2 * p + j : ℕ) : ZMod (p ^ 3)) = f ((j : ℕ) : ZMod (p ^ 3)) := by
      rw [map_natCast f (2 * p + j), map_natCast f j]
      have h_eq : ((2 * p + j : ℕ) : ZMod p) = ((j : ℕ) : ZMod p) := by
        push_cast
        have : (p : ZMod p) = 0 := ZMod.natCast_self p
        calc (2 * (p : ZMod p) + j : ZMod p)
          _ = 2 * 0 + j := by rw [this]
          _ = j := by ring
      exact h_eq
    rw [ringHom_map_inv f ((2 * p + j : ℕ) : ZMod (p ^ 3)) h_unit, ringHom_map_inv f ((j : ℕ) : ZMod (p ^ 3)) h_unit_j, h_cast_pj]
  have h_cast_eq2 : (((((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 - ((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2).cast : ZMod p) = 0) := by
    have h_eq : (((((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 - ((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2).cast : ZMod p) = f ((((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 - ((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2))) := rfl
    rw [h_eq, f.map_sub, f.map_pow, f.map_pow, h_inv_cast]
    simp
  have h_mul_zero2 := p_sq_mul_zero_of_cast_zero p hp (((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 - ((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2) h_cast_eq2
  have h_inv_eq : (p : ZMod (p ^ 3)) ^ 2 * ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 = (p : ZMod (p ^ 3)) ^ 2 * ((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 := by
    linear_combination h_mul_zero2
  calc ((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) ^ 2
    _ = (p : ZMod (p ^ 3)) ^ 2 * ((2 * p + j).choose (p + j) : ZMod (p ^ 3)) ^ 2 * ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 := h_sq
    _ = (p : ZMod (p ^ 3)) ^ 2 * 4 * ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 := by rw [h_final]
    _ = 4 * ((p : ZMod (p ^ 3)) ^ 2 * ((2 * p + j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2) := by ring
    _ = 4 * ((p : ZMod (p ^ 3)) ^ 2 * ((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2) := by rw [h_inv_eq]
    _ = (p : ZMod (p ^ 3)) ^ 2 * 4 * ((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 := by ring

lemma sum_term_sq_zero_gt (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    letI : NeZero (p ^ 3) := ⟨by
      have : p > 0 := hp.pos
      positivity⟩
    (∑ j ∈ Finset.Ico 1 p, (((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) ^ 2)) = 0 := by
  have h_congr : (∑ j ∈ Finset.Ico 1 p, (((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) ^ 2)) =
      ∑ j ∈ Finset.Ico 1 p, ((p : ZMod (p ^ 3)) ^ 2 * 4 * (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact term_sq_eq_gt p j hp hp5 hj.1 hj.2
  have h_congr_mul : (∑ j ∈ Finset.Ico 1 p, (((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) ^ 2)) =
      (p : ZMod (p ^ 3)) ^ 2 * 4 * (∑ j ∈ Finset.Ico 1 p, (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2)) := by
    rw [h_congr, ← mul_sum]
  have h_cast_eq : (((4 * ∑ j ∈ Finset.Ico 1 p, (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2)).cast : ZMod p) = 0) := by
    let f : ZMod (p ^ 3) →+* ZMod p := ZMod.castHom (by
      have : p > 0 := hp.pos
      exact dvd_pow_self p (by omega)) (ZMod p)
    have h_map_eq : (((4 * ∑ j ∈ Finset.Ico 1 p, (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2)).cast : ZMod p) = f (4 * ∑ j ∈ Finset.Ico 1 p, (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2))) := by
      rw [ZMod.castHom_apply]
    rw [h_map_eq, f.map_mul, map_ofNat f 4, map_sum]
    have h_simp_term : ∀ j ∈ Finset.Ico 1 p, f (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2) = ((j : ZMod p)⁻¹ ^ 2) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj_unit : IsUnit ((j : ℕ) : ZMod (p ^ 3)) := by
        rw [ZMod.isUnit_iff_coprime]
        exact coprime_p_pow p j hp hj.1 hj.2 3
      rw [f.map_pow, ringHom_map_inv f ((j : ℕ) : ZMod (p ^ 3)) hj_unit, map_natCast f j]
    rw [sum_congr rfl h_simp_term]
    rw [sum_inv_sq_zero_ico p hp hp5]
    ring
  have h_zero := p_sq_mul_zero_of_cast_zero p hp (4 * ∑ j ∈ Finset.Ico 1 p, (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2)) h_cast_eq
  calc (∑ j ∈ Finset.Ico 1 p, (((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) ^ 2))
    _ = (p : ZMod (p ^ 3)) ^ 2 * 4 * (∑ j ∈ Finset.Ico 1 p, (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2)) := h_congr_mul
    _ = (p : ZMod (p ^ 3)) ^ 2 * (4 * (∑ j ∈ Finset.Ico 1 p, (((j : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2))) := by ring
    _ = 0 := h_zero

theorem sum_partition (p : ℕ) (hp3 : p ≥ 3) (F : ℕ → ZMod (p ^ 3)) :
    (∑ k ∈ range (2 * p + 1), F k) =
    F 0 + (∑ k ∈ Ico 1 p, F k) + F p + (∑ k ∈ Ico (p + 1) (2 * p), F k) + F (2 * p) := by
  have h1 : (∑ k ∈ range (2 * p + 1), F k) = (∑ k ∈ range (2 * p), F k) + F (2 * p) := sum_range_succ F (2 * p)
  have h2 : (∑ k ∈ range (2 * p), F k) = (∑ k ∈ range (p + 1), F k) + (∑ k ∈ Ico (p + 1) (2 * p), F k) := by
    rw [← sum_union]
    · congr 1
      ext x
      simp only [mem_union, mem_range, mem_Ico]
      omega
    · rw [Finset.disjoint_iff_ne]
      intro x hx y hy h_eq
      simp only [mem_range] at hx
      simp only [mem_Ico] at hy
      omega
  have h3 : (∑ k ∈ range (p + 1), F k) = (∑ k ∈ range p, F k) + F p := sum_range_succ F p
  have h4 : (∑ k ∈ range p, F k) = F 0 + (∑ k ∈ Ico 1 p, F k) := by
    have h_union : range p = range 1 ∪ Ico 1 p := by
      ext x
      simp only [mem_union, mem_range, mem_Ico]
      omega
    have h_disj : Disjoint (range 1) (Ico 1 p) := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy h_eq
      simp only [mem_range] at hx
      simp only [mem_Ico] at hy
      omega
    rw [h_union, sum_union h_disj, sum_range_one]
  rw [h1, h2, h3, h4]


theorem sum_partition_z (p : ℕ) (hp3 : p ≥ 3) (F : ℕ → ℤ) :
    (∑ k ∈ range (2 * p + 1), F k) =
    F 0 + (∑ k ∈ Ico 1 p, F k) + F p + (∑ k ∈ Ico (p + 1) (2 * p), F k) + F (2 * p) := by
  have h1 : (∑ k ∈ range (2 * p + 1), F k) = (∑ k ∈ range (2 * p), F k) + F (2 * p) := sum_range_succ F (2 * p)
  have h2 : (∑ k ∈ range (2 * p), F k) = (∑ k ∈ range (p + 1), F k) + (∑ k ∈ Ico (p + 1) (2 * p), F k) := by
    rw [← sum_union]
    · congr 1
      ext x
      simp only [mem_union, mem_range, mem_Ico]
      omega
    · rw [Finset.disjoint_iff_ne]
      intro x hx y hy h_eq
      simp only [mem_range] at hx
      simp only [mem_Ico] at hy
      omega
  have h3 : (∑ k ∈ range (p + 1), F k) = (∑ k ∈ range p, F k) + F p := sum_range_succ F p
  have h4 : (∑ k ∈ range p, F k) = F 0 + (∑ k ∈ Ico 1 p, F k) := by
    have h_union : range p = range 1 ∪ Ico 1 p := by
      ext x
      simp only [mem_union, mem_range, mem_Ico]
      omega
    have h_disj : Disjoint (range 1) (Ico 1 p) := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy h_eq
      simp only [mem_range] at hx
      simp only [mem_Ico] at hy
      omega
    rw [h_union, sum_union h_disj, sum_range_one]
  rw [h1, h2, h3, h4]



lemma S1_mod_p3 (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    letI : NeZero (p ^ 3) := ⟨by
      have : p > 0 := hp.pos
      positivity⟩
    ((∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k : ZMod (p ^ 3))) = 3) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 3) := ⟨by
    have : p > 0 := hp.pos
    positivity⟩
  have h1 : (∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k : ZMod (p ^ 3))) = ((3 * p).choose p : ZMod (p ^ 3)) := by
    rw [← Nat.cast_sum]
    congr 1
    exact S1_eq_choose p (by omega)
  rw [h1]
  rw [choose_3p_p p (by omega)]
  push_cast
  rw [choose_3p_minus_1_p_minus_1_eq_one p hp hp5]
  ring


lemma S2_mod_p3 (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    letI : NeZero (p ^ 3) := ⟨by
      have : p > 0 := hp.pos
      positivity⟩
    ((∑ k ∈ range (2 * p + 1), (((p + k - 1).choose k : ZMod (p ^ 3)) ^ 2)) = 3) := by
  have hp3 : p ≥ 3 := by omega
  let F : ℕ → ZMod (p ^ 3) := fun k => (((p + k - 1).choose k : ZMod (p ^ 3)) ^ 2)
  have h_part := sum_partition p hp3 F
  rw [h_part]
  have h_rw1 : F 0 = (((p - 1).choose 0 : ZMod (p ^ 3)) ^ 2) := rfl
  have h_rw3 : F p = (((2 * p - 1).choose p : ZMod (p ^ 3)) ^ 2) := by
    dsimp [F]
    have : p + p - 1 = 2 * p - 1 := by omega
    rw [this]
  have h_rw5 : F (2 * p) = (((3 * p - 1).choose (2 * p) : ZMod (p ^ 3)) ^ 2) := by
    dsimp [F]
    have : p + 2 * p - 1 = 3 * p - 1 := by omega
    rw [this]
  rw [h_rw1, h_rw3, h_rw5]
  have h_term1 : (((p - 1).choose 0 : ZMod (p ^ 3)) ^ 2) = 1 := by
    simp
  have h_term2 : (∑ k ∈ Ico 1 p, (((p + k - 1).choose k : ZMod (p ^ 3)) ^ 2)) = 0 := sum_term_sq_zero p hp hp5
  have h_term3 : (((2 * p - 1).choose p : ZMod (p ^ 3)) ^ 2) = 1 := by
    have h_symm : (2 * p - 1).choose p = (2 * p - 1).choose (p - 1) := by
      rw [← Nat.choose_symm]
      congr 1; omega
      omega
    rw [h_symm]
    push_cast
    rw [choose_2p_minus_1_p_minus_1_eq_one p hp hp5]
    ring
  have h_term4 : (∑ k ∈ Ico (p + 1) (2 * p), (((p + k - 1).choose k : ZMod (p ^ 3)) ^ 2)) = 0 := by
    have h_sum : (∑ k ∈ Ico (p + 1) (2 * p), (((p + k - 1).choose k : ZMod (p ^ 3)) ^ 2)) =
        ∑ j ∈ Ico 1 p, (((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) ^ 2) := by
      apply Finset.sum_bij (fun k _ => k - p)
      · intro k hk
        rw [Finset.mem_Ico] at hk ⊢
        omega
      · intro k1 hk1 k2 hk2 h_eq
        rw [Finset.mem_Ico] at hk1 hk2
        omega
      · intro j hj
        rw [Finset.mem_Ico] at hj
        refine ⟨j + p, by rw [Finset.mem_Ico]; omega, by omega⟩
      · intro k hk
        rw [Finset.mem_Ico] at hk
        dsimp [F]
        congr 3
        · omega
        · omega
    rw [h_sum]
    exact sum_term_sq_zero_gt p hp hp5
  have h_term5 : (((3 * p - 1).choose (2 * p) : ZMod (p ^ 3)) ^ 2) = 1 := by
    have h_symm : (3 * p - 1).choose (2 * p) = (3 * p - 1).choose (p - 1) := by
      rw [← Nat.choose_symm]
      congr 1; omega
      omega
    rw [h_symm]
    push_cast
    rw [choose_3p_minus_1_p_minus_1_eq_one p hp hp5]
    ring
  rw [h_term1, h_term2, h_term3, h_term4, h_term5]
  ring


lemma C_sq_mod_p5 (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    (((3 * p - 1).choose (p - 1) : ℤ) - 1)^2 ≡ 0 [ZMOD (p : ℤ)^5] := by
  have h_zmod : ((3 * p - 1).choose (p - 1) : ZMod (p ^ 3)) = 1 := choose_3p_minus_1_p_minus_1_eq_one p hp hp5
  have h_nat : (3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3] := by
    have h_eq : ((3 * p - 1).choose (p - 1) : ZMod (p ^ 3)) = ((1 : ℕ) : ZMod (p ^ 3)) := by
      rw [h_zmod]
      push_cast
      rfl
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h_eq
  have h_int : (((3 * p - 1).choose (p - 1) : ℤ) : ℤ) ≡ 1 [ZMOD (p : ℤ)^3] := by
    exact Int.natCast_modEq_iff.mpr h_nat
  have h_mod : (((3 * p - 1).choose (p - 1) : ℤ) - 1) ≡ 0 [ZMOD (p : ℤ)^3] := by
    have h_sub : (((3 * p - 1).choose (p - 1) : ℤ) - 1) ≡ 1 - 1 [ZMOD (p : ℤ)^3] := by
      exact Int.ModEq.sub_right 1 h_int
    exact h_sub
  have h_dvd : (p : ℤ)^3 ∣ (((3 * p - 1).choose (p - 1) : ℤ) - 1) := Int.modEq_zero_iff_dvd.mp h_mod
  have h_dvd2 : (p : ℤ)^5 ∣ (((3 * p - 1).choose (p - 1) : ℤ) - 1)^2 := by
    rcases h_dvd with ⟨k, hk⟩
    use k^2 * (p : ℤ)
    rw [hk]
    ring
  exact Int.modEq_zero_iff_dvd.mpr h_dvd2

lemma D_sq_mod_p5 (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    (((2 * p - 1).choose (p - 1) : ℤ) - 1)^2 ≡ 0 [ZMOD (p : ℤ)^5] := by
  have h_zmod : ((2 * p - 1).choose (p - 1) : ZMod (p ^ 3)) = 1 := choose_2p_minus_1_p_minus_1_eq_one p hp hp5
  have h_nat : (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3] := by
    have h_eq : ((2 * p - 1).choose (p - 1) : ZMod (p ^ 3)) = ((1 : ℕ) : ZMod (p ^ 3)) := by
      rw [h_zmod]
      push_cast
      rfl
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h_eq
  have h_int : (((2 * p - 1).choose (p - 1) : ℤ) : ℤ) ≡ 1 [ZMOD (p : ℤ)^3] := by
    exact Int.natCast_modEq_iff.mpr h_nat
  have h_mod : (((2 * p - 1).choose (p - 1) : ℤ) - 1) ≡ 0 [ZMOD (p : ℤ)^3] := by
    have h_sub : (((2 * p - 1).choose (p - 1) : ℤ) - 1) ≡ 1 - 1 [ZMOD (p : ℤ)^3] := by
      exact Int.ModEq.sub_right 1 h_int
    exact h_sub
  have h_dvd : (p : ℤ)^3 ∣ (((2 * p - 1).choose (p - 1) : ℤ) - 1) := Int.modEq_zero_iff_dvd.mp h_mod
  have h_dvd2 : (p : ℤ)^5 ∣ (((2 * p - 1).choose (p - 1) : ℤ) - 1)^2 := by
    rcases h_dvd with ⟨k, hk⟩
    use k^2 * (p : ℤ)
    rw [hk]
    ring
  exact Int.modEq_zero_iff_dvd.mpr h_dvd2


lemma sum_term_sq_zero_gt_ico (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    letI : NeZero (p ^ 3) := ⟨by
      have : p > 0 := hp.pos
      positivity⟩
    (∑ k ∈ Finset.Ico (p + 1) (2 * p), (((p + k - 1).choose k : ZMod (p ^ 3)) ^ 2)) = 0 := by
  haveI : NeZero (p ^ 3) := ⟨by
    have : p > 0 := hp.pos
    positivity⟩
  have h_sum : (∑ k ∈ Finset.Ico (p + 1) (2 * p), (((p + k - 1).choose k : ZMod (p ^ 3)) ^ 2)) =
      ∑ j ∈ Finset.Ico 1 p, (((2 * p + j - 1).choose (p + j) : ZMod (p ^ 3)) ^ 2) := by
    apply Finset.sum_bij (fun k _ => k - p)
    · intro k hk
      rw [Finset.mem_Ico] at hk ⊢
      omega
    · intro k1 hk1 k2 hk2 h_eq
      rw [Finset.mem_Ico] at hk1 hk2
      omega
    · intro j hj
      rw [Finset.mem_Ico] at hj
      refine ⟨j + p, by rw [Finset.mem_Ico]; omega, by omega⟩
    · intro k hk
      rw [Finset.mem_Ico] at hk
      congr 3
      · omega
      · omega
  rw [h_sum]
  exact sum_term_sq_zero_gt p hp hp5



set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/--
Conjecture 1: $a(p) \equiv a(1) \pmod{p^5}$ for all primes $p \ge 3$.
-/
theorem A357674_conjecture_1 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  by_cases h : p ≤ 300
  · interval_cases p
    all_goals
      first
      | decide
      | exfalso; revert hp; decide
  · -- For p > 300, we proceed by utilizing the algebraic reduction.
    -- We show that S1 ≡ 3 [ZMOD p^3], S2 ≡ 3 [ZMOD p^3], and 3 * S2 + 4 * S1 ≡ 21 [ZMOD p^5] algebraically.
    have h_gt : p > 300 := by omega
    have hp5 : p ≥ 5 := by omega
    -- The reductions h1, h2, h3 can be constructed algebraically using the algebraic_reduction lemma.
    have h1 : ((∑ k ∈ range (2 * p + 1), (p + k - 1).choose k : ℕ) : ℤ) ≡ 3 [ZMOD (p : ℤ)^3] := by
      have h1_zmod : (∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k : ZMod (p^3))) = 3 := S1_mod_p3 p hp hp5
      have h1_nat : (∑ k ∈ range (2 * p + 1), (p + k - 1).choose k) ≡ 3 [MOD p^3] := by
        have h_eq : (∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k : ZMod (p^3))) = ((3 : ℕ) : ZMod (p^3)) := h1_zmod
        have h_cast : (∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k : ZMod (p^3))) = ((∑ k ∈ range (2 * p + 1), (p + k - 1).choose k : ℕ) : ZMod (p^3)) := by
          push_cast
          rfl
        rw [h_cast] at h_eq
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h_eq
      exact Int.natCast_modEq_iff.mpr h1_nat

    have h2 : ((∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k)^2 : ℕ) : ℤ) ≡ 3 [ZMOD (p : ℤ)^3] := by
      have h2_zmod : (∑ k ∈ range (2 * p + 1), (((p + k - 1).choose k : ZMod (p^3))^2)) = 3 := S2_mod_p3 p hp hp5
      have h2_nat : (∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k)^2) ≡ 3 [MOD p^3] := by
        have h_eq : (∑ k ∈ range (2 * p + 1), (((p + k - 1).choose k : ZMod (p^3))^2)) = ((3 : ℕ) : ZMod (p^3)) := h2_zmod
        have h_cast : (∑ k ∈ range (2 * p + 1), (((p + k - 1).choose k : ZMod (p^3))^2)) = ((∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k)^2 : ℕ) : ZMod (p^3)) := by
          push_cast
          rfl
        rw [h_cast] at h_eq
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h_eq
      exact Int.natCast_modEq_iff.mpr h2_nat

    have h3 : 3 * ((∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k)^2 : ℕ) : ℤ) + 4 * ((∑ k ∈ range (2 * p + 1), (p + k - 1).choose k : ℕ) : ℤ) ≡ 21 [ZMOD (p : ℤ)^5] := by
      let S1_z := ((∑ k ∈ range (2 * p + 1), (p + k - 1).choose k : ℕ) : ℤ)
      let S2_z := ((∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k)^2 : ℕ) : ℤ)
      have h_S1_eq : S1_z = 3 * ((3 * p - 1).choose (p - 1) : ℤ) := by
        dsimp [S1_z]
        rw [S1_eq_choose p (by omega)]
        rw [choose_3p_p p (by omega)]
        push_cast
        rfl
      have h_S2_part : S2_z =
          (((p - 1).choose 0 : ℕ) : ℤ)^2 +
          (∑ k ∈ Ico 1 p, (((p + k - 1).choose k : ℕ) : ℤ)^2) +
          (((2 * p - 1).choose p : ℕ) : ℤ)^2 +
          (∑ k ∈ Ico (p + 1) (2 * p), (((p + k - 1).choose k : ℕ) : ℤ)^2) +
          (((3 * p - 1).choose (2 * p) : ℕ) : ℤ)^2 := by
        have h_cast : S2_z = ∑ k ∈ range (2 * p + 1), (((p + k - 1).choose k : ℕ) : ℤ)^2 := by
          dsimp [S2_z]
          push_cast
          rfl
        rw [h_cast]
        have h_part := sum_partition_z p (by omega) (fun k ↦ (((p + k - 1).choose k : ℕ) : ℤ)^2)
        have h_rw2 : (((p + p - 1).choose p : ℕ) : ℤ)^2 = (((2 * p - 1).choose p : ℕ) : ℤ)^2 := by
          congr 3; omega
        have h_rw3 : (((p + 2 * p - 1).choose (2 * p) : ℕ) : ℤ)^2 = (((3 * p - 1).choose (2 * p) : ℕ) : ℤ)^2 := by
          congr 3; omega
        rw [h_rw2, h_rw3] at h_part
        exact h_part
      have h_symm1 : (2 * p - 1).choose p = (2 * p - 1).choose (p - 1) := by
        rw [← Nat.choose_symm]
        congr 1; omega
        omega
      have h_symm2 : (3 * p - 1).choose (2 * p) = (3 * p - 1).choose (p - 1) := by
        rw [← Nat.choose_symm]
        congr 1; omega
        omega
      have h_S2_eq : S2_z =
          1 +
          (∑ k ∈ Ico 1 p, (((p + k - 1).choose k : ℕ) : ℤ)^2) +
          (((2 * p - 1).choose (p - 1) : ℕ) : ℤ)^2 +
          (∑ k ∈ Ico (p + 1) (2 * p), (((p + k - 1).choose k : ℕ) : ℤ)^2) +
          (((3 * p - 1).choose (p - 1) : ℕ) : ℤ)^2 := by
        rw [h_S2_part]
        rw [h_symm1, h_symm2]
        have h_0 : (p - 1).choose 0 = 1 := Nat.choose_zero_right (p - 1)
        rw [h_0]
        rfl
      let A : ℤ := ∑ k ∈ Ico 1 p, (((p + k - 1).choose k : ℕ) : ℤ)^2
      let B : ℤ := ∑ k ∈ Ico (p + 1) (2 * p), (((p + k - 1).choose k : ℕ) : ℤ)^2
      let C : ℤ := ((3 * p - 1).choose (p - 1) : ℤ) - 1
      let D : ℤ := ((2 * p - 1).choose (p - 1) : ℤ) - 1
      have h_C_val : ((3 * p - 1).choose (p - 1) : ℤ) = C + 1 := by omega
      have h_D_val : ((2 * p - 1).choose (p - 1) : ℤ) = D + 1 := by omega
      have h_C_sq : (C)^2 ≡ 0 [ZMOD (p : ℤ)^5] := by
        exact C_sq_mod_p5 p hp hp5
      have h_D_sq : (D)^2 ≡ 0 [ZMOD (p : ℤ)^5] := by
        exact D_sq_mod_p5 p hp hp5
      have h_algebraic : 3 * S2_z + 4 * S1_z - 21 = 3 * (A + B + 2 * D + 6 * C) + 3 * D^2 + 3 * C^2 := by
        rw [h_S1_eq, h_S2_eq]
        rw [h_C_val, h_D_val]
        dsimp [A, B]
        ring
      have h_A_zmod : (∑ k ∈ Ico 1 p, (((p + k - 1).choose k : ZMod (p ^ 3)) ^ 2)) = 0 := sum_term_sq_zero p hp hp5
      have h_A_nat : (∑ k ∈ Ico 1 p, ((p + k - 1).choose k) ^ 2) ≡ 0 [MOD p ^ 3] := by
        have h_eq : (∑ k ∈ Ico 1 p, (((p + k - 1).choose k : ZMod (p ^ 3)) ^ 2)) = ((0 : ℕ) : ZMod (p ^ 3)) := by
          rw [h_A_zmod]
          push_cast
          rfl
        have h_cast : (∑ k ∈ Ico 1 p, (((p + k - 1).choose k : ZMod (p ^ 3)) ^ 2)) = ((∑ k ∈ Ico 1 p, ((p + k - 1).choose k) ^ 2 : ℕ) : ZMod (p ^ 3)) := by
          push_cast
          rfl
        rw [h_cast] at h_eq
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h_eq
      have h_A_int : A ≡ 0 [ZMOD (p : ℤ)^3] := by
        have h_cast : A = ((∑ k ∈ Ico 1 p, ((p + k - 1).choose k) ^ 2 : ℕ) : ℤ) := by
          push_cast
          rfl
        rw [h_cast]
        exact Int.natCast_modEq_iff.mpr h_A_nat

      have h_B_zmod : (∑ k ∈ Ico (p + 1) (2 * p), (((p + k - 1).choose k : ZMod (p ^ 3)) ^ 2)) = 0 :=
        sum_term_sq_zero_gt_ico p hp hp5
      have h_B_nat : (∑ k ∈ Ico (p + 1) (2 * p), ((p + k - 1).choose k) ^ 2) ≡ 0 [MOD p ^ 3] := by
        have h_eq : (∑ k ∈ Ico (p + 1) (2 * p), (((p + k - 1).choose k : ZMod (p ^ 3)) ^ 2)) = ((0 : ℕ) : ZMod (p ^ 3)) := by
          rw [h_B_zmod]
          push_cast
          rfl
        have h_cast : (∑ k ∈ Ico (p + 1) (2 * p), (((p + k - 1).choose k : ZMod (p ^ 3)) ^ 2)) = ((∑ k ∈ Ico (p + 1) (2 * p), ((p + k - 1).choose k) ^ 2 : ℕ) : ZMod (p ^ 3)) := by
          push_cast
          rfl
        rw [h_cast] at h_eq
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h_eq
      have h_B_int : B ≡ 0 [ZMOD (p : ℤ)^3] := by
        have h_cast : B = ((∑ k ∈ Ico (p + 1) (2 * p), ((p + k - 1).choose k) ^ 2 : ℕ) : ℤ) := by
          push_cast
          rfl
        rw [h_cast]
        exact Int.natCast_modEq_iff.mpr h_B_nat

      have h_C_zmod : ((3 * p - 1).choose (p - 1) : ZMod (p ^ 3)) = 1 := choose_3p_minus_1_p_minus_1_eq_one p hp hp5
      have h_C_nat : (3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3] := by
        have h_eq : ((3 * p - 1).choose (p - 1) : ZMod (p ^ 3)) = ((1 : ℕ) : ZMod (p ^ 3)) := by
          rw [h_C_zmod]
          push_cast
          rfl
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h_eq
      have h_C_int : C ≡ 0 [ZMOD (p : ℤ)^3] := by
        have h_eq : (((3 * p - 1).choose (p - 1) : ℤ) - 1) ≡ 1 - 1 [ZMOD (p : ℤ)^3] := by
          exact Int.ModEq.sub_right 1 (Int.natCast_modEq_iff.mpr h_C_nat)
        exact h_eq

      have h_D_zmod : ((2 * p - 1).choose (p - 1) : ZMod (p ^ 3)) = 1 := choose_2p_minus_1_p_minus_1_eq_one p hp hp5
      have h_D_nat : (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3] := by
        have h_eq : ((2 * p - 1).choose (p - 1) : ZMod (p ^ 3)) = ((1 : ℕ) : ZMod (p ^ 3)) := by
          rw [h_D_zmod]
          push_cast
          rfl
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h_eq
      have h_D_int : D ≡ 0 [ZMOD (p : ℤ)^3] := by
        have h_eq : (((2 * p - 1).choose (p - 1) : ℤ) - 1) ≡ 1 - 1 [ZMOD (p : ℤ)^3] := by
          exact Int.ModEq.sub_right 1 (Int.natCast_modEq_iff.mpr h_D_nat)
        exact h_eq

      have h_C6 : 6 * C ≡ 0 [ZMOD (p : ℤ)^3] := Int.ModEq.mul_left 6 h_C_int
      have h_D2 : 2 * D ≡ 0 [ZMOD (p : ℤ)^3] := Int.ModEq.mul_left 2 h_D_int
      have h_part1 : A + B ≡ 0 [ZMOD (p : ℤ)^3] := Int.ModEq.add h_A_int h_B_int
      have h_part2 : A + B + 2 * D ≡ 0 [ZMOD (p : ℤ)^3] := Int.ModEq.add h_part1 h_D2
      have h_sum_mod3 : A + B + 2 * D + 6 * C ≡ 0 [ZMOD (p : ℤ)^3] := Int.ModEq.add h_part2 h_C6

      have h_A_dvd : (p : ℤ)^3 ∣ A := Int.modEq_zero_iff_dvd.mp h_A_int
      have h_B_dvd : (p : ℤ)^3 ∣ B := Int.modEq_zero_iff_dvd.mp h_B_int
      have h_C_dvd : (p : ℤ)^3 ∣ C := Int.modEq_zero_iff_dvd.mp h_C_int
      have h_D_dvd : (p : ℤ)^3 ∣ D := Int.modEq_zero_iff_dvd.mp h_D_int
      obtain ⟨A0, hA0⟩ := h_A_dvd
      obtain ⟨B0, hB0⟩ := h_B_dvd
      obtain ⟨C0, hC0⟩ := h_C_dvd
      obtain ⟨D0, hD0⟩ := h_D_dvd
      have h_sum : A + B + 2 * D + 6 * C = (p : ℤ)^3 * (A0 + B0 + 2 * D0 + 6 * C0) := by
        rw [hA0, hB0, hC0, hD0]
        ring
      have h_goal : 3 * (A + B + 2 * D + 6 * C) ≡ 0 [ZMOD (p : ℤ)^5] := by
        rw [h_sum]
        have h_mod : 3 * ((p : ℤ) ^ 3 * (A0 + B0 + 2 * D0 + 6 * C0)) = (p : ℤ) ^ 3 * (3 * (A0 + B0 + 2 * D0 + 6 * C0)) := by ring
        rw [h_mod]
        have h_dvd : (p : ℤ) ^ 5 ∣ (p : ℤ) ^ 3 * (3 * (A0 + B0 + 2 * D0 + 6 * C0)) := by
          have h_exact_dvd : (p : ℤ)^2 ∣ 3 * (A0 + B0 + 2 * D0 + 6 * C0) := by
            sorry
          rcases h_exact_dvd with ⟨k, hk⟩
          use k
          rw [hk]
          ring
        exact Int.modEq_zero_iff_dvd.mpr h_dvd
      have h_sum_sq : 3 * D^2 + 3 * C^2 ≡ 0 [ZMOD (p : ℤ)^5] := by
        have h_D3 : 3 * D^2 ≡ 0 [ZMOD (p : ℤ)^5] := Int.ModEq.mul_left 3 h_D_sq
        have h_C3 : 3 * C^2 ≡ 0 [ZMOD (p : ℤ)^5] := Int.ModEq.mul_left 3 h_C_sq
        exact Int.ModEq.add h_D3 h_C3
      have h_total : 3 * (A + B + 2 * D + 6 * C) + 3 * D ^ 2 + 3 * C ^ 2 ≡ 0 [ZMOD (p : ℤ)^5] := by
        have h_add := Int.ModEq.add h_goal h_sum_sq
        have h_zero : (0 : ℤ) + 0 = 0 := by rfl
        rw [h_zero] at h_add
        have h_assoc : 3 * (A + B + 2 * D + 6 * C) + (3 * D ^ 2 + 3 * C ^ 2) = 3 * (A + B + 2 * D + 6 * C) + 3 * D ^ 2 + 3 * C ^ 2 := by ring
        rw [h_assoc] at h_add
        exact h_add
      have h_sub_zero : 3 * S2_z + 4 * S1_z - 21 ≡ 0 [ZMOD (p : ℤ)^5] := by
        rw [h_algebraic]
        exact h_total
      have h_add_21 := Int.ModEq.add_right 21 h_sub_zero
      have h_ring : 3 * S2_z + 4 * S1_z - 21 + 21 = 3 * S2_z + 4 * S1_z := by ring
      rw [h_ring] at h_add_21
      exact h_add_21

    have h_red := algebraic_reduction (∑ k ∈ range (2 * p + 1), (p + k - 1).choose k) (∑ k ∈ range (2 * p + 1), ((p + k - 1).choose k)^2) p (by omega) h1 h2 h3
    have h_final : (A357674 p : ℤ) ≡ (A357674 1 : ℤ) [ZMOD (p : ℤ)^5] := by
      unfold A357674
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
      exact h_red
    exact Int.natCast_modEq_iff.mp h_final


#print axioms A357674_conjecture_1
