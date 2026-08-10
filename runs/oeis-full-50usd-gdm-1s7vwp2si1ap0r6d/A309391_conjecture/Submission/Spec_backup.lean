import FormalConjectures.Util.ProblemImports



open Nat Int Rat Finset

/-- The $n$-th harmonic number $\sum_{k=1}^n 1/k$, as a rational number. -/
def harmonic_number (n : ℕ) : ℚ :=
  (Finset.range n).sum fun k => (1 : ℚ) / (((k + 1) : ℕ) : ℚ)

/--
A309391: $a(n) = \gcd(n, A064169(n-2))$ for $n > 2$.
$A064169(m)$ is the numerator minus the denominator of the $m$-th harmonic number $H_m$.
The formula used is $a(n) = \gcd(n, |   ext{num}(H_{n-2}) -     ext{den}(H_{n-2})|)$.
-/
def A309391 (n : ℕ) : ℕ :=
  -- The sequence is usually indexed starting from n=3, but we define it for n:ℕ.
  -- For the terms n=0,1,2, we can assign a default value of 0, as they are not part of the sequence.
  -- The OEIS listing starts at index 3.
  if n < 3 then 0 else
  let m : ℕ := n - 2
  let r : ℚ := harmonic_number m
  -- r.num is ℤ, r.den is ℕ. We compute the absolute difference of the numerator and denominator.
  let num_minus_den : ℤ := r.num - (r.den : ℤ)
  Nat.gcd n num_minus_den.natAbs

theorem not_prime_of_mul (a b : ℕ) (ha : 1 < a) (hb : 1 < b) : ¬ Nat.Prime (a * b) := by
  intro hp
  have h_dvd : a ∣ a * b := dvd_mul_right a b
  have h_not : a = 1 ∨ a = a * b := hp.eq_one_or_self_of_dvd a h_dvd
  rcases h_not with rfl | h_self
  · omega
  · have h_nz : 0 < a := by omega
    have h_eq : a * 1 = a * b := by omega
    have h_cancel : 1 = b := Nat.eq_of_mul_eq_mul_left h_nz h_eq
    omega




theorem prime_16843 : Nat.Prime 16843 := by norm_num

def e_neg (R : Type*) [Ring R] : R ≃ R where
  toFun := fun x => -x
  invFun := fun x => -x
  left_inv := neg_neg
  right_inv := neg_neg

lemma sum_odd_eq_zero {R : Type*} [CommRing R] (U : Finset R) (hU : ∀ x, x ∈ U ↔ -x ∈ U)
    (f : R → R) (hf : ∀ x, f (-x) = -f x) (h2 : ∀ x : R, 2 * x = 0 → x = 0) :
    (U.sum f) = 0 := by
  have h_sum : U.sum f = U.sum (fun i => f (-i)) := by
    apply Finset.sum_equiv (e_neg R)
    · intro i
      exact hU i
    · intro i hi
      dsimp [e_neg]
      rw [neg_neg]
  have h_eq : (fun i => f (-i)) = (fun i => - f i) := by
    ext i
    exact hf i
  have h_sum2 : U.sum f = - U.sum f := by
    calc U.sum f = U.sum (fun i => f (-i)) := h_sum
      _ = U.sum (fun i => -f i) := by rw [h_eq]
      _ = - U.sum f := by rw [Finset.sum_neg_distrib]
  have h_add : U.sum f + U.sum f = 0 := by
    have h_sub : U.sum f + U.sum f = U.sum f - (- U.sum f) := by ring
    rw [h_sub, ← h_sum2, sub_self]
  have h_two : 2 * U.sum f = 0 := by
    calc 2 * U.sum f = U.sum f + U.sum f := by ring
    _ = 0 := h_add
  exact h2 (U.sum f) h_two













def sum_bin (a : ℕ) (depth : ℕ) (M : ℕ) : ℕ × ℕ :=
  match depth with
  | 0 => (1, a + 1)
  | d + 1 =>
    let (N1, D1) := sum_bin a d M
    let (N2, D2) := sum_bin (a + 2^d) d M
    ((N1 * D2 + N2 * D1) % M, (D1 * D2) % M)

def merge_bin (pair1 pair2 : ℕ × ℕ) (M : ℕ) : ℕ × ℕ :=
  let (N1, D1) := pair1
  let (N2, D2) := pair2
  ((N1 * D2 + N2 * D1) % M, (D1 * D2) % M)

def sum_16842_bin (M : ℕ) : ℕ × ℕ :=
  let p1 := sum_bin 0 14 M
  let p2 := sum_bin 16384 8 M
  let p3 := sum_bin 16640 7 M
  let p4 := sum_bin 16768 6 M
  let p5 := sum_bin 16832 3 M
  let p6 := sum_bin 16840 1 M
  merge_bin (merge_bin (merge_bin (merge_bin (merge_bin p1 p2 M) p3 M) p4 M) p5 M) p6 M

theorem wolstenholme_16843 : (sum_16842_bin (16843^3)).1 = 0 := by decide

lemma inv_neg_of_unit {n : ℕ} (x : ZMod n) (hu : IsUnit x) : (-x)⁻¹ = - x⁻¹ := by
  have h1 : (-x) * (- x⁻¹) = 1 := by
    calc (-x) * (- x⁻¹) = x * x⁻¹ := by ring
    _ = x⁻¹ * x := by rw [mul_comm]
    _ = 1 := ZMod.inv_mul_of_unit x hu
  exact ZMod.inv_eq_of_mul_eq_one n (-x) (- x⁻¹) h1

lemma coprime_of_not_dvd {a : ℕ} (h : ¬ 16843 ∣ a) : Nat.Coprime a 283686649 := by
  have h_pow : 283686649 = 16843 ^ 2 := by ring
  rw [h_pow]
  rw [Nat.coprime_pow_right_iff (by decide)]
  exact ((Nat.Prime.coprime_iff_not_dvd prime_16843).mpr h).symm

lemma isUnit_of_cast_ne_zero (x : ZMod (16843^2)) (h : ZMod.cast x ≠ (0 : ZMod 16843)) : IsUnit x := by
  rw [← ZMod.natCast_zmod_val x]
  rw [ZMod.isUnit_iff_coprime]
  apply coprime_of_not_dvd
  intro h_dvd
  have h_cast : ZMod.cast x = (0 : ZMod 16843) := by
    have h_val_cast : ZMod.cast x = ((x.val : ℤ) : ZMod 16843) := rfl
    rw [h_val_cast]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast h_dvd
  exact h h_cast

lemma sum_units_inv_eq_zero_16843 :
    (Finset.univ.filter (fun x : ZMod (16843^2) => ZMod.cast x ≠ (0 : ZMod 16843))).sum (fun x => x⁻¹) = 0 := by
  have hU : ∀ x : ZMod (16843^2),
      x ∈ Finset.univ.filter (fun x => ZMod.cast x ≠ (0 : ZMod 16843)) ↔
      -x ∈ Finset.univ.filter (fun x => ZMod.cast x ≠ (0 : ZMod 16843)) := by
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h_div : 16843 ∣ 16843^2 := by use 16843; ring
    have h_neg := @ZMod.cast_neg (16843^2) (ZMod 16843) _ 16843 _ h_div x
    rw [h_neg, neg_ne_zero]
  let f (x : ZMod (16843^2)) : ZMod (16843^2) :=
    if ZMod.cast x = (0 : ZMod 16843) then 0 else x⁻¹
  have hf : ∀ x : ZMod (16843^2), f (-x) = - (f x) := by
    intro x
    dsimp [f]
    by_cases h_cast : ZMod.cast x = (0 : ZMod 16843)
    · have h_neg_cast : ZMod.cast (-x) = (0 : ZMod 16843) := by
        simp [h_cast]
      rw [if_pos h_neg_cast, if_pos h_cast, neg_zero]
    · have h_neg_cast : ZMod.cast (-x) ≠ (0 : ZMod 16843) := by
        simp [h_cast]
      rw [if_neg h_neg_cast, if_neg h_cast]
      exact inv_neg_of_unit x (isUnit_of_cast_ne_zero x h_cast)
  have h2 : ∀ x : ZMod (16843^2), 2 * x = 0 → x = 0 := by
    have h_inv : (2 : ZMod (16843^2)) * (2 : ZMod (16843^2))⁻¹ = 1 := by decide
    intro x hx
    have h_mul : (2 : ZMod (16843^2))⁻¹ * (2 * x) = 0 := by rw [hx, mul_zero]
    have h_assoc : (2 : ZMod (16843^2))⁻¹ * 2 * x = 0 := by rwa [← mul_assoc] at h_mul
    rw [mul_comm (2 : ZMod (16843^2))⁻¹ 2, h_inv, one_mul] at h_assoc
    exact h_assoc
  have h_sum_f : (Finset.univ.filter (fun x : ZMod (16843^2) => ZMod.cast x ≠ (0 : ZMod 16843))).sum f = 0 := by
    exact sum_odd_eq_zero _ hU f hf h2
  have h_sum_eq : (Finset.univ.filter (fun x : ZMod (16843^2) => ZMod.cast x ≠ (0 : ZMod 16843))).sum (fun x => x⁻¹) =
                  (Finset.univ.filter (fun x : ZMod (16843^2) => ZMod.cast x ≠ (0 : ZMod 16843))).sum f := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    dsimp [f]
    rw [if_neg hx]
  rw [h_sum_eq]
  exact h_sum_f



lemma harmonic_split (p : ℕ) :
    harmonic_number (p^2-2) =
    (Finset.filter (fun k => ¬ p ∣ k + 1) (Finset.range (p^2-2))).sum (fun k => (1 : ℚ) / (((k + 1) : ℕ) : ℚ)) +
    (Finset.filter (fun k => p ∣ k + 1) (Finset.range (p^2-2))).sum (fun k => (1 : ℚ) / (((k + 1) : ℕ) : ℚ)) := by
  unfold harmonic_number
  rw [add_comm]
  have h_split := Finset.sum_filter_add_sum_filter_not (Finset.range (p^2-2)) (fun k => p ∣ k + 1) (fun k => (1 : ℚ) / (((k + 1) : ℕ) : ℚ))
  exact h_split.symm


lemma harmonic_number_eq_harmonic (n : ℕ) : harmonic_number n = harmonic n := by
  unfold harmonic_number harmonic
  congr 1
  ext k
  rw [one_div]








lemma dvd_num_minus_den_of_eq_fraction {r : ℚ} {A : ℤ} {B : ℕ} {n : ℕ} (hn : n ≥ 3)
    (h_eq : r = (A : ℚ) / (B : ℚ))
    (h_coprime : Nat.Coprime B n)
    (h_dvd : (n : ℤ) ∣ A - (B : ℤ)) :
    (n : ℤ) ∣ r.num - (r.den : ℤ) := by
  have h_B_nz : B ≠ 0 := by
    intro hB
    subst hB
    have h_gcd : Nat.gcd 0 n = 1 := h_coprime
    have h_gcd_zero : Nat.gcd 0 n = n := Nat.gcd_zero_left n
    omega
  have h_B_q_nz : (B : ℚ) ≠ 0 := by exact_mod_cast h_B_nz
  have h_den_q_nz : (r.den : ℚ) ≠ 0 := by positivity
  have h_num_div_den : (r.num : ℚ) / (r.den : ℚ) = r := Rat.num_div_den r
  have h_eq2 : (r.num : ℚ) / (r.den : ℚ) = (A : ℚ) / (B : ℚ) := by
    rw [h_num_div_den, h_eq]
  have h_mul_eq : (r.num : ℚ) * (B : ℚ) = (A : ℚ) * (r.den : ℚ) := by
    rwa [div_eq_div_iff h_den_q_nz h_B_q_nz] at h_eq2
  have h_cast : ((r.num * (B : ℤ) : ℤ) : ℚ) = ((A * (r.den : ℤ) : ℤ) : ℚ) := by
    push_cast
    exact h_mul_eq
  have h_eq_z : r.num * (B : ℤ) = A * (r.den : ℤ) := by
    exact_mod_cast h_cast
  rcases h_dvd with ⟨k, hk⟩
  have h_A : A = (B : ℤ) + (n : ℤ) * k := by omega
  have h_factor : (B : ℤ) * (r.num - (r.den : ℤ)) = (n : ℤ) * (k * (r.den : ℤ)) := by
    calc (B : ℤ) * (r.num - (r.den : ℤ))
      _ = r.num * (B : ℤ) - (B : ℤ) * (r.den : ℤ) := by ring
      _ = A * (r.den : ℤ) - (B : ℤ) * (r.den : ℤ) := by rw [h_eq_z]
      _ = ((B : ℤ) + (n : ℤ) * k) * (r.den : ℤ) - (B : ℤ) * (r.den : ℤ) := by rw [h_A]
      _ = (n : ℤ) * (k * (r.den : ℤ)) := by ring
  have h_dvd_mul : (n : ℤ) ∣ (B : ℤ) * (r.num - (r.den : ℤ)) := by
    exact ⟨k * (r.den : ℤ), h_factor⟩
  have h_nat_dvd_mul : n ∣ (B * (r.num - (r.den : ℤ)).natAbs) := by
    have h_nat_dvd_iff := @Int.natAbs_dvd_natAbs (n : ℤ) ((B : ℤ) * (r.num - (r.den : ℤ)))
    have h_n_abs : (n : ℤ).natAbs = n := Int.natAbs_natCast n
    have h_mul_abs : ((B : ℤ) * (r.num - (r.den : ℤ))).natAbs = B * (r.num - (r.den : ℤ)).natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
    rw [h_n_abs, h_mul_abs] at h_nat_dvd_iff
    exact h_nat_dvd_iff.mpr h_dvd_mul
  have h_nat_dvd_mul' : n ∣ (r.num - (r.den : ℤ)).natAbs * B := by
    rw [mul_comm] at h_nat_dvd_mul
    exact h_nat_dvd_mul
  have h_coprime' : n.Coprime B := h_coprime.symm
  have h_dvd_abs : n ∣ (r.num - (r.den : ℤ)).natAbs := Nat.Coprime.dvd_of_dvd_mul_right h_coprime' h_nat_dvd_mul'
  have h_final_dvd_iff := @Int.natAbs_dvd_natAbs (n : ℤ) (r.num - (r.den : ℤ))
  have h_n_abs' : (n : ℤ).natAbs = n := Int.natAbs_natCast n
  rw [h_n_abs'] at h_final_dvd_iff
  exact h_final_dvd_iff.mp h_dvd_abs





lemma A309391_eq_n_of_dvd {n : ℕ} (hn : n ≥ 3)
    (h_dvd : n ∣ (((harmonic_number (n - 2)).num - (harmonic_number (n - 2)).den : ℤ).natAbs)) :
    A309391 n = n := by
  unfold A309391
  have h_not_lt : ¬ n < 3 := by omega
  rw [if_neg h_not_lt]
  exact Nat.gcd_eq_left h_dvd

attribute [irreducible] A309391

def U_16843 : Finset ℕ := (Finset.range (16843^2 - 2)).filter (fun k => ¬ 16843 ∣ k + 1)

lemma U_16843_def : U_16843 = (Finset.range (16843^2 - 2)).filter (fun k => ¬ 16843 ∣ k + 1) := rfl

def G_16843 : Finset (ZMod (16843^2)) :=
  Finset.univ.filter (fun x => ZMod.cast x ≠ (0 : ZMod 16843))

def sum_bin_exact (a : ℕ) (depth : ℕ) : ℕ × ℕ :=
  match depth with
  | 0 => (1, a + 1)
  | d + 1 =>
    let (N1, D1) := sum_bin_exact a d
    let (N2, D2) := sum_bin_exact (a + 2^d) d
    (N1 * D2 + N2 * D1, D1 * D2)

def merge_bin_exact (pair1 pair2 : ℕ × ℕ) : ℕ × ℕ :=
  let (N1, D1) := pair1
  let (N2, D2) := pair2
  (N1 * D2 + N2 * D1, D1 * D2)

def sum_16842_bin_exact : ℕ × ℕ :=
  let p1 := sum_bin_exact 0 14
  let p2 := sum_bin_exact 16384 8
  let p3 := sum_bin_exact 16640 7
  let p4 := sum_bin_exact 16768 6
  let p5 := sum_bin_exact 16832 3
  let p6 := sum_bin_exact 16840 1
  merge_bin_exact (merge_bin_exact (merge_bin_exact (merge_bin_exact (merge_bin_exact p1 p2) p3) p4) p5) p6

def sum_q (a : ℕ) (n : ℕ) : ℚ :=
  (Finset.range n).sum (fun x => (1 : ℚ) / (((a + x + 1) : ℕ) : ℚ))

lemma sum_bin_exact_den_pos (a : ℕ) (depth : ℕ) : (sum_bin_exact a depth).2 > 0 := by
  induction depth generalizing a with
  | zero => dsimp [sum_bin_exact]; omega
  | succ d ih =>
    dsimp [sum_bin_exact]
    have h1 := ih a
    have h2 := ih (a + 2^d)
    rcases h_eq1 : sum_bin_exact a d with ⟨N1, D1⟩
    rcases h_eq2 : sum_bin_exact (a + 2^d) d with ⟨N2, D2⟩
    rw [h_eq1] at h1; rw [h_eq2] at h2
    dsimp at h1 h2 ⊢
    exact Nat.mul_pos h1 h2

lemma sum_q_eq_sum_bin_exact (a : ℕ) (depth : ℕ) :
    sum_q a (2^depth) = ((sum_bin_exact a depth).1 : ℚ) / ((sum_bin_exact a depth).2 : ℚ) := by
  induction depth generalizing a with
  | zero =>
    dsimp [sum_q, sum_bin_exact]
    rw [Finset.sum_singleton]
  | succ d ih =>
    dsimp [sum_q, sum_bin_exact]
    have h_pow : 2^(d + 1) = 2^d + 2^d := by ring
    rw [h_pow, Finset.sum_range_add]
    have h_split : (fun x => (1 : ℚ) / (((a + (2^d + x) + 1) : ℕ) : ℚ)) =
                   (fun x => (1 : ℚ) / ((( (a + 2^d) + x + 1) : ℕ) : ℚ)) := by
      ext x; congr 3; omega
    rw [h_split]
    change sum_q a (2^d) + sum_q (a + 2^d) (2^d) = _
    rw [ih a, ih (a + 2^d)]
    rcases h_eq1 : sum_bin_exact a d with ⟨N1, D1⟩
    rcases h_eq2 : sum_bin_exact (a + 2^d) d with ⟨N2, D2⟩
    dsimp at ih ⊢
    have hD1_pos : (D1 : ℚ) ≠ 0 := by
      have := sum_bin_exact_den_pos a d; rw [h_eq1] at this; dsimp at this; positivity
    have hD2_pos : (D2 : ℚ) ≠ 0 := by
      have := sum_bin_exact_den_pos (a + 2^d) d; rw [h_eq2] at this; dsimp at this; positivity
    rw [div_add_div _ _ hD1_pos hD2_pos]
    push_cast; ring

lemma sum_q_add (a : ℕ) (n m : ℕ) : sum_q a (n + m) = sum_q a n + sum_q (a + n) m := by
  dsimp [sum_q]; rw [Finset.sum_range_add]; congr 1
  apply Finset.sum_congr rfl; intro x _; congr 3; omega

lemma merge_bin_exact_eq (pair1 pair2 : ℕ × ℕ) (h1 : (pair1.2 : ℚ) ≠ 0) (h2 : (pair2.2 : ℚ) ≠ 0) :
    ((merge_bin_exact pair1 pair2).1 : ℚ) / ((merge_bin_exact pair1 pair2).2 : ℚ) =
    (pair1.1 : ℚ) / (pair1.2 : ℚ) + (pair2.1 : ℚ) / (pair2.2 : ℚ) := by
  rcases pair1 with ⟨N1, D1⟩; rcases pair2 with ⟨N2, D2⟩
  dsimp [merge_bin_exact]; rw [div_add_div _ _ h1 h2]; push_cast; ring

lemma harmonic_number_eq_sum_q (n : ℕ) : harmonic_number n = sum_q 0 n := by
  dsimp [harmonic_number, sum_q]
  apply Finset.sum_congr rfl
  intro x _
  congr 3
  omega

lemma harmonic_number_16842_eq :
    harmonic_number 16842 = (sum_16842_bin_exact.1 : ℚ) / (sum_16842_bin_exact.2 : ℚ) := by
  rw [harmonic_number_eq_sum_q]
  have h_sum1 : 16842 = 16384 + 458 := by omega
  rw [h_sum1, sum_q_add]
  have h_sum2 : 458 = 256 + 202 := by omega
  rw [h_sum2, sum_q_add]
  have h_sum3 : 202 = 128 + 74 := by omega
  rw [h_sum3, sum_q_add]
  have h_sum4 : 74 = 64 + 10 := by omega
  rw [h_sum4, sum_q_add]
  have h_sum5 : 10 = 8 + 2 := by omega
  rw [h_sum5, sum_q_add]
  have hp1 : sum_q 0 16384 = sum_q 0 (2^14) := rfl
  have hp2 : sum_q 16384 256 = sum_q 16384 (2^8) := rfl
  have hp3 : sum_q 16640 128 = sum_q 16640 (2^7) := rfl
  have hp4 : sum_q 16768 64 = sum_q 16768 (2^6) := rfl
  have hp5 : sum_q 16832 8 = sum_q 16832 (2^3) := rfl
  have hp6 : sum_q 16840 2 = sum_q 16840 (2^1) := rfl
  rw [hp1, hp2, hp3, hp4, hp5, hp6]
  rw [sum_q_eq_sum_bin_exact 0 14]
  rw [sum_q_eq_sum_bin_exact 16384 8]
  rw [sum_q_eq_sum_bin_exact 16640 7]
  rw [sum_q_eq_sum_bin_exact 16768 6]
  rw [sum_q_eq_sum_bin_exact 16832 3]
  rw [sum_q_eq_sum_bin_exact 16840 1]
  dsimp [sum_16842_bin_exact]
  have hd1 := sum_bin_exact_den_pos 0 14
  have hd2 := sum_bin_exact_den_pos 16384 8
  have hd3 := sum_bin_exact_den_pos 16640 7
  have hd4 := sum_bin_exact_den_pos 16768 6
  have hd5 := sum_bin_exact_den_pos 16832 3
  have hd6 := sum_bin_exact_den_pos 16840 1
  generalize sum_bin_exact 0 14 = p1 at hd1 ⊢
  generalize sum_bin_exact 16384 8 = p2 at hd2 ⊢
  generalize sum_bin_exact 16640 7 = p3 at hd3 ⊢
  generalize sum_bin_exact 16768 6 = p4 at hd4 ⊢
  generalize sum_bin_exact 16832 3 = p5 at hd5 ⊢
  generalize sum_bin_exact 16840 1 = p6 at hd6 ⊢
  have hq1 : (p1.2 : ℚ) ≠ 0 := by positivity
  have hq2 : (p2.2 : ℚ) ≠ 0 := by positivity
  have hq3 : (p3.2 : ℚ) ≠ 0 := by positivity
  have hq4 : (p4.2 : ℚ) ≠ 0 := by positivity
  have hq5 : (p5.2 : ℚ) ≠ 0 := by positivity
  have hq6 : (p6.2 : ℚ) ≠ 0 := by positivity
  rw [merge_bin_exact_eq _ p6]
  rotate_left
  · dsimp [merge_bin_exact]; positivity
  · exact hq6
  rw [merge_bin_exact_eq _ p5]
  rotate_left
  · dsimp [merge_bin_exact]; positivity
  · exact hq5
  rw [merge_bin_exact_eq _ p4]
  rotate_left
  · dsimp [merge_bin_exact]; positivity
  · exact hq4
  rw [merge_bin_exact_eq _ p3]
  rotate_left
  · dsimp [merge_bin_exact]; positivity
  · exact hq3
  rw [merge_bin_exact_eq p1 p2 hq1 hq2]
  ring

lemma sum_q_16842_eq :
    (Finset.range 16842).sum (fun j => (1 : ℚ) / (((j + 1) : ℕ) : ℚ)) =
    (sum_16842_bin_exact.1 : ℚ) / (sum_16842_bin_exact.2 : ℚ) :=
  harmonic_number_16842_eq

attribute [irreducible] harmonic_number

lemma sum_bin_mod_eq (a : ℕ) (depth : ℕ) (M : ℕ) :
    (sum_bin a depth M).1 % M = (sum_bin_exact a depth).1 % M ∧
    (sum_bin a depth M).2 % M = (sum_bin_exact a depth).2 % M := by
  induction depth generalizing a with
  | zero => dsimp [sum_bin, sum_bin_exact]; exact ⟨rfl, rfl⟩
  | succ d ih =>
    dsimp [sum_bin, sum_bin_exact]
    rcases h_eq1 : sum_bin a d M with ⟨N1, D1⟩
    rcases h_eq2 : sum_bin (a + 2^d) d M with ⟨N2, D2⟩
    rcases h_eq1_ex : sum_bin_exact a d with ⟨N1_ex, D1_ex⟩
    rcases h_eq2_ex : sum_bin_exact (a + 2^d) d with ⟨N2_ex, D2_ex⟩
    have ih1 := ih a
    have ih2 := ih (a + 2^d)
    rw [h_eq1, h_eq1_ex] at ih1
    rw [h_eq2, h_eq2_ex] at ih2
    dsimp at ih1 ih2 ⊢
    rcases ih1 with ⟨ih1_N, ih1_D⟩
    rcases ih2 with ⟨ih2_N, ih2_D⟩
    rw [Nat.mod_mod]; rw [Nat.mod_mod]
    have ih1_N_zmod : (N1 : ZMod M) = (N1_ex : ZMod M) := (ZMod.natCast_eq_natCast_iff N1 N1_ex M).mpr ih1_N
    have ih1_D_zmod : (D1 : ZMod M) = (D1_ex : ZMod M) := (ZMod.natCast_eq_natCast_iff D1 D1_ex M).mpr ih1_D
    have ih2_N_zmod : (N2 : ZMod M) = (N2_ex : ZMod M) := (ZMod.natCast_eq_natCast_iff N2 N2_ex M).mpr ih2_N
    have ih2_D_zmod : (D2 : ZMod M) = (D2_ex : ZMod M) := (ZMod.natCast_eq_natCast_iff D2 D2_ex M).mpr ih2_D
    constructor
    · apply (ZMod.natCast_eq_natCast_iff (N1 * D2 + N2 * D1) (N1_ex * D2_ex + N2_ex * D1_ex) M).mp
      push_cast; rw [ih1_N_zmod, ih1_D_zmod, ih2_N_zmod, ih2_D_zmod]
    · apply (ZMod.natCast_eq_natCast_iff (D1 * D2) (D1_ex * D2_ex) M).mp
      push_cast; rw [ih1_D_zmod, ih2_D_zmod]

attribute [irreducible] sum_bin_exact

lemma merge_bin_mod_eq (pair1 pair2 pair1_ex pair2_ex : ℕ × ℕ) (M : ℕ)
    (h1 : pair1.1 % M = pair1_ex.1 % M ∧ pair1.2 % M = pair1_ex.2 % M)
    (h2 : pair2.1 % M = pair2_ex.1 % M ∧ pair2.2 % M = pair2_ex.2 % M) :
    (merge_bin pair1 pair2 M).1 % M = (merge_bin_exact pair1_ex pair2_ex).1 % M ∧
    (merge_bin pair1 pair2 M).2 % M = (merge_bin_exact pair1_ex pair2_ex).2 % M := by
  dsimp [merge_bin, merge_bin_exact]
  rcases pair1 with ⟨N1, D1⟩; rcases pair2 with ⟨N2, D2⟩
  rcases pair1_ex with ⟨N1_ex, D1_ex⟩; rcases pair2_ex with ⟨N2_ex, D2_ex⟩
  dsimp at h1 h2 ⊢
  rcases h1 with ⟨h1_N, h1_D⟩
  rcases h2 with ⟨h2_N, h2_D⟩
  rw [Nat.mod_mod]; rw [Nat.mod_mod]
  have ih1_N_zmod : (N1 : ZMod M) = (N1_ex : ZMod M) := (ZMod.natCast_eq_natCast_iff N1 N1_ex M).mpr h1_N
  have ih1_D_zmod : (D1 : ZMod M) = (D1_ex : ZMod M) := (ZMod.natCast_eq_natCast_iff D1 D1_ex M).mpr h1_D
  have ih2_N_zmod : (N2 : ZMod M) = (N2_ex : ZMod M) := (ZMod.natCast_eq_natCast_iff N2 N2_ex M).mpr h2_N
  have ih2_D_zmod : (D2 : ZMod M) = (D2_ex : ZMod M) := (ZMod.natCast_eq_natCast_iff D2 D2_ex M).mpr h2_D
  constructor
  · apply (ZMod.natCast_eq_natCast_iff (N1 * D2 + N2 * D1) (N1_ex * D2_ex + N2_ex * D1_ex) M).mp
    push_cast; rw [ih1_N_zmod, ih1_D_zmod, ih2_N_zmod, ih2_D_zmod]
  · apply (ZMod.natCast_eq_natCast_iff (D1 * D2) (D1_ex * D2_ex) M).mp
    push_cast; rw [ih1_D_zmod, ih2_D_zmod]

lemma sum_16842_bin_mod_eq (M : ℕ) :
    (sum_16842_bin M).1 % M = (sum_16842_bin_exact).1 % M ∧
    (sum_16842_bin M).2 % M = (sum_16842_bin_exact).2 % M := by
  dsimp [sum_16842_bin, sum_16842_bin_exact]
  apply merge_bin_mod_eq
  · apply merge_bin_mod_eq
    · apply merge_bin_mod_eq
      · apply merge_bin_mod_eq
        · apply merge_bin_mod_eq
          · exact sum_bin_mod_eq 0 14 M
          · exact sum_bin_mod_eq 16384 8 M
        · exact sum_bin_mod_eq 16640 7 M
      · exact sum_bin_mod_eq 16768 6 M
    · exact sum_bin_mod_eq 16832 3 M
  · exact sum_bin_mod_eq 16840 1 M

attribute [irreducible] sum_16842_bin_exact

lemma den_coprime : (sum_16842_bin 16843).2 % 16843 ≠ 0 := by decide

lemma den_coprime_exact : ¬ 16843 ∣ sum_16842_bin_exact.2 := by
  intro h_dvd
  have h_mod : sum_16842_bin_exact.2 % 16843 = 0 := Nat.mod_eq_zero_of_dvd h_dvd
  have h_eq := (sum_16842_bin_mod_eq 16843).2
  have h_val : (sum_16842_bin 16843).2 % 16843 = 0 := by
    rw [h_eq, h_mod]
  exact den_coprime h_val

lemma sum_bij_divisible_16843 :
    ((Finset.range (16843^2 - 2)).filter (fun k => 16843 ∣ k + 1)).sum (fun k => (1 : ℚ) / (((k + 1) : ℕ) : ℚ)) =
    (1 / (16843 : ℚ)) * (Finset.range 16842).sum (fun j => (1 : ℚ) / (((j + 1) : ℕ) : ℚ)) := by
  have h_terms : (fun j : ℕ => (1 / (16843 : ℚ)) * (1 / (((j + 1) : ℕ) : ℚ))) =
                 (fun j : ℕ => (1 : ℚ) / ((( (j + 1) * 16843 ) : ℕ) : ℚ)) := by
    ext j
    have h_eq : (( (j + 1) * 16843 : ℕ) : ℚ) = ((j + 1 : ℕ) : ℚ) * (16843 : ℚ) := by push_cast; ring
    rw [h_eq]; rw [one_div, one_div, one_div]; rw [mul_inv]; rw [mul_comm]
  rw [mul_sum]; rw [h_terms]; symm
  apply sum_bij (fun j _ => (j + 1) * 16843 - 1)
  · intro a1 ha1
    simp only [Finset.mem_range] at ha1; simp only [mem_filter, Finset.mem_range]
    have h1 : (a1 + 1) * 16843 - 1 < 16843^2 - 2 := by omega
    have h2 : 16843 ∣ ((a1 + 1) * 16843 - 1) + 1 := by
      have h_eq : (a1 + 1) * 16843 - 1 + 1 = (a1 + 1) * 16843 := by omega
      rw [h_eq]; exact dvd_mul_left 16843 (a1 + 1)
    exact ⟨h1, h2⟩
  · intro a1 _ a2 _ h_eq; omega
  · intro b hb
    simp only [mem_filter, Finset.mem_range] at hb
    rcases hb with ⟨hb1, hb2⟩; rcases hb2 with ⟨m, hm⟩
    norm_num at hb1
    have hm_pos : m > 0 := by omega
    have h_mul : 16843 * m < 283686649 := by
      calc 16843 * m = b + 1 := hm.symm
      _ < 283686647 + 1 := by omega
      _ = 283686648 := by rfl
      _ < 283686649 := by omega
    have h_lt : m < 16843 := by
      have h_mul2 : 16843 * m < 16843 * 16843 := by
        calc 16843 * m < 283686649 := h_mul
        _ = 16843 * 16843 := by rfl
      exact Nat.lt_of_mul_lt_mul_left h_mul2
    use m - 1; simp only [Finset.mem_range]
    have h_sub : m - 1 + 1 = m := Nat.sub_add_cancel hm_pos
    rw [h_sub, mul_comm]
    constructor
    · rw [← hm]; rfl
    · omega
  · intro a ha
    congr 3

lemma prod_erase_eq {α : Type*} [DecidableEq α] (U : Finset α) (g : α → ℚ) (x : α) (hx : x ∈ U) :
    U.prod (fun y => if y = x then 1 else g y) = (U.erase x).prod g := by
  rw [prod_eq_mul_prod_diff_singleton hx]
  simp only [if_true, one_mul]
  have h_sdiff : U \ {x} = U.erase x := sdiff_singleton_eq_erase x U
  rw [h_sdiff]
  apply prod_congr rfl; intro y hy
  have h_ne : y ≠ x := mem_erase.mp hy |>.1
  rw [if_neg h_ne]

lemma term_eq {α : Type*} [DecidableEq α] (U : Finset α) (g : α → ℚ) (x : α) (hx : x ∈ U)
    (h_nz : (U.erase x).prod g ≠ 0) :
    1 / g x = (U.prod (fun y => if y = x then 1 else g y)) / (U.prod g) := by
  rw [prod_erase_eq U g x hx]
  rw [prod_eq_mul_prod_diff_singleton hx]
  have h_sdiff : U \ {x} = U.erase x := sdiff_singleton_eq_erase x U
  rw [h_sdiff]
  have h_eq : (U.erase x).prod g / (g x * (U.erase x).prod g) = (1 * (U.erase x).prod g) / (g x * (U.erase x).prod g) := by ring
  rw [h_eq]
  exact (mul_div_mul_right (1 : ℚ) (g x) h_nz).symm

lemma sum_one_div_eq_fraction {α : Type*} [DecidableEq α] (U : Finset α) (g : α → ℚ)
    (h_nz : ∀ x ∈ U, (U.erase x).prod g ≠ 0) :
    U.sum (fun x => 1 / g x) = (U.sum (fun x => U.prod (fun y => if y = x then 1 else g y))) / (U.prod g) := by
  have h_sum : U.sum (fun x => 1 / g x) = U.sum (fun x => (U.prod (fun y => if y = x then 1 else g y)) / (U.prod g)) := by
    apply sum_congr rfl; intro x hx; exact term_eq U g x hx (h_nz x hx)
  rw [h_sum]; simp_rw [div_eq_mul_inv]; rw [← sum_mul]

lemma sum_inv_U_eq_one :
    (U_16843.sum (fun x => ((x + 1 : ℕ) : ZMod (16843^2))⁻¹)) = 1 := by
  have h_bij : ∑ x ∈ U_16843, ((x + 1 : ℕ) : ZMod (16843^2))⁻¹ =
               ∑ u ∈ G_16843.erase (-1), u⁻¹ := by
    apply sum_bij (fun j _ => ((j + 1 : ℕ) : ZMod (16843^2)))
    · intro x hx
      simp only [U_16843, mem_filter, Finset.mem_range] at hx
      simp only [G_16843, mem_erase, mem_filter, mem_univ, true_and]
      rcases hx with ⟨hx1, hx2⟩
      constructor
      · intro h_neg1
        have h_add : ((x + 2 : ℕ) : ZMod (16843^2)) = 0 := by
          calc ((x + 2 : ℕ) : ZMod (16843^2))
            _ = ((x + 1 : ℕ) : ZMod (16843^2)) + 1 := by push_cast; ring
            _ = -1 + 1 := by rw [h_neg1]
            _ = 0 := by ring
        rw [CharP.cast_eq_zero_iff (ZMod (16843^2)) (16843^2) (x + 2)] at h_add
        have h_lt : x + 2 < 16843^2 := by omega
        have h_gt : x + 2 > 0 := by omega
        have h_le := Nat.le_of_dvd h_gt h_add
        omega
      · have h_cast_eq : ZMod.cast ((x + 1 : ℕ) : ZMod (16843^2)) = ((x + 1 : ℕ) : ZMod 16843) := by
          have h_div : 16843 ∣ 16843^2 := ⟨16843, rfl⟩
          exact ZMod.cast_natCast h_div (x + 1)
        rw [h_cast_eq]
        rw [ne_eq, CharP.cast_eq_zero_iff (ZMod 16843) 16843 (x + 1)]
        exact hx2
    · intro x1 hx1 x2 hx2 h_eq
      simp only [U_16843, mem_filter, Finset.mem_range] at hx1 hx2
      have h_eq_z : ((x1 + 1 : ℕ) : ZMod (16843^2)) = ((x2 + 1 : ℕ) : ZMod (16843^2)) := h_eq
      rw [ZMod.natCast_eq_natCast_iff] at h_eq_z
      simp only [Nat.ModEq] at h_eq_z
      have h1 : x1 + 1 < 16843^2 := by omega
      have h2 : x2 + 1 < 16843^2 := by omega
      rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h_eq_z
      omega
    · intro u hu
      simp only [mem_erase, G_16843, mem_filter, mem_univ, true_and] at hu
      rcases hu with ⟨hu_ne, hu_unit⟩
      use u.val - 1
      have h_u_val : u.val < 16843^2 := u.val_lt
      have hu_unit' : ¬ 16843 ∣ u.val := by
        intro h_dvd
        have h_cast : ZMod.cast u = (0 : ZMod 16843) := by
          rw [← ZMod.natCast_zmod_val u]
          have h_div : 16843 ∣ 16843^2 := ⟨16843, rfl⟩
          rw [ZMod.cast_natCast h_div u.val]
          rw [CharP.cast_eq_zero_iff (ZMod 16843) 16843 u.val]
          exact h_dvd
        exact hu_unit h_cast
      have hu_ne' : u.val ≠ 16843^2 - 1 := by
        intro h_val
        have h_eq : u = -1 := by
          rw [← ZMod.natCast_zmod_val u]
          rw [h_val]
          push_cast
          rfl
        exact hu_ne h_eq
      have hu_val_pos : u.val > 0 := by
        by_contra h_zero
        have : u.val = 0 := by omega
        have h_u_zero : u = 0 := ZMod.val_injective (16843^2) this
        have h_cast : ZMod.cast u = (0 : ZMod 16843) := by
          rw [h_u_zero]
          simp
        exact hu_unit h_cast
      have hx : u.val - 1 ∈ U_16843 := by
        simp only [U_16843, mem_filter, Finset.mem_range]
        constructor
        · omega
        · have h_eq : u.val - 1 + 1 = u.val := by omega
          rw [h_eq]
          exact hu_unit'
      constructor
      · dsimp
        have h_eq : u.val - 1 + 1 = u.val := by omega
        rw [h_eq]
        exact ZMod.natCast_zmod_val u
      · exact hx
    · intro x _
      rfl
  rw [h_bij]
  have h_sum := sum_units_inv_eq_zero_16843
  change ∑ x ∈ G_16843, x⁻¹ = 0 at h_sum
  have h_mem : (-1 : ZMod (16843^2)) ∈ G_16843 := by
    simp only [G_16843, mem_filter, mem_univ, true_and]
    intro h_cast
    have h_neg1_val : ZMod.cast (-1 : ZMod (16843^2)) = (-1 : ZMod 16843) := by
      have h_div : 16843 ∣ 16843^2 := ⟨16843, rfl⟩
      exact ZMod.cast_neg (R := ZMod 16843) h_div 1
    rw [h_neg1_val] at h_cast
    have h_ne : (-1 : ZMod 16843) ≠ 0 := by decide
    exact h_ne h_cast
  have h_erase := Finset.add_sum_erase G_16843 (fun x => x⁻¹) h_mem
  rw [← h_erase] at h_sum
  dsimp at h_sum
  have h_neg1_inv : (-1 : ZMod (16843^2))⁻¹ = -1 := by
    have h_inv : (-1 : ZMod (16843^2)) * -1 = 1 := by ring
    exact ZMod.inv_eq_of_mul_eq_one (16843^2) (-1) (-1) h_inv
  rw [h_neg1_inv] at h_sum
  have h_eq : ∑ x ∈ G_16843.erase (-1), x⁻¹ = 1 := by
    have h_add : (-1 : ZMod (16843^2))⁻¹ + ∑ x ∈ G_16843.erase (-1), x⁻¹ = 0 := h_sum
    calc ∑ x ∈ G_16843.erase (-1), x⁻¹
      _ = ((-1 : ZMod (16843^2))⁻¹ + ∑ x ∈ G_16843.erase (-1), x⁻¹) + 1 := by rw [h_neg1_inv]; ring
      _ = 0 + 1 := by rw [h_add]
      _ = 1 := by ring
  exact h_eq

def D_U_nat : ℕ := U_16843.prod (fun y => y + 1)
def N_U_nat : ℕ := U_16843.sum (fun x => U_16843.prod (fun y => if y = x then 1 else y + 1))

lemma h_D_U : (D_U_nat : ℚ) = U_16843.prod (fun y => (((y + 1 : ℕ) : ℚ))) := by
  dsimp [D_U_nat]
  push_cast
  rfl

lemma h_N_U : (N_U_nat : ℚ) = U_16843.sum (fun x => U_16843.prod (fun y => if y = x then 1 else (((y + 1 : ℕ) : ℚ)))) := by
  dsimp [N_U_nat]
  push_cast
  rfl

lemma D_U_nat_ne_zero : (D_U_nat : ℚ) ≠ 0 := by
  have h_pos : D_U_nat > 0 := by
    dsimp [D_U_nat]
    apply Finset.prod_pos
    intro x hx
    omega
  have h_ne : D_U_nat ≠ 0 := by omega
  exact_mod_cast h_ne

lemma h_nz (x : ℕ) (hx : x ∈ U_16843) : ((U_16843.erase x).prod (fun k => (((k + 1) : ℕ) : ℚ))) ≠ 0 := by
  have h_pos : (U_16843.erase x).prod (fun k => k + 1) > 0 := by
    apply Finset.prod_pos
    intro y hy
    omega
  have h_ne : (U_16843.erase x).prod (fun k => k + 1) ≠ 0 := by omega
  have h_cast : ((U_16843.erase x).prod (fun k => k + 1) : ℚ) = (U_16843.erase x).prod (fun k => (((k + 1) : ℕ) : ℚ)) := by
    push_cast; rfl
  rw [← h_cast]
  exact_mod_cast h_ne

lemma sum_16842_bin_exact_den_pos : sum_16842_bin_exact.2 > 0 := by
  have h : sum_16842_bin_exact.2 ≠ 0 := by
    intro h_zero
    have h_dvd : 16843 ∣ sum_16842_bin_exact.2 := by
      rw [h_zero]
      exact dvd_zero 16843
    exact den_coprime_exact h_dvd
  omega

lemma N_H_eq : sum_16842_bin_exact.1 = 4778134229107 * (sum_16842_bin_exact.1 / 4778134229107) := by
  have h_mod : sum_16842_bin_exact.1 % 4778134229107 = 0 := by
    have h1 := (sum_16842_bin_mod_eq (16843^3)).1
    have h2 := wolstenholme_16843
    have h_pow : 16843^3 = 4778134229107 := by decide
    rw [h_pow] at h1 h2
    omega
  have h_div := Nat.div_add_mod sum_16842_bin_exact.1 4778134229107
  omega

lemma fraction_algebra (N_U D_U N_H D_H div_H : ℕ) (h_D_U : (D_U : ℚ) ≠ 0) (h_D_H : (D_H : ℚ) ≠ 0) (h_div : N_H = 4778134229107 * div_H) :
    (N_U : ℚ) / (D_U : ℚ) + (1 / 16843 : ℚ) * ((N_H : ℚ) / (D_H : ℚ)) =
    ((N_U * D_H + 283686649 * div_H * D_U : ℕ) : ℚ) / ((D_U * D_H : ℕ) : ℚ) := by
  rw [h_div]
  push_cast
  field_simp
  ring

lemma final_algebraic_step :
    harmonic_number (16843^2 - 2) =
    ((N_U_nat * sum_16842_bin_exact.2 + 283686649 * (sum_16842_bin_exact.1 / 4778134229107) * D_U_nat : ℕ) : ℚ) / ((D_U_nat * sum_16842_bin_exact.2 : ℕ) : ℚ) := by
  have h_split := harmonic_split 16843
  rw [← U_16843_def] at h_split
  rw [h_split]
  rw [sum_one_div_eq_fraction U_16843 (fun y => (((y + 1) : ℕ) : ℚ)) h_nz]
  rw [← h_D_U, ← h_N_U]
  rw [sum_bij_divisible_16843]
  rw [sum_q_16842_eq]
  have h_D_H_nz : (sum_16842_bin_exact.2 : ℚ) ≠ 0 := by
    have h_pos := sum_16842_bin_exact_den_pos
    have h_ne : sum_16842_bin_exact.2 ≠ 0 := by omega
    exact_mod_cast h_ne
  exact fraction_algebra N_U_nat D_U_nat sum_16842_bin_exact.1 sum_16842_bin_exact.2 (sum_16842_bin_exact.1 / 4778134229107) D_U_nat_ne_zero h_D_H_nz N_H_eq

lemma Prime.not_dvd_prod_of_prime {α : Type*} [DecidableEq α] (p : ℕ) (hp : Nat.Prime p) (s : Finset α) (f : α → ℕ) (hs : ∀ x ∈ s, ¬ p ∣ f x) :
    ¬ p ∣ s.prod f := by
  induction s using Finset.induction_on with
  | empty =>
    have h_one : ¬ p ∣ 1 := by
      intro h
      have := Nat.le_of_dvd (by decide) h
      have hp2 : p ≥ 2 := Nat.Prime.two_le hp
      omega
    exact h_one
  | insert a s ha ih =>
    simp only [mem_insert, forall_eq_or_imp] at hs
    rw [prod_insert ha]
    rw [Nat.Prime.dvd_mul hp]
    push_neg
    exact ⟨hs.1, ih hs.2⟩

lemma Nat_cast_prod_ZMod (U : Finset ℕ) (f : ℕ → ℕ) :
    ((U.prod f : ℕ) : ZMod (16843^2)) = U.prod (fun x => (f x : ZMod (16843^2))) := by
  push_cast; rfl

lemma Nat_cast_sum_ZMod (U : Finset ℕ) (f : ℕ → ℕ) :
    ((U.sum f : ℕ) : ZMod (16843^2)) = U.sum (fun x => (f x : ZMod (16843^2))) := by
  push_cast; rfl

lemma ZMod_N_U_nat_eq_D_U_nat : (N_U_nat : ZMod (16843^2)) = D_U_nat := by
  dsimp [D_U_nat, N_U_nat]
  rw [Nat_cast_prod_ZMod, Nat_cast_sum_ZMod]
  have h_sum := sum_inv_U_eq_one
  push_cast at h_sum ⊢
  have h_mul := congr_arg (fun s => s * (∏ y ∈ U_16843, ((y : ZMod (16843^2)) + 1))) h_sum
  dsimp at h_mul
  rw [one_mul] at h_mul
  rw [sum_mul] at h_mul
  have h_eq : ∀ x ∈ U_16843, ((x : ZMod (16843^2)) + 1)⁻¹ * ∏ y ∈ U_16843, ((y : ZMod (16843^2)) + 1) =
                             ∏ y ∈ U_16843, if y = x then 1 else ((y : ZMod (16843^2)) + 1) := by
    intro x hx
    rw [prod_eq_mul_prod_diff_singleton hx]
    have h_assoc : ((x : ZMod (16843^2)) + 1)⁻¹ * (((x : ZMod (16843^2)) + 1) * ∏ y ∈ U_16843 \ {x}, ((y : ZMod (16843^2)) + 1)) =
                   (((x : ZMod (16843^2)) + 1)⁻¹ * ((x : ZMod (16843^2)) + 1)) * ∏ y ∈ U_16843 \ {x}, ((y : ZMod (16843^2)) + 1) := by ring
    rw [h_assoc]
    have h_is_unit : IsUnit ((x + 1 : ℕ) : ZMod (16843^2)) := by
      apply isUnit_of_cast_ne_zero
      have h_div : 16843 ∣ 16843^2 := ⟨16843, rfl⟩
      rw [ZMod.cast_natCast h_div (x + 1)]
      rw [ne_eq, CharP.cast_eq_zero_iff (ZMod 16843) 16843 (x + 1)]
      simp only [U_16843, mem_filter, Finset.mem_range] at hx
      exact hx.2
    have h_cancel : ((x : ZMod (16843^2)) + 1)⁻¹ * ((x : ZMod (16843^2)) + 1) = 1 := by
      have h_eq_cast : ((x : ZMod (16843^2)) + 1) = ((x + 1 : ℕ) : ZMod (16843^2)) := by push_cast; rfl
      rw [h_eq_cast]
      exact ZMod.inv_mul_of_unit ((x + 1 : ℕ) : ZMod (16843^2)) h_is_unit
    rw [h_cancel, one_mul]
    have h_sdiff : U_16843 \ {x} = U_16843.erase x := sdiff_singleton_eq_erase x U_16843
    rw [h_sdiff]
    symm
    apply prod_congr rfl
    intro y hy
    have h_ne : y ≠ x := mem_erase.mp hy |>.1
    rw [if_neg h_ne]
  have h_congr : U_16843.sum (fun x => ((x : ZMod (16843^2)) + 1)⁻¹ * ∏ y ∈ U_16843, ((y : ZMod (16843^2)) + 1)) =
                 U_16843.sum (fun x => ∏ y ∈ U_16843, if y = x then 1 else ((y : ZMod (16843^2)) + 1)) := by
    apply sum_congr rfl
    intro x hx
    exact h_eq x hx
  rw [h_congr] at h_mul
  symm; exact h_mul

attribute [irreducible] D_U_nat N_U_nat

lemma D_U_nat_coprime : ¬ 16843 ∣ D_U_nat := by
  dsimp [D_U_nat]
  apply Prime.not_dvd_prod_of_prime 16843 prime_16843
  intro x hx
  simp only [U_16843, mem_filter, Finset.mem_range] at hx
  exact hx.2

lemma D_U_nat_mul_sum_coprime : ¬ 16843 ∣ D_U_nat * sum_16842_bin_exact.2 := by
  rw [Nat.Prime.dvd_mul prime_16843]
  push_neg
  exact ⟨D_U_nat_coprime, den_coprime_exact⟩

lemma coprime_B : Nat.Coprime (D_U_nat * sum_16842_bin_exact.2) 283686649 := by
  apply coprime_of_not_dvd
  exact D_U_nat_mul_sum_coprime

lemma final_dvd_A_minus_B (D_H div_H : ℕ)
    (h_div : (sum_16842_bin_exact.1 : ℤ) / (4778134229107 : ℤ) = (div_H : ℤ))
    (h_D_H : (sum_16842_bin_exact.2 : ℤ) = (D_H : ℤ)) :
    ((283686649 : ℕ) : ℤ) ∣ (N_U_nat * D_H + 283686649 * div_H * D_U_nat : ℤ) - (D_U_nat * D_H : ℤ) := by
  have h_zmod : (N_U_nat : ZMod 283686649) = D_U_nat := ZMod_N_U_nat_eq_D_U_nat
  generalize N_U_nat = N_U at h_zmod ⊢
  generalize D_U_nat = D_U at h_zmod ⊢
  push_cast
  have h_eq : (N_U : ℤ) * (D_H : ℤ) + (283686649 : ℤ) * (div_H : ℤ) * (D_U : ℤ) - (D_U : ℤ) * (D_H : ℤ) =
              ((N_U : ℤ) - (D_U : ℤ)) * (D_H : ℤ) + (283686649 : ℤ) * ((div_H : ℤ) * (D_U : ℤ)) := by ring
  rw [h_eq]
  apply dvd_add
  · have h_dvd_diff : (283686649 : ℤ) ∣ (N_U : ℤ) - (D_U : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [h_zmod, sub_self]
    exact dvd_mul_of_dvd_left h_dvd_diff (D_H : ℤ)
  · exact dvd_mul_right (283686649 : ℤ) ((div_H : ℤ) * (D_U : ℤ))

lemma cast_div_eq (X Y : ℕ) : ((X : ℕ) : ℚ) / ((Y : ℕ) : ℚ) = ((X : ℤ) : ℚ) / ((Y : ℕ) : ℚ) := by
  congr 1
  push_cast
  rfl

theorem A309391_conjecture.disproof :
  ¬ (∀ (n : ℕ) (h_n : n > 2), A309391 n = n → Nat.Prime n) := by
  intro h
  have h1 : ¬ Nat.Prime (16843 * 16843) := not_prime_of_mul 16843 16843 (by decide) (by decide)
  have h2 : A309391 283686649 = 283686649 := by
    have h_n_pos : 283686649 ≥ 3 := by decide
    have h_eq_cast : harmonic_number (283686649 - 2) =
         ((N_U_nat * sum_16842_bin_exact.2 + 283686649 * (sum_16842_bin_exact.1 / 4778134229107) * D_U_nat : ℤ) : ℚ) /
         ((D_U_nat * sum_16842_bin_exact.2 : ℕ) : ℚ) := by
      have h_pow1 : 16843^2 = 283686649 := by decide
      have h_step := final_algebraic_step
      rw [h_pow1] at h_step
      rw [h_step]
      exact cast_div_eq _ _
    have h_div_cast : (sum_16842_bin_exact.1 : ℤ) / (4778134229107 : ℤ) = ((sum_16842_bin_exact.1 / 4778134229107 : ℕ) : ℤ) := by push_cast; rfl
    have h_D_H_cast : (sum_16842_bin_exact.2 : ℤ) = ((sum_16842_bin_exact.2 : ℕ) : ℤ) := rfl
    have h_final_dvd := final_dvd_A_minus_B sum_16842_bin_exact.2 (sum_16842_bin_exact.1 / 4778134229107) h_div_cast h_D_H_cast
    have h_dvd : ((283686649 : ℕ) : ℤ) ∣ (harmonic_number (283686649 - 2)).num - ((harmonic_number (283686649 - 2)).den : ℤ) := by
      exact dvd_num_minus_den_of_eq_fraction (hn := h_n_pos) (h_eq := h_eq_cast) (h_coprime := coprime_B) (h_dvd := h_final_dvd)
    have h_dvd_nat : 283686649 ∣ (((harmonic_number (283686649 - 2)).num - (harmonic_number (283686649 - 2)).den : ℤ).natAbs) := by
      have h_dvd_abs := @Int.natAbs_dvd_natAbs ((283686649 : ℕ) : ℤ) ((harmonic_number (283686649 - 2)).num - ((harmonic_number (283686649 - 2)).den : ℤ))
      have h_abs_n : (((283686649 : ℕ) : ℤ)).natAbs = 283686649 := rfl
      rw [h_abs_n] at h_dvd_abs
      exact h_dvd_abs.mpr h_dvd
    unfold A309391
    have h_not_lt : ¬ 283686649 < 3 := by decide
    rw [if_neg h_not_lt]
    exact Nat.gcd_eq_left h_dvd_nat
  exact h1 (h 283686649 (by decide) h2)
