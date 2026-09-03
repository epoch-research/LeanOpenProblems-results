import FormalConjecturesUtil

/-!
# Arithmetic parameters for the finite FT squarefree bound

This file contains only arithmetic estimates.  The constants are `D = 2^20` and
`A = 2^60`; the natural-number quotient in `B` is intentional.
-/

namespace FTParameters

/-- The denominator in the summable per-band error. -/
def D : ℕ := 2 ^ 20

/-- The scale of the left endpoint of a band. -/
def A : ℕ := 2 ^ 60

/-- The left endpoint of a band. -/
def N (H j s : ℕ) : ℕ := A * H * 16 ^ j * 2 ^ s

/-- The integer quotient used as the first rectangle parameter. -/
def B (H q j s : ℕ) : ℕ := N H j s / q

/-- The second rectangle parameter. -/
def V (H q j s : ℕ) : ℕ := B H q j s * 2 ^ (19 + j)

theorem D_pos : 0 < D := by norm_num [D]

theorem A_pos : 0 < A := by norm_num [A]

/-- Every band starts at least `256 * H`. -/
theorem large_N (H j s : ℕ) : 256 * H ≤ N H j s := by
  unfold N
  calc
    256 * H ≤ A * H := Nat.mul_le_mul_right H (by norm_num [A])
    _ ≤ A * H * 16 ^ j := Nat.le_mul_of_pos_right _ (by positivity)
    _ ≤ A * H * 16 ^ j * 2 ^ s := Nat.le_mul_of_pos_right _ (by positivity)

theorem H_le_N (H j s : ℕ) : H ≤ N H j s := by
  have h := large_N H j s
  omega

theorem N_pos {H : ℕ} (j s : ℕ) (hH : 0 < H) : 0 < N H j s :=
  lt_of_lt_of_le hH (H_le_N H j s)

theorem B_pos {H q : ℕ} (j s : ℕ) (hq : 0 < q) (hqH : q ≤ H) :
    0 < B H q j s :=
  Nat.div_pos (hqH.trans (H_le_N H j s)) hq

theorem V_pos {H q : ℕ} (j s : ℕ) (hq : 0 < q) (hqH : q ≤ H) :
    0 < V H q j s := by
  unfold V
  exact Nat.mul_pos (B_pos j s hq hqH) (by positivity)

theorem q_mul_B_le (H q j s : ℕ) : q * B H q j s ≤ N H j s :=
  Nat.mul_div_le _ _

/-- The two elementary quotient estimates, including the factor-two upper bound. -/
theorem quotient_bounds {H q : ℕ} (j s : ℕ) (hq : 0 < q) (hqH : q ≤ H) :
    q * B H q j s ≤ N H j s ∧
      N H j s < q * (B H q j s + 1) ∧
      q * (B H q j s + 1) ≤ 2 * q * B H q j s := by
  refine ⟨q_mul_B_le H q j s, Nat.lt_mul_div_succ _ hq, ?_⟩
  have hB := B_pos j s hq hqH
  calc
    q * (B H q j s + 1) ≤ q * (2 * B H q j s) :=
      Nat.mul_le_mul_left q (by omega)
    _ = 2 * q * B H q j s := by ring

/-- The `x` term loses only one factor of `q`, despite `x ≤ q^5`. -/
theorem x_mul_B_pow_four_le {x q : ℕ} (H j s : ℕ) (hx : x ≤ q ^ 5) :
    x * B H q j s ^ 4 ≤ q * N H j s ^ 4 := by
  calc
    x * B H q j s ^ 4 ≤ q ^ 5 * B H q j s ^ 4 := Nat.mul_le_mul_right _ hx
    _ = q * (q * B H q j s) ^ 4 := by ring
    _ ≤ q * N H j s ^ 4 :=
      Nat.mul_le_mul_left q (Nat.pow_le_pow_left (q_mul_B_le H q j s) 4)

/-- The precise power identity behind the smallness estimate. -/
theorem eight_mul_pow_cube (j : ℕ) : 8 * (2 ^ (19 + j)) ^ 3 = A * 8 ^ j := by
  have hj : (2 ^ j : ℕ) ^ 3 = 8 ^ j := by
    rw [← pow_mul, Nat.mul_comm j 3, pow_mul]
    norm_num
  calc
    8 * (2 ^ (19 + j)) ^ 3 = (8 * (2 ^ 19) ^ 3) * (2 ^ j) ^ 3 := by
      rw [pow_add, mul_pow]
      ring
    _ = A * 8 ^ j := by rw [hj]; norm_num [A]

theorem q_mul_A_mul_eight_pow_le {H q : ℕ} (j s : ℕ) (hqH : q ≤ H) :
    q * A * 8 ^ j ≤ N H j s := by
  have hp : 8 ^ j ≤ 16 ^ j * 2 ^ s :=
    (Nat.pow_le_pow_left (by decide : 8 ≤ 16) j).trans
      (Nat.le_mul_of_pos_right _ (by positivity))
  calc
    q * A * 8 ^ j ≤ H * A * (16 ^ j * 2 ^ s) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right A hqH) hp
    _ = N H j s := by unfold N; ring

/-- A division-free smallness estimate, with the explicit margin `5/8`. -/
theorem smallness_margin {x H q : ℕ} (j s : ℕ) (hqH : q ≤ H) (hx : x ≤ q ^ 5) :
    8 * (5 * x * B H q j s * V H q j s ^ 3) ≤ 5 * N H j s ^ 5 := by
  calc
    8 * (5 * x * B H q j s * V H q j s ^ 3) =
        5 * (x * B H q j s ^ 4) * (8 * (2 ^ (19 + j)) ^ 3) := by
      unfold V
      rw [mul_pow]
      ring
    _ = 5 * (x * B H q j s ^ 4) * (A * 8 ^ j) := by rw [eight_mul_pow_cube]
    _ ≤ 5 * (q * N H j s ^ 4) * (A * 8 ^ j) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 5 (x_mul_B_pow_four_le H j s hx))
    _ = 5 * (q * A * 8 ^ j) * N H j s ^ 4 := by ring
    _ ≤ 5 * N H j s * N H j s ^ 4 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 5 (q_mul_A_mul_eight_pow_le j s hqH))
    _ = 5 * N H j s ^ 5 := by ring

theorem smallness {x H q : ℕ} (j s : ℕ) (hq : 0 < q) (hqH : q ≤ H)
    (hx : x ≤ q ^ 5) :
    5 * x * B H q j s * V H q j s ^ 3 < N H j s ^ 5 := by
  apply Nat.lt_of_mul_lt_mul_left (a := 8)
  calc
    8 * (5 * x * B H q j s * V H q j s ^ 3) ≤ 5 * N H j s ^ 5 :=
      smallness_margin j s hqH hx
    _ < 8 * N H j s ^ 5 :=
      Nat.mul_lt_mul_of_pos_right (by decide) (pow_pos (N_pos j s (hq.trans_le hqH)) 5)

/-- All the natural-number hypotheses needed for one FT band. -/
theorem parameter_bounds {x H q : ℕ} (j s : ℕ) (hq : 0 < q) (hqH : q ≤ H)
    (hx : x ≤ q ^ 5) :
    0 < N H j s ∧ 256 * H ≤ N H j s ∧ 0 < B H q j s ∧ 0 < V H q j s ∧
      5 * x * B H q j s * V H q j s ^ 3 < N H j s ^ 5 :=
  ⟨N_pos j s (hq.trans_le hqH), large_N H j s, B_pos j s hq hqH,
    V_pos j s hq hqH, smallness j s hq hqH hx⟩

/-- The natural quotient is large enough to bound the rational ratio. -/
theorem N_div_B_le {H q : ℕ} (j s : ℕ) (hq : 0 < q) (hqH : q ≤ H) :
    (N H j s : ℚ) / (B H q j s : ℚ) ≤ 2 * (q : ℚ) := by
  apply (div_le_iff₀ (show (0 : ℚ) < (B H q j s : ℚ) by
    exact_mod_cast B_pos j s hq hqH)).2
  have hb := quotient_bounds j s hq hqH
  exact_mod_cast hb.2.1.le.trans hb.2.2

theorem x_term_le {x H q : ℕ} (j s : ℕ) (hq : 0 < q) (hqH : q ≤ H)
    (hx : x ≤ q ^ 5) :
    (x : ℚ) * (B H q j s : ℚ) ^ 4 / (N H j s : ℚ) ^ 4 ≤ (q : ℚ) := by
  have hN : (0 : ℚ) < (N H j s : ℚ) := by
    exact_mod_cast N_pos j s (hq.trans_le hqH)
  apply (div_le_iff₀ (pow_pos hN 4)).2
  exact_mod_cast x_mul_B_pow_four_le H j s hx

/-- Cancellation of `B` makes the error independent of both `q` and `s`. -/
theorem error_eq {H q : ℕ} (j s : ℕ) (hB : 0 < B H q j s) :
    1440 * (H : ℚ) * (B H q j s : ℚ) / (V H q j s : ℚ) =
      2880 * (H : ℚ) / ((D : ℚ) * 2 ^ j) := by
  have hBne : (B H q j s : ℚ) ≠ 0 := by exact_mod_cast hB.ne'
  simp only [V, D, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  field_simp
  ring

/-- Convert the rational FT rectangle estimate to the summable per-band bound. -/
theorem band_bound {x H q t : ℕ} (j s : ℕ) (hq : 0 < q) (hqH : q ≤ H)
    (hx : x ≤ q ^ 5)
    (ht : (t : ℚ) ≤ 2 + 2 * (N H j s : ℚ) / (B H q j s : ℚ) +
      8 * (x : ℚ) * (B H q j s : ℚ) ^ 4 / (N H j s : ℚ) ^ 4 +
      1440 * (H : ℚ) * (B H q j s : ℚ) / (V H q j s : ℚ)) :
    (t : ℚ) ≤ 14 * (q : ℚ) + 2880 * (H : ℚ) / ((D : ℚ) * 2 ^ j) := by
  have hq' : (1 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hratio := mul_le_mul_of_nonneg_left (N_div_B_le j s hq hqH)
    (by norm_num : (0 : ℚ) ≤ 2)
  have hxterm := mul_le_mul_of_nonneg_left (x_term_le j s hq hqH hx)
    (by norm_num : (0 : ℚ) ≤ 8)
  rw [error_eq j s (B_pos j s hq hqH)] at ht
  simp only [div_eq_mul_inv] at ht hratio hxterm ⊢
  linarith

/-- A natural-number, division-free form of the per-band bound. -/
theorem band_bound_nat {x H q t : ℕ} (j s : ℕ) (hq : 0 < q) (hqH : q ≤ H)
    (hx : x ≤ q ^ 5)
    (ht : (t : ℚ) ≤ 2 + 2 * (N H j s : ℚ) / (B H q j s : ℚ) +
      8 * (x : ℚ) * (B H q j s : ℚ) ^ 4 / (N H j s : ℚ) ^ 4 +
      1440 * (H : ℚ) * (B H q j s : ℚ) / (V H q j s : ℚ)) :
    D * 2 ^ j * t ≤ 14 * q * D * 2 ^ j + 2880 * H := by
  have hd : (0 : ℚ) < (D : ℚ) * 2 ^ j :=
    mul_pos (by exact_mod_cast D_pos) (by positivity)
  have h := mul_le_mul_of_nonneg_left (band_bound j s hq hqH hx ht) hd.le
  have heq : ((D : ℚ) * 2 ^ j) *
      (14 * (q : ℚ) + 2880 * (H : ℚ) / ((D : ℚ) * 2 ^ j)) =
      14 * (q : ℚ) * (D : ℚ) * 2 ^ j + 2880 * (H : ℚ) := by
    have hDne : (D : ℚ) ≠ 0 := by exact_mod_cast D_pos.ne'
    field_simp [hDne]
  rw [heq] at h
  exact_mod_cast h

/-- The finite dyadic geometric sum is at most two, including when `J = 0`. -/
theorem geometric_sum_le (J : ℕ) :
    (∑ j : Fin J, (1 : ℚ) / 2 ^ (j : ℕ)) ≤ 2 := by
  calc
    (∑ j : Fin J, (1 : ℚ) / 2 ^ (j : ℕ)) =
        ∑ j ∈ Finset.range J, (1 / 2 : ℚ) ^ j := by
      rw [Fin.sum_univ_eq_sum_range (fun j => (1 : ℚ) / 2 ^ j) J]
      simp only [div_pow, one_pow]
    _ ≤ 2 := by
      have h := geom_sum_mul_neg (1 / 2 : ℚ) J
      have hp : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ J := by positivity
      norm_num at h
      linarith

/-- Sum four subbands at each dyadic scale, before imposing the size of `H`. -/
theorem sum_band_estimates (H q J : ℕ) (t : Fin J → Fin 4 → ℕ)
    (ht : ∀ (j : Fin J) (s : Fin 4),
      (t j s : ℚ) ≤ 14 * (q : ℚ) + 2880 * (H : ℚ) / ((D : ℚ) * 2 ^ (j : ℕ))) :
    ((∑ j : Fin J, ∑ s : Fin 4, t j s : ℕ) : ℚ) ≤
      56 * (q : ℚ) * (J : ℚ) + 23040 * (H : ℚ) / (D : ℚ) := by
  have hfirst : ((∑ j : Fin J, ∑ s : Fin 4, t j s : ℕ) : ℚ) ≤
      ∑ j : Fin J, 4 * (14 * (q : ℚ) +
        2880 * (H : ℚ) / ((D : ℚ) * 2 ^ (j : ℕ))) := by
    push_cast
    apply Finset.sum_le_sum
    intro j hj
    calc
      (∑ s : Fin 4, (t j s : ℚ)) ≤
          ∑ _s : Fin 4, (14 * (q : ℚ) +
            2880 * (H : ℚ) / ((D : ℚ) * 2 ^ (j : ℕ))) :=
        Finset.sum_le_sum (fun s _hs => ht j s)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_ofNat]
  have heq : (∑ j : Fin J, 4 * (14 * (q : ℚ) +
      2880 * (H : ℚ) / ((D : ℚ) * 2 ^ (j : ℕ)))) =
      56 * (q : ℚ) * (J : ℚ) +
        (11520 * (H : ℚ) / (D : ℚ)) * (∑ j : Fin J, (1 : ℚ) / 2 ^ (j : ℕ)) := by
    calc
      _ = ∑ j : Fin J, (56 * (q : ℚ) +
          (11520 * (H : ℚ) / (D : ℚ)) * ((1 : ℚ) / 2 ^ (j : ℕ))) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
        ring
  rw [heq] at hfirst
  have herr := mul_le_mul_of_nonneg_left (geometric_sum_le J)
    (show (0 : ℚ) ≤ 11520 * (H : ℚ) / (D : ℚ) by positivity)
  calc
    _ ≤ 56 * (q : ℚ) * (J : ℚ) +
        (11520 * (H : ℚ) / (D : ℚ)) * (∑ j : Fin J, (1 : ℚ) / 2 ^ (j : ℕ)) := hfirst
    _ ≤ 56 * (q : ℚ) * (J : ℚ) + (11520 * (H : ℚ) / (D : ℚ)) * 2 :=
      add_le_add le_rfl herr
    _ = _ := by ring

/-- The global scale hypothesis implies the weaker per-band hypothesis. -/
theorem q_le_H {H q J : ℕ} (hH : 2048 * q * (J + 1) ≤ H) : q ≤ H := by
  calc
    q ≤ 2048 * q := Nat.le_mul_of_pos_left _ (by decide)
    _ ≤ 2048 * q * (J + 1) := Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ H := hH

/-- The sharper aggregate coefficient is `101 / 2048`. -/
theorem sum_bound_sharp {H q J : ℕ} (t : Fin J → Fin 4 → ℕ)
    (hH : 2048 * q * (J + 1) ≤ H)
    (ht : ∀ (j : Fin J) (s : Fin 4),
      (t j s : ℚ) ≤ 14 * (q : ℚ) + 2880 * (H : ℚ) / ((D : ℚ) * 2 ^ (j : ℕ))) :
    2048 * (∑ j : Fin J, ∑ s : Fin 4, t j s) ≤ 101 * H := by
  have hqJ : (2048 : ℚ) * (q : ℚ) * (J : ℚ) ≤ (H : ℚ) := by
    exact_mod_cast (Nat.mul_le_mul_left (2048 * q) (Nat.le_succ J)).trans hH
  have hsum := sum_band_estimates H q J t ht
  norm_num [D] at hsum
  have h : (2048 : ℚ) * ((∑ j : Fin J, ∑ s : Fin 4, t j s : ℕ) : ℚ) ≤
      101 * (H : ℚ) := by
    push_cast
    linarith
  exact_mod_cast h

/-- The required global estimate for counts satisfying the simplified band bound. -/
theorem sum_bound {H q J : ℕ} (t : Fin J → Fin 4 → ℕ)
    (hH : 2048 * q * (J + 1) ≤ H)
    (ht : ∀ (j : Fin J) (s : Fin 4),
      (t j s : ℚ) ≤ 14 * (q : ℚ) + 2880 * (H : ℚ) / ((D : ℚ) * 2 ^ (j : ℕ))) :
    16 * (∑ j : Fin J, ∑ s : Fin 4, t j s) ≤ H := by
  have h := sum_bound_sharp t hH ht
  omega

/-- Apply the original rational estimate in every band and sum the resulting counts. -/
theorem total_bound {x H q J : ℕ} (t : Fin J → Fin 4 → ℕ)
    (hq : 0 < q) (hx : x ≤ q ^ 5) (hH : 2048 * q * (J + 1) ≤ H)
    (ht : ∀ (j : Fin J) (s : Fin 4),
      (t j s : ℚ) ≤ 2 + 2 * (N H j s : ℚ) / (B H q j s : ℚ) +
        8 * (x : ℚ) * (B H q j s : ℚ) ^ 4 / (N H j s : ℚ) ^ 4 +
        1440 * (H : ℚ) * (B H q j s : ℚ) / (V H q j s : ℚ)) :
    16 * (∑ j : Fin J, ∑ s : Fin 4, t j s) ≤ H := by
  apply sum_bound t hH
  intro j s
  exact band_bound j s hq (q_le_H hH) hx (ht j s)

end FTParameters
