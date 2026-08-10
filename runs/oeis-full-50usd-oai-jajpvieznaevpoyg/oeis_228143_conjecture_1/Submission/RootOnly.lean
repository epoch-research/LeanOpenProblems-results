import FormalConjectures.Util.ProblemImports
open PowerSeries BigOperators Finset
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0

lemma coeff_error_high_int (n : ℕ) (S : PowerSeries ℤ) (c : ℤ) :
    PowerSeries.coeff (n+1) ((PowerSeries.monomial (n+1) c)^2 * S) = 0 := by
  rw [PowerSeries.monomial_eq_C_mul_X_pow]
  rw [show (PowerSeries.C c * (PowerSeries.X : PowerSeries ℤ) ^ (n+1)) ^ 2 * S =
      ((PowerSeries.C c)^2 * S) * (PowerSeries.X : PowerSeries ℤ) ^ (2*(n+1)) by ring]
  rw [PowerSeries.coeff_mul_X_pow']
  have h : n + 1 < 2 * (n + 1) := by omega
  simp [h]

lemma coeff_pow7_mul_monomial_high_int (n : ℕ) (P : PowerSeries ℤ) (c : ℤ)
    (hP0 : PowerSeries.coeff 0 P = 1) :
    PowerSeries.coeff (n+1) (P ^ 7 * PowerSeries.monomial (n+1) c) = c := by
  rw [PowerSeries.monomial_eq_C_mul_X_pow]
  rw [← mul_assoc]
  rw [PowerSeries.coeff_mul_X_pow']
  have hc : PowerSeries.constantCoeff P = 1 := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hP0
  simp [hc]

lemma coeff_pow8_add_monomial_high_int (n : ℕ) (P : PowerSeries ℤ) (c : ℤ)
    (hP0 : PowerSeries.coeff 0 P = 1) :
    PowerSeries.coeff (n+1) ((P + PowerSeries.monomial (n+1) c) ^ 8)
      = PowerSeries.coeff (n+1) (P ^ 8) + 8 * c := by
  let M : PowerSeries ℤ := PowerSeries.monomial (n+1) c
  let S : PowerSeries ℤ :=
    28 • P^6 + 56 • (P^5*M) + 70 • (P^4*M^2) + 56 • (P^3*M^3) +
    28 • (P^2*M^4) + 8 • (P*M^5) + M^6
  have hid : (P + M)^8 = P^8 + 8 • (P^7 * M) + M^2 * S := by
    dsimp [S]
    ring
  change PowerSeries.coeff (n+1) ((P + M)^8) = PowerSeries.coeff (n+1) (P^8) + 8*c
  rw [hid]
  simp only [map_add, map_nsmul]
  rw [coeff_pow7_mul_monomial_high_int n P c hP0]
  have herr : PowerSeries.coeff (n+1) (M^2 * S) = 0 := by
    dsimp [M]
    exact coeff_error_high_int n S c
  rw [herr]
  simp

lemma coeff_pos_pow8_one_add_two_dvd16_int (E : PowerSeries ℤ) {m : ℕ} (hm : 0 < m) :
    (16 : ℤ) ∣ PowerSeries.coeff m ((1 + 2 • E) ^ 8) := by
  let S : PowerSeries ℤ := E + 7 • E^2 + 28 • E^3 + 70 • E^4 + 112 • E^5 + 112 • E^6 + 64 • E^7 + 16 • E^8
  have hid : (1 + 2 • E)^8 = 1 + 16 • S := by
    dsimp [S]
    ring
  rw [hid]
  use PowerSeries.coeff m S
  simp [hm.ne']
  change PowerSeries.coeff m (PowerSeries.C (16 : ℤ) * S) = 16 * PowerSeries.coeff m S
  rw [PowerSeries.coeff_C_mul]

noncomputable def rootCoeff16 (d : ℕ → ℤ) : ℕ → ℤ
| 0 => 1
| n+1 =>
    ((16 * d (n+1) - PowerSeries.coeff (n+1)
      ((PowerSeries.mk fun k => if h : k < n+1 then rootCoeff16 d k else 0 : PowerSeries ℤ) ^ 8)) / 8)
termination_by n => n

lemma rootCoeff16_zero (d : ℕ → ℤ) : rootCoeff16 d 0 = 1 := rootCoeff16.eq_1 d

lemma partial_const16 (d : ℕ → ℤ) (n : ℕ) :
    PowerSeries.coeff 0 (PowerSeries.mk fun k => if h : k < n+1 then rootCoeff16 d k else 0 : PowerSeries ℤ) = 1 := by
  simp [rootCoeff16_zero]

lemma partial_as_one_add_two16 (d : ℕ → ℤ) (n : ℕ)
    (hev : ∀ k, 0 < k → k < n+1 → (2 : ℤ) ∣ rootCoeff16 d k) :
    ∃ E : PowerSeries ℤ, (PowerSeries.mk fun k => if h : k < n+1 then rootCoeff16 d k else 0 : PowerSeries ℤ) = 1 + 2 • E := by
  let E : PowerSeries ℤ := PowerSeries.mk fun k => if k = 0 then 0 else ((if h : k < n+1 then rootCoeff16 d k else 0 : ℤ) / 2)
  refine ⟨E, ?_⟩
  ext k
  by_cases hk0 : k = 0
  · subst hk0
    simp [E, rootCoeff16_zero]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    by_cases hkn : k < n+1
    · obtain ⟨z, hz⟩ := hev k hkpos hkn
      have hklen : k ≤ n := by omega
      simp only [map_add, PowerSeries.coeff_one, PowerSeries.coeff_mk, PowerSeries.coeff_smul]
      simp [E, hk0, hkn, hklen, hz]
    · have hklen : ¬ k ≤ n := by omega
      simp only [map_add, PowerSeries.coeff_one, PowerSeries.coeff_mk, PowerSeries.coeff_smul]
      simp [E, hk0, hkn, hklen]

lemma partial_pow8_coeff_dvd16_16 (d : ℕ → ℤ) (n : ℕ)
    (hev : ∀ k, 0 < k → k < n+1 → (2 : ℤ) ∣ rootCoeff16 d k) :
    (16 : ℤ) ∣ PowerSeries.coeff (n+1)
      ((PowerSeries.mk fun k => if h : k < n+1 then rootCoeff16 d k else 0 : PowerSeries ℤ) ^ 8) := by
  obtain ⟨E, hE⟩ := partial_as_one_add_two16 d n hev
  rw [hE]
  exact coeff_pos_pow8_one_add_two_dvd16_int E (Nat.succ_pos n)

lemma div16_sub_div8_eq (a z : ℤ) : (16 * a - 16 * z) / 8 = 2 * (a - z) := by
  rw [show 16 * a - 16 * z = 8 * (2 * (a - z)) by ring]
  rw [Int.mul_ediv_cancel_left]
  norm_num

lemma rootCoeff16_even_pos (d : ℕ → ℤ) : ∀ n, 0 < n → (2 : ℤ) ∣ rootCoeff16 d n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => omega
    | succ m =>
      rw [rootCoeff16.eq_2]
      have hev : ∀ k, 0 < k → k < m+1 → (2 : ℤ) ∣ rootCoeff16 d k := by
        intro k hkpos hkm
        exact ih k (by omega) hkpos
      obtain ⟨z, hz⟩ := partial_pow8_coeff_dvd16_16 d m hev
      rw [hz, div16_sub_div8_eq]
      simpa [mul_comm] using dvd_mul_left 2 (d (m+1) - z)

lemma coeff_pow_eq_coeff_trunc_pow16 {m a : ℕ} (f : PowerSeries ℤ) :
    PowerSeries.coeff m (f^a) = PowerSeries.coeff m (((PowerSeries.trunc (m+1) f : Polynomial ℤ) : PowerSeries ℤ)^a) := by
  rw [← PowerSeries.coeff_coe_trunc_of_lt (f := f^a) (n := m) (m := m+1) (Nat.lt_succ_self m)]
  rw [← PowerSeries.coeff_coe_trunc_of_lt (f := (((PowerSeries.trunc (m+1) f : Polynomial ℤ) : PowerSeries ℤ)^a)) (n := m) (m := m+1) (Nat.lt_succ_self m)]
  congr 1
  exact congr_arg (fun p : Polynomial ℤ => (p : PowerSeries ℤ)) (PowerSeries.trunc_trunc_pow f (m+1) a).symm

lemma coeff_eq_of_trunc_eq_pow8 {m : ℕ} {f g : PowerSeries ℤ}
    (h : PowerSeries.trunc (m+1) f = PowerSeries.trunc (m+1) g) :
    PowerSeries.coeff m (f^8) = PowerSeries.coeff m (g^8) := by
  rw [coeff_pow_eq_coeff_trunc_pow16 (m := m) (a := 8) f]
  rw [coeff_pow_eq_coeff_trunc_pow16 (m := m) (a := 8) g]
  rw [h]

lemma trunc_C_eq_partial_add_monomial (d : ℕ → ℤ) (n : ℕ) :
    PowerSeries.trunc (n+2) (PowerSeries.mk (rootCoeff16 d)) =
    PowerSeries.trunc (n+2)
      ((PowerSeries.mk fun k => if h : k < n+1 then rootCoeff16 d k else 0 : PowerSeries ℤ)
        + PowerSeries.monomial (n+1) (rootCoeff16 d (n+1))) := by
  ext k
  simp only [map_add, Polynomial.coeff_add, PowerSeries.coeff_trunc, PowerSeries.coeff_mk,
    PowerSeries.coeff_monomial]
  by_cases hk : k < n + 2
  · simp [hk]
    have hle : k ≤ n+1 := by omega
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · have hne : k ≠ n+1 := by omega
      simp [hlt, hne]
      intro hbad
      omega
    · subst heq
      simp
  · simp [hk]

lemma rootCoeff16_spec_int (d : ℕ → ℤ) :
    (PowerSeries.mk (rootCoeff16 d) : PowerSeries ℤ) ^ 8 =
      PowerSeries.mk fun n => if n = 0 then 1 else 16 * d n := by
  ext m
  cases m with
  | zero =>
    simp [rootCoeff16_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    let P : PowerSeries ℤ := PowerSeries.mk fun k => if h : k < n+1 then rootCoeff16 d k else 0
    let c : ℤ := rootCoeff16 d (n+1)
    have hcoeff : PowerSeries.coeff (n+1) ((PowerSeries.mk (rootCoeff16 d) : PowerSeries ℤ)^8)
        = PowerSeries.coeff (n+1) ((P + PowerSeries.monomial (n+1) c)^8) := by
      apply coeff_eq_of_trunc_eq_pow8
      dsimp [P, c]
      exact trunc_C_eq_partial_add_monomial d n
    rw [hcoeff]
    have hP0 : PowerSeries.coeff 0 P = 1 := by dsimp [P]; exact partial_const16 d n
    rw [coeff_pow8_add_monomial_high_int n P c hP0]
    dsimp [c]
    have hev : ∀ k, 0 < k → k < n+1 → (2 : ℤ) ∣ rootCoeff16 d k := by
      intro k hkpos hkn
      exact rootCoeff16_even_pos d k hkpos
    obtain ⟨z, hz⟩ := partial_pow8_coeff_dvd16_16 d n hev
    dsimp [P] at hz
    change PowerSeries.coeff (n+1) (P^8) = 16 * z at hz
    rw [rootCoeff16.eq_2]
    change PowerSeries.coeff (n+1) (P ^ 8) +
      8 * ((16 * d (n+1) - PowerSeries.coeff (n+1) (P ^ 8)) / 8) =
      PowerSeries.coeff (n+1) (PowerSeries.mk fun n => if n = 0 then 1 else 16 * d n)
    rw [hz, div16_sub_div8_eq]
    simp
    ring
