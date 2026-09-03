import FormalConjecturesUtil

/-!
Exact finite-group rectangle counts, and a conditional first-moment budget
for voltage covers. No commutativity of the group is assumed. These results
are not bounds on all deterministic covers and do not settle Erdős 714.
-/

open Finset Classical
set_option maxHeartbeats 1000000

namespace Erdos714RandomVoltage

variable {I J Γ : Type*} [Group Γ]

abbrev Matrix := Option I → Option J → Γ

/-- Flatness relative to the distinguished row and column. -/
def Flat (M : Matrix (I := I) (J := J) (Γ := Γ)) : Prop :=
  ∀ i j, M i j = M i none * (M none none)⁻¹ * M none j

/-- Actual sheet assignments for one indexed base rectangle. -/
def Lifts (M : Matrix (I := I) (J := J) (Γ := Γ)) :=
  {p : (Option I → Γ) × (Option J → Γ) // ∀ i j, p.2 j = p.1 i * M i j}

/-- Anchor the sheet on the distinguished row at the identity. -/
def flatEquiv : {M : Matrix (I := I) (J := J) (Γ := Γ) // Flat M} ≃
    (I → Γ) × (Option J → Γ) where
  toFun M := (fun i => M.val none none * (M.val (some i) none)⁻¹, M.val none)
  invFun p := ⟨fun i j => (i.elim 1 p.1)⁻¹ * p.2 j, by
    intro i j
    simp only [Option.elim_none, inv_one, one_mul]
    group⟩
  left_inv M := by
    apply Subtype.ext
    funext i j
    cases i with
    | none => simp
    | some i =>
      change (M.val none none * (M.val (some i) none)⁻¹)⁻¹ * M.val none j = _
      rw [M.property (some i) j]
      group
  right_inv p := by
    apply Prod.ext
    · funext i
      change (1⁻¹ * p.2 none) * ((p.1 i)⁻¹ * p.2 none)⁻¹ = p.1 i
      group
    · funext j
      simp

/-- All sheet assignments are obtained by a common left translation. -/
def liftsEquiv (M : Matrix (I := I) (J := J) (Γ := Γ)) (hM : Flat M) :
    Lifts M ≃ Γ where
  toFun p := p.val.1 none
  invFun g := ⟨(fun i => g * M none none * (M i none)⁻¹,
      fun j => g * M none j), by
    intro i j
    dsimp only
    rw [hM i j]
    group⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      change p.val.1 none * M none none * (M i none)⁻¹ = p.val.1 i
      rw [← p.property none none, p.property i none]
      group
    · funext j
      exact (p.property none j).symm
  right_inv g := by
    change g * M none none * (M none none)⁻¹ = g
    group

lemma flat_of_lift {M : Matrix (I := I) (J := J) (Γ := Γ)} (p : Lifts M) : Flat M := by
  have he (i j) : M i j = (p.val.1 i)⁻¹ * p.val.2 j := by
    rw [p.property i j]
    group
  intro i j
  simp only [he]
  group

/-- Jointly choosing voltages and a lift is equivalent to choosing the sheets;
the voltages are then forced. -/
def allLiftsEquiv : (Σ M : Matrix (I := I) (J := J) (Γ := Γ), Lifts M) ≃
    (Option I → Γ) × (Option J → Γ) where
  toFun p := p.2.val
  invFun p := ⟨fun i j => (p.1 i)⁻¹ * p.2 j, ⟨p, by
    intro i j
    dsimp only
    group⟩⟩
  left_inv p := by
    rcases p with ⟨M, p, hp⟩
    have he : (fun i j => (p.1 i)⁻¹ * p.2 j) = M := by
      funext i j
      rw [hp i j]
      group
    dsimp only
    cases he
    rfl
  right_inv p := rfl

variable [Fintype I] [Fintype J] [Fintype Γ]

noncomputable instance (M : Matrix (I := I) (J := J) (Γ := Γ)) : Fintype (Lifts M) := by
  unfold Lifts
  infer_instance

/-- There are q^(r+s-1) flat r-by-s matrices. -/
theorem card_flat : Fintype.card {M : Matrix (I := I) (J := J) (Γ := Γ) // Flat M} =
    Fintype.card Γ ^ (Fintype.card I + Fintype.card J + 1) := by
  rw [Fintype.card_congr flatEquiv]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_option, ← pow_add]
  congr 1

/-- The fraction of flat matrices is exactly q^(-(r-1)(s-1)), expressed
without division. It depends on group order, not on commutativity. -/
theorem card_flat_mul :
    Fintype.card {M : Matrix (I := I) (J := J) (Γ := Γ) // Flat M} *
        Fintype.card Γ ^ (Fintype.card I * Fintype.card J) =
      Fintype.card (Matrix (I := I) (J := J) (Γ := Γ)) := by
  rw [card_flat]
  simp only [Matrix, Fintype.card_fun, Fintype.card_option, ← pow_add, ← pow_mul]
  congr 1
  ring

theorem card_lifts (M : Matrix (I := I) (J := J) (Γ := Γ)) :
    Fintype.card (Lifts M) = if Flat M then Fintype.card Γ else 0 := by
  by_cases hM : Flat M
  · rw [if_pos hM]
    exact Fintype.card_congr (liftsEquiv M hM)
  · rw [if_neg hM]
    letI : IsEmpty (Lifts M) := ⟨fun p => hM (flat_of_lift p)⟩
    exact Fintype.card_of_isEmpty

/-- Sum over all voltage assignments. This is the numerator of the exact
expected number of lifts under independent uniform edge labels. -/
theorem sum_card_lifts :
    (∑ M : Matrix (I := I) (J := J) (Γ := Γ), Fintype.card (Lifts M)) =
      Fintype.card Γ ^ (Fintype.card I + Fintype.card J + 2) := by
  rw [← Fintype.card_sigma, Fintype.card_congr allLiftsEquiv]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_option, ← pow_add]
  congr 1
  omega

/-- Expected lifts, after clearing the common denominator. -/
theorem sum_card_lifts_mul :
    (∑ M : Matrix (I := I) (J := J) (Γ := Γ), Fintype.card (Lifts M)) *
        Fintype.card Γ ^ (Fintype.card I * Fintype.card J) =
      Fintype.card Γ * Fintype.card (Matrix (I := I) (J := J) (Γ := Γ)) := by
  rw [sum_card_lifts]
  simp only [Matrix, Fintype.card_fun, Fintype.card_option, ← pow_add, ← pow_mul]
  rw [← pow_succ']
  congr 1
  ring

/-- Exact probability for independently uniform labels on a rectangle. -/
theorem flat_fraction :
    (Fintype.card {M : Matrix (I := I) (J := J) (Γ := Γ) // Flat M} : ℚ) /
        Fintype.card (Matrix (I := I) (J := J) (Γ := Γ)) =
      1 / (Fintype.card Γ : ℚ) ^ (Fintype.card I * Fintype.card J) := by
  have h := congrArg (fun n : ℕ => (n : ℚ)) (card_flat_mul (I := I) (J := J) (Γ := Γ))
  push_cast at h
  apply (div_eq_div_iff (by exact_mod_cast Fintype.card_ne_zero)
    (pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero))).mpr
  simpa only [one_mul] using h

/-- Exact expectation for independently uniform labels on a rectangle.
The factor q, rather than 1, counts the distinct common sheet translations. -/
theorem average_lifts :
    (∑ M : Matrix (I := I) (J := J) (Γ := Γ), (Fintype.card (Lifts M) : ℚ)) /
        Fintype.card (Matrix (I := I) (J := J) (Γ := Γ)) =
      Fintype.card Γ / (Fintype.card Γ : ℚ) ^ (Fintype.card I * Fintype.card J) := by
  have h := congrArg (fun n : ℕ => (n : ℚ))
    (sum_card_lifts_mul (I := I) (J := J) (Γ := Γ))
  push_cast at h
  apply (div_eq_div_iff (by exact_mod_cast Fintype.card_ne_zero)
    (pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero))).mpr
  exact h

/-- In the fourth case, a fixed base rectangle contributes exactly L^(-8)
expected lifts. -/
theorem fourth_average_lifts (hI : Fintype.card I = 3) (hJ : Fintype.card J = 3) :
    (∑ M : Matrix (I := I) (J := J) (Γ := Γ), (Fintype.card (Lifts M) : ℚ)) /
        Fintype.card (Matrix (I := I) (J := J) (Γ := Γ)) =
      1 / (Fintype.card Γ : ℚ)^8 := by
  rw [average_lifts, hI, hJ]
  have hn : (Fintype.card Γ : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  norm_num
  field_simp

/-- Conditional budget calculation: with base edge scale q^(2r-1) and base
copy scale q^(r*r), the elementary random-cover deletion certificate requires
at least q sheets. The monomial budget is an explicit hypothesis. -/
theorem budget_requires_sheets (r : ℕ) (hr : 2 ≤ r) (q L : ℝ)
    (hq : 0 < q) (hL : 0 ≤ L)
    (hbudget : q^(r*r) ≤ q^(2*r-1)*L^((r-1)*(r-1))) : q ≤ L := by
  have hdeg : r*r = (2*r-1)+(r-1)*(r-1) := by
    have h₁ : r-1+1 = r := by omega
    have h₂ : 2*r-1+1 = 2*r := by omega
    nlinarith
  rw [hdeg, pow_add] at hbudget
  have hpow := (mul_le_mul_iff_right₀ (pow_pos hq (2*r-1))).mp hbudget
  have hpos : 0 < (r-1)*(r-1) := Nat.mul_pos (by omega) (by omega)
  exact (pow_le_pow_iff_left₀ hq.le hL hpos.ne').mp hpow

/-- The cover's order/edge monomials are consequently at most the ordinary
alteration scale. This is NOT a bound for arbitrary deterministic covers. -/
theorem budget_alteration_scale (r : ℕ) (hr : 2 ≤ r) (q L : ℝ)
    (hq : 0 < q) (hL : 0 ≤ L)
    (hbudget : q^(r*r) ≤ q^(2*r-1)*L^((r-1)*(r-1))) :
    (q^(2*r-1)*L)^(r+1) ≤ (q^r*L)^(2*r) := by
  have hqL := budget_requires_sheets r hr q L hq hL hbudget
  have hdeg : (2*r-1)*(r+1) = r*(2*r)+(r-1) := by
    have h₁ : r-1+1 = r := by omega
    have h₂ : 2*r-1+1 = 2*r := by omega
    nlinarith
  have hpow := pow_le_pow_left₀ hq.le hqL (r-1)
  calc
    (q^(2*r-1)*L)^(r+1) = q^(r*(2*r))*(q^(r-1)*L^(r+1)) := by
      rw [mul_pow, ← pow_mul, hdeg, pow_add]
      ring
    _ ≤ q^(r*(2*r))*(L^(r-1)*L^(r+1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (pow_nonneg hL _))
        (by positivity)
    _ = (q^r*L)^(2*r) := by
      rw [mul_pow, ← pow_mul, ← pow_add]
      congr 2
      omega

end Erdos714RandomVoltage

#print axioms Erdos714RandomVoltage.card_flat_mul
#print axioms Erdos714RandomVoltage.card_lifts
#print axioms Erdos714RandomVoltage.sum_card_lifts_mul
#print axioms Erdos714RandomVoltage.budget_requires_sheets
#print axioms Erdos714RandomVoltage.budget_alteration_scale

#print axioms Erdos714RandomVoltage.flat_fraction
#print axioms Erdos714RandomVoltage.average_lifts
#print axioms Erdos714RandomVoltage.fourth_average_lifts
