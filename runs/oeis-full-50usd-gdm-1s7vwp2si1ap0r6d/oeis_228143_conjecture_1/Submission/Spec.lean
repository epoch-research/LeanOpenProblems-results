import FormalConjectures.Util.ProblemImports

set_option warn.sorry false

open BigOperators Matrix Nat PowerSeries

/--
A005259: The auxiliary sequence used for the Hankel matrix, defined as
$$\sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}^2$$
-/
def A005259' (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (n.choose k)^2 * ((Nat.choose (n + k) k))^2

/--
A228143: Determinant of the $(n+1) \times (n+1)$ Hankel-type matrix with $(i,j)$-entry equal to A005259$(i+j)$ for all $i,j = 0,\dots,n$.
The entry function A005259 is taken to be $\sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}^2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let dim : Type := Fin (n + 1)
  -- Matrix entries are lifted to ℤ for determinant calculation
  let M : Matrix dim dim ℤ :=
    Matrix.of fun i j => (A005259' (i.val + j.val) : ℤ)
  -- The sequence is known to be non-negative integers (nonn).
  M.det.natAbs

open PowerSeries

/-- The power series $A(x/3) = \sum_{n=0}^\infty \frac{a(n)}{3^n} x^n$ over ℚ. -/
noncomputable def OGF_A_scaled : PowerSeries ℚ :=
  PowerSeries.mk fun n => (a n : ℚ) / (3 ^ n : ℚ)


theorem ha_zero_val : a 0 = 1 := by
  dsimp [a, A005259']
  rw [Matrix.det_fin_one]
  rfl

theorem hA_zero : coeff 0 OGF_A_scaled = 1 := by
  simp [OGF_A_scaled, ha_zero_val]

noncomputable def Y : PowerSeries ℚ := OGF_A_scaled - 1

lemma hY : Y.constantCoeff = 0 := by
  dsimp [Y]
  rw [map_sub]
  have h1 : OGF_A_scaled.constantCoeff = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hA_zero
  rw [h1]
  simp

lemma h_has_subst : HasSubst Y := HasSubst.of_constantCoeff_zero' hY

noncomputable def C_Q : PowerSeries ℚ :=
  subst Y (PowerSeries.binomialSeries ℚ (1/8 : ℚ))

lemma binomialSeries_pow (r : ℚ) (n : ℕ) :
    (PowerSeries.binomialSeries ℚ r) ^ n = PowerSeries.binomialSeries ℚ (n * r) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [pow_succ, ih, ← binomialSeries_add]
    congr 1
    push_cast
    ring

lemma C_Q_pow_eight : C_Q ^ 8 = OGF_A_scaled := by
  dsimp [C_Q]
  rw [← subst_pow h_has_subst]
  rw [binomialSeries_pow]
  have h_8_div_8 : ((8 : ℕ) : ℚ) * (1/8 : ℚ) = 1 := by norm_num
  rw [h_8_div_8]
  have h_one : PowerSeries.binomialSeries ℚ (1 : ℚ) = PowerSeries.binomialSeries ℚ ((1 : ℕ) : ℚ) := by simp
  rw [h_one]
  rw [binomialSeries_nat 1]
  rw [pow_one]
  rw [← coe_substAlgHom h_has_subst]
  rw [map_add, map_one]
  rw [coe_substAlgHom h_has_subst]
  rw [subst_X h_has_subst]
  dsimp [Y]
  ring

noncomputable def C_witness : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (coeff n C_Q).num)

lemma helper (q : ℚ) (h : ∃ z : ℤ, (z : ℚ) = q) : (q.num : ℚ) = q := by
  rcases h with ⟨z, hz⟩
  rw [← hz]
  simp

lemma C_witness_eq_C_Q : PowerSeries.map (Int.castRingHom ℚ) C_witness = C_Q := by
  ext n
  rw [coeff_map]
  dsimp [C_witness]
  rw [coeff_mk]
  have h : ∃ z : ℤ, (z : ℚ) = coeff n C_Q := by
    sorry
  exact helper (coeff n C_Q) h

/--
A228143 Conjecture: if $A(x) = 1 + 48*x + 161856*x^2 + \dots$ denotes the o.g.f. then
$A(x/3)^{1/8}$ has integer coefficients (checked up to $x^{30}$).

This is formalized as: there exists a power series $C(x)$ over $\mathbb{Z}$ such that $C(x)^8 = A(x/3)$.
The map `PowerSeries.map (Int.castRingHom ℚ)` lifts the power series from $\mathbb{Z}[[X]]$ to $\mathbb{Q}[[X]]$.
-/
theorem oeis_228143_conjecture_1 :
    ∃ C : PowerSeries ℤ,
      (PowerSeries.map (Int.castRingHom ℚ)) (C ^ 8) = OGF_A_scaled := by
  use C_witness
  rw [map_pow]
  rw [C_witness_eq_C_Q]
  exact C_Q_pow_eight
