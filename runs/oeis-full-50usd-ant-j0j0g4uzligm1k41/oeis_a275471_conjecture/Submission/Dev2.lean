import FormalConjectures.Util.ProblemImports

open Nat

/-- Balanced residue: for `m > 0` and any integer `β`, there is an integer `x`
with `4 (m x + β)^2 ≤ m^2` (i.e. `|m x + β| ≤ m/2`). -/
theorem balanced_residue (β m : ℤ) (hm : 0 < m) :
    ∃ x : ℤ, 4 * (m * x + β) ^ 2 ≤ m ^ 2 := by
  set r := β % m with hr
  have h0 : 0 ≤ r := Int.emod_nonneg β (by omega)
  have h1 : r < m := Int.emod_lt_of_pos β hm
  by_cases hcase : 2 * r ≤ m
  · refine ⟨-(β / m), ?_⟩
    have : m * -(β / m) + β = r := by
      have := Int.ediv_add_emod β m; ring_nf; omega
    rw [this]; nlinarith [h0, h1, hcase]
  · push_neg at hcase
    refine ⟨-(β / m) - 1, ?_⟩
    have : m * (-(β / m) - 1) + β = r - m := by
      have := Int.ediv_add_emod β m; ring_nf; omega
    rw [this]; nlinarith [h0, h1, hcase]

namespace ThreeSq
open Matrix

abbrev Vec (n : ℕ) := Fin n → ℤ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℤ

/-- Value of the quadratic form with Gram matrix `G` at integer vector `v`. -/
def Q {n : ℕ} (G : Mat n) (v : Vec n) : ℤ := v ⬝ᵥ G.mulVec v

/-- Positive-definiteness over integer vectors. -/
def PD {n : ℕ} (G : Mat n) : Prop := ∀ v : Vec n, v ≠ 0 → 0 < Q G v

lemma Q_conj {n : ℕ} (G U : Mat n) (v : Vec n) :
    Q G (U.mulVec v) = Q (Uᵀ * G * U) v := by
  unfold Q
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  conv_rhs => rw [dotProduct_mulVec, vecMul_transpose]

/-- Existence of a minimum value vector for an integral positive-definite form. -/
lemma exists_min {n : ℕ} (G : Mat n) (hn : 0 < n) (hPD : PD G) :
    ∃ v : Vec n, v ≠ 0 ∧ 0 < Q G v ∧ ∀ w : Vec n, w ≠ 0 → Q G v ≤ Q G w := by
  let P : ℤ → Prop := fun z => ∃ v : Vec n, v ≠ 0 ∧ Q G v = z
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, P z → b ≤ z := by
    refine ⟨0, ?_⟩
    rintro z ⟨v, hv, rfl⟩
    exact le_of_lt (hPD v hv)
  set v0 : Vec n := fun i => if i = ⟨0, hn⟩ then 1 else 0 with hv0
  have e0 : v0 ≠ 0 := by
    intro h
    have := congrFun h (⟨0, hn⟩ : Fin n)
    simp [hv0] at this
  have hinh : ∃ z : ℤ, P z := ⟨Q G v0, _, e0, rfl⟩
  obtain ⟨lb, ⟨v, hv, hvlb⟩, hmin⟩ := Int.exists_least_of_bdd hbdd hinh
  refine ⟨v, hv, ?_, ?_⟩
  · have := hPD v hv; rw [hvlb] at this ⊢; exact this
  · intro w hw
    rw [hvlb]
    exact hmin (Q G w) ⟨w, hw, rfl⟩

/-- Conjugation by a unimodular matrix preserves positive-definiteness. -/
lemma PD_conj {n : ℕ} {G U : Mat n} (hU : IsUnit U.det) (hPD : PD G) : PD (Uᵀ * G * U) := by
  intro v hv
  rw [← Q_conj]
  apply hPD
  intro h
  apply hv
  have hdet : U.det ≠ 0 := hU.ne_zero
  by_contra hvne
  exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hvne, h⟩)

/-- A coprime pair extends to the first column of a determinant-1 integer 2×2 matrix. -/
lemma extend2 (p q : ℤ) (h : IsCoprime p q) :
    ∃ U : Mat 2, U.det = 1 ∧ U.mulVec ![1, 0] = ![p, q] := by
  obtain ⟨a, b, hab⟩ := h
  -- a*p + b*q = 1
  refine ⟨!![p, -b; q, a], ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; ring_nf; linarith [hab]
  · funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma Q_smul {n : ℕ} (G : Mat n) (c : ℤ) (v : Vec n) : Q G (c • v) = c ^ 2 * Q G v := by
  unfold Q
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
  ring

/-- A minimum vector of a 2×2 form has coprime entries. -/
lemma min_coprime2 {G : Mat 2} (hPD : PD G) {v : Vec 2} (hv : v ≠ 0)
    (hmin : ∀ w : Vec 2, w ≠ 0 → Q G v ≤ Q G w) : IsCoprime (v 0) (v 1) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  set d : ℕ := Int.gcd (v 0) (v 1) with hd
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso; rw [hd, Int.gcd_eq_zero_iff] at h0
      apply hv; funext i; fin_cases i <;> simp [h0.1, h0.2]
    · exact h0
  by_contra hne
  have hd2 : 2 ≤ d := by omega
  have hdvd0 : (d : ℤ) ∣ v 0 := Int.gcd_dvd_left _ _
  have hdvd1 : (d : ℤ) ∣ v 1 := Int.gcd_dvd_right _ _
  set w : Vec 2 := ![v 0 / d, v 1 / d] with hw
  have hvw : v = (d : ℤ) • w := by
    funext i; fin_cases i <;>
      simp [hw, Int.mul_ediv_cancel' hdvd0, Int.mul_ediv_cancel' hdvd1]
  have hwne : w ≠ 0 := by
    intro h; apply hv; rw [hvw, h, smul_zero]
  have hkey : Q G v = (d : ℤ) ^ 2 * Q G w := by rw [hvw, Q_smul]
  have hge : Q G v ≤ Q G w := hmin w hwne
  have hpos : 0 < Q G w := hPD w hwne
  have hd2' : (4 : ℤ) ≤ (d : ℤ) ^ 2 := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd2
    nlinarith
  nlinarith [hkey, hge, hpos, hd2']

lemma Q_e0_eq {n : ℕ} (G : Mat n) (hn : 0 < n) :
    Q G (Pi.single (⟨0, hn⟩) 1) = G ⟨0, hn⟩ ⟨0, hn⟩ := by
  unfold Q
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Hermite bound in dimension 2: `3 m² ≤ 4 det` for the minimum value `m`. -/
lemma hermite2 (G : Mat 2) (hsymm : G.IsSymm) (hPD : PD G) :
    ∃ v : Vec 2, v ≠ 0 ∧ 3 * (Q G v) ^ 2 ≤ 4 * G.det := by
  obtain ⟨v, hv, hvpos, hmin⟩ := exists_min G (by norm_num) hPD
  refine ⟨v, hv, ?_⟩
  set m := Q G v with hm
  -- v is primitive, extend to unimodular U
  have hcop := min_coprime2 hPD hv hmin
  obtain ⟨U, hUdet, hUcol⟩ := extend2 (v 0) (v 1) hcop
  have hv01 : (![v 0, v 1] : Vec 2) = v := by
    funext i; fin_cases i <;> rfl
  rw [hv01] at hUcol
  set G' := Uᵀ * G * U with hG'
  have hUunit : IsUnit U.det := by rw [hUdet]; exact isUnit_one
  -- min value preserved
  have hPD' : PD G' := PD_conj hUunit hPD
  have hmin' : ∀ w : Vec 2, w ≠ 0 → m ≤ Q G' w := by
    intro w hw
    rw [hG', ← Q_conj]
    apply hmin
    intro hUw
    apply hw
    have hdet : U.det ≠ 0 := hUunit.ne_zero
    by_contra hwne
    exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hwne, hUw⟩)
  -- G' 0 0 = m
  have hG'00 : G' 0 0 = m := by
    have : Q G' ![1, 0] = m := by
      rw [hG', ← Q_conj, hUcol]
    rw [← this]; unfold Q; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  -- symmetry
  have hsymm' : G' 1 0 = G' 0 1 := by
    have : G'ᵀ = G' := by
      rw [hG', Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        hsymm.eq, mul_assoc]
    have := congrFun (congrFun this 0) 1
    simpa using this
  -- determinant preserved and = entries
  have hdetG' : G'.det = G.det := by
    rw [hG', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hUdet]; ring
  have hdetEntries : G'.det = G' 0 0 * G' 1 1 - G' 0 1 * G' 1 0 := Matrix.det_fin_two G'
  -- balanced residue
  obtain ⟨x, hbr⟩ := balanced_residue (G' 0 1) m (by rw [hm] at hvpos ⊢; exact hvpos)
  -- value at ![x,1]
  have hmx : (0 : ℤ) < m := by rw [hm] at hvpos; exact hvpos
  have hQw : Q G' ![x, 1] = G' 0 0 * x ^ 2 + (G' 0 1 + G' 1 0) * x + G' 1 1 := by
    unfold Q; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  have hwne : (![x, 1] : Vec 2) ≠ 0 := by
    intro h; have := congrFun h 1; simp at this
  have hge : m ≤ Q G' ![x, 1] := hmin' _ hwne
  rw [hsymm'] at hQw
  -- now combine
  have hkey : m * Q G' ![x, 1] = (m * x + G' 0 1) ^ 2 + G'.det := by
    rw [hQw, hdetEntries, hsymm', hG'00]; ring
  rw [hdetG'] at hkey hdetEntries
  nlinarith [hkey, hge, hbr, hmx, mul_le_mul_of_nonneg_left hge (le_of_lt hmx)]

/-- Embed a 2×2 matrix into the top-left of a 3×3 matrix (identity on the last coordinate). -/
def embedTL (V : Mat 2) : Mat 3 :=
  !![V 0 0, V 0 1, 0; V 1 0, V 1 1, 0; 0, 0, 1]

/-- Put a 2×2 matrix into the bottom-right of a 3×3 matrix (identity on the first coordinate). -/
def diagBR (W : Mat 2) : Mat 3 :=
  !![1, 0, 0; 0, W 0 0, W 0 1; 0, W 1 0, W 1 1]

lemma det_embedTL (V : Mat 2) : (embedTL V).det = V.det := by
  rw [embedTL, Matrix.det_fin_three, Matrix.det_fin_two]; simp

lemma det_diagBR (W : Mat 2) : (diagBR W).det = W.det := by
  rw [diagBR, Matrix.det_fin_three, Matrix.det_fin_two]; simp

lemma embedTL_col0 (V : Mat 2) : (embedTL V).mulVec ![1, 0, 0] = ![V 0 0, V 1 0, 0] := by
  funext i; fin_cases i <;> simp [embedTL, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

lemma diagBR_mulVec (W : Mat 2) (a x y : ℤ) :
    (diagBR W).mulVec ![a, x, y] = ![a, W 0 0 * x + W 0 1 * y, W 1 0 * x + W 1 1 * y] := by
  funext i; fin_cases i <;> simp [diagBR, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- A primitive 3-vector extends to the first column of a determinant-1 integer 3×3 matrix. -/
lemma extend3 (a b c : ℤ) (h : Int.gcd (Int.gcd a b) c = 1) :
    ∃ U : Mat 3, U.det = 1 ∧ U.mulVec ![1, 0, 0] = ![a, b, c] := by
  set g : ℤ := (Int.gcd b c : ℤ) with hg
  by_cases hbc : b = 0 ∧ c = 0
  · -- g = 0, a is a unit
    obtain ⟨hb, hc⟩ := hbc
    rw [hb, hc] at h
    have hna : a.natAbs = 1 := by
      simpa only [Int.gcd_zero_right, Int.natAbs_natCast] using h
    have ha : a = 1 ∨ a = -1 := by
      have := Int.natAbs_eq_iff.mp hna; simpa using this
    rcases ha with ha | ha <;>
    · refine ⟨!![a, 0, 0; 0, 1, 0; 0, 0, a], ?_, ?_⟩
      · subst ha; simp [Matrix.det_fin_three]
      · funext i; fin_cases i <;>
          simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hb, hc]
  · -- g ≠ 0
    have hgpos : 0 < g := by
      rw [hg]
      rcases Nat.eq_zero_or_pos (Int.gcd b c) with h0 | h0
      · exfalso; rw [Int.gcd_eq_zero_iff] at h0; exact hbc ⟨h0.1, h0.2⟩
      · exact_mod_cast h0
    have hgb : g ∣ b := by rw [hg]; exact Int.gcd_dvd_left b c
    have hgc : g ∣ c := by rw [hg]; exact Int.gcd_dvd_right b c
    set b1 : ℤ := b / g with hb1
    set c1 : ℤ := c / g with hc1
    have hbb : b = g * b1 := by rw [hb1, Int.mul_ediv_cancel' hgb]
    have hcc : c = g * c1 := by rw [hc1, Int.mul_ediv_cancel' hgc]
    have hgN : 0 < Int.gcd b c := by
      have h' := hgpos; rw [hg] at h'; exact_mod_cast h'
    have hcop_bc : IsCoprime b1 c1 := by
      rw [Int.isCoprime_iff_gcd_eq_one, hb1, hc1, hg]
      exact Int.gcd_div_gcd_div_gcd hgN
    have hcop_ag : IsCoprime a g := by
      rw [Int.isCoprime_iff_gcd_eq_one, hg, ← Int.gcd_assoc]; exact h
    obtain ⟨V, hVdet, hVcol⟩ := extend2 a g hcop_ag
    obtain ⟨W, hWdet, hWcol⟩ := extend2 b1 c1 hcop_bc
    refine ⟨diagBR W * embedTL V, ?_, ?_⟩
    · rw [Matrix.det_mul, det_diagBR, det_embedTL, hVdet, hWdet]; ring
    · rw [← Matrix.mulVec_mulVec, embedTL_col0]
      have hV0 : V 0 0 = a := by have := congrFun hVcol 0; simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
      have hV1 : V 1 0 = g := by have := congrFun hVcol 1; simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
      rw [hV0, hV1, diagBR_mulVec]
      have hW0 : W 0 0 = b1 := by have := congrFun hWcol 0; simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
      have hW1 : W 1 0 = c1 := by have := congrFun hWcol 1; simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
      funext i; fin_cases i <;> simp [hW0, hW1, hbb, hcc] <;> ring

/-- A minimum vector of a 3×3 form has overall gcd 1. -/
lemma min_coprime3 {G : Mat 3} (hPD : PD G) {v : Vec 3} (hv : v ≠ 0)
    (hmin : ∀ w : Vec 3, w ≠ 0 → Q G v ≤ Q G w) :
    Int.gcd (Int.gcd (v 0) (v 1)) (v 2) = 1 := by
  set d : ℕ := Int.gcd (Int.gcd (v 0) (v 1)) (v 2) with hd
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso; rw [hd] at h0
      rw [Int.gcd_eq_zero_iff] at h0
      obtain ⟨h01, h2⟩ := h0
      rw [Nat.cast_eq_zero, Int.gcd_eq_zero_iff] at h01
      apply hv; funext i; fin_cases i <;> simp [h01.1, h01.2, h2]
    · exact h0
  by_contra hne
  have hd2 : 2 ≤ d := by omega
  have hdvd2 : (d : ℤ) ∣ v 2 := Int.gcd_dvd_right _ _
  have hdvd01 : (d : ℤ) ∣ Int.gcd (v 0) (v 1) := Int.gcd_dvd_left _ _
  have hdvd0 : (d : ℤ) ∣ v 0 := dvd_trans hdvd01 (Int.gcd_dvd_left _ _)
  have hdvd1 : (d : ℤ) ∣ v 1 := dvd_trans hdvd01 (Int.gcd_dvd_right _ _)
  set w : Vec 3 := ![v 0 / d, v 1 / d, v 2 / d] with hw
  have hvw : v = (d : ℤ) • w := by
    funext i; fin_cases i <;>
      simp [hw, Int.mul_ediv_cancel' hdvd0, Int.mul_ediv_cancel' hdvd1,
        Int.mul_ediv_cancel' hdvd2]
  have hwne : w ≠ 0 := by intro h; apply hv; rw [hvw, h, smul_zero]
  have hkey : Q G v = (d : ℤ) ^ 2 * Q G w := by rw [hvw, Q_smul]
  have hge : Q G v ≤ Q G w := hmin w hwne
  have hpos : 0 < Q G w := hPD w hwne
  have hd2' : (4 : ℤ) ≤ (d : ℤ) ^ 2 := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd2
    nlinarith
  nlinarith [hkey, hge, hpos, hd2']

/-- Conjugate of a symmetric matrix by `U` is symmetric. -/
lemma symm_conj {n : ℕ} {G U : Mat n} (hsymm : G.IsSymm) : (Uᵀ * G * U)ᵀ = Uᵀ * G * U := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hsymm.eq, mul_assoc]

set_option maxHeartbeats 1000000 in
/-- A determinant-1 positive definite integral ternary form represents `1`. -/
lemma repr_one_3 (G : Mat 3) (hsymm : G.IsSymm) (hPD : PD G) (hdet : G.det = 1) :
    ∃ v : Vec 3, v ≠ 0 ∧ Q G v = 1 := by
  obtain ⟨v, hv, hvpos, hmin⟩ := exists_min G (by norm_num) hPD
  set m := Q G v with hm
  have hmx : (0 : ℤ) < m := by rw [hm] at hvpos; exact hvpos
  have hcop := min_coprime3 hPD hv hmin
  obtain ⟨U, hUdet, hUcol⟩ := extend3 (v 0) (v 1) (v 2) hcop
  have hv3 : (![v 0, v 1, v 2] : Vec 3) = v := by funext i; fin_cases i <;> rfl
  rw [hv3] at hUcol
  set G' := Uᵀ * G * U with hG'
  have hUunit : IsUnit U.det := by rw [hUdet]; exact isUnit_one
  have hmin' : ∀ w : Vec 3, w ≠ 0 → m ≤ Q G' w := by
    intro w hw
    rw [hG', ← Q_conj]
    apply hmin
    intro hUw; apply hw
    by_contra hwne
    exact hUunit.ne_zero (Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hwne, hUw⟩)
  have hG'00 : G' 0 0 = m := by
    have : Q G' ![1, 0, 0] = m := by rw [hG', ← Q_conj, hUcol]
    rw [← this]; unfold Q; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hsymm' : G'ᵀ = G' := symm_conj hsymm
  have hg10 : G' 1 0 = G' 0 1 := by
    have h := congrFun (congrFun hsymm' 0) 1; rwa [Matrix.transpose_apply] at h
  have hg20 : G' 2 0 = G' 0 2 := by
    have h := congrFun (congrFun hsymm' 0) 2; rwa [Matrix.transpose_apply] at h
  have hg21 : G' 2 1 = G' 1 2 := by
    have h := congrFun (congrFun hsymm' 1) 2; rwa [Matrix.transpose_apply] at h
  have hdetG' : G'.det = 1 := by
    rw [hG', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hUdet, hdet]; ring
  -- the Schur complement 2×2 form
  set H' : Mat 2 := !![m * (G' 1 1) - (G' 0 1) ^ 2, m * (G' 1 2) - (G' 0 1) * (G' 0 2);
      m * (G' 1 2) - (G' 0 1) * (G' 0 2), m * (G' 2 2) - (G' 0 2) ^ 2] with hH'
  have e2 : ∀ y z : ℤ, Q H' ![y, z] =
      (m * (G' 1 1) - (G' 0 1) ^ 2) * y ^ 2
      + 2 * (m * (G' 1 2) - (G' 0 1) * (G' 0 2)) * y * z
      + (m * (G' 2 2) - (G' 0 2) ^ 2) * z ^ 2 := by
    intro y z; unfold Q
    simp [hH', Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  have hident : ∀ x y z : ℤ,
      m * Q G' ![x, y, z] = (m * x + (G' 0 1) * y + (G' 0 2) * z) ^ 2 + Q H' ![y, z] := by
    intro x y z
    have e1 : Q G' ![x, y, z] = G' 0 0 * x ^ 2 + G' 1 1 * y ^ 2 + G' 2 2 * z ^ 2
        + (G' 0 1 + G' 1 0) * x * y + (G' 0 2 + G' 2 0) * x * z + (G' 1 2 + G' 2 1) * y * z := by
      unfold Q; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring
    rw [e1, e2, hg10, hg20, hg21, hG'00]; ring
  have hHsymm : H'.IsSymm := by
    rw [Matrix.IsSymm, hH']; funext i j; fin_cases i <;> fin_cases j <;> simp
  -- lower bound: for nonzero (y,z), 3 m^2 ≤ 4 Q H' (y,z)
  have hlb : ∀ w : Vec 2, w ≠ 0 → 3 * m ^ 2 ≤ 4 * Q H' w := by
    intro w hw
    obtain ⟨x, hbr⟩ := balanced_residue (G' 0 1 * w 0 + G' 0 2 * w 1) m hmx
    have hwne3 : (![x, w 0, w 1] : Vec 3) ≠ 0 := by
      intro h; apply hw
      funext i; fin_cases i
      · have := congrFun h 1; simpa using this
      · have := congrFun h 2; simpa using this
    have hge : m ≤ Q G' ![x, w 0, w 1] := hmin' _ hwne3
    have hid := hident x (w 0) (w 1)
    have hw01 : (![w 0, w 1] : Vec 2) = w := by funext i; fin_cases i <;> rfl
    rw [hw01] at hid
    have hmm : m * m ≤ m * Q G' ![x, w 0, w 1] :=
      mul_le_mul_of_nonneg_left hge (le_of_lt hmx)
    have key : m * m ≤ (m * x + G' 0 1 * w 0 + G' 0 2 * w 1) ^ 2 + Q H' w := by
      rw [← hid]; exact hmm
    nlinarith [key, hbr]
  have hHPD : PD H' := by
    intro w hw
    have := hlb w hw
    nlinarith [this, sq_nonneg m, hmx]
  -- det H' = m
  have hHdet : H'.det = m := by
    rw [hH', Matrix.det_fin_two_of]
    have hd3 := hdetG'
    rw [Matrix.det_fin_three] at hd3
    rw [hg10, hg20, hg21, hG'00] at hd3
    linear_combination m * hd3
  -- apply Hermite in dimension 2
  obtain ⟨w', hw'ne, hw'bound⟩ := hermite2 H' hHsymm hHPD
  rw [hHdet] at hw'bound
  have hw'lb := hlb w' hw'ne
  set Qh := Q H' w' with hQh
  have hQhpos : 0 ≤ Qh := by nlinarith [hw'lb, hmx]
  have h1 : (0 : ℤ) ≤ 4 * Qh - 3 * m ^ 2 := by linarith [hw'lb]
  have h2 : (0 : ℤ) ≤ 4 * Qh + 3 * m ^ 2 := by nlinarith [hQhpos, hmx]
  have hsq : 9 * m ^ 4 ≤ 16 * Qh ^ 2 := by nlinarith [mul_nonneg h1 h2]
  have h4 : 27 * m ^ 4 ≤ 64 * m := by nlinarith [hsq, hw'bound]
  have h27 : 27 * m ^ 3 ≤ 64 := le_of_mul_le_mul_left (by nlinarith [h4]) hmx
  have hmeq : m = 1 := by
    rcases lt_or_ge m 2 with h | h
    · omega
    · exfalso
      have hcube : (8 : ℤ) ≤ m ^ 3 := by nlinarith [h, sq_nonneg (m + 1)]
      omega
  exact ⟨v, hv, by rw [← hm, hmeq]⟩

/-- If `Pᵀ G P = 1` then `G = (P⁻¹)ᵀ * P⁻¹`. -/
lemma conj_eq_one_inv {n : ℕ} {G P : Mat n} (hP : IsUnit P.det) (h : Pᵀ * G * P = 1) :
    G = (P⁻¹)ᵀ * P⁻¹ := by
  have hPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hL : (P⁻¹)ᵀ * Pᵀ = 1 := by
    rw [← Matrix.transpose_mul, hPinv, Matrix.transpose_one]
  have step : (P⁻¹)ᵀ * Pᵀ * G * (P * P⁻¹) = G := by rw [hL, hPinv, one_mul, mul_one]
  calc G = (P⁻¹)ᵀ * Pᵀ * G * (P * P⁻¹) := step.symm
    _ = (P⁻¹)ᵀ * (Pᵀ * G * P) * P⁻¹ := by simp only [mul_assoc]
    _ = (P⁻¹)ᵀ * (1 : Mat n) * P⁻¹ := by rw [h]
    _ = (P⁻¹)ᵀ * P⁻¹ := by rw [mul_one]

/-- For a 3×3 form diagonalized to the identity, the `(0,0)` entry is a sum of three squares. -/
lemma sum3_of_conj_one {G P : Mat 3} (hP : IsUnit P.det) (h : Pᵀ * G * P = 1) :
    ∃ a b c : ℤ, G 0 0 = a ^ 2 + b ^ 2 + c ^ 2 := by
  have hG := conj_eq_one_inv hP h
  refine ⟨P⁻¹ 0 0, P⁻¹ 1 0, P⁻¹ 2 0, ?_⟩
  rw [hG]
  simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  ring

lemma diagBR_one : diagBR (1 : Mat 2) = (1 : Mat 3) := by
  funext i j; fin_cases i <;> fin_cases j <;>
    simp [diagBR, Matrix.one_apply]

lemma diagBR_mul (A B : Mat 2) : diagBR (A * B) = diagBR A * diagBR B := by
  funext i j; fin_cases i <;> fin_cases j <;>
    simp [diagBR, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

lemma diagBR_transpose (A : Mat 2) : (diagBR A)ᵀ = diagBR Aᵀ := by
  funext i j; fin_cases i <;> fin_cases j <;>
    simp [diagBR, Matrix.transpose_apply]

lemma det_diagBR_unit {A : Mat 2} (hA : IsUnit A.det) : IsUnit (diagBR A).det := by
  rw [det_diagBR]; exact hA

/-- If a positive definite form has value `1` at `v`, then `v` is primitive (2D). -/
lemma coprime2_of_value {G : Mat 2} (hPD : PD G) {v : Vec 2} (hv : v ≠ 0) (h1 : Q G v = 1) :
    IsCoprime (v 0) (v 1) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  set d : ℕ := Int.gcd (v 0) (v 1) with hd
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso; rw [hd, Int.gcd_eq_zero_iff] at h0
      apply hv; funext i; fin_cases i <;> simp [h0.1, h0.2]
    · exact h0
  by_contra hne
  have hd2 : 2 ≤ d := by omega
  have hdvd0 : (d : ℤ) ∣ v 0 := Int.gcd_dvd_left _ _
  have hdvd1 : (d : ℤ) ∣ v 1 := Int.gcd_dvd_right _ _
  set w : Vec 2 := ![v 0 / d, v 1 / d] with hw
  have hvw : v = (d : ℤ) • w := by
    funext i; fin_cases i <;>
      simp [hw, Int.mul_ediv_cancel' hdvd0, Int.mul_ediv_cancel' hdvd1]
  have hwne : w ≠ 0 := by intro h; apply hv; rw [hvw, h, smul_zero]
  have hkey : Q G v = (d : ℤ) ^ 2 * Q G w := by rw [hvw, Q_smul]
  have hpos : 0 < Q G w := hPD w hwne
  have hd2' : (4 : ℤ) ≤ (d : ℤ) ^ 2 := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd2
    nlinarith
  nlinarith [hkey, h1, hpos, hd2']

/-- A determinant-1 positive definite integral binary form represents `1` primitively. -/
lemma repr_one_2 (G : Mat 2) (hsymm : G.IsSymm) (hPD : PD G) (hdet : G.det = 1) :
    ∃ v : Vec 2, v ≠ 0 ∧ Q G v = 1 ∧ IsCoprime (v 0) (v 1) := by
  obtain ⟨v, hv, hvpos, hmin⟩ := exists_min G (by norm_num) hPD
  obtain ⟨v2, hv2, hb⟩ := hermite2 G hsymm hPD
  rw [hdet] at hb
  have hle : Q G v ≤ Q G v2 := hmin v2 hv2
  have hm1 : Q G v ≤ 1 := by nlinarith [hb, hle, hvpos, hPD v2 hv2]
  have hQ1 : Q G v = 1 := by omega
  exact ⟨v, hv, hQ1, coprime2_of_value hPD hv hQ1⟩

/-- A determinant-1 positive definite integral binary form is congruent to the identity. -/
lemma diagonalize2 (G : Mat 2) (hsymm : G.IsSymm) (hPD : PD G) (hdet : G.det = 1) :
    ∃ P : Mat 2, IsUnit P.det ∧ Pᵀ * G * P = 1 := by
  obtain ⟨v, hv, hQ1, hcop⟩ := repr_one_2 G hsymm hPD hdet
  obtain ⟨V, hVdet, hVcol⟩ := extend2 (v 0) (v 1) hcop
  have hv2 : (![v 0, v 1] : Vec 2) = v := by funext i; fin_cases i <;> rfl
  rw [hv2] at hVcol
  set G₁ := Vᵀ * G * V with hG₁
  have hVunit : IsUnit V.det := by rw [hVdet]; exact isUnit_one
  have hG₁00 : G₁ 0 0 = 1 := by
    have : Q G₁ ![1, 0] = 1 := by rw [hG₁, ← Q_conj, hVcol, hQ1]
    rw [← this]; unfold Q; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hsymm₁ : G₁ᵀ = G₁ := symm_conj hsymm
  have hg10 : G₁ 1 0 = G₁ 0 1 := by
    have h := congrFun (congrFun hsymm₁ 0) 1; rwa [Matrix.transpose_apply] at h
  have hdet₁ : G₁.det = 1 := by
    rw [hG₁, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hVdet, hdet]; ring
  have hdetrel : G₁ 1 1 - (G₁ 0 1) ^ 2 = 1 := by
    rw [Matrix.det_fin_two] at hdet₁; rw [hg10] at hdet₁; nlinarith [hdet₁, hG₁00]
  set S2 : Mat 2 := !![1, -(G₁ 0 1); 0, 1] with hS2
  refine ⟨V * S2, ?_, ?_⟩
  · rw [Matrix.det_mul, hVdet, hS2, Matrix.det_fin_two_of]; norm_num
  · have heq : (V * S2)ᵀ * G * (V * S2) = S2ᵀ * G₁ * S2 := by
      rw [hG₁]; rw [Matrix.transpose_mul]; noncomm_ring
    rw [heq]
    funext i j; fin_cases i <;> fin_cases j <;>
      simp [hS2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply,
        hG₁00, hg10] <;> nlinarith [hdetrel, hG₁00, hg10]

/-- If a positive definite ternary form has value `1` at `v`, then `v` is primitive. -/
lemma coprime3_of_value {G : Mat 3} (hPD : PD G) {v : Vec 3} (hv : v ≠ 0) (h1 : Q G v = 1) :
    Int.gcd (Int.gcd (v 0) (v 1)) (v 2) = 1 := by
  set d : ℕ := Int.gcd (Int.gcd (v 0) (v 1)) (v 2) with hd
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso; rw [hd] at h0
      rw [Int.gcd_eq_zero_iff] at h0
      obtain ⟨h01, h2⟩ := h0
      rw [Nat.cast_eq_zero, Int.gcd_eq_zero_iff] at h01
      apply hv; funext i; fin_cases i <;> simp [h01.1, h01.2, h2]
    · exact h0
  by_contra hne
  have hd2 : 2 ≤ d := by omega
  have hdvd2 : (d : ℤ) ∣ v 2 := Int.gcd_dvd_right _ _
  have hdvd01 : (d : ℤ) ∣ Int.gcd (v 0) (v 1) := Int.gcd_dvd_left _ _
  have hdvd0 : (d : ℤ) ∣ v 0 := dvd_trans hdvd01 (Int.gcd_dvd_left _ _)
  have hdvd1 : (d : ℤ) ∣ v 1 := dvd_trans hdvd01 (Int.gcd_dvd_right _ _)
  set w : Vec 3 := ![v 0 / d, v 1 / d, v 2 / d] with hw
  have hvw : v = (d : ℤ) • w := by
    funext i; fin_cases i <;>
      simp [hw, Int.mul_ediv_cancel' hdvd0, Int.mul_ediv_cancel' hdvd1,
        Int.mul_ediv_cancel' hdvd2]
  have hwne : w ≠ 0 := by intro h; apply hv; rw [hvw, h, smul_zero]
  have hkey : Q G v = (d : ℤ) ^ 2 * Q G w := by rw [hvw, Q_smul]
  have hpos : 0 < Q G w := hPD w hwne
  have hd2' : (4 : ℤ) ≤ (d : ℤ) ^ 2 := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd2
    nlinarith
  nlinarith [hkey, h1, hpos, hd2']

set_option maxHeartbeats 1000000 in
/-- A determinant-1 positive definite integral ternary form is congruent to the identity. -/
lemma diagonalize3 (G : Mat 3) (hsymm : G.IsSymm) (hPD : PD G) (hdet : G.det = 1) :
    ∃ P : Mat 3, IsUnit P.det ∧ Pᵀ * G * P = 1 := by
  obtain ⟨w, hw, hQ1⟩ := repr_one_3 G hsymm hPD hdet
  have hcop := coprime3_of_value hPD hw hQ1
  obtain ⟨U, hUdet, hUcol⟩ := extend3 (w 0) (w 1) (w 2) hcop
  have hw3 : (![w 0, w 1, w 2] : Vec 3) = w := by funext i; fin_cases i <;> rfl
  rw [hw3] at hUcol
  set G₁ := Uᵀ * G * U with hG₁
  have hUunit : IsUnit U.det := by rw [hUdet]; exact isUnit_one
  have hPD₁ : PD G₁ := PD_conj hUunit hPD
  have hG₁00 : G₁ 0 0 = 1 := by
    have : Q G₁ ![1, 0, 0] = 1 := by rw [hG₁, ← Q_conj, hUcol, hQ1]
    rw [← this]; unfold Q; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hsymm₁ : G₁ᵀ = G₁ := symm_conj hsymm
  have hg10 : G₁ 1 0 = G₁ 0 1 := by
    have h := congrFun (congrFun hsymm₁ 0) 1; rwa [Matrix.transpose_apply] at h
  have hg20 : G₁ 2 0 = G₁ 0 2 := by
    have h := congrFun (congrFun hsymm₁ 0) 2; rwa [Matrix.transpose_apply] at h
  have hg21 : G₁ 2 1 = G₁ 1 2 := by
    have h := congrFun (congrFun hsymm₁ 1) 2; rwa [Matrix.transpose_apply] at h
  have hdet₁ : G₁.det = 1 := by
    rw [hG₁, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hUdet, hdet]; ring
  set S : Mat 3 := !![1, -(G₁ 0 1), -(G₁ 0 2); 0, 1, 0; 0, 0, 1] with hS
  have hSdet : S.det = 1 := by rw [hS, Matrix.det_fin_three]; simp
  set G₂ := Sᵀ * G₁ * S with hG₂
  set h : Mat 2 := !![G₁ 1 1 - (G₁ 0 1) ^ 2, G₁ 1 2 - (G₁ 0 1) * (G₁ 0 2);
      G₁ 1 2 - (G₁ 0 1) * (G₁ 0 2), G₁ 2 2 - (G₁ 0 2) ^ 2] with hh
  have s00 : S 0 0 = 1 := by rw [hS]; rfl
  have s01 : S 0 1 = -(G₁ 0 1) := by rw [hS]; rfl
  have s02 : S 0 2 = -(G₁ 0 2) := by rw [hS]; rfl
  have s10 : S 1 0 = 0 := by rw [hS]; rfl
  have s11 : S 1 1 = 1 := by rw [hS]; rfl
  have s12 : S 1 2 = 0 := by rw [hS]; rfl
  have s20 : S 2 0 = 0 := by rw [hS]; rfl
  have s21 : S 2 1 = 0 := by rw [hS]; rfl
  have s22 : S 2 2 = 1 := by rw [hS]; rfl
  have hh00 : h 0 0 = G₁ 1 1 - (G₁ 0 1) ^ 2 := by rw [hh]; rfl
  have hh01 : h 0 1 = G₁ 1 2 - (G₁ 0 1) * (G₁ 0 2) := by rw [hh]; rfl
  have hh10 : h 1 0 = G₁ 1 2 - (G₁ 0 1) * (G₁ 0 2) := by rw [hh]; rfl
  have hh11 : h 1 1 = G₁ 2 2 - (G₁ 0 2) ^ 2 := by rw [hh]; rfl
  have fin2 : ∀ (hh : 2 < 3), (⟨2, hh⟩ : Fin 3) = 2 := fun _ => rfl
  have hG₂eq : G₂ = diagBR h := by
    funext i j
    rw [hG₂]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.mk_zero, Fin.mk_one, fin2, Fin.isValue,
        diagBR, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
        s00, s01, s02, s10, s11, s12, s20, s21, s22,
        hg10, hg20, hg21, hG₁00, hh00, hh01, hh10, hh11,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply] <;> ring
  have hPD₂ : PD G₂ := by rw [hG₂]; exact PD_conj (by rw [hSdet]; exact isUnit_one) hPD₁
  have hPDh : PD h := by
    intro u hu
    have hwu : (![(0 : ℤ), u 0, u 1] : Vec 3) ≠ 0 := by
      intro hcon; apply hu; funext i; fin_cases i
      · have := congrFun hcon 1; simpa using this
      · have := congrFun hcon 2; simpa using this
    have := hPD₂ ![0, u 0, u 1] hwu
    rw [hG₂eq] at this
    have heval : Q (diagBR h) ![0, u 0, u 1] = Q h u := by
      unfold Q
      have hu2 : (![u 0, u 1] : Vec 2) = u := by funext i; fin_cases i <;> rfl
      rw [diagBR_mulVec]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three, hu2]
    rwa [heval] at this
  have hdeth : h.det = 1 := by
    have : G₂.det = 1 := by
      rw [hG₂, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hSdet, hdet₁]; ring
    rw [hG₂eq, det_diagBR] at this; exact this
  have hsymmh : h.IsSymm := by
    rw [Matrix.IsSymm, hh]; funext i j; fin_cases i <;> fin_cases j <;> simp
  obtain ⟨P₂, hP₂unit, hP₂eq⟩ := diagonalize2 h hsymmh hPDh hdeth
  refine ⟨U * S * diagBR P₂, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, det_diagBR, hUdet, hSdet, one_mul, one_mul]; exact hP₂unit
  · have hchain : (U * S * diagBR P₂)ᵀ * G * (U * S * diagBR P₂)
        = (diagBR P₂)ᵀ * G₂ * diagBR P₂ := by
      rw [hG₂, hG₁]
      rw [Matrix.transpose_mul, Matrix.transpose_mul]
      noncomm_ring
    rw [hchain, hG₂eq, diagBR_transpose, ← diagBR_mul, ← diagBR_mul, hP₂eq, diagBR_one]

/-- A determinant-1 positive definite symmetric integral ternary form has its `(0,0)` entry a
sum of three squares. -/
lemma three_sq_of_det1 (G : Mat 3) (hsymm : G.IsSymm) (hPD : PD G) (hdet : G.det = 1) :
    ∃ a b c : ℤ, G 0 0 = a ^ 2 + b ^ 2 + c ^ 2 := by
  obtain ⟨P, hPunit, hPeq⟩ := diagonalize3 G hsymm hPD hdet
  exact sum3_of_conj_one hPunit hPeq

set_option maxHeartbeats 1000000 in
/-- If we can find integers `m, k, ℓ` making the form `[[n,1,0],[1,m,k],[0,k,ℓ]]` have
determinant `1` and positive-definiteness conditions `n>0`, `nm-1>0`, then `n` is a sum
of three squares. -/
lemma three_sq_from_params (n m k ℓ : ℤ) (hn : 0 < n) (hd2 : 0 < n * m - 1)
    (hdet : n * (m * ℓ - k ^ 2) - ℓ = 1) : ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  set G : Mat 3 := !![n, 1, 0; 1, m, k; 0, k, ℓ] with hG
  have g00 : G 0 0 = n := by rw [hG]; rfl
  have g01 : G 0 1 = 1 := by rw [hG]; rfl
  have g02 : G 0 2 = 0 := by rw [hG]; rfl
  have g10 : G 1 0 = 1 := by rw [hG]; rfl
  have g11 : G 1 1 = m := by rw [hG]; rfl
  have g12 : G 1 2 = k := by rw [hG]; rfl
  have g20 : G 2 0 = 0 := by rw [hG]; rfl
  have g21 : G 2 1 = k := by rw [hG]; rfl
  have g22 : G 2 2 = ℓ := by rw [hG]; rfl
  have hsymm : G.IsSymm := by
    have fin2 : ∀ (hh : 2 < 3), (⟨2, hh⟩ : Fin 3) = 2 := fun _ => rfl
    show Gᵀ = G; funext i j; fin_cases i <;> fin_cases j <;>
      simp only [Fin.mk_zero, Fin.mk_one, fin2, Fin.isValue, Matrix.transpose_apply,
        g00, g01, g02, g10, g11, g12, g20, g21, g22]
  have hdetG : G.det = 1 := by
    rw [Matrix.det_fin_three, g00, g01, g02, g10, g11, g12, g20, g21, g22]
    linear_combination hdet
  have hG00 : G 0 0 = n := g00
  have hPD : PD G := by
    intro v hv
    have hQval : Q G v = n * (v 0) ^ 2 + m * (v 1) ^ 2 + ℓ * (v 2) ^ 2
        + 2 * (v 0) * (v 1) + 2 * k * (v 1) * (v 2) := by
      simp only [Q, Matrix.mulVec, dotProduct, Fin.sum_univ_three, g00, g01, g02, g10, g11, g12,
        g20, g21, g22]
      ring
    set v0 := v 0 with hv0
    set v1 := v 1 with hv1
    set v2 := v 2 with hv2
    have hne : v0 ≠ 0 ∨ v1 ≠ 0 ∨ v2 ≠ 0 := by
      by_contra h; push_neg at h
      obtain ⟨h0, h1, h2⟩ := h
      apply hv; funext i; fin_cases i
      · exact h0
      · exact h1
      · exact h2
    have key : (n * m - 1) * n * (Q G v) =
        (n * m - 1) * (n * v0 + v1) ^ 2 + ((n * m - 1) * v1 + n * k * v2) ^ 2
        + n * v2 ^ 2 * (n * (m * ℓ - k ^ 2) - ℓ) := by
      rw [hQval]; ring
    rw [hdet, mul_one] at key
    have hsq : ∀ a : ℤ, a ≠ 0 → 0 < a ^ 2 := by
      intro a ha; rcases lt_or_gt_of_ne ha with h | h <;> nlinarith
    have hT1 : 0 ≤ (n * m - 1) * (n * v0 + v1) ^ 2 := by positivity
    have hT2 : 0 ≤ ((n * m - 1) * v1 + n * k * v2) ^ 2 := sq_nonneg _
    have hT3 : 0 ≤ n * v2 ^ 2 := by positivity
    have hrhs : 0 < (n * m - 1) * (n * v0 + v1) ^ 2 + ((n * m - 1) * v1 + n * k * v2) ^ 2
        + n * v2 ^ 2 := by
      by_cases hz2 : v2 = 0
      · by_cases hz1 : v1 = 0
        · have hv0ne : v0 ≠ 0 := by
            rcases hne with h | h | h
            · exact h
            · exact absurd hz1 h
            · exact absurd hz2 h
          have hp1 : 0 < (n * v0 + v1) ^ 2 := by
            rw [hz1, add_zero]; exact hsq _ (mul_ne_zero (ne_of_gt hn) hv0ne)
          have : 0 < (n * m - 1) * (n * v0 + v1) ^ 2 := mul_pos hd2 hp1
          linarith
        · have hp2 : 0 < ((n * m - 1) * v1 + n * k * v2) ^ 2 := by
            apply hsq; rw [hz2, mul_zero, add_zero]
            exact mul_ne_zero (ne_of_gt hd2) hz1
          linarith
      · have hp3 : 0 < n * v2 ^ 2 := mul_pos hn (hsq _ hz2)
        linarith
    have hcoef : 0 < (n * m - 1) * n := mul_pos hd2 hn
    nlinarith [key, hrhs, hcoef]
  obtain ⟨a, b, c, h⟩ := three_sq_of_det1 G hsymm hPD hdetG
  exact ⟨a, b, c, by rw [← hG00, h]⟩

open scoped NumberTheorySymbols in
/-- From `J(-n | p) = 1` for a prime `p ∤ n`, deduce `-n` is a square mod `p`. -/
lemma isSquare_of_jac (n : ℤ) (p : ℕ) [Fact p.Prime] (hj : jacobiSym (-n) p = 1) :
    IsSquare (-(n : ZMod p)) := by
  have h := ZMod.isSquare_of_jacobiSym_eq_one hj
  rwa [show ((-n : ℤ) : ZMod p) = -(n : ZMod p) by push_cast; ring] at h

open scoped NumberTheorySymbols in
/-- Reciprocity for `n ≡ 1 mod 4` (odd): if `p ≡ 1 mod 4` and `n ∣ p+1` then `J(-n|p)=1`. -/
lemma jac_n1mod4 (n p : ℕ) (hn4 : n % 4 = 1) (hno : Odd n)
    (hp4 : p % 4 = 1) (hpn : (n : ℤ) ∣ ((p : ℤ) + 1)) : jacobiSym (-(n : ℤ)) p = 1 := by
  have hpodd : Odd p := by rw [Nat.odd_iff]; omega
  rw [show (-(n : ℤ)) = (-1) * (n : ℤ) by ring, jacobiSym.mul_left]
  rw [jacobiSym.at_neg_one hpodd, ZMod.χ₄_nat_one_mod_four hp4]
  rw [jacobiSym.quadratic_reciprocity_one_mod_four' hno hp4]
  have hmod : (p : ℤ) % (n : ℤ) = (-1) % (n : ℤ) := by
    have h2 : ((p : ℤ)) ≡ (-1) [ZMOD (n : ℤ)] := by
      rw [Int.modEq_iff_dvd, show (-1 : ℤ) - ↑p = -(↑p + 1) from by ring]; exact dvd_neg.mpr hpn
    exact h2
  rw [jacobiSym.mod_left' hmod, jacobiSym.at_neg_one hno, ZMod.χ₄_nat_one_mod_four hn4]
  norm_num

open scoped NumberTheorySymbols in
/-- Reciprocity for `n ≡ 3 mod 8` using the factor `2`: if `p ≡ 1 mod 4` and `n ∣ 2p+1`
then `J(-n|p)=1`. -/
lemma jac_n3mod8 (n p : ℕ) (hn8 : n % 8 = 3) (hno : Odd n) (hp4 : p % 4 = 1)
    (hpn : (n : ℤ) ∣ (2 * (p : ℤ) + 1)) : jacobiSym (-(n : ℤ)) p = 1 := by
  have hpodd : Odd p := by rw [Nat.odd_iff]; omega
  rw [show (-(n : ℤ)) = (-1) * (n : ℤ) by ring, jacobiSym.mul_left,
      jacobiSym.at_neg_one hpodd, ZMod.χ₄_nat_one_mod_four hp4, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four' hno hp4]
  have hmod : (2 * (p : ℤ)) % (n : ℤ) = (-1) % (n : ℤ) := by
    have h2 : (2 * (p : ℤ)) ≡ (-1) [ZMOD (n : ℤ)] := by
      rw [Int.modEq_iff_dvd, show (-1 : ℤ) - 2 * p = -(2 * p + 1) from by ring]
      exact dvd_neg.mpr hpn
    exact h2
  have key : jacobiSym 2 n * jacobiSym (p : ℤ) n = jacobiSym (-1 : ℤ) n := by
    rw [← jacobiSym.mul_left]; exact jacobiSym.mod_left' hmod
  rw [jacobiSym.at_two hno, jacobiSym.at_neg_one hno] at key
  have h8 : ZMod.χ₈ (n : ℕ) = -1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight]; split_ifs <;> omega
  have h4 : ZMod.χ₄ (n : ℕ) = -1 := ZMod.χ₄_nat_three_mod_four (by omega)
  rw [h8, h4] at key
  linarith [key]

open scoped NumberTheorySymbols in
/-- Reciprocity for `n = 2n'`, `n' ≡ 1 mod 4`: if `p ≡ 1 mod 8` and `n ∣ p+1` then `J(-n|p)=1`. -/
lemma jac_n2mod8 (n p n' : ℕ) (hn : n = 2 * n') (hn'4 : n' % 4 = 1) (hno' : Odd n')
    (hp8 : p % 8 = 1) (hpn' : (n' : ℤ) ∣ ((p : ℤ) + 1)) : jacobiSym (-(n : ℤ)) p = 1 := by
  have hpodd : Odd p := by rw [Nat.odd_iff]; omega
  have hp4 : p % 4 = 1 := by omega
  have hnZ : (-(n : ℤ)) = (-1) * (2 * (n' : ℤ)) := by rw [hn]; push_cast; ring
  rw [hnZ, jacobiSym.mul_left, jacobiSym.mul_left,
      jacobiSym.at_neg_one hpodd, ZMod.χ₄_nat_one_mod_four hp4, one_mul,
      jacobiSym.at_two hpodd]
  have h8 : ZMod.χ₈ (p : ℕ) = 1 := by rw [ZMod.χ₈_nat_eq_if_mod_eight]; split_ifs <;> omega
  rw [h8, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four' hno' hp4]
  have hmod : (p : ℤ) % (n' : ℤ) = (-1) % (n' : ℤ) := by
    have h2 : ((p : ℤ)) ≡ (-1) [ZMOD (n' : ℤ)] := by
      rw [Int.modEq_iff_dvd, show (-1 : ℤ) - ↑p = -(↑p + 1) from by ring]; exact dvd_neg.mpr hpn'
    exact h2
  rw [jacobiSym.mod_left' hmod, jacobiSym.at_neg_one hno', ZMod.χ₄_nat_one_mod_four hn'4]

open scoped NumberTheorySymbols in
/-- Reciprocity for `n = 2n'`, `n' ≡ 3 mod 4`: if `p ≡ 3 mod 8` and `n ∣ p+1` then `J(-n|p)=1`. -/
lemma jac_n6mod8 (n p n' : ℕ) (hn : n = 2 * n') (hn'4 : n' % 4 = 3) (hno' : Odd n')
    (hp8 : p % 8 = 3) (hpn' : (n' : ℤ) ∣ ((p : ℤ) + 1)) : jacobiSym (-(n : ℤ)) p = 1 := by
  have hpodd : Odd p := by rw [Nat.odd_iff]; omega
  have hp4 : p % 4 = 3 := by omega
  have hnZ : (-(n : ℤ)) = (-1) * (2 * (n' : ℤ)) := by rw [hn]; push_cast; ring
  rw [hnZ, jacobiSym.mul_left, jacobiSym.mul_left,
      jacobiSym.at_neg_one hpodd, ZMod.χ₄_nat_three_mod_four hp4,
      jacobiSym.at_two hpodd]
  have h8 : ZMod.χ₈ (p : ℕ) = -1 := by rw [ZMod.χ₈_nat_eq_if_mod_eight]; split_ifs <;> omega
  rw [h8]
  have hrec : jacobiSym (n' : ℤ) p = - jacobiSym (p : ℤ) n' :=
    jacobiSym.quadratic_reciprocity_three_mod_four hp4 hn'4
  rw [hrec]
  have hmod : (p : ℤ) % (n' : ℤ) = (-1) % (n' : ℤ) := by
    have h2 : ((p : ℤ)) ≡ (-1) [ZMOD (n' : ℤ)] := by
      rw [Int.modEq_iff_dvd, show (-1 : ℤ) - ↑p = -(↑p + 1) from by ring]; exact dvd_neg.mpr hpn'
    exact h2
  rw [jacobiSym.mod_left' hmod, jacobiSym.at_neg_one hno', ZMod.χ₄_nat_three_mod_four hn'4]
  ring

/-- If `-n` is a square mod a prime `p` not dividing `n`, then `p ∣ n k² + 1` for some `k`. -/
lemma exists_k_of_isSquare (n : ℤ) (p : ℕ) [Fact p.Prime] (hpn : ¬ (p : ℤ) ∣ n)
    (hsq : IsSquare (-(n : ZMod p))) : ∃ k₀ : ℤ, (p : ℤ) ∣ n * k₀ ^ 2 + 1 := by
  obtain ⟨r, hr⟩ := hsq
  have hne : (n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpn
  set k : ZMod p := r * (n : ZMod p)⁻¹ with hkdef
  refine ⟨(k.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have hkcast : ((k.val : ℕ) : ZMod p) = k := by simp [ZMod.natCast_val, ZMod.cast_id]
  rw [hkcast, hkdef]
  have hstep : (n : ZMod p) * (r * (n : ZMod p)⁻¹) ^ 2 = r * r * (n : ZMod p)⁻¹ := by
    field_simp
  rw [hstep, ← hr, neg_mul, mul_inv_cancel₀ hne]; ring

/-- If there is `D > 0` with `n ∣ D+1` and `D ∣ n k² + 1`, then `n` is a sum of three squares. -/
lemma three_sq_of_div (n : ℤ) (hn : 0 < n) (D : ℤ) (hD : 0 < D) (hDn : n ∣ (D + 1))
    (k₀ : ℤ) (hk : D ∣ n * k₀ ^ 2 + 1) : ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  obtain ⟨m, hm⟩ := hDn
  obtain ⟨ℓ, hℓ⟩ := hk
  refine three_sq_from_params n m k₀ ℓ hn ?_ ?_
  · have : n * m - 1 = D := by linarith
    rw [this]; exact hD
  · linear_combination -ℓ * hm - hℓ

/-- Construction for `n` with `n ∣ p+1` and `-n` a QR mod the prime `p` (handles `n ≡ 1 mod 4`
and the even cases). -/
lemma three_sq_via_Dp (n : ℤ) (hn : 0 < n) (p : ℕ) [Fact p.Prime]
    (hpn1 : n ∣ ((p : ℤ) + 1)) (hpnd : ¬ (p : ℤ) ∣ n) (hsq : IsSquare (-(n : ZMod p))) :
    ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  obtain ⟨k₀, hk⟩ := exists_k_of_isSquare n p hpnd hsq
  exact three_sq_of_div n hn p (by exact_mod_cast (Fact.out : p.Prime).pos) hpn1 k₀ hk

/-- Construction for odd `n ≡ 3 mod 8` using `D = 2p`. -/
lemma three_sq_via_D2p (n : ℤ) (hn : 0 < n) (hodd : Odd n) (p : ℕ) [Fact p.Prime]
    (hpodd : Odd p) (hpn1 : n ∣ (2 * (p : ℤ) + 1)) (hpnd : ¬ (p : ℤ) ∣ n)
    (hsq : IsSquare (-(n : ZMod p))) : ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  obtain ⟨k₀, hk0⟩ := exists_k_of_isSquare n p hpnd hsq
  set k : ℤ := if Odd k₀ then k₀ else k₀ + p with hkdef
  have hpk : (p : ℤ) ∣ n * k ^ 2 + 1 := by
    by_cases h : Odd k₀
    · simp only [hkdef, if_pos h]; exact hk0
    · simp only [hkdef, if_neg h]
      have he : n * (k₀ + p) ^ 2 + 1 = (n * k₀ ^ 2 + 1) + (p : ℤ) * (n * (2 * k₀ + p)) := by ring
      rw [he]; exact dvd_add hk0 (Dvd.intro _ rfl)
  have hkodd : Odd k := by
    by_cases h : Odd k₀
    · simpa only [hkdef, if_pos h] using h
    · simp only [hkdef, if_neg h]
      rw [Int.not_odd_iff_even] at h
      have hpZ : Odd (p:ℤ) := by exact_mod_cast hpodd
      exact h.add_odd hpZ
  have h2k : (2 : ℤ) ∣ n * k ^ 2 + 1 := by
    have hodd2 : Odd (n * k ^ 2) := hodd.mul (hkodd.pow)
    obtain ⟨t, ht⟩ := hodd2
    exact ⟨t + 1, by rw [ht]; ring⟩
  have hcop : IsCoprime (2 : ℤ) (p : ℤ) := by
    have hpZ : Odd (p:ℤ) := by exact_mod_cast hpodd
    obtain ⟨t, ht⟩ := hpZ
    exact ⟨-t, 1, by rw [ht]; ring⟩
  have hdvd : (2 * (p : ℤ)) ∣ n * k ^ 2 + 1 := hcop.mul_dvd h2k hpk
  have h2p : (0:ℤ) < 2 * (p:ℤ) := by
    have : (0:ℤ) < (p:ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
    linarith
  exact three_sq_of_div n hn (2 * p) h2p hpn1 k hdvd

/-- If there is a prime `p` with `n ∣ p+1` and `p ∣ n k² + 1`, then `n` is a sum of three
squares.  (Here `m = (p+1)/n`, `ℓ = (n k²+1)/p` give a determinant-1 PD form.) -/
lemma three_sq_of_prime (n : ℤ) (hn : 0 < n) (p : ℕ) (hp : p.Prime)
    (hpn : n ∣ (p + 1)) (k₀ : ℤ) (hk : (p : ℤ) ∣ n * k₀ ^ 2 + 1) :
    ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  obtain ⟨m, hm⟩ := hpn
  obtain ⟨ℓ, hℓ⟩ := hk
  have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
  refine three_sq_from_params n m k₀ ℓ hn ?_ ?_
  · have : n * m - 1 = (p : ℤ) := by linarith [hm]
    rw [this]; linarith
  · linear_combination -ℓ * hm - hℓ

/-- Helper: a coprime residue `A` mod `4*n` with `A ≡ 1 mod 4`, `n ∣ A+1`, gives a Dirichlet
prime `p > n` with `p % 4 = 1` and `n ∣ p+1`, and `¬ p ∣ n`. -/
lemma dirichlet_prime (n A : ℕ) (hn0 : 0 < n) (hcop : Nat.Coprime A (4 * n))
    (hA4 : A % 4 = 1) (hAn : n ∣ A + 1) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ (n : ℤ) ∣ ((p : ℤ) + 1) ∧ ¬ (p : ℤ) ∣ (n : ℤ) := by
  obtain ⟨p, hpgt, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_modEq n (q := 4 * n)
    (by positivity) hcop
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · have h4 : p ≡ A [MOD 4] := hpmod.of_mul_right n
    simpa [Nat.ModEq, hA4] using h4
  · have hn : p ≡ A [MOD n] := hpmod.of_mul_left 4
    have hdvd : n ∣ p + 1 := by
      have h0 : p + 1 ≡ A + 1 [MOD n] := hn.add_right 1
      have h1 : A + 1 ≡ 0 [MOD n] := (Nat.modEq_zero_iff_dvd).mpr hAn
      exact (Nat.modEq_zero_iff_dvd).mp (h0.trans h1)
    exact_mod_cast hdvd
  · intro hc
    have hpdvd : p ∣ n := by exact_mod_cast hc
    have : p ≤ n := Nat.le_of_dvd hn0 hpdvd
    omega

/-- Dirichlet prime variant giving `n ∣ 2p+1`. -/
lemma dirichlet_prime2 (n A : ℕ) (hn0 : 0 < n) (hcop : Nat.Coprime A (4 * n))
    (hA4 : A % 4 = 1) (hAn : n ∣ 2 * A + 1) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ (n : ℤ) ∣ (2 * (p : ℤ) + 1) ∧ ¬ (p : ℤ) ∣ (n : ℤ) := by
  obtain ⟨p, hpgt, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_modEq n (q := 4 * n)
    (by positivity) hcop
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · have h4 : p ≡ A [MOD 4] := hpmod.of_mul_right n
    simpa [Nat.ModEq, hA4] using h4
  · have hn : p ≡ A [MOD n] := hpmod.of_mul_left 4
    have h0 : 2 * p + 1 ≡ 2 * A + 1 [MOD n] := (hn.mul_left 2).add_right 1
    have hdvd : n ∣ 2 * p + 1 :=
      (Nat.modEq_zero_iff_dvd).mp (h0.trans (Nat.modEq_zero_iff_dvd.mpr hAn))
    exact_mod_cast hdvd
  · intro hc
    have hpdvd : p ∣ n := by exact_mod_cast hc
    have := Nat.le_of_dvd hn0 hpdvd; omega

/-- Three squares for `n ≡ 3 mod 8`. -/
lemma three_sq_n3mod8 (n : ℕ) (hn8 : n % 8 = 3) :
    ∃ a b c : ℤ, (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 := by
  have hno : Odd n := by rw [Nat.odd_iff]; omega
  have hn0 : 0 < n := by omega
  have hcop4n : Nat.Coprime 4 n := by
    have h2 : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hno
    simpa using h2.pow_left 2
  set cr := Nat.chineseRemainder hcop4n 1 ((n - 1) / 2) with hcr
  have ha4 : (cr : ℕ) ≡ 1 [MOD 4] := cr.property.1
  have han : (cr : ℕ) ≡ ((n - 1) / 2) [MOD n] := cr.property.2
  set A := (cr : ℕ) with hAdef
  have hA4 : A % 4 = 1 := by simpa [Nat.ModEq] using ha4
  have hAodd : A % 2 = 1 := by omega
  have hAn : n ∣ 2 * A + 1 := by
    have h0 : 2 * A ≡ 2 * ((n - 1) / 2) [MOD n] := han.mul_left 2
    have h1 : 2 * ((n - 1) / 2) = n - 1 := by omega
    rw [h1] at h0
    have h2 : 2 * A + 1 ≡ (n - 1) + 1 [MOD n] := h0.add_right 1
    have h3 : (n - 1) + 1 = n := by omega
    rw [h3] at h2
    exact (Nat.modEq_zero_iff_dvd).mp (h2.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))
  have hcopA4 : Nat.Coprime A 4 := by
    have : Nat.Coprime A 2 := Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hAodd)
    simpa using this.pow_right 2
  have hcopAn : Nat.Coprime A n := by
    have hg3 : Nat.gcd A n ∣ 2 * A + 1 := (Nat.gcd_dvd_right A n).trans hAn
    have h2a : Nat.gcd A n ∣ 2 * A := (Nat.gcd_dvd_left A n).mul_left 2
    have : Nat.gcd A n ∣ 1 := (Nat.dvd_add_right h2a).mp hg3
    exact Nat.dvd_one.mp this
  have hcopA4n : Nat.Coprime A (4 * n) := hcopA4.mul_right hcopAn
  obtain ⟨p, hp, hp4, hpn1, hpnd⟩ := dirichlet_prime2 n A hn0 hcopA4n hA4 hAn
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := by rw [Nat.odd_iff]; omega
  have hj := jac_n3mod8 n p hn8 hno hp4 hpn1
  exact three_sq_via_D2p (n : ℤ) (by exact_mod_cast hn0) (by exact_mod_cast hno) p hpodd
    hpn1 hpnd (isSquare_of_jac _ _ hj)

/-- Three squares for odd `n ≡ 1 mod 4`. -/
lemma three_sq_n1mod4 (n : ℕ) (hn1 : n % 4 = 1) :
    ∃ a b c : ℤ, (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 := by
  have hno : Odd n := by rw [Nat.odd_iff]; omega
  have hn0 : 0 < n := by omega
  have hcop4n : Nat.Coprime 4 n := by
    have h2 : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hno
    simpa using h2.pow_left 2
  set cr := Nat.chineseRemainder hcop4n 1 (n - 1) with hcr
  have ha4 : (cr : ℕ) ≡ 1 [MOD 4] := cr.property.1
  have han : (cr : ℕ) ≡ (n - 1) [MOD n] := cr.property.2
  set A := (cr : ℕ) with hAdef
  have hA4 : A % 4 = 1 := by simpa [Nat.ModEq] using ha4
  have hAodd : A % 2 = 1 := by omega
  have hAn : n ∣ A + 1 := by
    have h0 : A + 1 ≡ (n - 1) + 1 [MOD n] := han.add_right 1
    have h1 : (n - 1) + 1 = n := by omega
    rw [h1] at h0
    exact (Nat.modEq_zero_iff_dvd).mp (h0.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))
  have hcopA4 : Nat.Coprime A 4 := by
    have : Nat.Coprime A 2 := Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hAodd)
    simpa using this.pow_right 2
  have hcopAn : Nat.Coprime A n := by
    have hg3 : Nat.gcd A n ∣ A + 1 := (Nat.gcd_dvd_right A n).trans hAn
    have : Nat.gcd A n ∣ 1 := by
      exact (Nat.dvd_add_right (Nat.gcd_dvd_left A n)).mp hg3
    exact Nat.dvd_one.mp this
  have hcopA4n : Nat.Coprime A (4 * n) := hcopA4.mul_right hcopAn
  obtain ⟨p, hp, hp4, hpn1, hpnd⟩ := dirichlet_prime n A hn0 hcopA4n hA4 hAn
  haveI : Fact p.Prime := ⟨hp⟩
  have hj := jac_n1mod4 n p hn1 hno hp4 hpn1
  exact three_sq_via_Dp (n : ℤ) (by exact_mod_cast hn0) p hpn1 hpnd
    (isSquare_of_jac _ _ hj)

end ThreeSq
