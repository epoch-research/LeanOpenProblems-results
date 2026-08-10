import FormalConjectures.Util.ProblemImports

open scoped BigOperators

/-!
Development toward the three-squares theorem.
Step 1: Davenport–Cassels lemma for the form `x² + y² + z²`.
-/

namespace ThreeSq

/-- Round a rational to a nearest integer, with `|q - round q| ≤ 1/2`. -/
noncomputable def rnd (q : ℚ) : ℤ := round q

lemma rnd_close (q : ℚ) : |q - (rnd q : ℚ)| ≤ 1/2 := by
  have := abs_sub_round q
  simpa [rnd] using this

/-- The squared distance of a rational triple to its nearest integer triple is `< 1`
unless the triple is integral. -/
lemma dist_lt_one (x y z : ℚ) :
    (x - (rnd x:ℚ))^2 + (y - (rnd y:ℚ))^2 + (z - (rnd z:ℚ))^2 ≤ 3/4 := by
  have hx := rnd_close x
  have hy := rnd_close y
  have hz := rnd_close z
  have hx2 : (x - (rnd x:ℚ))^2 ≤ (1/2)^2 := by
    apply sq_le_sq' <;> linarith [abs_le.1 hx]
  have hy2 : (y - (rnd y:ℚ))^2 ≤ (1/2)^2 := by
    apply sq_le_sq' <;> linarith [abs_le.1 hy]
  have hz2 : (z - (rnd z:ℚ))^2 ≤ (1/2)^2 := by
    apply sq_le_sq' <;> linarith [abs_le.1 hz]
  nlinarith [hx2, hy2, hz2]

/-- Centered division: for `d > 0` there is an integer `w` with `4*(a-d*w)^2 ≤ d^2`,
i.e. `|a - d*w| ≤ d/2`. -/
lemma exists_centered (a d : ℤ) (hd : 0 < d) : ∃ w : ℤ, 4 * (a - d * w) ^ 2 ≤ d ^ 2 := by
  refine ⟨round ((a : ℚ) / d), ?_⟩
  have hdq : (0:ℚ) < d := by exact_mod_cast hd
  have hclose : |(a : ℚ) / d - (round ((a:ℚ)/d) : ℚ)| ≤ 1/2 := abs_sub_round _
  -- multiply by d
  have hb : |(a : ℚ) - d * (round ((a:ℚ)/d) : ℚ)| ≤ d / 2 := by
    have heq : (a : ℚ) - d * (round ((a:ℚ)/d) : ℚ)
        = d * ((a:ℚ)/d - (round ((a:ℚ)/d):ℚ)) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos hdq]
    calc d * |(a:ℚ)/d - (round ((a:ℚ)/d):ℚ)| ≤ d * (1/2) := by
            apply mul_le_mul_of_nonneg_left hclose (le_of_lt hdq)
      _ = d / 2 := by ring
  -- square both sides
  have hsq : ((a : ℚ) - d * (round ((a:ℚ)/d):ℚ))^2 ≤ (d/2)^2 := by
    have h := abs_le.1 hb
    nlinarith [h.1, h.2]
  -- now cast to ℤ
  set w := round ((a:ℚ)/d) with hw
  have hcast : (((4 * (a - d * w)^2 : ℤ)) : ℚ) ≤ ((d^2 : ℤ) : ℚ) := by
    push_cast
    nlinarith [hsq]
  exact_mod_cast hcast

/-- **Davenport–Cassels** for the sum of three squares: if some positive multiple
`n * d²` of `n` is a sum of three integer squares, then so is `n`. -/
theorem davenport_cassels (n : ℤ)
    (h : ∃ a b c d : ℤ, 0 < d ∧ a ^ 2 + b ^ 2 + c ^ 2 = n * d ^ 2) :
    ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n := by
  -- the set of positive `d` that work
  obtain ⟨a0, b0, c0, d0, hd0, hrep0⟩ := h
  -- well-founded: minimal positive d
  have hne : ∃ d : ℕ, 0 < d ∧ ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n * (d:ℤ) ^ 2 := by
    refine ⟨d0.toNat, ?_, a0, b0, c0, ?_⟩
    · omega
    · rw [Int.toNat_of_nonneg (le_of_lt hd0)]; exact hrep0
  classical
  obtain ⟨hdpos, a, b, c, hrep⟩ := Nat.find_spec hne
  set d := Nat.find hne with hd_def
  -- claim d = 1
  by_cases hd1 : d = 1
  · refine ⟨a, b, c, ?_⟩
    have hdone : ((d : ℤ)) = 1 := by exact_mod_cast hd1
    rw [hdone] at hrep; simpa using hrep
  · exfalso
    -- d ≥ 2
    have hd2 : 2 ≤ d := by omega
    have hdZ : (1:ℤ) < (d:ℤ) := by exact_mod_cast hd2
    have hdZpos : (0:ℤ) < (d:ℤ) := by exact_mod_cast hdpos
    -- centered approximations
    obtain ⟨wa, hwa⟩ := exists_centered a (d:ℤ) hdZpos
    obtain ⟨wb, hwb⟩ := exists_centered b (d:ℤ) hdZpos
    obtain ⟨wc, hwc⟩ := exists_centered c (d:ℤ) hdZpos
    -- abbreviations as genuine (non-let) variables to avoid `isDefEq` blowup
    obtain ⟨W, hW⟩ : ∃ W : ℤ, W = wa ^ 2 + wb ^ 2 + wc ^ 2 := ⟨_, rfl⟩
    obtain ⟨S, hS⟩ : ∃ S : ℤ, S = a * wa + b * wb + c * wc := ⟨_, rfl⟩
    obtain ⟨K, hK⟩ : ∃ K : ℤ, K = n * d - 2 * S + d * W := ⟨_, rfl⟩
    -- |u|^2 = d * K  where u = v - d w
    have hu2 : (a - d * wa) ^ 2 + (b - d * wb) ^ 2 + (c - d * wc) ^ 2 = (d:ℤ) * K := by
      simp only [hK, hS, hW]
      linear_combination hrep
    -- |u|^2 < d^2
    have hu2lt : (a - d * wa) ^ 2 + (b - d * wb) ^ 2 + (c - d * wc) ^ 2 < (d:ℤ) ^ 2 := by
      nlinarith [hwa, hwb, hwc, mul_pos hdZpos hdZpos]
    -- hence K < d  and  0 ≤ K
    have hSnn : 0 ≤ (a - d * wa) ^ 2 + (b - d * wb) ^ 2 + (c - d * wc) ^ 2 := by positivity
    have hKnonneg : 0 ≤ K := by
      rw [hu2] at hSnn
      nlinarith [hSnn, hdZpos]
    have hKlt : K < (d:ℤ) := by nlinarith [hu2, hu2lt, hdZpos]
    rcases eq_or_lt_of_le hKnonneg with hK0 | hKpos
    · -- K = 0  ⇒  u = 0  ⇒  n = W, an integer rep, so d = 1
      have huzero : (a - d * wa) ^ 2 + (b - d * wb) ^ 2 + (c - d * wc) ^ 2 = 0 := by
        rw [hu2, ← hK0]; ring
      have hxa : (a - d * wa) ^ 2 = 0 := by
        linarith only [sq_nonneg (a-d*wa), sq_nonneg (b-d*wb), sq_nonneg (c-d*wc), huzero]
      have hxb : (b - d * wb) ^ 2 = 0 := by
        linarith only [sq_nonneg (a-d*wa), sq_nonneg (b-d*wb), sq_nonneg (c-d*wc), huzero]
      have hxc : (c - d * wc) ^ 2 = 0 := by
        linarith only [sq_nonneg (a-d*wa), sq_nonneg (b-d*wb), sq_nonneg (c-d*wc), huzero]
      have ha : a = d * wa := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hxa; linarith
      have hb' : b = d * wb := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hxb; linarith
      have hc' : c = d * wc := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hxc; linarith
      have hnW : n = W := by
        have hcancel : n * (d:ℤ)^2 = W * (d:ℤ)^2 := by
          rw [← hrep, hW]; rw [ha, hb', hc']; ring
        have hd2ne : (d:ℤ)^2 ≠ 0 := by positivity
        exact mul_right_cancel₀ hd2ne hcancel
      have hwork : 0 < 1 ∧ ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n * ((1:ℕ):ℤ) ^ 2 := by
        refine ⟨one_pos, wa, wb, wc, ?_⟩
        push_cast; rw [hnW, hW]; ring
      have hfind := Nat.find_le (h := hne) hwork
      rw [← hd_def] at hfind
      omega
    · -- K ≥ 1, build a smaller representation
      have hid : (K * wa + (W - n) * (a - d * wa)) ^ 2
          + (K * wb + (W - n) * (b - d * wb)) ^ 2
          + (K * wc + (W - n) * (c - d * wc)) ^ 2 = n * K ^ 2 := by
        simp only [hK, hS, hW]
        linear_combination (n - (wa^2+wb^2+wc^2))^2 * hrep
      have hKnat : 0 < K.toNat := by omega
      have hwork : 0 < K.toNat ∧ ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n * ((K.toNat:ℕ):ℤ) ^ 2 := by
        refine ⟨hKnat, K * wa + (W - n) * (a - d * wa),
          K * wb + (W - n) * (b - d * wb), K * wc + (W - n) * (c - d * wc), ?_⟩
        rw [Int.toNat_of_nonneg (le_of_lt hKpos)]
        exact hid
      have hle := Nat.find_le (h := hne) hwork
      rw [← hd_def] at hle
      have hlt : (K.toNat : ℤ) < (d:ℤ) := by
        rw [Int.toNat_of_nonneg (le_of_lt hKpos)]; exact hKlt
      omega

end ThreeSq
