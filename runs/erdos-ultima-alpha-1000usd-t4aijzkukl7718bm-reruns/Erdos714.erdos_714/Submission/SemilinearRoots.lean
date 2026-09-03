import FormalConjecturesUtil

/-!
A semilinear root bound investigated as an ingredient for Erdős 714.
This file asserts no graph construction and does not settle the conjecture.
-/

namespace Erdos714Semilinear

variable {F : Type*} [Field F]

/-- The cross ratio used in the semilinear fixed-point argument. -/
def ratio (x y z w : F) : F := (x-y)*(z-w)/((x-w)*(z-y))

lemma ratio_ne_zero {x y z w : F} (hxy : x ≠ y) (hzw : z ≠ w)
    (hxw : x ≠ w) (hzy : z ≠ y) : ratio x y z w ≠ 0 := by
  exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hxy) (sub_ne_zero.mpr hzw))
    (mul_ne_zero (sub_ne_zero.mpr hxw) (sub_ne_zero.mpr hzy))

lemma ratio_ne_one {x y z w : F} (hxz : x ≠ z) (hyw : y ≠ w)
    (hxw : x ≠ w) (hzy : z ≠ y) : ratio x y z w ≠ 1 := by
  intro h
  have hden := mul_ne_zero (sub_ne_zero.mpr hxw) (sub_ne_zero.mpr hzy)
  have he : (x-y)*(z-w) = (x-w)*(z-y) := by
    simpa only [one_mul] using (div_eq_iff hden).mp h
  have hp : (x-z)*(y-w) = 0 := by linear_combination he
  exact (mul_ne_zero (sub_ne_zero.mpr hxz) (sub_ne_zero.mpr hyw)) hp

lemma map_ratio (σ : F →+* F) (x y z w : F) :
    σ (ratio x y z w) = ratio (σ x) (σ y) (σ z) (σ w) := by
  simp [ratio]

/-- Multiplying a difference of two root equations yields the fractional-linear
transformation law for that difference. -/
lemma root_difference (σ : F →+* F) (a b x y : F)
    (hx : x * σ x + a*x + b = 0) (hy : y * σ y + a*y + b = 0) :
    (σ x - σ y) * (x*y) = b*(x-y) := by
  linear_combination y * hx - x * hy

lemma root_nonzero (σ : F →+* F) (a b x : F) (hb : b ≠ 0)
    (hx : x * σ x + a*x + b = 0) : x ≠ 0 := by
  intro h
  subst x
  exact hb (by simpa using hx)

lemma root_difference_div (σ : F →+* F) (a b x y : F) (hb : b ≠ 0)
    (hx : x * σ x + a*x + b = 0) (hy : y * σ y + a*y + b = 0) :
    σ x - σ y = b*(x-y)/(x*y) := by
  apply (eq_div_iff (mul_ne_zero (root_nonzero σ a b x hb hx)
    (root_nonzero σ a b y hb hy))).mpr
  exact root_difference σ a b x y hx hy

/-- The cross ratio of four roots of a nonsingular semilinear quadratic is
fixed by the field endomorphism. -/
lemma ratio_fixed (σ : F →+* F) (a b x y z w : F) (hb : b ≠ 0)
    (hx : x * σ x + a*x + b = 0) (hy : y * σ y + a*y + b = 0)
    (hz : z * σ z + a*z + b = 0) (hw : w * σ w + a*w + b = 0) :
    σ (ratio x y z w) = ratio x y z w := by
  have hx0 := root_nonzero σ a b x hb hx
  have hy0 := root_nonzero σ a b y hb hy
  have hz0 := root_nonzero σ a b z hb hz
  have hw0 := root_nonzero σ a b w hb hw
  rw [map_ratio]
  unfold ratio
  rw [root_difference_div σ a b x y hb hx hy,
    root_difference_div σ a b z w hb hz hw,
    root_difference_div σ a b x w hb hx hw,
    root_difference_div σ a b z y hb hz hy]
  field_simp

/-- If the fixed field has only zero and one, the equation has at most three
roots. The endomorphism may be an arbitrarily high Frobenius power. -/
theorem root_bound (σ : F →+* F)
    (hfix : ∀ x : F, σ x = x → x = 0 ∨ x = 1)
    (a b : F) (S : Finset F)
    (hS : ∀ x ∈ S, x * σ x + a*x + b = 0) : S.card ≤ 3 := by
  classical
  by_contra! hcard
  obtain ⟨x, y, z, w, hx, hy, hz, hw, hxy, hxz, hxw, hyz, hyw, hzw⟩ :=
    Finset.three_lt_card_iff.mp hcard
  by_cases hb : b = 0
  · subst b
    have hroot (v : F) (hv : v ∈ S) : v = 0 ∨ σ v = -a := by
      have he : v * (σ v + a) = 0 := by
        linear_combination hS v hv
      rcases mul_eq_zero.mp he with h | h
      · exact Or.inl h
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    have hlim : S ⊆ {0, x, y} := by
      intro v hv
      rcases hroot v hv with hv0 | hv1
      · simp [hv0]
      by_cases hx0 : x = 0
      · have hy0 : y ≠ 0 := by simpa [hx0] using hxy.symm
        have hy1 := (hroot y hy).resolve_left hy0
        have hvy : v = y := σ.injective (hv1.trans hy1.symm)
        simp [hvy]
      · have hx1 := (hroot x hx).resolve_left hx0
        have hvx : v = x := σ.injective (hv1.trans hx1.symm)
        simp [hvx]
    exact (not_le_of_gt hcard) ((Finset.card_le_card hlim).trans Finset.card_le_three)
  · have hf := ratio_fixed σ a b x y z w hb (hS x hx) (hS y hy) (hS z hz)
      (hS w hw)
    rcases hfix _ hf with h | h
    · exact ratio_ne_zero hxy hzw hxw hyz.symm h
    · exact ratio_ne_one hxz hyw hxw hyz.symm h

/-- A translate of the same equation allows a second semilinear coefficient. -/
theorem shifted_root_bound (σ : F →+* F)
    (hfix : ∀ x : F, σ x = x → x = 0 ∨ x = 1)
    (a b d : F) (S : Finset F)
    (hS : ∀ x ∈ S, x * σ x + d*σ x + a*x + b = 0) : S.card ≤ 3 := by
  classical
  have h := root_bound σ hfix (a - σ d) (b - a*d)
    (S.image (fun x => x+d)) ?_
  · rwa [Finset.card_image_of_injective _ (fun x y h => add_right_cancel h)] at h
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [map_add]
    linear_combination hS x hx


/-- A nonconstant affine semilinear equation has at most two roots. -/
theorem affine_root_bound (σ : F →+* F)
    (hfix : ∀ x : F, σ x = x → x = 0 ∨ x = 1)
    (a b d : F) (hd : d ≠ 0) (S : Finset F)
    (hS : ∀ x ∈ S, d*σ x + a*x + b = 0) : S.card ≤ 2 := by
  classical
  by_contra! hcard
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp hcard
  have hzy : z-y ≠ 0 := sub_ne_zero.mpr hyz.symm
  have hszy : σ z-σ y ≠ 0 := sub_ne_zero.mpr (σ.injective.ne hyz.symm)
  have hfixed : σ ((x-y)/(z-y)) = (x-y)/(z-y) := by
    rw [map_div₀, map_sub, map_sub]
    apply (div_eq_div_iff hszy hzy).mpr
    apply mul_left_cancel₀ hd
    linear_combination (z-y) * (hS x hx) - (x-y) * (hS z hz) + (x-z) * (hS y hy)
  rcases hfix _ hfixed with h | h
  · exact (div_ne_zero (sub_ne_zero.mpr hxy) hzy) h
  · have he : x-y = z-y := by simpa only [one_mul] using (div_eq_iff hzy).mp h
    exact hxz (sub_left_inj.mp he)

/-- All nonzero linear combinations of the four semilinear monomials have
at most three roots. In geometric language they form a four-dimensional arc. -/
theorem four_term_root_bound (σ : F →+* F)
    (hfix : ∀ x : F, σ x = x → x = 0 ∨ x = 1)
    (a b c d : F) (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) (S : Finset F)
    (hS : ∀ x ∈ S, c*x*σ x + d*σ x + a*x + b = 0) : S.card ≤ 3 := by
  classical
  by_cases hc : c = 0
  · subst c
    by_cases hd : d = 0
    · subst d
      by_cases ha : a = 0
      · subst a
        have hb : b ≠ 0 := by simpa using hne
        have he : S = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          exact hb (by simpa using hS x hx)
        simp [he]
      · have hcard : S.card ≤ 1 := by
          apply Finset.card_le_one_iff.mpr
          intro x y hx hy
          apply mul_left_cancel₀ ha
          linear_combination hS x hx - hS y hy
        omega
    · have hcard := affine_root_bound σ hfix a b d hd S
        (fun x hx => by simpa using hS x hx)
      omega
  · apply shifted_root_bound σ hfix (a/c) (b/c) (d/c) S
    intro x hx
    apply mul_left_cancel₀ hc
    calc
      c * (x * σ x + (d/c)*σ x + (a/c)*x + b/c) =
          c*x*σ x + d*σ x + a*x + b := by field_simp
      _ = c*0 := by rw [hS x hx, mul_zero]

/-- The fixed-field hypothesis follows from the usual coprimality of Frobenius
exponent and binary extension degree. -/
theorem binary_frobenius_fixed [Fintype F] [CharP F 2]
    {k m : ℕ} (hcard : Fintype.card F = 2^k) (hcop : m.Coprime k)
    (x : F) (hx : iterateFrobenius F 2 m x = x) : x = 0 ∨ x = 1 := by
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  · right
    have hp : 1 ≤ 2^m := Nat.succ_le_of_lt (pow_pos (by decide) _)
    have hxpow : x ^ (2^m-1) = 1 := by
      apply mul_right_cancel₀ hx0
      rw [← pow_succ, Nat.sub_add_cancel hp, one_mul]
      exact hx
    have hxcard : x ^ (2^k-1) = 1 := by
      rw [← hcard]
      exact FiniteField.pow_card_sub_one_eq_one x hx0
    have hord : orderOf x ∣ Nat.gcd (2^m-1) (2^k-1) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hxpow) (orderOf_dvd_of_pow_eq_one hxcard)
    rw [Nat.pow_sub_one_gcd_pow_sub_one, hcop.gcd_eq_one] at hord
    norm_num at hord
    exact hord

/-- A finite-field root bound for Gold-type polynomials, uniform in the
Frobenius exponent. This is a root theorem, not yet an incidence construction. -/
theorem binary_polynomial_root_bound [Fintype F] [CharP F 2]
    {k m : ℕ} (hcard : Fintype.card F = 2^k) (hcop : m.Coprime k)
    (a b d : F) (S : Finset F)
    (hS : ∀ x ∈ S, x^(2^m+1) + d*x^(2^m) + a*x + b = 0) : S.card ≤ 3 := by
  apply shifted_root_bound (iterateFrobenius F 2 m)
    (binary_frobenius_fixed hcard hcop) a b d S
  intro x hx
  simpa only [iterateFrobenius_def, pow_succ, mul_comm] using hS x hx

/-- The full four-coefficient version over a finite binary field. -/
theorem binary_four_term_root_bound [Fintype F] [CharP F 2]
    {k m : ℕ} (hcard : Fintype.card F = 2^k) (hcop : m.Coprime k)
    (a b c d : F) (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) (S : Finset F)
    (hS : ∀ x ∈ S, c*x^(2^m+1) + d*x^(2^m) + a*x + b = 0) : S.card ≤ 3 := by
  apply four_term_root_bound (iterateFrobenius F 2 m)
    (binary_frobenius_fixed hcard hcop) a b c d hne S
  intro x hx
  simpa only [iterateFrobenius_def, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hS x hx

end Erdos714Semilinear

#print axioms Erdos714Semilinear.affine_root_bound
#print axioms Erdos714Semilinear.four_term_root_bound
#print axioms Erdos714Semilinear.binary_four_term_root_bound
#print axioms Erdos714Semilinear.ratio_fixed
#print axioms Erdos714Semilinear.root_bound
#print axioms Erdos714Semilinear.shifted_root_bound
#print axioms Erdos714Semilinear.binary_frobenius_fixed
#print axioms Erdos714Semilinear.binary_polynomial_root_bound
