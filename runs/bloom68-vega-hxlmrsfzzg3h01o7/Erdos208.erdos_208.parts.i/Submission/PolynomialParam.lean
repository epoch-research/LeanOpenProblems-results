import FormalConjecturesUtil

/-!
# Integer-polynomial parameter hits in a short interval

If `N = M * P^2` has distinct values at a finite set of integer parameters,
all values lie in `(x, x + H]`, and `H < P.eval t` at every parameter, then
the number of parameters is at most `3 * N.natDegree + 1`.

The proof uses divisibility of the derivative, the mean value theorem, the
intermediate value theorem, and the degree bound for polynomial roots.
No primality, coefficient-height bound, or positivity of `M` is needed.
This is a structural counting lemma, not a squarefree-gap theorem.
-/

namespace PolynomialParam

open Polynomial

/-- The square factor forces the corresponding factor in every derivative value. -/
theorem eval_dvd_derivative_mul_sq (M P : Polynomial ℤ) (t : ℤ) :
    P.eval t ∣ (M * P ^ 2).derivative.eval t := by
  refine ⟨M.derivative.eval t * P.eval t + 2 * M.eval t * P.derivative.eval t, ?_⟩
  simp only [derivative_mul, derivative_sq, eval_add, eval_mul, eval_pow, eval_C]
  ring

/-- A derivative larger than the value-window width must cross one of the two
thresholds before the next parameter, provided the parameters are at least one apart. -/
theorem exists_derivative_threshold_between (F : Polynomial ℝ) {a b H : ℝ}
    (hH : 0 < H) (hsep : 1 ≤ b - a)
    (hvalues : |F.eval b - F.eval a| < H)
    (hderiv : H < |F.derivative.eval a|) :
    ∃ c ∈ Set.Ioo a b, F.derivative.eval c = H ∨ F.derivative.eval c = -H := by
  have hpos : 0 < b - a := lt_of_lt_of_le zero_lt_one hsep
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope
    (fun t => F.eval t) (fun t => F.derivative.eval t) (sub_pos.mp hpos)
    F.continuous.continuousOn (fun t _ => F.hasDerivAt t)
  have hsmall : |F.derivative.eval c| < H := by
    rw [hcd, abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
    exact hvalues.trans_le (le_mul_of_one_le_right hH.le hsep)
  rcases lt_abs.mp hderiv with hlarge | hlarge
  · obtain ⟨r, hr, heq⟩ := intermediate_value_Ioo' hc.1.le
      F.derivative.continuous.continuousOn
      (show H ∈ Set.Ioo (F.derivative.eval c) (F.derivative.eval a) from
        ⟨(abs_lt.mp hsmall).2, hlarge⟩)
    exact ⟨r, ⟨hr.1, hr.2.trans hc.2⟩, Or.inl heq⟩
  · obtain ⟨r, hr, heq⟩ := intermediate_value_Ioo hc.1.le
      F.derivative.continuous.continuousOn
      (show -H ∈ Set.Ioo (F.derivative.eval a) (F.derivative.eval c) from
        ⟨by linarith, (abs_lt.mp hsmall).1⟩)
    exact ⟨r, ⟨hr.1, hr.2.trans hc.2⟩, Or.inr heq⟩

/-- A one-separated finite set of real parameters with large derivatives has
at most twice the derivative degree, plus one, hits in a window of width `H`. -/
theorem card_le_of_large_derivative (F : Polynomial ℝ) (S : Finset ℝ) (x H : ℝ)
    (hH : 0 < H)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a < b → 1 ≤ b - a)
    (hvalues : ∀ t ∈ S, x < F.eval t ∧ F.eval t ≤ x + H)
    (hderiv : ∀ t ∈ S, H < |F.derivative.eval t|) :
    S.card ≤ 2 * F.derivative.natDegree + 1 := by
  classical
  obtain hS | hS := S.eq_empty_or_nonempty
  · simp [hS]
  obtain ⟨t₀, ht₀⟩ := hS
  have hshift (v : ℝ) (hv : |v| = H) : F.derivative - C v ≠ 0 := by
    intro hz
    have heval := congrArg (fun Q : Polynomial ℝ => Q.eval t₀) hz
    have heq : F.derivative.eval t₀ = v := by
      simpa only [eval_sub, eval_C, eval_zero, sub_eq_zero] using heval
    have hlt := hderiv t₀ ht₀
    rw [heq, hv] at hlt
    exact (lt_irrefl H) hlt
  have hplus : F.derivative - C H ≠ 0 := hshift H (abs_of_pos hH)
  have hminus : F.derivative - C (-H) ≠ 0 :=
    hshift (-H) (by rw [abs_neg, abs_of_pos hH])
  let R : Finset ℝ := (F.derivative - C H).roots.toFinset ∪
    (F.derivative - C (-H)).roots.toFinset
  have hcount : S.card ≤ R.card + 1 := by
    apply Finset.card_le_of_interleaved
    intro a ha b hb hab _
    have hwindow : |F.eval b - F.eval a| < H := by
      obtain ⟨ha₁, ha₂⟩ := hvalues a ha
      obtain ⟨hb₁, hb₂⟩ := hvalues b hb
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    obtain ⟨c, hc, heq⟩ := exists_derivative_threshold_between F hH
      (hsep a ha b hb hab) hwindow (hderiv a ha)
    refine ⟨c, ?_, hc⟩
    apply Finset.mem_union.mpr
    rcases heq with heq | heq
    · apply Or.inl
      apply Multiset.mem_toFinset.mpr
      apply (mem_roots hplus).mpr
      simp only [IsRoot.def, eval_sub, eval_C, heq, sub_self]
    · apply Or.inr
      apply Multiset.mem_toFinset.mpr
      apply (mem_roots hminus).mpr
      simp only [IsRoot.def, eval_sub, eval_C, heq, sub_self]
  have hroot_count (v : ℝ) :
      (F.derivative - C v).roots.toFinset.card ≤ F.derivative.natDegree := by
    calc
      _ ≤ (F.derivative - C v).roots.card := Multiset.toFinset_card_le _
      _ ≤ (F.derivative - C v).natDegree := card_roots' _
      _ = F.derivative.natDegree := natDegree_sub_C
  have hR : R.card ≤ 2 * F.derivative.natDegree := by
    have hu := Finset.card_union_le (F.derivative - C H).roots.toFinset
      (F.derivative - C (-H)).roots.toFinset
    have hp := hroot_count H
    have hm := hroot_count (-H)
    dsimp [R]
    omega
  omega

/-- Integer-polynomial hits are controlled by the derivative degree when every
nonzero derivative value at a hit has absolute value greater than `H`.
Injectivity is only needed to handle the identically zero derivative. -/
theorem card_le_of_derivative_gap (N : Polynomial ℤ) (S : Finset ℤ) (x H : ℤ)
    (hH : 0 < H) (hinj : Set.InjOn (fun t => N.eval t) (S : Set ℤ))
    (hvalues : ∀ t ∈ S, x < N.eval t ∧ N.eval t ≤ x + H)
    (hderiv : ∀ t ∈ S, N.derivative.eval t ≠ 0 → H < |N.derivative.eval t|) :
    S.card ≤ 3 * N.derivative.natDegree + 1 := by
  classical
  by_cases hzero : N.derivative = 0
  · have hconst := eq_C_of_derivative_eq_zero hzero
    have hcard : S.card ≤ 1 := Finset.card_le_one.mpr (by
      intro a ha b hb
      apply hinj ha hb
      rw [hconst]
      simp only [eval_C])
    omega
  have hcritical :
      (S.filter (fun t => N.derivative.eval t = 0)).card ≤ N.derivative.natDegree := by
    apply card_le_degree_of_subset_roots
    intro t ht
    exact (mem_roots hzero).mpr (Finset.mem_filter.mp ht).2
  let T : Finset ℤ := S.filter (fun t => N.derivative.eval t ≠ 0)
  let A : Finset ℝ := T.image (fun t : ℤ => (t : ℝ))
  let F : Polynomial ℝ := N.map (Int.castRingHom ℝ)
  have hFeval (t : ℤ) : F.eval (t : ℝ) = (↑(N.eval t) : ℝ) := by
    exact eval_map_apply (p := N) (Int.castRingHom ℝ) t
  have hFderiv (t : ℤ) : F.derivative.eval (t : ℝ) = (↑(N.derivative.eval t) : ℝ) := by
    dsimp [F]
    rw [derivative_map]
    exact eval_map_apply (p := N.derivative) (Int.castRingHom ℝ) t
  have hreal : A.card ≤ 2 * F.derivative.natDegree + 1 := by
    apply card_le_of_large_derivative F A (x : ℝ) (H : ℝ) (by exact_mod_cast hH)
    · intro a ha b hb hab
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hb
      have hst : s < t := by exact_mod_cast hab
      have hsep : (1 : ℤ) ≤ t - s := by omega
      exact_mod_cast hsep
    · intro a ha
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
      rw [hFeval]
      obtain ⟨hlo, hhi⟩ := hvalues t (Finset.mem_filter.mp ht).1
      constructor
      · exact_mod_cast hlo
      · exact_mod_cast hhi
    · intro a ha
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
      rw [hFderiv]
      exact_mod_cast hderiv t (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2
  have hAcard : A.card = T.card := Finset.card_image_of_injective T Int.cast_injective
  have hdegree : F.derivative.natDegree ≤ N.derivative.natDegree := by
    dsimp [F]
    rw [derivative_map]
    exact natDegree_map_le
  have hpartition := Finset.card_filter_add_card_filter_not (s := S)
    (fun t => N.derivative.eval t = 0)
  change (S.filter (fun t => N.derivative.eval t = 0)).card + T.card = S.card at hpartition
  omega

/-- Degree-only bound for integer-polynomial parameter hits with a large square
factor. No primality, coefficient-height, or sign hypothesis on `M` is required. -/
theorem card_parameter_hits_le (M P N : Polynomial ℤ) (S : Finset ℤ) (x H : ℤ)
    (hN : N = M * P ^ 2) (hH : 0 < H)
    (hinj : Set.InjOn (fun t => N.eval t) (S : Set ℤ))
    (hvalues : ∀ t ∈ S, x < N.eval t ∧ N.eval t ≤ x + H)
    (hP : ∀ t ∈ S, H < P.eval t) :
    S.card ≤ 3 * N.natDegree + 1 := by
  have hcount : S.card ≤ 3 * N.derivative.natDegree + 1 := by
    apply card_le_of_derivative_gap N S x H hH hinj hvalues
    intro t ht hne
    have hdiv : P.eval t ∣ N.derivative.eval t := by
      rw [hN]
      exact eval_dvd_derivative_mul_sq M P t
    exact (hP t ht).trans_le
      (Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdiv))
  have hdegree := natDegree_derivative_le N
  omega

end PolynomialParam
