import Submission.Work

/-!
Truncated inclusion–exclusion for uniform prime-residue covers.
This file develops finite upper-bound criteria; it does not assert the quadratic conjecture.
-/
open scoped Function

namespace Erdos970.BrunCriterion

noncomputable def truncSets (P : Finset ℕ) (t : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun Q => Q.card ≤ t)

noncomputable def truncDensity (P : Finset ℕ) (t : ℕ) : ℝ :=
  ∑ Q ∈ truncSets P t, (-1 : ℝ) ^ Q.card / (∏ p ∈ Q, (p : ℝ))

theorem signed_trunc_eq (P : Finset ℕ) (t : ℕ) :
    (∑ Q ∈ truncSets P t, (-1 : ℤ) ^ Q.card) =
      ∑ j ∈ Finset.range (t + 1), (-1 : ℤ) ^ j * P.card.choose j := by
  classical
  have hmap : ∀ Q ∈ truncSets P t, Q.card ∈ Finset.range (t + 1) := by
    intro Q hQ
    exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hQ).2; omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro j hj
  have heq : (truncSets P t).filter (fun Q => Q.card = j) = P.powersetCard j := by
    ext Q
    simp only [truncSets, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    have hjt := Finset.mem_range.mp hj
    constructor
    · rintro ⟨⟨hQP, hqt⟩, hcard⟩
      exact ⟨hQP, hcard⟩
    · rintro ⟨hQP, hcard⟩
      exact ⟨⟨hQP, by omega⟩, hcard⟩
  rw [heq, Finset.sum_powersetCard]
  simp [mul_comm]

theorem signed_trunc_nonpos {P : Finset ℕ} {t : ℕ}
    (hP : P.Nonempty) (ht : Odd t) : (∑ Q ∈ truncSets P t, (-1 : ℤ) ^ Q.card) ≤ 0 := by
  rw [signed_trunc_eq]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.mpr hP).ne'
  rw [hn, Int.alternating_sum_range_choose_eq_choose, ht.neg_one_pow]
  simp

/-- A covered interval makes every odd Bonferroni truncation nonpositive. -/
theorem cover_truncated_count_nonpos (P : Finset ℕ) (r : ℕ → ℕ) (m t : ℕ)
    (ht : Odd t) (hcover : ∀ i < m, ∃ p ∈ P, i ≡ r p [MOD p]) :
    (∑ Q ∈ truncSets P t, (-1 : ℤ) ^ Q.card *
      ((Finset.range m).filter (fun i => ∀ p ∈ Q, i ≡ r p [MOD p])).card) ≤ 0 := by
  classical
  have hpoint (i : ℕ) (hi : i ∈ Finset.range m) :
      (∑ Q ∈ truncSets P t, if (∀ p ∈ Q, i ≡ r p [MOD p]) then (-1 : ℤ) ^ Q.card else 0) ≤ 0 := by
    let B := P.filter (fun p => i ≡ r p [MOD p])
    have hB : B.Nonempty := by
      obtain ⟨p, hp, hip⟩ := hcover i (Finset.mem_range.mp hi)
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, hip⟩⟩
    have heq : (truncSets P t).filter (fun Q => ∀ p ∈ Q, i ≡ r p [MOD p]) = truncSets B t := by
      ext Q
      simp only [truncSets, Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff, B]
      aesop
    rw [← Finset.sum_filter, heq]
    exact signed_trunc_nonpos hB ht
  have heq (Q : Finset ℕ) :
      (-1 : ℤ) ^ Q.card * ((Finset.range m).filter (fun i => ∀ p ∈ Q, i ≡ r p [MOD p])).card =
        ∑ i ∈ Finset.range m, if (∀ p ∈ Q, i ≡ r p [MOD p]) then (-1 : ℤ) ^ Q.card else 0 := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  simp_rw [heq]
  rw [Finset.sum_comm]
  exact Finset.sum_nonpos hpoint

/-- Counting a single residue class differs from interval length divided by the modulus by at most one. -/
theorem residue_count_error (m d r : ℕ) (hd : 0 < d) :
    |(((Finset.range m).filter (fun i => i ≡ r [MOD d])).card : ℝ) - (m : ℝ) / d| ≤ 1 := by
  classical
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card m hd r]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdiv : ((m / d : ℕ) : ℝ) * d ≤ m := by exact_mod_cast Nat.div_mul_le_self m d
  have hdiv' : (m : ℝ) < (((m / d : ℕ) : ℝ) + 1) * d := by
    exact_mod_cast (show m < (m / d + 1) * d by simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ m hd)
  have hlo := (le_div_iff₀ hdR).mpr hdiv
  have hhi := (div_lt_iff₀ hdR).mpr hdiv'
  rw [abs_le]
  split_ifs <;> push_cast <;> constructor <;> linarith

/-- Intersections of prime classes are a single residue class modulo the prime product. -/
theorem intersection_residue (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (r : ℕ → ℕ) :
    ∃ b : ℕ, ∀ i : ℕ, (∀ p ∈ Q, i ≡ r p [MOD p]) ↔ i ≡ b [MOD ∏ p ∈ Q, p] := by
  classical
  have hco : Set.Pairwise (↑Q : Set ℕ) Nat.Coprime :=
    fun p hp q hq hpq => (Nat.coprime_primes (hQ p hp) (hQ q hq)).mpr hpq
  let b := Nat.chineseRemainderOfFinset r id Q (fun p hp => (hQ p hp).ne_zero) hco
  refine ⟨b.val, fun i => ?_⟩
  have hlist : Q.toList.Pairwise (Nat.Coprime on id) :=
    Q.nodup_toList.pairwise_of_forall_ne (by simpa using hco)
  have heq : i ≡ b.val [MOD ∏ p ∈ Q, p] ↔ ∀ p ∈ Q, i ≡ b.val [MOD p] := by
    simpa using (Nat.modEq_list_map_prod_iff (a := i) (b := b.val) hlist)
  rw [heq]
  constructor
  · intro hi p hp
    exact (hi p hp).trans (b.property p hp).symm
  · intro hi p hp
    exact (hi p hp).trans (b.property p hp)

theorem intersection_count_error (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (r : ℕ → ℕ) (m : ℕ) :
    |(((Finset.range m).filter (fun i => ∀ p ∈ Q, i ≡ r p [MOD p])).card : ℝ) -
      (m : ℝ) / (∏ p ∈ Q, (p : ℝ))| ≤ 1 := by
  classical
  obtain ⟨b, hb⟩ := intersection_residue Q hQ r
  simp_rw [hb]
  rw [← Nat.cast_prod]
  exact residue_count_error m _ b (Finset.prod_pos (fun p hp => (hQ p hp).pos))

/-- Every cover satisfies the truncated-sieve upper bound on its length. -/
theorem cover_density_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : ℕ → ℕ) (m t : ℕ)
    (ht : Odd t) (hcover : ∀ i < m, ∃ p ∈ P, i ≡ r p [MOD p]) :
    (m : ℝ) * truncDensity P t ≤ (truncSets P t).card := by
  classical
  let C (Q : Finset ℕ) := ((Finset.range m).filter (fun i => ∀ p ∈ Q, i ≡ r p [MOD p])).card
  have hsum : (∑ Q ∈ truncSets P t, (-1 : ℝ) ^ Q.card * C Q) ≤ 0 := by
    exact_mod_cast cover_truncated_count_nonpos P r m t ht hcover
  have hterm (Q : Finset ℕ) (hQ : Q ∈ truncSets P t) :
      (m : ℝ) * ((-1 : ℝ) ^ Q.card / (∏ p ∈ Q, (p : ℝ))) ≤
        (-1 : ℝ) ^ Q.card * C Q + 1 := by
    have hQP := Finset.mem_powerset.mp (Finset.mem_filter.mp hQ).1
    have hh := intersection_count_error Q (fun p hp => hP p (hQP hp)) r m
    change |(C Q : ℝ) - _| ≤ 1 at hh
    have hh' : |(-1 : ℝ) ^ Q.card * ((C Q : ℝ) - (m : ℝ) / (∏ p ∈ Q, (p : ℝ)))| ≤ 1 := by
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hh
    have hlo := (abs_le.mp hh').1
    simp only [div_eq_mul_inv] at hlo ⊢
    nlinarith only [hlo]
  calc
    (m : ℝ) * truncDensity P t = ∑ Q ∈ truncSets P t,
        (m : ℝ) * ((-1 : ℝ) ^ Q.card / (∏ p ∈ Q, (p : ℝ))) := Finset.mul_sum ..
    _ ≤ ∑ Q ∈ truncSets P t, ((-1 : ℝ) ^ Q.card * C Q + 1) := Finset.sum_le_sum hterm
    _ = (∑ Q ∈ truncSets P t, (-1 : ℝ) ^ Q.card * C Q) + (truncSets P t).card := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ _ := by linarith

/-- A simple polynomial bound on the number of retained subsets. -/
theorem truncSets_card_le (P : Finset ℕ) (t : ℕ) :
    (truncSets P t).card ≤ (P.card + 1) ^ t := by
  classical
  have heq : (truncSets P t).card = ∑ j ∈ Finset.range (t + 1), P.card.choose j := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := Finset.range (t + 1))
      (fun Q hQ => Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hQ).2; omega))]
    apply Finset.sum_congr rfl
    intro j hj
    have he : (truncSets P t).filter (fun Q => Q.card = j) = P.powersetCard j := by
      ext Q
      simp only [truncSets, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
      have hjt := Finset.mem_range.mp hj
      constructor
      · rintro ⟨⟨hQP, hqt⟩, hcard⟩
        exact ⟨hQP, hcard⟩
      · rintro ⟨hQP, hcard⟩
        exact ⟨⟨hQP, by omega⟩, hcard⟩
    rw [he, Finset.card_powersetCard]
  rw [heq, add_pow]
  apply Finset.sum_le_sum
  intro j hj
  have hjt : j ≤ t := by simpa using hj
  have hchoose : 1 ≤ t.choose j := Nat.choose_pos hjt
  simpa only [one_pow, mul_one] using
    (Nat.choose_le_pow P.card j).trans (Nat.le_mul_of_pos_right _ hchoose)

/-- The discarded tail is bounded by evaluating the subset generating function at `2`. -/
theorem trunc_value_lower (P : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p) (t : ℕ) :
    (∏ p ∈ P, (1 - w p)) - (∏ p ∈ P, (1 + 2 * w p)) / (2 : ℝ) ^ (t + 1) ≤
      ∑ Q ∈ truncSets P t, (-1 : ℝ) ^ Q.card * ∏ p ∈ Q, w p := by
  classical
  let A := truncSets P t
  let U := P.powerset
  let f (Q : Finset ℕ) := (-1 : ℝ) ^ Q.card * ∏ p ∈ Q, w p
  let v (Q : Finset ℕ) := ∏ p ∈ Q, 2 * w p
  have hAU : A ⊆ U := Finset.filter_subset _ _
  have hfull : (∏ p ∈ P, (1 - w p)) = ∑ Q ∈ U, f Q := by
    simpa only [Finset.prod_const_one, mul_one] using Finset.prod_sub (fun _ => (1 : ℝ)) w P
  have hgen : (∏ p ∈ P, (1 + 2 * w p)) = ∑ Q ∈ U, v Q := Finset.prod_one_add P
  have hnonneg (Q : Finset ℕ) (hQ : Q ∈ U) : 0 ≤ ∏ p ∈ Q, w p :=
    Finset.prod_nonneg (fun p hp => hw p (Finset.mem_powerset.mp hQ hp))
  have hvnonneg (Q : Finset ℕ) (hQ : Q ∈ U) : 0 ≤ v Q :=
    Finset.prod_nonneg (fun p hp => mul_nonneg (by norm_num) (hw p (Finset.mem_powerset.mp hQ hp)))
  have hterm (Q : Finset ℕ) (hQ : Q ∈ U \ A) : (2 : ℝ) ^ (t + 1) * f Q ≤ v Q := by
    obtain ⟨hQU, hQA⟩ := Finset.mem_sdiff.mp hQ
    have htQ : t + 1 ≤ Q.card := by
      have hnot : ¬Q.card ≤ t := fun hh => hQA (Finset.mem_filter.mpr ⟨hQU, hh⟩)
      omega
    have hsign : (-1 : ℝ) ^ Q.card ≤ 1 := by
      simpa only [abs_pow, abs_neg, abs_one, one_pow] using le_abs_self ((-1 : ℝ) ^ Q.card)
    have hf : f Q ≤ ∏ p ∈ Q, w p := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsign (hnonneg Q hQU)
    have hpow : (2 : ℝ) ^ (t + 1) ≤ 2 ^ Q.card := pow_le_pow_right₀ (by norm_num) htQ
    calc
      (2 : ℝ) ^ (t + 1) * f Q ≤ 2 ^ (t + 1) * (∏ p ∈ Q, w p) :=
        mul_le_mul_of_nonneg_left hf (by positivity)
      _ ≤ 2 ^ Q.card * (∏ p ∈ Q, w p) := mul_le_mul_of_nonneg_right hpow (hnonneg Q hQU)
      _ = v Q := by simp only [v, Finset.prod_mul_distrib, Finset.prod_const]
  have hsum : (2 : ℝ) ^ (t + 1) * (∑ Q ∈ U \ A, f Q) ≤ ∏ p ∈ P, (1 + 2 * w p) := by
    rw [Finset.mul_sum, hgen]
    exact (Finset.sum_le_sum hterm).trans
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun Q hQ _ => hvnonneg Q hQ))
  have htail := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (t + 1))).mpr
    (show (∑ Q ∈ U \ A, f Q) * 2 ^ (t + 1) ≤ ∏ p ∈ P, (1 + 2 * w p) by nlinarith only [hsum])
  have hsplit := Finset.sum_sdiff hAU (f := f)
  rw [hfull]
  change _ ≤ ∑ Q ∈ A, f Q
  linarith

/-- Distinct primes give elementary bounds for the density and its generating function. -/
theorem prime_product_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (1 / ((P.card : ℝ) + 1) ≤ ∏ p ∈ P, (1 - 1 / (p : ℝ))) ∧
    (∏ p ∈ P, (1 + 2 * (1 / (p : ℝ)))) ≤ ((P.card : ℝ) + 1) ^ 2 := by
  classical
  induction P using Finset.induction_on_max with
  | h0 => norm_num
  | @step p P hlt ih =>
    have hp : p.Prime := hP p (Finset.mem_insert_self _ _)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hpP : p ∉ P := fun hh => (hlt p hh).false
    have hsub : P ⊆ Finset.Ico 2 p := fun q hq => Finset.mem_Ico.mpr ⟨(hP' q hq).two_le, hlt q hq⟩
    have hcard : P.card + 2 ≤ p := by
      have hh := Finset.card_le_card hsub
      simp only [Nat.card_Ico] at hh
      have := hp.two_le
      omega
    have hpR : (P.card : ℝ) + 2 ≤ p := by exact_mod_cast hcard
    have hpRpos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hkpos : 0 < (P.card : ℝ) + 1 := by positivity
    have hkpos2 : 0 < (P.card : ℝ) + 2 := by positivity
    have hinv := one_div_le_one_div_of_le hkpos2 hpR
    have hinv' := one_div_le_one_div_of_le hkpos (show (P.card : ℝ) + 1 ≤ p by linarith)
    have hfac : 0 ≤ 1 - 1 / (p : ℝ) := by
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
      have hh := (div_le_one hpRpos).mpr hp1
      linarith
    obtain ⟨hden, hgen⟩ := ih hP'
    rw [Finset.card_insert_of_notMem hpP, Nat.cast_add, Nat.cast_one]
    simp only [Finset.prod_insert hpP]
    constructor
    · have heq : (1 - 1 / ((P.card : ℝ) + 2)) * (1 / ((P.card : ℝ) + 1)) =
          1 / ((P.card : ℝ) + 2) := by field_simp; ring
      have hh : 1 / ((P.card : ℝ) + 2) ≤
          (1 - 1 / (p : ℝ)) * (1 / ((P.card : ℝ) + 1)) := by
        rw [← heq]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      convert hh.trans (mul_le_mul_of_nonneg_left hden hfac) using 1 <;> congr 1 <;> ring
    · have heq : (1 + 2 * (1 / ((P.card : ℝ) + 1))) * ((P.card : ℝ) + 1) ^ 2 =
          ((P.card : ℝ) + 2) ^ 2 - 1 := by field_simp; ring
      calc
        _ ≤ (1 + 2 * (1 / (p : ℝ))) * ((P.card : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left hgen (by positivity)
        _ ≤ (1 + 2 * (1 / ((P.card : ℝ) + 1))) * ((P.card : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
        _ = ((P.card : ℝ) + 2) ^ 2 - 1 := heq
        _ ≤ _ := by nlinarith

/-- A fully explicit finite upper bound from an odd truncation of sufficiently high order. -/
theorem isJacobsthalBound_of_trunc_order (k t : ℕ) (ht : Odd t)
    (hpow : 2 * (k + 1) ^ 3 ≤ 2 ^ (t + 1)) :
    IsJacobsthalBound k (4 * (k + 1) ^ (t + 1)) := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hPk, r, hcover⟩ :=
    (not_isJacobsthalBound_iff_cover k (4 * (k + 1) ^ (t + 1))).mp hbad
  let K : ℝ := (k : ℝ) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hPkR : (P.card : ℝ) + 1 ≤ K := by
    dsimp only [K]
    exact_mod_cast Nat.add_le_add_right hPk 1
  obtain ⟨hden, hgen⟩ := prime_product_bounds P hP
  have hden' : 1 / K ≤ ∏ p ∈ P, (1 - 1 / (p : ℝ)) :=
    (one_div_le_one_div_of_le (by positivity) hPkR).trans hden
  have hgen' : (∏ p ∈ P, (1 + 2 * (1 / (p : ℝ)))) ≤ K ^ 2 :=
    hgen.trans (pow_le_pow_left₀ (by positivity) hPkR _)
  have hpowR : 2 * K ^ 3 ≤ (2 : ℝ) ^ (t + 1) := by
    dsimp only [K]
    exact_mod_cast hpow
  have herr : K ^ 2 / (2 : ℝ) ^ (t + 1) ≤ 1 / (2 * K) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [hpowR]
  have htail := trunc_value_lower P (fun p => 1 / (p : ℝ)) (fun p hp => by positivity) t
  have heq : (∑ Q ∈ truncSets P t, (-1 : ℝ) ^ Q.card * ∏ p ∈ Q, (1 / (p : ℝ))) =
      truncDensity P t := by
    simp only [truncDensity, div_eq_mul_inv, one_mul, Finset.prod_inv_distrib]
  rw [heq] at htail
  have hgen'' := (div_le_div_of_nonneg_right hgen' (by positivity : (0 : ℝ) ≤ 2 ^ (t + 1))).trans herr
  have hinv : 1 / K = 2 * (1 / (2 * K)) := by field_simp
  have hdensity : 1 / (2 * K) ≤ truncDensity P t := by linarith
  have hc := cover_density_le P hP r (4 * (k + 1) ^ (t + 1)) t ht hcover
  have hcardR : ((truncSets P t).card : ℝ) ≤ K ^ t := by
    have hh : (truncSets P t).card ≤ (k + 1) ^ t :=
      (truncSets_card_le P t).trans (Nat.pow_le_pow_left (Nat.add_le_add_right hPk 1) t)
    dsimp only [K]
    exact_mod_cast hh
  have hm : ((4 * (k + 1) ^ (t + 1) : ℕ) : ℝ) = 4 * K ^ (t + 1) := by
    dsimp only [K]
    push_cast
    rfl
  rw [hm] at hc
  have hl := mul_le_mul_of_nonneg_left hdensity (show 0 ≤ 4 * K ^ (t + 1) by positivity)
  have hcancel : 4 * K ^ (t + 1) * (1 / (2 * K)) = 2 * K ^ t := by
    rw [pow_succ]
    field_simp
    ring
  rw [hcancel] at hl
  have hpos : 0 < K ^ t := by positivity
  linarith

/-- A quasipolynomial uniform bound obtained by elementary truncated inclusion–exclusion. -/
theorem isJacobsthalBound_quasipolynomial (k : ℕ) :
    IsJacobsthalBound k (4 * (k + 1) ^ (4 * Nat.clog 2 (k + 1) + 2)) := by
  let L := Nat.clog 2 (k + 1)
  have hL : k + 1 ≤ 2 ^ L := Nat.le_pow_clog (by decide) (k + 1)
  have hodd : Odd (4 * L + 1) := ⟨2 * L, by omega⟩
  have hpow : 2 * (k + 1) ^ 3 ≤ 2 ^ ((4 * L + 1) + 1) := by
    calc
      2 * (k + 1) ^ 3 ≤ 2 * (2 ^ L) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL 3)
      _ = 2 ^ (3 * L + 1) := by
        rw [show 3 * L + 1 = L * 3 + 1 by omega, pow_add, pow_mul]
        ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  convert isJacobsthalBound_of_trunc_order k (4 * L + 1) hodd hpow using 1

theorem jacobsthalFunction_le_quasipolynomial (k : ℕ) :
    jacobsthalFunction k ≤ 4 * (k + 1) ^ (4 * Nat.clog 2 (k + 1) + 2) :=
  (jacobsthalFunction_le_iff k _).mpr (isJacobsthalBound_quasipolynomial k)

#print axioms cover_truncated_count_nonpos
#print axioms intersection_count_error
#print axioms cover_density_le
#print axioms trunc_value_lower
#print axioms isJacobsthalBound_of_trunc_order
#print axioms jacobsthalFunction_le_quasipolynomial
end Erdos970.BrunCriterion
