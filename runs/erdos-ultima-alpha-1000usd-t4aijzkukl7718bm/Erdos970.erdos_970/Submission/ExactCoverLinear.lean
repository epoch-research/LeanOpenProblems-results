import Submission.DisjointCoverBound
import Submission.PrimeSetMertens

/-!
Exact prime-class covers have a uniform linear length bound. This is strictly
stronger than the earlier quadratic bound for exact covers, but does not apply
to the overlapping covers in Jacobsthal's problem.
-/
namespace Erdos970.DisjointCover
open Finset Real
open Erdos970.WeightedMertens

lemma hits_card_real_le (m p a : ℕ) (hp : 0 < p) :
    ((hits m p a).card : ℝ) ≤ (m : ℝ) / p + 1 := by
  have h := hits_card_le m p a
  have h' : ((hits m p a).card : ℝ) ≤ ((m - 1) / p : ℕ) + 1 := by
    exact_mod_cast h
  have hd : (((m - 1) / p : ℕ) : ℝ) ≤ (m : ℝ) / p := by
    apply (Nat.cast_div_le).trans
    exact div_le_div_of_nonneg_right (by exact_mod_cast (Nat.sub_le m 1)) (by positivity)
  linarith

lemma cover_length_real_le {P : Finset ℕ} {r : ℕ → ℕ} {m : ℕ}
    (h : ∀ i < m, ∃ p ∈ P, i ≡ r p [MOD p]) (hP : ∀ p ∈ P, p.Prime) :
    (m : ℝ) ≤ (m : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹) + P.card := by
  have hc : (m : ℝ) ≤ ∑ p ∈ P, ((hits m p (r p)).card : ℝ) := by
    exact_mod_cast cover_card_le_sum h
  calc
    _ ≤ _ := hc
    _ ≤ ∑ p ∈ P, ((m : ℝ) / p + 1) :=
      sum_le_sum (fun p hp => hits_card_real_le m p (r p) (hP p hp).pos)
    _ = _ := by simp [sum_add_distrib, div_eq_mul_inv, mul_sum]

lemma tail_power_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (x : ℝ) (hx : 12 ≤ x) (hlog : 12 * (boundConstant + 1) ≤ log x)
    (n : ℕ) (hn : 2 ≤ n) (hn4 : n ≤ 4) :
    (∑ p ∈ P.filter (fun p : ℕ => x ^ n < (p : ℝ)), (p : ℝ)⁻¹) ≤
      log (4 / (n : ℝ)) + 1 / 12 + (P.card : ℝ) / x ^ 4 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ha : 2 ≤ x ^ n := by
    have hh := pow_le_pow_right₀ hx1 hn
    have hx2 : 2 ≤ x ^ 2 := by nlinarith
    exact hx2.trans hh
  have hb : x ^ n ≤ x ^ 4 := pow_le_pow_right₀ hx1 hn4
  have ht := prime_set_tail P hP ha hb
  have he : log (log (x ^ 4)) - log (log (x ^ n)) = log (4 / (n : ℝ)) := by
    rw [← log_div (by rw [log_pow]; positivity) (by rw [log_pow]; positivity)]
    congr 1
    simp only [log_pow, Nat.cast_ofNat]
    field_simp
  have herr : 2 * (boundConstant + 1) / log (x ^ n) ≤ (1 : ℝ) / 12 := by
    rw [log_pow]
    apply (div_le_iff₀ (mul_pos hn0 hl)).mpr
    have hm := mul_le_mul_of_nonneg_right hnR hl.le
    nlinarith
  rw [he] at ht
  linarith

/-- A separated prime family has reciprocal mass bounded away from one, up to
its cardinality tail. The separation is supplied by exactness and CRT. -/
lemma separated_reciprocal_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (x : ℝ) (hx : 12 ≤ x) (hlog : 12 * (boundConstant + 1) ≤ log x)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → x ^ 4 < (p : ℝ) * q) :
    (∑ p ∈ P, (p : ℝ)⁻¹) ≤ 11 / 12 + (P.card : ℝ) / x ^ 4 := by
  classical
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  by_cases hne : P.Nonempty
  · let p := P.min' hne
    have hp : p ∈ P := P.min'_mem hne
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hsplit := sum_erase_add P (fun q : ℕ => (q : ℝ)⁻¹) hp
    by_cases hpx : (p : ℝ) ≤ x
    · have hsub : P.erase p ⊆ P.filter (fun q : ℕ => x ^ 3 < (q : ℝ)) := by
        intro q hq
        obtain ⟨hqp, hqP⟩ := mem_erase.mp hq
        refine mem_filter.mpr ⟨hqP, ?_⟩
        have hs := hsep p hp q hqP hqp.symm
        by_contra hbad
        have hqx : (q : ℝ) ≤ x ^ 3 := le_of_not_gt hbad
        have hm := mul_le_mul hpx hqx (by positivity : (0 : ℝ) ≤ q) hx0.le
        nlinarith
      have hsum : (∑ q ∈ P.erase p, (q : ℝ)⁻¹) ≤
          ∑ q ∈ P.filter (fun q : ℕ => x ^ 3 < (q : ℝ)), (q : ℝ)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      have ht := tail_power_bound P hP x hx hlog 3 (by omega) (by omega)
      have hlog43 : log (4 / (3 : ℝ)) ≤ 1 / 3 := by
        have hh := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
        linarith
      have hinv : (p : ℝ)⁻¹ ≤ (1 : ℝ) / 2 := by
        simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hp2
      norm_num only [Nat.cast_ofNat] at ht
      linarith
    · have hpx' : x < (p : ℝ) := lt_of_not_ge hpx
      have hsub : P.erase p ⊆ P.filter (fun q : ℕ => x ^ 2 < (q : ℝ)) := by
        intro q hq
        obtain ⟨hqp, hqP⟩ := mem_erase.mp hq
        refine mem_filter.mpr ⟨hqP, ?_⟩
        have hs := hsep p hp q hqP hqp.symm
        have hpq : (p : ℝ) ≤ q := by exact_mod_cast (P.min'_le q hqP)
        by_contra hbad
        have hqx : (q : ℝ) ≤ x ^ 2 := le_of_not_gt hbad
        have hm := mul_le_mul (hpq.trans hqx) hqx (by positivity : (0 : ℝ) ≤ q) (sq_nonneg x)
        nlinarith
      have hsum : (∑ q ∈ P.erase p, (q : ℝ)⁻¹) ≤
          ∑ q ∈ P.filter (fun q : ℕ => x ^ 2 < (q : ℝ)), (q : ℝ)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      have ht := tail_power_bound P hP x hx hlog 2 (by omega) (by omega)
      norm_num only [Nat.cast_ofNat, show (4 : ℝ) / 2 = 2 by norm_num] at ht
      have hlog2 : log 2 ≤ (3 : ℝ) / 4 := by linarith [log_two_lt_d9]
      have hinv : (p : ℝ)⁻¹ ≤ (1 : ℝ) / 12 := by
        simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 12) (hx.trans hpx'.le)
      linarith
  · have he : P = ∅ := not_nonempty_iff_eq_empty.mp hne
    norm_num [he]

lemma exact_cover_linear_of_root {P : Finset ℕ} {r : ℕ → ℕ} {m : ℕ}
    (h : ExactCover P r m) (hP : ∀ p ∈ P, p.Prime)
    (x : ℝ) (hx : 12 ≤ x) (hlog : 12 * (boundConstant + 1) ≤ log x)
    (hm : (m : ℝ) = x ^ 4) : (m : ℝ) ≤ 24 * P.card := by
  have hx0 : 0 < x := by linarith
  have hm0 : (0 : ℝ) < m := by rw [hm]; positivity
  have hs : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → x ^ 4 < (p : ℝ) * q := by
    intro p hp q hq hpq
    rw [← hm]
    exact_mod_cast product_gt_of_exact h hp hq (hP p hp).pos (hP q hq).pos
      ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq) hpq
  have hh := separated_reciprocal_bound P hP x hx hlog hs
  rw [← hm] at hh
  have hmultiply := mul_le_mul_of_nonneg_left hh hm0.le
  have hcancel : (m : ℝ) * ((11 : ℝ) / 12 + (P.card : ℝ) / m) =
      (11 : ℝ) / 12 * m + P.card := by
    rw [mul_add, mul_div_cancel₀ _ hm0.ne']
    ring
  rw [hcancel] at hmultiply
  have hc := cover_length_real_le h.1 hP
  linarith

/-- There is an absolute linear bound for exact prime-class covers. -/
theorem prime_exact_cover_linear :
    ∃ C > (0 : ℝ), ∀ (P : Finset ℕ) (r : ℕ → ℕ) (m : ℕ),
      (∀ p ∈ P, p.Prime) → ExactCover P r m → (m : ℝ) ≤ C * P.card := by
  have hroot : Filter.Tendsto (fun m : ℕ => sqrt (sqrt (m : ℝ))) Filter.atTop Filter.atTop :=
    tendsto_sqrt_atTop.comp (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hx : ∀ᶠ m : ℕ in Filter.atTop, 12 ≤ sqrt (sqrt (m : ℝ)) :=
    hroot.eventually (Filter.eventually_ge_atTop _)
  have hl : ∀ᶠ m : ℕ in Filter.atTop,
      12 * (boundConstant + 1) ≤ log (sqrt (sqrt (m : ℝ))) :=
    (tendsto_log_atTop.comp hroot).eventually (Filter.eventually_ge_atTop _)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (hx.and hl)
  refine ⟨(M : ℝ) + 24, by positivity, ?_⟩
  intro P r m hP h
  by_cases hmM : M ≤ m
  · have hmroot : (m : ℝ) = sqrt (sqrt (m : ℝ)) ^ 4 := by
      rw [show sqrt (sqrt (m : ℝ)) ^ 4 = (sqrt (sqrt (m : ℝ)) ^ 2) ^ 2 by ring,
        sq_sqrt (sqrt_nonneg _), sq_sqrt (by positivity)]
    have hc := exact_cover_linear_of_root h hP _ (hM m hmM).1 (hM m hmM).2 hmroot
    have hn : (0 : ℝ) ≤ (M : ℝ) * (P.card : ℝ) :=
      mul_nonneg (Nat.cast_nonneg M) (Nat.cast_nonneg P.card)
    nlinarith
  · by_cases hm : m = 0
    · simp [hm]; positivity
    · obtain ⟨p, hp, _⟩ := h.1 0 (by omega)
      have hk : (1 : ℝ) ≤ P.card := by exact_mod_cast (card_pos.mpr ⟨p, hp⟩)
      have hmm : (m : ℝ) ≤ M := by exact_mod_cast (show m ≤ M by omega)
      nlinarith

#print axioms prime_exact_cover_linear
end Erdos970.DisjointCover
