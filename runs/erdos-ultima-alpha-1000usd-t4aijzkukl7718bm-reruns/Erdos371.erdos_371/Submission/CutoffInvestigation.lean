import FormalConjecturesUtil

/-! Density of periodic predicates, for investigating the cutoff approach to Erdős 371. -/

open Filter
open scoped Topology

namespace Erdos371Exploration

lemma periodic_count_blocks (p : ℕ → Prop) [DecidablePred p] {Q : ℕ}
    (hp : ∀ n, p (n + Q) ↔ p n) (r q : ℕ) :
    ((Finset.range (r + Q * q)).filter p).card =
      q * ((Finset.range Q).filter p).card + ((Finset.range r).filter p).card := by
  let f : ℕ → ℕ := fun n => if p n then 1 else 0
  have hf (n : ℕ) : f (Q + n) = f n := by simp [f, Nat.add_comm Q n, hp]
  have hcount (n : ℕ) : ((Finset.range n).filter p).card = ∑ x ∈ Finset.range n, f x := by
    simpa [f] using (Finset.sum_boole (R := ℕ) p (Finset.range n)).symm
  have hb (n : ℕ) : ((Finset.range (n + Q)).filter p).card =
      ((Finset.range n).filter p).card + ((Finset.range Q).filter p).card := by
    simp only [hcount]
    rw [Nat.add_comm n Q, Finset.sum_range_add]
    have he : (∑ x ∈ Finset.range n, f (Q + x)) = ∑ x ∈ Finset.range n, f x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hf x
    change (∑ x ∈ Finset.range Q, f x) + (∑ x ∈ Finset.range n, f (Q + x)) =
      (∑ x ∈ Finset.range n, f x) + (∑ x ∈ Finset.range Q, f x)
    rw [he, Nat.add_comm]
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, hb, ih, Nat.succ_mul]
      omega

lemma periodic_count_remainder (p : ℕ → Prop) [DecidablePred p] {Q : ℕ}
    (hp : ∀ n, p (n + Q) ↔ p n) (n : ℕ) :
    ((Finset.range n).filter p).card =
      (n / Q) * ((Finset.range Q).filter p).card +
        ((Finset.range (n % Q)).filter p).card := by
  have h := periodic_count_blocks p hp (n % Q) (n / Q)
  rwa [Nat.mod_add_div] at h

lemma partialDensity_eq_count (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    {n | p n}.partialDensity Set.univ n =
      (((Finset.range n).filter p).card : ℝ) / n := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  congr 2
  have he : {n | p n} ∩ Set.Iio n = ↑((Finset.range n).filter p) := by
    ext k
    simp [and_comm]
  rw [he, Set.ncard_coe_finset]

lemma periodic_half_density (p : ℕ → Prop) [DecidablePred p] {Q : ℕ} (hQ : 0 < Q)
    (hp : ∀ n, p (n + Q) ↔ p n)
    (hc : 2 * ((Finset.range Q).filter p).card = Q) :
    {n | p n}.HasDensity (1 / 2) := by
  let c := fun n => ((Finset.range n).filter p).card
  have hbound (n : ℕ) :
      (n : ℝ) - Q ≤ 2 * (c n : ℝ) ∧ 2 * (c n : ℝ) ≤ (n : ℝ) + Q := by
    have hform := periodic_count_remainder p hp n
    change c n = (n / Q) * c Q + c (n % Q) at hform
    have hrem : c (n % Q) ≤ n % Q := by
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    have hdiv := Nat.mod_add_div n Q
    have hrlt := Nat.mod_lt n hQ
    have hc' : 2 * c Q = Q := hc
    have ha : 2 * c n + Q ≥ n ∧ 2 * c n ≤ n + Q := by
      constructor <;> nlinarith
    constructor
    · have hr : (n : ℝ) ≤ 2 * (c n : ℝ) + Q := by exact_mod_cast ha.1
      linarith
    · exact_mod_cast ha.2
  have hlim : Tendsto (fun n : ℕ => (Q : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) - Q / n) atTop (𝓝 (1 / 2)) := by
    simpa using tendsto_const_nhds.sub hlim
  have hupp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) + Q / n) atTop (𝓝 (1 / 2)) := by
    simpa using tendsto_const_nhds.add hlim
  rw [Set.HasDensity]
  simp_rw [partialDensity_eq_count]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hb := (hbound n).1
    change (1 / 2 : ℝ) - Q / n ≤ (c n : ℝ) / n
    apply (le_div_iff₀ hn').mpr
    have he : ((1 / 2 : ℝ) - Q / n) * n = (n : ℝ) / 2 - Q := by
      field_simp
    rw [he]
    have hQ' : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
    linarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hb := (hbound n).2
    change (c n : ℝ) / n ≤ (1 / 2 : ℝ) + Q / n
    apply (div_le_iff₀ hn').mpr
    have he : ((1 / 2 : ℝ) + Q / n) * n = (n : ℝ) / 2 + Q := by
      field_simp
    rw [he]
    have hQ' : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
    linarith

end Erdos371Exploration


/-! Finite-cutoff symmetry for the largest-prime-factor comparison. -/

namespace Erdos371Exploration

/-- Keep just the prime divisors present in a fixed modulus. -/
def cut (Q n : ℕ) : ℕ := Nat.maxPrimeFac (Nat.gcd n Q)

lemma cut_periodic (Q n : ℕ) : cut Q (n + Q) = cut Q n := by
  simp [cut, Nat.gcd_add_self_left]

lemma cut_reflect (Q n : ℕ) (hn : n ≤ Q) : cut Q (Q - n) = cut Q n := by
  simp only [cut, Nat.gcd_self_sub_left hn]

lemma cut_consecutive_ne {Q : ℕ} (hQ : 0 < Q) (h2 : 2 ∣ Q) (n : ℕ) :
    cut Q (n + 1) ≠ cut Q n := by
  intro h
  have hd : cut Q (n + 1) ∣ n + 1 :=
    Nat.dvd_trans Nat.maxPrimeFac_dvd (Nat.gcd_dvd_left _ _)
  have hd' : cut Q (n + 1) ∣ n := by
    rw [h]
    exact Nat.dvd_trans Nat.maxPrimeFac_dvd (Nat.gcd_dvd_left _ _)
  have h1 : cut Q (n + 1) = 1 :=
    Nat.dvd_one.mp ((Nat.dvd_add_iff_right hd').mpr hd)
  have hp : 2 ∣ n ∨ 2 ∣ n + 1 := by
    simp only [Nat.dvd_iff_mod_eq_zero]
    omega
  rcases hp with hp | hp
  · have hh : 2 ≤ cut Q n :=
      Nat.le_maxPrimeFac (Nat.ne_of_gt (Nat.gcd_pos_of_pos_right n hQ))
        Nat.prime_two (Nat.dvd_gcd hp h2)
    omega
  · have hh : 2 ≤ cut Q (n + 1) :=
      Nat.le_maxPrimeFac (Nat.ne_of_gt (Nat.gcd_pos_of_pos_right (n + 1) hQ))
        Nat.prime_two (Nat.dvd_gcd hp h2)
    omega

lemma cut_reflect_comparison {Q : ℕ} (hQ : 0 < Q) (h2 : 2 ∣ Q)
    {n : ℕ} (hn : n < Q) :
    (cut Q (Q - 1 - n) < cut Q (Q - 1 - n + 1)) ↔
      ¬(cut Q n < cut Q (n + 1)) := by
  have hsub : Q - 1 - n = Q - (n + 1) := by omega
  have hadd : Q - 1 - n + 1 = Q - n := by omega
  rw [hadd, hsub, cut_reflect Q n (by omega),
    cut_reflect Q (n + 1) (by omega)]
  have hne := cut_consecutive_ne hQ h2 n
  omega

lemma cut_count_half_period {Q : ℕ} (hQ : 0 < Q) (h2 : 2 ∣ Q) :
    2 * ((Finset.range Q).filter (fun n => cut Q n < cut Q (n + 1))).card = Q := by
  let p := fun n => cut Q n < cut Q (n + 1)
  have hr {n : ℕ} (hn : n < Q) : p (Q - 1 - n) ↔ ¬p n :=
    cut_reflect_comparison hQ h2 hn
  have hh : ((Finset.range Q).filter p).card =
      ((Finset.range Q).filter (fun n => ¬p n)).card := by
    apply Finset.card_bij' (fun n _ => Q - 1 - n) (fun n _ => Q - 1 - n)
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
      constructor
      · omega
      · rw [hr hn.1]
        exact not_not.mpr hn.2
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
      exact ⟨by omega, (hr hn.1).mpr hn.2⟩
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      omega
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      omega
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.range Q) p
  simp only [Finset.card_range] at hc
  change 2 * ((Finset.range Q).filter p).card = Q
  omega

lemma factorial_cut_eventually_eq (n : ℕ) (hn : 0 < n) :
    ∀ k ≥ n, cut k.factorial n = Nat.maxPrimeFac n := by
  intro k hk
  rw [cut, Nat.gcd_eq_left_iff_dvd.mpr (Nat.dvd_factorial hn hk)]

end Erdos371Exploration


namespace Erdos371Exploration

lemma cut_hasDensity_half {Q : ℕ} (hQ : 0 < Q) (h2 : 2 ∣ Q) :
    {n | cut Q n < cut Q (n + 1)}.HasDensity (1 / 2) := by
  apply periodic_half_density _ hQ _ (cut_count_half_period hQ h2)
  intro n
  rw [show n + Q + 1 = (n + 1) + Q by omega, cut_periodic, cut_periodic]

lemma reflection_half_count (p : ℕ → Prop) [DecidablePred p] {Q : ℕ} (hQ : 0 < Q)
    (hr : ∀ n < Q, p (Q - 1 - n) ↔ ¬p n) :
    2 * ((Finset.range Q).filter p).card = Q := by
  have hh : ((Finset.range Q).filter p).card =
      ((Finset.range Q).filter (fun n => ¬p n)).card := by
    apply Finset.card_bij' (fun n _ => Q - 1 - n) (fun n _ => Q - 1 - n)
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
      constructor
      · omega
      · rw [hr n hn.1]
        exact not_not.mpr hn.2
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
      exact ⟨by omega, (hr n hn.1).mpr hn.2⟩
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      omega
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      omega
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.range Q) p
  simp only [Finset.card_range] at hc
  omega

lemma gcd_consecutive_ne {Q : ℕ} (hQ : 0 < Q) (h2 : 2 ∣ Q) (n : ℕ) :
    Nat.gcd (n + 1) Q ≠ Nat.gcd n Q := by
  intro h
  have hd : Nat.gcd (n + 1) Q ∣ n + 1 := Nat.gcd_dvd_left _ _
  have hd' : Nat.gcd (n + 1) Q ∣ n := by
    rw [h]
    exact Nat.gcd_dvd_left _ _
  have h1 : Nat.gcd (n + 1) Q = 1 :=
    Nat.dvd_one.mp ((Nat.dvd_add_iff_right hd').mpr hd)
  have hp : 2 ∣ n ∨ 2 ∣ n + 1 := by
    simp only [Nat.dvd_iff_mod_eq_zero]
    omega
  rcases hp with hp | hp
  · have hh : 2 ≤ Nat.gcd n Q :=
      Nat.le_of_dvd (Nat.gcd_pos_of_pos_right n hQ) (Nat.dvd_gcd hp h2)
    omega
  · have hh : 2 ≤ Nat.gcd (n + 1) Q :=
      Nat.le_of_dvd (Nat.gcd_pos_of_pos_right (n + 1) hQ) (Nat.dvd_gcd hp h2)
    omega

lemma gcd_hasDensity_half {Q : ℕ} (hQ : 0 < Q) (h2 : 2 ∣ Q) :
    {n | Nat.gcd n Q < Nat.gcd (n + 1) Q}.HasDensity (1 / 2) := by
  apply periodic_half_density _ hQ
  · intro n
    rw [show n + Q + 1 = (n + 1) + Q by omega,
      Nat.gcd_add_self_left, Nat.gcd_add_self_left]
  · apply reflection_half_count _ hQ
    intro n hn
    have hsub : Q - 1 - n = Q - (n + 1) := by omega
    have hadd : Q - 1 - n + 1 = Q - n := by omega
    rw [hadd, hsub, Nat.gcd_self_sub_left (show n ≤ Q by omega),
      Nat.gcd_self_sub_left (show n + 1 ≤ Q by omega)]
    have hne := gcd_consecutive_ne hQ h2 n
    omega

/-- A family of sets all of density one half. -/
def gcdApproximation (k : ℕ) : Set ℕ :=
    {n | Nat.gcd n (k + 2).factorial < Nat.gcd (n + 1) (k + 2).factorial}

lemma gcdApproximation_density (k : ℕ) : (gcdApproximation k).HasDensity (1 / 2) := by
  exact gcd_hasDensity_half (Nat.factorial_pos _) (Nat.dvd_factorial (by decide) (by omega))

/-- Nevertheless, membership is eventually true at every fixed positive integer. -/
lemma gcdApproximation_eventually_mem (n : ℕ) (hn : 0 < n) :
    ∀ᶠ k in atTop, n ∈ gcdApproximation k := by
  filter_upwards [eventually_ge_atTop n] with k hk
  change Nat.gcd n (k + 2).factorial < Nat.gcd (n + 1) (k + 2).factorial
  rw [Nat.gcd_eq_left_iff_dvd.mpr (Nat.dvd_factorial hn (by omega)),
    Nat.gcd_eq_left_iff_dvd.mpr (Nat.dvd_factorial (by omega) (by omega))]
  omega


lemma gcdApproximation_zero_not_mem (k : ℕ) : 0 ∉ gcdApproximation k := by
  change ¬Nat.gcd 0 (k + 2).factorial < Nat.gcd 1 (k + 2).factorial
  simp only [Nat.gcd_zero_left, Nat.gcd_one_left, not_lt]
  exact Nat.factorial_pos _

lemma gcdApproximation_eventually_mem_iff (n : ℕ) :
    (∀ᶠ k in atTop, n ∈ gcdApproximation k) ↔ 0 < n := by
  constructor
  · intro h
    by_contra hn
    have hn0 : n = 0 := by omega
    obtain ⟨k, hk⟩ := h.exists
    subst n
    exact gcdApproximation_zero_not_mem k hk
  · exact gcdApproximation_eventually_mem n

lemma density_compl {S : Set ℕ} {d : ℝ} (h : S.HasDensity d) :
    Sᶜ.HasDensity (1 - d) := by
  have hid (n : ℕ) (hn : n ≠ 0) :
      Sᶜ.partialDensity Set.univ n = 1 - S.partialDensity Set.univ n := by
    have hc : (S ∩ Set.Iio n).ncard + (Sᶜ ∩ Set.Iio n).ncard = n := by
      simpa [Set.diff_eq, Set.inter_comm] using
        Set.ncard_inter_add_ncard_diff_eq_ncard (Set.Iio n) S
    have hr : ((S ∩ Set.Iio n).ncard : ℝ) +
        ((Sᶜ ∩ Set.Iio n).ncard : ℝ) = n := by exact_mod_cast hc
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    apply (eq_sub_iff_add_eq).mpr
    rw [← add_div, add_comm, hr, div_self hn']
  apply Tendsto.congr' _ (tendsto_const_nhds.sub h)
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (hid n (Nat.ne_of_gt hn)).symm

lemma positive_hasDensity_one : {n : ℕ | 0 < n}.HasDensity 1 := by
  have h := density_compl (Nat.hasDensity_zero_of_finite (Set.finite_singleton 0))
  have he : ({0} : Set ℕ)ᶜ = {n | 0 < n} := by
    ext n
    simp
  simpa only [he, sub_zero] using h

/-- Pointwise eventual membership does not preserve natural density, even when
all approximating sets have density one half. This is not a disproof of Erdős 371. -/
lemma density_exchange_is_invalid :
    ¬(∀ (A : ℕ → Set ℕ) (S : Set ℕ),
      (∀ k, (A k).HasDensity (1 / 2)) →
      (∀ n, (∀ᶠ k in atTop, n ∈ A k) ↔ n ∈ S) →
      S.HasDensity (1 / 2)) := by
  intro h
  have hbad := h gcdApproximation {n : ℕ | 0 < n} gcdApproximation_density
    gcdApproximation_eventually_mem_iff
  have he := tendsto_nhds_unique hbad positive_hasDensity_one
  norm_num at he

end Erdos371Exploration
