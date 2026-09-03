import FormalConjecturesUtil
import Submission.EuclideanCompression
import Submission.WeightedSmoothCount
import Submission.CofactorDensity
import Submission.BoundedPrimeGap

/-! Counting ascents that terminate at zero under the residue reduction.
This is not a density balance theorem for ascents and descents. -/

namespace Erdos371TerminalCompression

open Erdos371PrimeDiscrepancy Erdos371EuclideanCompression
open Erdos371WeightedSmoothCount Erdos371BoundedPrimeGap

noncomputable def H (N : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ)

lemma H_nonneg (N : ℕ) : 0 ≤ H N := by
  unfold H
  exact Finset.sum_nonneg (fun _ _ => by positivity)

lemma H_mono {N M : ℕ} (h : N ≤ M) : H N ≤ H M := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨hk1, hkN.trans h⟩
  · intro k hk hkn
    positivity

lemma H_le_log (N : ℕ) : H N ≤ 1 + Real.log N := by
  have he : H N = (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp [H, one_div]
  rw [he]
  exact harmonic_le_one_add_log N

def products (q N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N / q ^ 2)).biUnion fun u =>
    (Finset.Icc 1 (N / (q ^ 2 * u))).image fun v =>
      (1 + q * u) * (1 + q * v) - 1

lemma products_card_bound {q : ℕ} (hq : 0 < q) (N : ℕ) :
    ((products q N).card : ℝ) ≤ (N : ℝ) / (q : ℝ) ^ 2 * H N := by
  have hc : (products q N).card ≤
      ∑ u ∈ Finset.Icc 1 (N / q ^ 2), N / (q ^ 2 * u) := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro u hu
    simpa using (Finset.card_image_le (s := Finset.Icc 1 (N / (q ^ 2 * u)))
      (f := fun v => (1 + q * u) * (1 + q * v) - 1))
  calc
    _ ≤ ∑ u ∈ Finset.Icc 1 (N / q ^ 2), ((N / (q ^ 2 * u) : ℕ) : ℝ) := by
      exact_mod_cast hc
    _ ≤ ∑ u ∈ Finset.Icc 1 (N / q ^ 2), (N : ℝ) / ((q : ℝ) ^ 2 * u) := by
      apply Finset.sum_le_sum
      intro u hu
      have hd : ((N / (q ^ 2 * u) : ℕ) : ℝ) ≤ (N : ℝ) / ((q ^ 2 * u : ℕ) : ℝ) :=
        Nat.cast_div_le
      push_cast at hd
      exact hd
    _ = (N : ℝ) / (q : ℝ) ^ 2 * H (N / q ^ 2) := by
      rw [H, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (H_mono (Nat.div_le_self _ _)) (by positivity)

def terminalSet : Set ℕ := {n | 1 < n ∧ P n < P (n + 1) ∧ ascend n = 0}

lemma terminal_product {n : ℕ} (hn : n ∈ terminalSet) (hnprime : ¬(n + 1).Prime) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧
      n = (1 + P n * u) * (1 + P n * v) - 1 := by
  obtain ⟨hn1, hinc, hzero⟩ := hn
  obtain ⟨hc, hp⟩ := (ascent_terminal_iff hn1 hinc).mp hzero
  let a := (n + 1) / P (n + 1)
  have ha : a * P (n + 1) = n + 1 := Nat.div_mul_cancel Nat.maxPrimeFac_dvd
  have hq : (P n).Prime := Nat.prime_maxPrimeFac_of_one_lt n hn1
  have hpp : (P (n + 1)).Prime := Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)
  have hap : 0 < a := Nat.div_pos Nat.maxPrimeFac_le hpp.pos
  have ha1 : a ≠ 1 := by
    intro he
    have he' : P (n + 1) = n + 1 := by simpa [he] using ha
    exact hnprime (he' ▸ hpp)
  have he1 : 1 + P n * (a / P n) = a := by
    have he := Nat.mod_add_div a (P n)
    rw [show a % P n = 1 from hc] at he
    exact he
  have he2 : 1 + P n * (P (n + 1) / P n) = P (n + 1) := by
    have he := Nat.mod_add_div (P (n + 1)) (P n)
    rw [hp] at he
    exact he
  have hu : 0 < (a / P n : ℕ) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have he : a = 1 := by simpa [hz] using he1.symm
    exact ha1 he
  have hv : 0 < P (n + 1) / P n := Nat.div_pos hinc.le hq.pos
  refine ⟨a / P n, P (n + 1) / P n, hu, hv, ?_⟩
  rw [he1, he2, ha]
  omega

lemma mem_products {n N q u v : ℕ} (hq : 0 < q) (hu : 0 < u) (hv : 0 < v)
    (hnN : n < N) (he : n = (1 + q * u) * (1 + q * v) - 1) :
    n ∈ products q N := by
  have hmul : (1 + q * u) * (1 + q * v) = n + 1 := by
    have hh : 0 < (1 + q * u) * (1 + q * v) := by positivity
    omega
  have hbound : q ^ 2 * u * v ≤ N := by nlinarith
  have huN : u ≤ N / q ^ 2 := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < q ^ 2)).mpr
    have hh := Nat.le_mul_of_pos_right (q ^ 2 * u) hv
    nlinarith
  have hvN : v ≤ N / (q ^ 2 * u) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < q ^ 2 * u)).mpr
    nlinarith
  apply Finset.mem_biUnion.mpr
  refine ⟨u, Finset.mem_Icc.mpr ⟨hu, huN⟩, ?_⟩
  exact Finset.mem_image.mpr ⟨v, Finset.mem_Icc.mpr ⟨hv, hvN⟩, he.symm⟩

lemma sum_reciprocal_sq {K : ℕ} (hK : 0 < K) (B : ℕ) :
    (∑ q ∈ Finset.Ico K B, 1 / (q : ℝ)^2) ≤ 2 / (K : ℝ) := by
  have hh := reciprocal_sum_bound hK B 1
  have ht : (∑ q ∈ Finset.Ico K B, 1 / ((q : ℝ) * (q + 1))) ≤ 1 / (K : ℝ) := by
    by_cases hKB : K ≤ B
    · have he : (∑ q ∈ Finset.Ico K B, 1 / ((q : ℝ) * (q + 1))) =
          ∑ q ∈ Finset.Ico K B, ((-1 / (q + 1 : ℕ)) - (-1 / (q : ℝ))) := by
        apply Finset.sum_congr rfl
        intro q hq
        have hq0 : (q : ℝ) ≠ 0 := by
          have := (Finset.mem_Ico.mp hq).1
          exact_mod_cast (by omega : q ≠ 0)
        push_cast
        field_simp
        ring
      rw [he, Finset.sum_Ico_sub (fun q : ℕ => -1 / (q : ℝ)) hKB]
      have hb : 0 ≤ 1 / (B : ℝ) := by positivity
      simp only [neg_div]
      linarith
    · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty]
      positivity
  calc
    _ ≤ ∑ q ∈ Finset.Ico K B, 2 * (1 / ((q : ℝ) * (q + 1))) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq1 : (1 : ℝ) ≤ q := by
        have := (Finset.mem_Ico.mp hq).1
        exact_mod_cast (by omega : 1 ≤ q)
      rw [mul_one_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    _ = 2 * ∑ q ∈ Finset.Ico K B, 1 / ((q : ℝ) * (q + 1)) := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 / (K : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2)
      simpa only [mul_one_div] using hm

lemma product_cover_card {K : ℕ} (hK : 0 < K) (N : ℕ) :
    (((Finset.Ico K (N + 1)).biUnion (fun q => products q N)).card : ℝ) ≤
      2 * N * H N / K := by
  calc
    _ ≤ ∑ q ∈ Finset.Ico K (N + 1), ((products q N).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := Finset.Ico K (N + 1))
        (t := fun q => products q N))
    _ ≤ ∑ q ∈ Finset.Ico K (N + 1), (N : ℝ) / (q : ℝ)^2 * H N := by
      apply Finset.sum_le_sum
      intro q hq
      exact products_card_bound (by have := (Finset.mem_Ico.mp hq).1; omega) N
    _ = (N * H N) * ∑ q ∈ Finset.Ico K (N + 1), 1 / (q : ℝ)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ (N * H N) * (2 / (K : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_sq hK _) (mul_nonneg (Nat.cast_nonneg _) (H_nonneg _))
    _ = _ := by ring

lemma terminal_partialDensity_bound {K N : ℕ} (hK : 0 < K) (hN : 0 < N) :
    terminalSet.partialDensity Set.univ N ≤
      (1 + Real.sqrt N * Real.exp (2 * Real.sqrt K)) / N +
      (Nat.primeCounting N : ℝ) / N + 2 * H N / K := by
  let G := (Finset.range N).filter (fun n => 1 < n ∧ P n < P (n + 1) ∧ ascend n = 0)
  let L := (Finset.range N).filter (fun n => P n ≤ K)
  let F := (Finset.range N).filter (fun n => (n + 1).Prime)
  let C := (Finset.Ico K (N + 1)).biUnion (fun q => products q N)
  have hsub : G ⊆ (L ∪ F) ∪ C := by
    intro n hn
    obtain ⟨hnN, hterm⟩ := Finset.mem_filter.mp hn
    by_cases hlo : P n ≤ K
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnN, hlo⟩))
    by_cases hp : (n + 1).Prime
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnN, hp⟩))
    · apply Finset.mem_union_right
      obtain ⟨u, v, hu, hv, he⟩ := terminal_product hterm hp
      apply Finset.mem_biUnion.mpr
      refine ⟨P n, Finset.mem_Ico.mpr ⟨by omega, ?_⟩, ?_⟩
      · have hnlt := Finset.mem_range.mp hnN
        have hb : P n ≤ n := Nat.maxPrimeFac_le
        omega
      · exact mem_products (by omega) hu hv (Finset.mem_range.mp hnN) he
  have hc : G.card ≤ L.card + F.card + C.card := by
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hf : F.card ≤ Nat.primeCounting N := by
    rw [← show (N + 1).primesBelow.card = Nat.primeCounting N by
      rw [Nat.primesBelow_card_eq_primeCounting']; rfl]
    apply Finset.card_le_card_of_injOn (fun n => n + 1)
    · intro n hn
      simp only [Finset.mem_coe, F, Finset.mem_filter] at hn
      obtain ⟨hnN, hp⟩ := hn
      exact Nat.mem_primesBelow.mpr ⟨by
        change n + 1 < N + 1
        have := Finset.mem_range.mp hnN
        omega, hp⟩
    · intro n hn m hm he
      change n + 1 = m + 1 at he
      omega
  have hl : (L.card : ℝ) ≤ 1 + Real.sqrt N * Real.exp (2 * Real.sqrt K) :=
    smooth_count_exp_bound K N
  have hC : (C.card : ℝ) ≤ 2 * N * H N / K := product_cover_card hK N
  have hc' : (G.card : ℝ) ≤ L.card + F.card + C.card := by exact_mod_cast hc
  have hf' : (F.card : ℝ) ≤ Nat.primeCounting N := by exact_mod_cast hf
  have hg : terminalSet.partialDensity Set.univ N = (G.card : ℝ) / N :=
    partialDensity_filter _ N
  rw [hg]
  calc
    _ ≤ (1 + Real.sqrt N * Real.exp (2 * Real.sqrt K) + Nat.primeCounting N +
        2 * N * H N / K) / N := div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    _ = _ := by
      have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      have hk : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
      field_simp

lemma terminal_window_bound {N T : ℕ} (hN : 0 < N) (hT : 0 < T)
    (hlo : 8 * (T : ℝ) ≤ Real.log N) (hhi : Real.log N ≤ 8 * (T + 1 : ℝ)) :
    terminalSet.partialDensity Set.univ N ≤
      1 / (N : ℝ) + Real.exp (-2 * (T : ℝ)) + (Nat.primeCounting N : ℝ) / N +
      18 / (T : ℝ)^2 + 16 / (T : ℝ) := by
  have hb := terminal_partialDensity_bound (K := T ^ 2) (by positivity) hN
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  have hsK : Real.sqrt (T ^ 2 : ℕ) = T := by
    push_cast
    exact Real.sqrt_sq (Nat.cast_nonneg T)
  have hex : Real.exp (4 * (T : ℝ)) ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    calc
      (Real.exp (4 * (T : ℝ)))^2 = Real.exp (8 * (T : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ Real.exp (Real.log N) := Real.exp_le_exp.mpr hlo
      _ = N := Real.exp_log hn
  have hsmooth : (1 + Real.sqrt N * Real.exp (2 * Real.sqrt (T ^ 2 : ℕ))) / N ≤
      1 / (N : ℝ) + Real.exp (-2 * (T : ℝ)) := by
    rw [hsK, add_div]
    have he : Real.sqrt N * Real.exp (2 * (T : ℝ)) / N = Real.exp (2 * (T : ℝ)) / Real.sqrt N := by
      apply (div_eq_div_iff hn.ne' hsN.ne').mpr
      calc
        (Real.sqrt N * Real.exp (2 * (T : ℝ))) * Real.sqrt N =
            Real.exp (2 * (T : ℝ)) * (Real.sqrt N)^2 := by ring
        _ = _ := by rw [Real.sq_sqrt hn.le]
    rw [he]
    suffices hh : Real.exp (2 * (T : ℝ)) / Real.sqrt N ≤ Real.exp (-2 * (T : ℝ)) by linarith
    calc
      Real.exp (2 * (T : ℝ)) / Real.sqrt N ≤ Real.exp (2 * (T : ℝ)) / Real.exp (4 * (T : ℝ)) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hex
      _ = Real.exp (-2 * (T : ℝ)) := by
        rw [← Real.exp_sub]
        congr 1
        ring
  have hH : H N ≤ 9 + 8 * (T : ℝ) := by
    have hh := H_le_log N
    linarith
  have hratio : 2 * H N / (T ^ 2 : ℕ) ≤ 18 / (T : ℝ)^2 + 16 / (T : ℝ) := by
    calc
      _ ≤ 2 * (9 + 8 * (T : ℝ)) / (T ^ 2 : ℕ) :=
        div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      _ = _ := by
        push_cast
        field_simp
        ring
  linarith

open Filter
open scoped Topology

noncomputable def cutoff (N : ℕ) : ℕ := ⌊Real.log (N : ℝ) / 8⌋₊

lemma cutoff_tendsto_atTop : Tendsto cutoff atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    (((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
      (by norm_num : (0 : ℝ) < 8)))

lemma cutoff_window {N : ℕ} (hN : 0 < N) :
    8 * (cutoff N : ℝ) ≤ Real.log N ∧
    Real.log N ≤ 8 * (cutoff N + 1 : ℝ) := by
  have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlo := Nat.floor_le (show 0 ≤ Real.log (N : ℝ) / 8 by positivity)
  have hhi := Nat.lt_floor_add_one (Real.log (N : ℝ) / 8)
  change 8 * (⌊Real.log (N : ℝ) / 8⌋₊ : ℝ) ≤ _ ∧
    _ ≤ 8 * ((⌊Real.log (N : ℝ) / 8⌋₊ : ℝ) + 1)
  constructor <;> linarith

lemma terminalSet_hasDensity_zero : terminalSet.HasDensity 0 := by
  have ht : Tendsto (fun N : ℕ => (cutoff N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp cutoff_tendsto_atTop
  have hex : Tendsto (fun N : ℕ => Real.exp (-2 * (cutoff N : ℝ)))
      atTop (𝓝 0) := by
    simpa only [neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (ht.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hsq : Tendsto (fun N : ℕ => (18 : ℝ) / (cutoff N : ℝ)^2)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_pow] using
      ((tendsto_const_div_atTop_nhds_zero_nat (18 : ℝ)).comp
        ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp cutoff_tendsto_atTop))
  have hlin : Tendsto (fun N : ℕ => (16 : ℝ) / cutoff N) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (16 : ℝ)).comp cutoff_tendsto_atTop
  have hu : Tendsto (fun N : ℕ =>
      1 / (N : ℝ) + Real.exp (-2 * (cutoff N : ℝ)) +
      (Nat.primeCounting N : ℝ) / N +
      18 / (cutoff N : ℝ)^2 + 16 / (cutoff N : ℝ)) atTop (𝓝 0) := by
    simpa using (((tendsto_one_div_atTop_nhds_zero_nat.add hex).add
      Erdos371CofactorDensity.primeCounting_ratio_tendsto_zero).add hsq).add hlin
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall (fun N => by unfold Set.partialDensity; positivity)
  · filter_upwards [eventually_gt_atTop 0,
      cutoff_tendsto_atTop.eventually (eventually_gt_atTop 0)] with N hN hT
    exact terminal_window_bound hN hT (cutoff_window hN).1 (cutoff_window hN).2

end Erdos371TerminalCompression

#print axioms Erdos371TerminalCompression.terminalSet_hasDensity_zero

