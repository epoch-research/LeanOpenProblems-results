import Submission.FiniteTaperExplore
import Submission.LogTuningExplore

/-! Finite integer sets with logarithmic representation counts on arbitrarily
large intervals of any prescribed fixed multiplicative length. This is not
an infinite-set existence theorem: the approximating sets need not agree. -/
namespace Erdos66Annulus
set_option maxHeartbeats 1000000
open Filter AdditiveCombinatorics Erdos66ConstantProfile Erdos66FiniteTaper
  Erdos66LogTuning
open scoped Topology

/-- A finite-annulus approximation, with coefficient exactly one. -/
theorem exists_logarithmic_annulus (ε : ℝ) (hε : 0 < ε) (R N₀ : ℕ) (hR : 1 ≤ R) :
    ∃ N : ℕ, N₀ ≤ N ∧ 0 < N ∧ ∃ A : Set ℕ, A.Finite ∧
      ∀ n : ℕ, N ≤ n → n ≤ R * N → |(sumRep A n : ℝ) / Real.log n - 1| < ε := by
  let δ : ℝ := min (ε / 8) (1 / 8)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ ≤ ε / 8 := min_le_left _ _
  have hδsmall : δ ≤ 1 / 8 := min_le_right _ _
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp (b_tendsto_zero.eventually_lt_const (half_pos hδ))
  let q₀ := max Q 1
  have hq₀ : 1 ≤ q₀ := le_max_right _ _
  have hbq₀ : b q₀ < δ / 2 := hQ _ (le_max_left _ _)
  let L := R * q₀
  have hL : q₀ ≤ L := by dsimp [L]; nlinarith
  obtain ⟨T, hTbig⟩ := exists_nat_gt (max (1 : ℝ) (max (1 / b L) (64 * (L + 2) / δ)))
  have hTreal : (1 : ℝ) < T := lt_of_le_of_lt (le_max_left _ _) hTbig
  have hT : 1 ≤ T := by exact_mod_cast hTreal.le
  have hTb : 1 / b L < (T : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hTbig
  have hTδ : 64 * ((L : ℝ) + 2) < δ * T := by
    have hh : 64 * ((L : ℝ) + 2) / δ < T :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hTbig
    have hx := (div_lt_iff₀ hδ).mp hh
    linarith
  have hlevels : 1 ≤ (T : ℝ) ^ 2 * b L := by
    have hbL := b_pos L
    have hh := (div_lt_iff₀ hbL).mp hTb
    have hsq : (T : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hsq hbL.le
    linarith
  let d : ℝ := 2 * (T : ℝ) ^ 4
  have hd : 0 < d := by dsimp [d]; positivity
  have hev : ∀ᶠ p : ℕ in atTop,
      T ≤ thickness d p ∧ ∀ n : ℕ,
        (p * thickness d p) ^ 2 ≤ n → n ≤ (L + 1) * (p * thickness d p) ^ 2 →
        |(2 * d) * (thickness d p : ℝ) ^ 2 / Real.log n - 1| < δ :=
    ((thickness_atTop hd).eventually (eventually_ge_atTop T)).and (tuned_mean_uniform hd L hδ)
  obtain ⟨P, hP⟩ := eventually_atTop.mp hev
  obtain ⟨p, hp, hpN, hblocks⟩ := exists_tapered_integer_blocks T L (max P (max N₀ 2)) hlevels
  have hpP : P ≤ p := by omega
  have hp2 : 2 ≤ p := by omega
  let K := thickness d p
  have hTK : T ≤ K := (hP p hpP).1
  have hK : 0 < K := by omega
  obtain ⟨A, hAfinite, hA⟩ := hblocks K hK
  let M := (p * K) ^ 2
  let μ : ℝ := 4 * (K : ℝ) ^ 2 * (T : ℝ) ^ 4
  have hK1 : 1 ≤ K := by omega
  have hpK : p ≤ p * K := by nlinarith
  have hMp : p ≤ M := by dsimp [M]; nlinarith
  have hM : 1 < M := by omega
  have hNM : M ≤ q₀ * M := by nlinarith
  refine ⟨q₀ * M, by omega, by omega, A, hAfinite, ?_⟩
  intro n hnlo hnhi
  have hnM : M ≤ n := by omega
  have hnLM : n ≤ L * M := by
    dsimp [L]
    nlinarith
  have hnU : n ≤ (L + 1) * M := by nlinarith
  let q := n / M
  let t := n % M
  have ht : t < M := Nat.mod_lt n (by omega)
  have hnt : q * M + t = n := Nat.div_add_mod' n M
  have hqq₀ : q₀ ≤ q := by
    by_contra hh
    have hh' : q + 1 ≤ q₀ := by omega
    nlinarith
  have hqL : q ≤ L := by
    by_contra hh
    have hh' : L + 1 ≤ q := by omega
    nlinarith
  have hq : 0 < q := by omega
  have hbq : b q < δ / 2 := lt_of_le_of_lt (b_antitone hqq₀) hbq₀
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have herr := (hA q hq hqL t ht).trans (taper_error_bound T K q L hT hTK hqL)
  have hround : 128 * (K : ℝ) ^ 2 * (T : ℝ) ^ 3 * (L + 2) < (δ / 2) * μ := by
    have hpos : 0 < 2 * (K : ℝ) ^ 2 * (T : ℝ) ^ 3 := by positivity
    have hh := mul_lt_mul_of_pos_left hTδ hpos
    dsimp [μ]
    nlinarith
  have hendpoint : μ * b q < μ * (δ / 2) := mul_lt_mul_of_pos_left hbq hμ
  have herr' : |(sumRep A n : ℝ) - μ| < δ * μ := by
    change |(sumRep A (q * M + t) : ℝ) - μ| ≤ μ * b q +
      128 * (K : ℝ) ^ 2 * (T : ℝ) ^ 3 * (L + 2) at herr
    rw [hnt] at herr
    nlinarith
  have htune : |μ / Real.log n - 1| < δ := by
    have hh := (hP p hpP).2 n hnM hnU
    dsimp only [μ, d, K]
    convert hh using 2 <;> ring
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hdiv : |(sumRep A n : ℝ) / Real.log n - μ / Real.log n| < δ * (μ / Real.log n) := by
    rw [← sub_div, abs_div, abs_of_pos hlog]
    have hh := div_lt_div_of_pos_right herr' hlog
    simpa only [mul_div_assoc] using hh
  have hratio : μ / Real.log n < 1 + δ := by
    have hh := (abs_lt.mp htune).2
    linarith
  calc
    |(sumRep A n : ℝ) / Real.log n - 1| =
        |((sumRep A n : ℝ) / Real.log n - μ / Real.log n) + (μ / Real.log n - 1)| := by congr 1; ring
    _ ≤ |(sumRep A n : ℝ) / Real.log n - μ / Real.log n| + |μ / Real.log n - 1| := abs_add_le _ _
    _ < δ * (μ / Real.log n) + δ := add_lt_add hdiv htune
    _ ≤ δ * (1 + δ) + δ := by nlinarith
    _ < ε := by nlinarith [mul_le_mul_of_nonneg_left hδsmall hδ.le]

end Erdos66Annulus
