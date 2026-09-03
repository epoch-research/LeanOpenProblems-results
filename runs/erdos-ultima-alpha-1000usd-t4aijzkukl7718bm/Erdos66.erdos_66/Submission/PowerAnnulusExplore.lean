import Submission.RelativeCyclicFamilyExplore
import Submission.BinaryBlockTransferExplore
import Submission.PowerAnnulusGeometryExplore
import Submission.TranslateExplore

/-! Finite power-length logarithmic annuli. These are not a compatible
infinite construction and do not settle Erdos 66. -/
namespace Erdos66PowerAnnulus
open Filter AdditiveCombinatorics Erdos66RelativeCyclicFamily Erdos66BinaryBlockTransfer
  Erdos66RandomConstantProfile Erdos66ExponentialProfileParameters Erdos66PowerAnnulusGeometry
  Erdos66Translate Erdos66IntegerBlock
open scoped Topology Classical
set_option maxHeartbeats 1000000

lemma binary_support (M : ℕ) [NeZero M] (B : Finset (ZMod M)) (D : Set ℕ) (L : ℕ)
    (hD : ∀ n ∈ D, n ≤ L) : binaryBlocks M B D ⊆ Set.Iio ((L + 1) * M) := by
  intro n hn
  change (n : ZMod M) ∈ (if n / M ∈ D then B else ∅) at hn
  have hd : n / M ∈ D := by
    by_contra hh
    simp only [if_neg hh, Finset.notMem_empty] at hn
  have hq := hD _ hd
  have ht := Nat.mod_lt n (NeZero.pos M)
  have he := Nat.div_add_mod' n M
  change n < (L + 1) * M
  nlinarith

lemma normalize (c δ ε a r l₀ l : ℝ) (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 4 * c * δ < ε) (ha : a ≤ δ) (hl₀ : 0 < l₀)
    (hlo : l₀ ≤ l) (hhi : l ≤ (1 + a / 2) * l₀)
    (herr : |r - c * l₀| ≤ c * l₀ * (2 * δ + δ ^ 2)) :
    |r / l - c| < ε := by
  have hl : 0 < l := hl₀.trans_le hlo
  have hs : δ ^ 2 ≤ δ := by nlinarith
  have hE : c * l₀ * (2 * δ + δ ^ 2) ≤ 3 * c * δ * l₀ := by
    have hh := mul_le_mul_of_nonneg_left hs (mul_nonneg hc.le hl₀.le)
    nlinarith
  have herr' := abs_le.mp (herr.trans hE)
  have hd : c * (l - l₀) ≤ c * δ * l₀ := by
    have hh := mul_le_mul_of_nonneg_left hhi hc.le
    have hh' := mul_le_mul_of_nonneg_right ha (mul_nonneg hc.le hl₀.le)
    nlinarith [mul_pos (mul_pos hc hδ) hl₀]
  have hmul := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 4 * c * δ by positivity)
  have hstrict := mul_lt_mul_of_pos_right hε hl
  have hlr : (c - ε) * l < r := by nlinarith
  have hrl : r < (c + ε) * l := by
    have hcl := mul_le_mul_of_nonneg_left hlo hc.le
    nlinarith [mul_pos (mul_pos hc hδ) hl₀]
  have h₁ := (lt_div_iff₀ hl).mpr hlr
  have h₂ := (div_lt_iff₀ hl).mpr hrl
  rw [abs_lt]
  constructor <;> linarith

/-- For any positive coefficient and accuracy, one fixed positive power
increment works on arbitrarily late finite annuli. The approximating sets
also satisfy the upper bound at every integer target. -/
theorem exists_power_annulus (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N₀ : ℕ,
      ∃ N : ℕ, N₀ ≤ N ∧ 0 < N ∧ ∃ A : Set ℕ, A.Finite ∧ A ⊆ Set.Ici N₀ ∧
        (∀ n : ℕ, (sumRep A n : ℝ) / Real.log n < c + ε) ∧
        ∀ n : ℕ, N ≤ n → (n : ℝ) ≤ (N : ℝ) ^ (1 + δ) →
          |(sumRep A n : ℝ) / Real.log n - c| < ε := by
  let d : ℝ := min (ε / (16 * (c + 1))) (1 / 16)
  have hd : 0 < d := lt_min (by positivity) (by norm_num)
  have hdsmall : d ≤ 1 / 16 := min_le_right _ _
  have hd1 : d ≤ 1 := by linarith
  have hdε : d * (16 * (c + 1)) ≤ ε :=
    (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  have hcdε : 4 * c * d < ε := by nlinarith
  obtain ⟨β, hβ, hfamily⟩ := exists_relative_cyclic_family d hd 1
  let k : ℝ := min (d ^ 2 / 256) (d * β / c)
  have hk : 0 < k := lt_min (by positivity) (by positivity)
  have hkd : 256 * k ≤ d ^ 2 := by have hh := min_le_left (d ^ 2 / 256) (d * β / c); dsimp [k]; linarith
  let a : ℝ := k * c / β
  have ha : 0 < a := by dsimp [a]; positivity
  have had : a ≤ d := by
    have hh := (le_div_iff₀ hc).mp (min_le_right (d ^ 2 / 256) (d * β / c))
    apply (div_le_iff₀ hβ).mpr
    exact hh
  refine ⟨a / 8, by positivity, fun N₀ ↦ ?_⟩
  let μf : ℕ → ℝ := fun M ↦ c * Real.log M / β
  have hμtop : Tendsto μf atTop atTop := by
    exact ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc).atTop_div_const hβ
  obtain ⟨P, hP⟩ := eventually_atTop.mp
    (hμtop.eventually (eventually_parameters d k hd hk hkd))
  obtain ⟨M, hMP, hM, C, hC0, hCmono, hC⟩ := hfamily (max P (max N₀ 2))
  letI := hM
  have hM2 : 2 ≤ M := by omega
  have hM0 : 0 < M := by omega
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM0
  have hlogM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  let μ := μf M
  let q₀ := start μ d
  let L := cutoff μ k
  have hparam := hP M (by omega)
  obtain ⟨hμ, hμlarge, hq₀, hL, hsmall⟩ := hparam
  change 1 ≤ μ at hμ
  change 4 ≤ d * μ at hμlarge
  change (q₀ : ℝ) + 3 ≤ Real.exp (k * μ / 4) at hq₀
  change Real.exp (k * μ / 2) ≤ (L : ℝ) at hL
  change 2 * (2 * (L : ℝ) + 1) * Real.exp (-d ^ 2 * (μ + 1) / 128) < 1 at hsmall
  have htune : β * μ = c * Real.log M := by dsimp [μ, μf]; field_simp
  have hscale : k * μ = a * Real.log M := by dsimp [a, μ, μf]; ring
  obtain ⟨D, hDfin, hDsupport, hDupper, hDgood⟩ := exists_constant_profile μ d ⌈μ⌉₊ q₀ L
    hμ hd hd1 hμlarge (by linarith [Nat.le_ceil μ]) (start_condition μ d hd) hsmall
  let B := C 1
  have hB (z : ZMod M) : |(((B.filter (fun x ↦ z - x ∈ B)).card : ℝ) - β)| ≤ d * β := by
    simpa only [Nat.cast_one, mul_one, B] using hC 1 le_rfl 1 le_rfl z
  let A₀ := binaryBlocks M B D
  let A := shift A₀ M
  have hA₀supp : A₀ ⊆ Set.Iio ((L + 1) * M) := binary_support M B D L hDsupport
  have hA₀fin : A₀.Finite := (Set.finite_Iio _).subset hA₀supp
  have hupper (n : ℕ) : (sumRep A₀ n : ℝ) ≤ (β * μ) * (1 + d) ^ 2 := by
    have hBup (z : ZMod M) : ((B.filter (fun x ↦ z - x ∈ B)).card : ℝ) ≤ β * (1 + d) := by
      have hh := (abs_le.mp (hB z)).2
      nlinarith
    have hh := binary_block_upper M B D (β * (1 + d)) ((1 + d) * μ)
      (by positivity) (by positivity) hBup hDupper n
    change (sumRep A₀ n : ℝ) ≤ _ at hh
    convert hh using 1 <;> ring
  let N := M * (q₀ + 3)
  have hNM : M ≤ N := by dsimp [N]; nlinarith
  have hNpos : 0 < N := by omega
  refine ⟨N, by omega, hNpos, A, shift_finite hA₀fin M, ?_, ?_, ?_⟩
  · intro n hn
    have hh := shift_ge A₀ M hn
    change N₀ ≤ n
    omega
  · intro n
    by_cases hn : n < 2 * M
    · rw [show sumRep A n = 0 from sumRep_shift_zero A₀ hn, Nat.cast_zero, zero_div]
      positivity
    · have hn2 : 2 * M ≤ n := by omega
      have hnM : M ≤ n := by omega
      have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hlogle : Real.log M ≤ Real.log n := Real.log_le_log hMreal (by exact_mod_cast hnM)
      have hh := hupper (n - 2 * M)
      rw [htune] at hh
      have he : c * (1 + d) ^ 2 < c + ε := by
        have hs : d ^ 2 ≤ d := by nlinarith
        have hs' := mul_le_mul_of_nonneg_left hs hc.le
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hlogle (show 0 ≤ c * (1 + d) ^ 2 by positivity)
      have hstrict := mul_lt_mul_of_pos_right he hlogn
      rw [show sumRep A n = sumRep A₀ (n - 2 * M) from sumRep_shift_eq_sub A₀ hn2]
      apply (div_lt_iff₀ hlogn).mpr
      nlinarith
  · intro n hnlo hnhi
    have hgeom := geometry M q₀ L a hM2 ha.le (had.trans hd1)
      (by simpa only [← hscale] using hq₀) (by simpa only [← hscale] using hL) n hnlo hnhi
    obtain ⟨hnL, hloglo, hloghi⟩ := hgeom
    have hn2 : 2 * M ≤ n := by dsimp [N] at hnlo; nlinarith
    let q := (n - 2 * M) / M
    let t := (n - 2 * M) % M
    have ht : t < M := Nat.mod_lt _ hM0
    have hnt : q * M + t = n - 2 * M := Nat.div_add_mod' _ M
    have hsub : n - 2 * M + 2 * M = n := Nat.sub_add_cancel hn2
    have hqlo : q₀ + 1 ≤ q := by
      by_contra hh
      have hqle : q ≤ q₀ := by omega
      dsimp [N] at hnlo
      nlinarith
    have hqhi : q ≤ L := by
      by_contra hh
      have hqle : L + 1 ≤ q := by omega
      nlinarith
    have herr := binary_block_error M B D β μ d d hβ.le (by linarith) hd.le hd.le hB
      q t (by omega) ht (hDgood q (by omega) hqhi).le (hDgood (q - 1) (by omega) (by omega)).le
    have herr' : |(sumRep A n : ℝ) - c * Real.log M| ≤
        c * Real.log M * (2 * d + d ^ 2) := by
      rw [show sumRep A n = sumRep A₀ (n - 2 * M) from sumRep_shift_eq_sub A₀ hn2]
      change |(sumRep A₀ (q * M + t) : ℝ) - β * μ| ≤ _ at herr
      rw [hnt, htune] at herr
      convert herr using 1 <;> ring
    exact normalize c d ε a _ _ _ hc hd hd1 hcdε had hlogM hloglo hloghi herr'

end Erdos66PowerAnnulus
