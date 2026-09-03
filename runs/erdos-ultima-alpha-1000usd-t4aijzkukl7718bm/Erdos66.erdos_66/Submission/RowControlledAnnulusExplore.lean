import Submission.ShiftedUpperAnnulusExplore
import Submission.ShiftedFiniteRowsExplore

/-! Upper-bounded accurate annuli with a row bound sufficiently small for
uniform extension of every old prefix shorter than one row. -/
namespace Erdos66RowControlledAnnulus
open Filter AdditiveCombinatorics Erdos66LogTuning Erdos66ConstantProfile Erdos66FiniteTaper
  Erdos66ShiftedProfile Erdos66ShiftedBlock Erdos66ShiftedFinite Erdos66Translate
  Erdos66ShiftedUpperAnnulus Erdos66ShiftedFiniteRows Erdos66RowSparsePrefix Erdos66RowSparseShift
open scoped Topology Classical
set_option maxHeartbeats 1800000

/-- Uniformly upper-bounded finite approximations, supported arbitrarily far
out, with an arbitrarily long multiplicative interval of two-sided accuracy. -/
theorem exists_row_controlled_annulus (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε)
    (R N₀ : ℕ) (hR : 1 ≤ R) :
    ∃ N : ℕ, N₀ ≤ N ∧ 0 < N ∧ ∃ b H : ℕ, 2 ≤ b ∧ N₀ ≤ b ∧ b^2 ≤ N ∧
      ∃ A : Set ℕ, A.Finite ∧ A ⊆ Set.Ici (b^2) ∧ RowSparse A b H ∧
      4*(H : ℝ)/Real.log ((b^2 : ℕ) : ℝ) < ε ∧
      (∀ n : ℕ, (sumRep A n : ℝ) / Real.log n < c + ε) ∧
      ∀ n : ℕ, N ≤ n → n ≤ R * N → |(sumRep A n : ℝ) / Real.log n - c| < ε := by
  let δ : ℝ := min (ε / (8 * (c + 1))) (1 / 8)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ ≤ ε / (8 * (c + 1)) := min_le_left _ _
  have hδsmall : δ ≤ 1 / 8 := min_le_right _ _
  obtain ⟨S, hS⟩ := eventually_atTop.mp
    ((b_tendsto_zero.pow 2).eventually_lt_const (show (0 : ℝ) ^ 2 < δ / 4 by simpa using (show (0 : ℝ) < δ / 4 by positivity)))
  let s := S
  have hbs : b s ^ 2 < δ / 4 := hS s le_rfl
  have hs0 : Tendsto (fun q ↦ 2 * (s : ℝ) * b q) atTop (𝓝 0) := by
    simpa using b_tendsto_zero.const_mul (2 * (s : ℝ))
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp (hs0.eventually_lt_const (show 0 < δ / 4 by positivity))
  let q₀ := max Q 1
  have hq₀ : 1 ≤ q₀ := le_max_right _ _
  have hbq₀ : 2 * (s : ℝ) * b q₀ < δ / 4 := hQ _ (le_max_left _ _)
  let L := R * (q₀ + 2)
  have hL : q₀ + 2 ≤ L := by dsimp [L]; nlinarith
  obtain ⟨T, hTbig⟩ := exists_nat_gt
    (max (1 : ℝ) (max (1 / b (L + s)) (64 * (2 * L + 4) / δ)))
  have hTreal : (1 : ℝ) < T := lt_of_le_of_lt (le_max_left _ _) hTbig
  have hT : 1 ≤ T := by exact_mod_cast hTreal.le
  have hTb : 1 / b (L + s) < (T : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hTbig
  have hTδ : 64 * (2 * (L : ℝ) + 4) < δ * T := by
    have hh : 64 * (2 * (L : ℝ) + 4) / δ < T :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hTbig
    have hx := (div_lt_iff₀ hδ).mp hh
    linarith
  have hlevels : 1 ≤ (T : ℝ) ^ 2 * b (L + s) := by
    have hbL := b_pos (L + s)
    have hh := (div_lt_iff₀ hbL).mp hTb
    have hsq : (T : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hsq hbL.le
    linarith
  let d : ℝ := 2 * (T : ℝ) ^ 4 / c
  have hd : 0 < d := by dsimp [d]; positivity
  have hev : ∀ᶠ p : ℕ in atTop,
      T ≤ thickness d p ∧ ∀ n : ℕ,
        (p * thickness d p) ^ 2 ≤ n → n ≤ (2 * L + 4) * (p * thickness d p) ^ 2 →
        |(2 * d) * (thickness d p : ℝ) ^ 2 / Real.log n - 1| < δ := by
    simpa only [Nat.add_assoc, show 3 + 1 = 4 from rfl] using
      ((thickness_atTop hd).eventually (eventually_ge_atTop T)).and
        (tuned_mean_uniform hd (2 * L + 3) hδ)
  have hrowlim := (thickness_log_ratio hd).const_mul (8*((4*T^2+4 : ℕ) : ℝ))
  simp only [mul_zero] at hrowlim
  obtain ⟨P, hP⟩ := eventually_atTop.mp (hev.and (hrowlim.eventually_lt_const hε))
  obtain ⟨p, hp, hpN, hblocks⟩ := exists_shifted_finite_blocks_with_rows T s L (max P (max N₀ 2)) hlevels
  have hpP : P ≤ p := by omega
  have hp2 : 2 ≤ p := by omega
  let K := thickness d p
  have hTK : T ≤ K := (hP p hpP).1.1
  have hK : 0 < K := by omega
  obtain ⟨A₀, hAfin, hsupport, hrows, hu, hgood⟩ := hblocks K hK
  let M := (p * K) ^ 2
  let μ : ℝ := 4 * (K : ℝ) ^ 2 * (T : ℝ) ^ 4
  let A := shift A₀ M
  have hK1 : 1 ≤ K := by omega
  have hpK : p ≤ p * K := by nlinarith
  have hMp : p ≤ M := by dsimp [M]; nlinarith
  have hM : 1 < M := by omega
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hsuppA : A ⊆ Set.Iio ((L + 2) * M) := by
    intro x hx
    have hh := shift_lt hsupport hx
    change x < (L + 2) * M
    change x < (L + 1) * M + M at hh
    nlinarith
  have hround : 128 * (K : ℝ) ^ 2 * (T : ℝ) ^ 3 * (2 * L + 4) < (δ / 2) * μ := by
    have hpos : 0 < 2 * (K : ℝ) ^ 2 * (T : ℝ) ^ 3 := by positivity
    have hh := mul_lt_mul_of_pos_left hTδ hpos
    dsimp [μ]
    nlinarith
  have hglobal : ∀ n, (sumRep A₀ n : ℝ) < μ * (1 + δ) := by
    intro n
    have he := mul_le_mul_of_nonneg_left (carryError_bound T K hT hTK)
      (show (0 : ℝ) ≤ 2 * L + 3 by positivity)
    have he' : (2 * (L : ℝ) + 3) * carryError T K < (δ / 2) * μ := by
      have hpos : 0 ≤ (K : ℝ) ^ 2 * (T : ℝ) ^ 3 := by positivity
      have hpos' : 0 ≤ (K : ℝ) ^ 2 * (T : ℝ) ^ 3 * L := by positivity
      nlinarith
    have hh := hu n
    change (sumRep A₀ n : ℝ) ≤ μ * (1 + b s ^ 2) + (2 * L + 3) * carryError T K at hh
    have hbs' := mul_lt_mul_of_pos_left hbs hμ
    nlinarith
  have htune (n : ℕ) (hnM : M ≤ n) (hnU : n ≤ (2 * L + 4) * M) :
      |μ / Real.log n - c| < c * δ := by
    have hh := mul_lt_mul_of_pos_left ((hP p hpP).1.2 n hnM hnU) hc
    rw [← abs_of_pos hc, ← abs_mul] at hh
    simp only [abs_of_pos hc] at hh
    convert hh using 1
    dsimp [μ, d, K]
    congr 1
    field_simp
    <;> ring
  have hlog (n : ℕ) (hnM : M ≤ n) : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hrowA : RowSparse A (p*K) (2*K*(4*T^2+4)) := by
    have hh := rowSparse_shift (Nat.mul_pos (by omega : 0<p) hK) hrows M
    convert hh using 1 <;> ring
  have hrowcost : 4*((2*K*(4*T^2+4) : ℕ) : ℝ)/Real.log (M : ℝ) < ε := by
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp2)
    have hcomp : Real.log (p : ℝ) ≤ Real.log (M : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0<p by omega)) (by exact_mod_cast hMp)
    have hh := div_le_div_of_nonneg_left
      (show (0 : ℝ) ≤ 4*((2*K*(4*T^2+4) : ℕ) : ℝ) by positivity) hlogp hcomp
    apply hh.trans_lt
    convert (hP p hpP).2 using 1
    dsimp [K]
    push_cast
    ring
  refine ⟨(q₀ + 2) * M, by nlinarith [show N₀ < p by omega], by positivity,
    p*K,2*K*(4*T^2+4),by omega,by omega,by
      change M ≤ (q₀+2)*M
      nlinarith,
    A, shift_finite hAfin M, ?_, hrowA, hrowcost, ?_, ?_⟩
  · intro x hx
    exact shift_ge A₀ M hx
  · intro n
    by_cases hnlo : n < 2 * M
    · rw [sumRep_shift_zero A₀ hnlo, Nat.cast_zero, zero_div]
      positivity
    by_cases hnhi : 2 * ((L + 2) * M) ≤ n
    · rw [sumRep_zero_of_bounded hsuppA hnhi, Nat.cast_zero, zero_div]
      positivity
    have hnM : M ≤ n := by omega
    have hnU : n ≤ (2 * L + 4) * M := by nlinarith
    have he : (sumRep A n : ℝ) < μ * (1 + δ) := by
      rw [sumRep_shift_eq_sub A₀ (by omega)]
      exact hglobal _
    have hh := (abs_lt.mp (htune n hnM hnU)).2
    have hr : μ / Real.log n < c * (1 + δ) := by linarith
    have he' := div_lt_div_of_pos_right he (hlog n hnM)
    have hε' : δ * (8 * (c + 1)) ≤ ε := (le_div_iff₀ (by positivity)).mp hδε
    have hsq : δ * δ ≤ δ / 8 := by nlinarith [mul_le_mul_of_nonneg_left hδsmall hδ.le]
    have hcε := mul_le_mul_of_nonneg_left hsq hc.le
    have hr' := mul_lt_mul_of_pos_right hr (show 0 < 1 + δ by linarith)
    rw [mul_div_right_comm] at he'
    nlinarith
  · intro n hnlo hnhi
    have hn2M : 2 * M ≤ n := by nlinarith
    have hnM : M ≤ n := by omega
    have hnLM : n ≤ L * M := by dsimp [L]; nlinarith
    have hnU : n ≤ (2 * L + 4) * M := by nlinarith
    let q := (n - 2 * M) / M
    let t := (n - 2 * M) % M
    have ht : t < M := Nat.mod_lt _ (by omega)
    have hnt : q * M + t = n - 2 * M := Nat.div_add_mod' _ M
    have hqq₀ : q₀ ≤ q := by
      by_contra hh
      have hh' : q + 1 ≤ q₀ := by omega
      have hsub : n - 2 * M + 2 * M = n := Nat.sub_add_cancel hn2M
      nlinarith
    have hqL : q ≤ L := by
      by_contra hh
      have hh' : L + 1 ≤ q := by omega
      nlinarith [Nat.sub_le n (2 * M)]
    have hbq : 2 * (s : ℝ) * b q < δ / 4 := by
      have hh := mul_le_mul_of_nonneg_left (b_antitone hqq₀) (show 0 ≤ 2 * (s : ℝ) by positivity)
      linarith
    have herr := hgood q hqL t ht
    have herr₁ := taper_error_bound T K q L hT hTK hqL
    have herr₂ : 8 * (K : ℝ) ^ 2 * (T : ℝ) ^ 2 * (q + 1) + (q + 2) * carryError T K ≤
        128 * (K : ℝ) ^ 2 * (T : ℝ) ^ 3 * (2 * L + 4) := by
      have hpos : 0 ≤ (K : ℝ) ^ 2 * (T : ℝ) ^ 3 := by positivity
      have hpos' : 0 ≤ (K : ℝ) ^ 2 * (T : ℝ) ^ 3 * L := by positivity
      nlinarith
    have hprofile : μ * (2 * s * b q + b s ^ 2) < μ * (δ / 2) :=
      mul_lt_mul_of_pos_left (by linarith) hμ
    have he : |(sumRep A n : ℝ) - μ| < δ * μ := by
      rw [sumRep_shift_eq_sub A₀ hn2M]
      change |(sumRep A₀ (q * M + t) : ℝ) - μ| ≤ μ * (2 * s * b q + b s ^ 2) +
        8 * (K : ℝ) ^ 2 * (T : ℝ) ^ 2 * (q + 1) + (q + 2) * carryError T K at herr
      rw [hnt] at herr
      nlinarith
    exact normalize_error hc hδ hδsmall hδε (hlog n hnM) he (htune n hnM hnU)


end Erdos66RowControlledAnnulus
