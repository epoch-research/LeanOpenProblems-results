import FormalConjecturesUtil
import Submission.DensitySequenceDiagnostic
import Submission.BinomialRelaxationEquivalence

/-! Integer-valued sequences with an irrational pure-power asymptotic and a
bounded integer dilation defect. They are not asserted to be extremal-number
sequences of any fixed graph. -/
open Filter Asymptotics
open scoped Topology
namespace Erdos713IntegerDilationDiagnostic
open Erdos713DensitySequence
set_option maxHeartbeats 1000000

noncomputable def index : ℝ := Real.log 31 / Real.log 16

lemma index_scale : (16 : ℝ) ^ index = 31 := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have hlog : Real.log 16 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 16)).ne'
  convert Real.exp_log (by norm_num : (0 : ℝ) < 31) using 1
  congr 1
  dsimp [index]
  field_simp

lemma index_bounds : (6 : ℝ)/5 < index ∧ index < (5 : ℝ)/4 := by
  have hlog : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have hl := Real.log_lt_log (by positivity : (0 : ℝ) < 16^6)
    (by norm_num : (16 : ℝ)^6 < 31^5)
  have hu := Real.log_lt_log (by positivity : (0 : ℝ) < 31^4)
    (by norm_num : (31 : ℝ)^4 < 16^5)
  rw [Real.log_pow, Real.log_pow] at hl hu
  constructor
  · dsimp [index]
    apply (lt_div_iff₀ hlog).mpr
    norm_num at hl
    linarith
  · dsimp [index]
    apply (div_lt_iff₀ hlog).mpr
    norm_num at hu
    linarith

lemma index_irrational : Irrational index := by
  intro hr
  obtain ⟨p,q,hq,hpq⟩ :=
    Erdos713BinomialRelaxation.nat_fraction_of_positive_rational
      (by linarith [index_bounds.1] : 0 < index) hr
  have hp : 0 < p := by
    have hh : (0 : ℝ) < p := hpq ▸ mul_pos (by linarith [index_bounds.1])
      (by exact_mod_cast hq)
    exact_mod_cast hh
  have heR : (16 : ℝ)^p = 31^q := by
    rw [← Real.rpow_natCast, ← hpq, Real.rpow_mul_natCast (by norm_num), index_scale]
  have he : (16 : ℕ)^p = 31^q := by exact_mod_cast heR
  have hmod := congrArg (fun n : ℕ => n % 2) he
  simp [Nat.pow_mod, hp.ne'] at hmod

lemma raw_dilation {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    31 * raw c index n ≤ raw c index (16*n) ∧
      raw c index (16*n) < 31 * raw c index n + 31 := by
  have hx : 0 ≤ c*(n : ℝ)^index := by positivity
  have he : c*((16*n : ℕ) : ℝ)^index = 31*(c*(n : ℝ)^index) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg n), index_scale]
    ring
  have hlo := Nat.floor_le hx
  have hhi := Nat.lt_floor_add_one (c*(n : ℝ)^index)
  have hy : 0 ≤ c*((16*n : ℕ) : ℝ)^index := by positivity
  have hbig := Nat.floor_le hy
  constructor
  · apply Nat.le_floor
    rw [he]
    simpa only [Nat.cast_mul, Nat.cast_ofNat, raw] using
      mul_le_mul_of_nonneg_left hlo (show (0 : ℝ) ≤ 31 by norm_num)
  · have hh : (raw c index (16*n) : ℝ) < 31*(raw c index n : ℝ)+31 := by
      dsimp [raw]
      conv_rhs at hbig => rw [he]
      nlinarith
    exact_mod_cast hh

/-- The bounded defect survives the complete-graph truncation eventually. -/
lemma seq_dilation {c : ℝ} (hc : 0 ≤ c) :
    ∀ᶠ n : ℕ in atTop, ∃ e : ℕ, e < 31 ∧
      seq c index (16*n) = 31 * seq c index n + e := by
  have hraw := seq_eventually_raw (by linarith [index_bounds.2] : index < 2) hc
  have htop : Tendsto (fun n : ℕ => 16*n) atTop atTop :=
    tendsto_atTop_mono (fun n => show n ≤ 16*n by omega) tendsto_id
  filter_upwards [hraw, hraw.comp_tendsto htop] with n hn hn'
  simp only [Function.comp_apply] at hn'
  rw [hn, hn']
  have hb := raw_dilation hc n
  refine ⟨raw c index (16*n) - 31 * raw c index n, ?_, ?_⟩ <;> omega

/-- All the numerical sampling properties still coexist with an integer
scaling recurrence having a uniformly bounded natural error term. -/
theorem exists_irrational_integer_dilation (N : ℕ) :
    ∃ (r c : ℝ) (f : ℕ → ℕ), (6 : ℝ)/5 < r ∧ r < (5 : ℝ)/4 ∧ Irrational r ∧
      0 < c ∧ Monotone f ∧ (∀ a b, f a+f b ≤ f (a+b)) ∧
      (∀ n, f n ≤ n.choose 2) ∧ (∀ n ≤ N, f n = n.choose 2) ∧
      AntitoneOn (fun n : ℕ => (f n : ℝ)/(n.choose 2 : ℝ)) (Set.Ici 2) ∧
      IsEquivalent atTop (fun n : ℕ => (f n : ℝ)) (fun n : ℕ => c*(n : ℝ)^r) ∧
      (∀ᶠ n : ℕ in atTop, ∃ e : ℕ, e < 31 ∧ f (16*n) = 31*f n+e) := by
  let c : ℝ := (N : ℝ)^2+2
  have hc2 : 2 ≤ c := by dsimp [c]; nlinarith [sq_nonneg (N : ℝ)]
  have hc : 0 < c := by linarith
  have hr1 : 1 ≤ index := by linarith [index_bounds.1]
  have hr2 : index < 2 := by linarith [index_bounds.2]
  refine ⟨index,c,seq c index,index_bounds.1,index_bounds.2,index_irrational,hc,
    seq_monotone (by linarith) hc.le,seq_superadditive hr1 hc.le,
    fun _ => min_le_left _ _,?_,?_,
    seq_asymptotic (by linarith) hr2 hc,seq_dilation hc.le⟩
  · intro n hn
    exact seq_complete_prefix (by linarith) (by dsimp [c]; linarith) hn
  · apply seq_density_antitone hr1 hr2.le hc.le
    nlinarith [index_bounds.2]

#print axioms index_irrational
#print axioms raw_dilation
#print axioms seq_dilation
#print axioms exists_irrational_integer_dilation
end Erdos713IntegerDilationDiagnostic
