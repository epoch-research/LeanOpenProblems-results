import Submission.DigitMemoryLowerExplore

/-! A logarithmic form of the variable-width lower bound. At the selected
lengths k, logarithmic state width must be at least a constant times k/log k. -/
namespace Erdos66DigitMemoryLog
open Filter AdditiveCombinatorics Erdos66DigitMemoryParameters Erdos66DigitMemoryLower
  Erdos66DfaCounting
open scoped Topology
set_option maxHeartbeats 2800000
universe u

lemma memory_inequality {b j S : ℕ} (hb : 1 < b) (hj : 1≤j) (hS : b^(2^j)<S) :
    (wordLength b j:ℝ)*Real.log b*Real.log 2 <
      64*b*Real.log S*Real.log (wordLength b j) := by
  have hb0 : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
  have hb1 : (1:ℝ)<b := by exact_mod_cast hb
  have hj1 : (1:ℝ)≤j := by exact_mod_cast hj
  have hp : (0:ℝ)<(2:ℝ)^j := pow_pos (by norm_num) j
  have hlogb : 0<Real.log (b:ℝ) := Real.log_pos hb1
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hword : 2^j≤wordLength b j := by
    have hh : 1≤64*b*j := by nlinarith
    simpa only [one_mul,wordLength] using Nat.mul_le_mul_right (2^j) hh
  have hlen : (j:ℝ)*Real.log 2≤Real.log (wordLength b j) := by
    have hh := Real.log_le_log hp (show (2:ℝ)^j≤(wordLength b j:ℝ) by exact_mod_cast hword)
    simpa only [Real.log_pow] using hh
  have hlen0 : 0<Real.log (wordLength b j) := by
    have hh : 0<(j:ℝ)*Real.log 2 := mul_pos (by linarith) hlog2
    exact hh.trans_le hlen
  have hwidth : (2:ℝ)^j*Real.log b<Real.log S := by
    have hh := Real.log_lt_log (pow_pos hb0 (2^j))
      (show (b:ℝ)^(2^j)<(S:ℝ) by exact_mod_cast hS)
    simpa only [Real.log_pow,Nat.cast_pow,Nat.cast_ofNat] using hh
  have hprod : (2:ℝ)^j*Real.log b*((j:ℝ)*Real.log 2)<
      Real.log S*Real.log (wordLength b j) :=
    (mul_le_mul_of_nonneg_left hlen (mul_nonneg hp.le hlogb.le)).trans_lt
      (mul_lt_mul_of_pos_right hwidth hlen0)
  have hscale := mul_lt_mul_of_pos_left hprod (show (0:ℝ)<64*b by positivity)
  convert hscale using 1 <;> simp only [wordLength,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] <;> ring

/-- The constant is positive for every base b>=2. This is a precise
near-linear memory lower bound along the selected lengths, not a claim
about all algorithms or arbitrary unbounded-width descriptions. -/
theorem witness_eventual_memory_lower {b : ℕ} (hb : 1 < b)
    (σ : ℕ → Type u) [∀ j, Fintype (σ j)]
    (E : (j : ℕ) → ℕ → σ j → Fin b → σ j → Prop)
    (initial : (j : ℕ) → σ j) (T : (j : ℕ) → Set (σ j)) (A : Set ℕ)
    (hrec : ∀ j n, n<b^(wordLength b j) → (n∈A ↔ ∃ z∈T j,
      Erdos66LayeredPath.Path (E j) 0 (finWord hb (wordLength b j) n) (initial j) z))
    (c : ℝ) (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ᶠ j : ℕ in atTop,
      (wordLength b j:ℝ)*Real.log b*Real.log 2 <
        64*b*Real.log (Fintype.card (σ j))*Real.log (wordLength b j) := by
  filter_upwards [witness_eventual_width_lower hb σ E initial T A hrec c hc ht,
    eventually_ge_atTop 1] with j hj hj1
  exact memory_inequality hb hj1 hj

end Erdos66DigitMemoryLog
