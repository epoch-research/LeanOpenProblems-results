import Submission.DigitBoxExponentExplore

/-! Elementary parameters for a near-linear-in-word-length memory lower
bound. The selected lengths are 64*b*j*2^j. -/
namespace Erdos66DigitMemoryParameters
open Filter
open scoped Topology
set_option maxHeartbeats 2600000

def wordLength (b j : ℕ) : ℕ := 64*b*j*2^j

def blockLength (j : ℕ) : ℕ := 8*2^j

def numBlocks (b j : ℕ) : ℕ := 8*b*j

lemma lengths_multiply (b j : ℕ) : blockLength j*numBlocks b j=wordLength b j := by
  unfold blockLength numBlocks wordLength
  ring

lemma eventual_cap_bound {b : ℕ} (hb : 1 < b) (L : ℕ) :
    ∀ᶠ j : ℕ in atTop, L*(wordLength b j+1)≤b^(2*j) := by
  have h1 := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)).const_mul
    ((L:ℝ)*(64*b))
  have h0 := (tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<2)).const_mul (L:ℝ)
  have ht := h1.add h0
  simp only [mul_zero,zero_add] at ht
  have ht' : Tendsto (fun j : ℕ ↦ ((L:ℝ)*(64*b*j+1))/(2:ℝ)^j) atTop (𝓝 0) := by
    apply ht.congr
    intro j
    simp only [pow_one,pow_zero]
    ring
  filter_upwards [ht'.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with j hj
  have hj' : L*(64*b*j+1)≤2^j := by
    have he := (div_lt_one (pow_pos (by norm_num : (0:ℝ)<2) j)).mp hj
    exact_mod_cast he.le
  have hp : 1≤2^j := one_le_pow₀ (by decide : 1≤(2:ℕ))
  have hinner : wordLength b j+1≤(64*b*j+1)*2^j := by
    unfold wordLength
    nlinarith
  calc
    L*(wordLength b j+1) ≤ L*((64*b*j+1)*2^j) := Nat.mul_le_mul_left _ hinner
    _ = (L*(64*b*j+1))*2^j := by ring
    _ ≤ 2^j*2^j := Nat.mul_le_mul_right _ hj'
    _ = 2^(2*j) := by rw [two_mul,pow_add]
    _ ≤ b^(2*j) := Nat.pow_le_pow_left (by omega) _

lemma count_bound_algebra (b j : ℕ) :
    (b^(2^j))^(numBlocks b j+1)*(b^(2*j))^(b*blockLength j)=
      b^((24*b*j+1)*2^j) := by
  rw [←pow_mul,←pow_mul,←pow_add]
  congr 1
  unfold numBlocks blockLength
  ring

lemma count_sq_half {b j a : ℕ} (hb : 1 < b) (hj : 1≤j)
    (ha : a≤b^((24*b*j+1)*2^j)) : 2*a^2≤b^(wordLength b j) := by
  have hp : 1≤2^j := one_le_pow₀ (by decide : 1≤(2:ℕ))
  have hbj : 2≤b*j := by nlinarith
  have hexp : 2*((24*b*j+1)*2^j)+1≤wordLength b j := by
    unfold wordLength
    nlinarith [Nat.mul_le_mul_right (2^j) hbj]
  calc
    2*a^2 ≤ b*(b^((24*b*j+1)*2^j))^2 :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left ha 2)
    _ = b^(2*((24*b*j+1)*2^j)+1) := by
      rw [←pow_mul,pow_succ,Nat.mul_comm ((24*b*j+1)*2^j) 2]
      exact Nat.mul_comm _ _
    _ ≤ b^(wordLength b j) := Nat.pow_le_pow_right (by omega) hexp

lemma wordLength_ge (b j : ℕ) (hb : 1≤b) : j≤wordLength b j := by
  have hp : 1≤2^j := one_le_pow₀ (by decide : 1≤(2:ℕ))
  unfold wordLength
  nlinarith [Nat.mul_le_mul_right j hb,Nat.mul_le_mul_right (64*b*j) hp]

lemma cutoff_large {b : ℕ} (hb : 1 < b) (M : ℕ) :
    ∀ᶠ j : ℕ in atTop, 2*M<b^(wordLength b j) := by
  filter_upwards [eventually_ge_atTop (2*M+1)] with j hj
  exact (show 2*M<wordLength b j from
    lt_of_lt_of_le (by omega) (wordLength_ge b j (by omega))).trans (Nat.lt_pow_self hb)

end Erdos66DigitMemoryParameters
