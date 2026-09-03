import Submission.DfaLoopCodeExplore
import Submission.Explore

/-! A digit-recognized set cannot have a nonzero finite logarithmic
representation limit. This is only a restricted-class obstruction. -/
namespace Erdos66DfaCounting
open Erdos66DigitLoopPeak Erdos66DfaLoopCode Erdos66Counting
open Filter AdditiveCombinatorics
open scoped Classical Topology
set_option maxHeartbeats 2000000

variable {b : ℕ}

def finWord (hb : 1 < b) (k m : ℕ) : List (Fin b) :=
  (Nat.digitsAppend b k m).attach.map
    (fun d ↦ ⟨d.val, Nat.lt_of_mem_digitsAppend hb k d.val d.property⟩)

lemma code_finWord (hb : 1 < b) (k m : ℕ) : code (finWord hb k m) = m := by
  simp only [code, finWord, List.map_map, Function.comp_def, List.attach_map_subtype_val]
  rw [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]

lemma length_finWord (hb : 1 < b) (k m : ℕ) (hm : m < b^k) :
    (finWord hb k m).length = k := by
  simp only [finWord, List.length_map, List.length_attach]
  exact Nat.length_digitsAppend hb k hm

lemma finWord_injective (hb : 1 < b) (k : ℕ) : Function.Injective (finWord hb k) := by
  intro m n he
  simpa only [code_finWord] using congrArg code he

lemma count_bound {σ : Type*} [Fintype σ] (hb : 1 < b) (M : DFA (Fin b) σ)
    (A : Set ℕ) (hrec : ∀ w, code w ∈ A ↔ w ∈ M.accepts)
    (hunique : ContextLoopUnique M) (k : ℕ) :
    count A (b^k) ≤ ((k+1)*(b+1))^Fintype.card σ := by
  let W := (cutoff A (b^k)).image (finWord hb k)
  have hcard : W.card = count A (b^k) :=
    Finset.card_image_of_injective _ (finWord_injective hb k)
  rw [←hcard]
  simpa only [Fintype.card_fin] using accepted_finset_bound M hunique k W (by
    intro w hw
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hw
    have hm' := mem_cutoff.mp hm
    exact ⟨length_finWord hb k m hm'.1, (hrec _).mp (by simpa only [code_finWord] using hm'.2)⟩)

lemma basis_count_bound (A : Set ℕ) (M : ℕ)
    (hM : ∀ n ≥ M, 1 ≤ sumRep A n) (N : ℕ) : N ≤ M + count A N ^ 2 := by
  have h : N-M ≤ count A N ^ 2 := calc
    N-M = ∑ n ∈ Finset.Ico M N, 1 := by simp
    _ ≤ ∑ n ∈ Finset.Ico M N, sumRep A n := by
      apply Finset.sum_le_sum
      intro n hn
      exact hM n (Finset.mem_Ico.mp hn).1
    _ ≤ ∑ n ∈ Finset.range N, sumRep A n := by
      apply Finset.sum_le_sum_of_subset
      intro n hn
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
    _ ≤ count A N ^ 2 := cumulative_le_count_sq A N
  omega

lemma shifted_poly_div_exp (hb : 1 < b) (S : ℕ) :
    Tendsto (fun k : ℕ ↦ (((k:ℝ)+1)*(b+1))^S / (b:ℝ)^k) atTop (𝓝 0) := by
  have hb' : 1 < (b:ℝ) := by exact_mod_cast hb
  have hshift : Tendsto (fun k : ℕ ↦ k+1) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ Nat.le_succ k) tendsto_id
  have hh := ((tendsto_pow_const_div_const_pow_of_one_lt S hb').comp hshift).mul_const
    ((b:ℝ)*(b+1)^S)
  simp only [zero_mul] at hh
  apply hh.congr
  intro k
  simp only [Function.comp_def, Nat.cast_add, Nat.cast_one, pow_succ]
  rw [mul_pow]
  field_simp

lemma no_poly_count_basis (hb : 1 < b) (A : Set ℕ) (S : ℕ)
    (hcount : ∀ k, count A (b^k) ≤ ((k+1)*(b+1))^S)
    (M : ℕ) (hM : ∀ n ≥ M, 1 ≤ sumRep A n) : False := by
  have hb' : 1 < (b:ℝ) := by exact_mod_cast hb
  have hconst : Tendsto (fun k : ℕ ↦ (M:ℝ)/(b:ℝ)^k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt 0 hb').const_mul (M:ℝ)
  have ht := hconst.add (shifted_poly_div_exp hb (S*2))
  simp only [zero_add] at ht
  have hle : ∀ k : ℕ, (1:ℝ) ≤ (M:ℝ)/(b:ℝ)^k +
      (((k:ℝ)+1)*(b+1))^(S*2)/(b:ℝ)^k := by
    intro k
    have hi : b^k ≤ M + (((k+1)*(b+1))^S)^2 :=
      (basis_count_bound A M hM (b^k)).trans (Nat.add_le_add_left
        (Nat.pow_le_pow_left (hcount k) 2) M)
    have hi' : (b:ℝ)^k ≤ (M:ℝ) + (((k:ℝ)+1)*(b+1))^(S*2) := by
      exact_mod_cast (show b^k ≤ M + ((k+1)*(b+1))^(S*2) by simpa only [pow_mul] using hi)
    rw [←add_div, le_div_iff₀ (pow_pos (by positivity : (0:ℝ)<b) k), one_mul]
    exact hi'
  have := ge_of_tendsto ht (Filter.Eventually.of_forall hle)
  norm_num at this

/-- No set recognized by a finite digit automaton (including zero padding)
has a nonzero finite logarithmic representation limit. -/
theorem no_nonzero_log_limit {σ : Type*} [Fintype σ] (hb : 1 < b)
    (M : DFA (Fin b) σ) (A : Set ℕ)
    (hrec : ∀ w, code w ∈ A ↔ w ∈ M.accepts) (c : ℝ) (hc : c ≠ 0) :
    ¬ Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) := by
  intro ht
  have hu := loop_unique_of_log_limit hb M A (fun w hw ↦ (hrec w).mpr hw) c ht
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((Erdos66Explore.sumRep_tendsto_atTop hc ht).eventually_ge_atTop 1)
  exact no_poly_count_basis hb A (Fintype.card σ) (count_bound hb M A hrec hu) N hN

end Erdos66DfaCounting
