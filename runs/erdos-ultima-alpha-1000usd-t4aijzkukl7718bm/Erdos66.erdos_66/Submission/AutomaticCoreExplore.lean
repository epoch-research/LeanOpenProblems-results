import Submission.DfaCountingExplore

/-! An automatic subset of a hypothetical witness has negligible counting
mass. In particular, a sparse perturbation of an automatic core does not
supply a witness. This is not a disproof of the unrestricted conjecture. -/
namespace Erdos66AutomaticCore
open Erdos66DfaCounting Erdos66DfaLoopCode Erdos66DigitLoopPeak Erdos66Counting
open Filter AdditiveCombinatorics
open scoped Classical Topology
set_option maxHeartbeats 2000000

lemma count_mono_sets {A B : Set ℕ} (h : A ⊆ B) (N : ℕ) : count A N ≤ count B N := by
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hn,ha⟩ := mem_cutoff.mp hn
  exact mem_cutoff.mpr ⟨hn,h ha⟩

lemma count_mono_cutoff (A : Set ℕ) {N M : ℕ} (h : N ≤ M) : count A N ≤ count A M := by
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hn,ha⟩ := mem_cutoff.mp hn
  exact mem_cutoff.mpr ⟨hn.trans_le h,ha⟩

lemma nat_log_tendsto {b : ℕ} (hb : 1 < b) : Tendsto (Nat.log b) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (b^k)] with n hn
  exact Nat.le_log_of_pow_le hb hn

lemma shifted_twice_poly_div_exp {b : ℕ} (hb : 1 < b) (S : ℕ) :
    Tendsto (fun k : ℕ ↦ (((k:ℝ)+2)*(b+1))^S / (b:ℝ)^k) atTop (𝓝 0) := by
  have hshift : Tendsto (fun k : ℕ ↦ k+1) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ Nat.le_succ k) tendsto_id
  have hh := ((shifted_poly_div_exp hb S).comp hshift).mul_const (b:ℝ)
  simp only [zero_mul] at hh
  apply hh.congr
  intro k
  simp only [Function.comp_def, Nat.cast_add, Nat.cast_one, pow_succ]
  have hb0 : (b:ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have he : ((k:ℝ)+1)+1=k+2 := by ring
  rw [he]
  field_simp

/-- Polynomial digit-word growth is negligible even on the square-root
scale, at every natural cutoff, not just at base powers. -/
lemma count_sq_div_zero_of_poly_bound {b : ℕ} (hb : 1 < b) (B : Set ℕ) (S : ℕ)
    (hcount : ∀ k, count B (b^k) ≤ ((k+1)*(b+1))^S) :
    Tendsto (fun N : ℕ ↦ (count B N : ℝ)^2/N) atTop (𝓝 0) := by
  have ht := (shifted_twice_poly_div_exp hb (S*2)).comp (nat_log_tendsto hb)
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ by positivity)) ?_ ht
  filter_upwards [eventually_ge_atTop 1] with N hN
  let k := Nat.log b N
  have hlow : b^k ≤ N := Nat.pow_log_le_self b (by omega)
  have hhigh : N ≤ b^(k+1) := (Nat.lt_pow_succ_log_self hb N).le
  have hmass : count B N ≤ ((k+2)*(b+1))^S := by
    have hh := (count_mono_cutoff B hhigh).trans (hcount (k+1))
    simpa only [Nat.add_assoc] using hh
  have hmass' : (count B N : ℝ)^2 ≤ (((k:ℝ)+2)*(b+1))^(S*2) := by
    exact_mod_cast (show count B N ^ 2 ≤ ((k+2)*(b+1))^(S*2) by
      simpa only [pow_mul] using Nat.pow_le_pow_left hmass 2)
  change (count B N : ℝ)^2/(N:ℝ) ≤ (((k:ℝ)+2)*(b+1))^(S*2)/(b:ℝ)^k
  exact div_le_div₀ (by positivity) hmass' (pow_pos (by exact_mod_cast (show 0<b by omega)) _)
    (by exact_mod_cast hlow)

/-- A square-root-negligible subset is negligible relative to any eventual
additive basis. -/
lemma negligible_relative_to_basis (A B : Set ℕ)
    (hB : Tendsto (fun N : ℕ ↦ (count B N : ℝ)^2/N) atTop (𝓝 0))
    (M : ℕ) (hM : ∀ n ≥ M, 1 ≤ sumRep A n) :
    Tendsto (fun N ↦ (count B N : ℝ)/count A N) atTop (𝓝 0) := by
  have hsq : Tendsto (fun N ↦ ((count B N : ℝ)/count A N)^2) atTop (𝓝 0) := by
    have ht := hB.const_mul 2
    simp only [mul_zero] at ht
    apply squeeze_zero' (Eventually.of_forall (fun N ↦ sq_nonneg _)) ?_ ht
    filter_upwards [eventually_ge_atTop (2*M+1)] with N hN
    have hb := basis_count_bound A M hM N
    have hpos : 0 < count A N := by
      by_contra hh
      have hz : count A N=0 := by omega
      simp only [hz, zero_pow (by decide : 2≠0), Nat.add_zero] at hb
      omega
    have ha : (N:ℝ) ≤ 2*(count A N : ℝ)^2 := by
      have hh : (N:ℝ) ≤ (M:ℝ)+(count A N : ℝ)^2 := by exact_mod_cast hb
      have hh' : 2*(M:ℝ)+1 ≤ N := by exact_mod_cast hN
      linarith
    have ha0 : (0:ℝ) < count A N := by exact_mod_cast hpos
    have hn0 : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
    rw [div_pow, ←mul_div_assoc, div_le_div_iff₀ (sq_pos_of_pos ha0) hn0]
    nlinarith [mul_le_mul_of_nonneg_left ha (sq_nonneg (count B N : ℝ))]
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simp only [Real.sqrt_zero] at ht
  apply ht.congr
  intro N
  exact Real.sqrt_sq (by positivity)

/-- Any automatic subset of a hypothetical witness has zero relative
counting density inside that witness. -/
theorem automatic_subset_negligible {b : ℕ} {σ : Type*} [Fintype σ]
    (hb : 1 < b) (M : DFA (Fin b) σ) (A B : Set ℕ)
    (hrec : ∀ w, code w ∈ B ↔ w ∈ M.accepts) (hBA : B ⊆ A)
    (c : ℝ) (hc : c ≠ 0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun N ↦ (count B N : ℝ)/count A N) atTop (𝓝 0) := by
  have hu := loop_unique_of_log_limit hb M A (fun w hw ↦ hBA ((hrec w).mpr hw)) c ht
  have hB := count_sq_div_zero_of_poly_bound hb B (Fintype.card σ) (count_bound hb M B hrec hu)
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    ((Erdos66Explore.sumRep_tendsto_atTop hc ht).eventually_ge_atTop 1)
  exact negligible_relative_to_basis A B hB K hK

lemma count_difference {A B : Set ℕ} (hBA : B ⊆ A) (N : ℕ) :
    count (A \ B) N = count A N - count B N := by
  have he : cutoff (A \ B) N = cutoff A N \ cutoff B N := by
    ext n
    simp only [mem_cutoff, Set.mem_diff, Finset.mem_sdiff]
    tauto
  have hs : cutoff B N ⊆ cutoff A N := by
    intro n hn
    exact mem_cutoff.mpr ⟨(mem_cutoff.mp hn).1,hBA (mem_cutoff.mp hn).2⟩
  unfold count
  rw [he,Finset.card_sdiff_of_subset hs]

lemma count_positive_eventually {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ᶠ N in atTop, 0 < count A N := by
  obtain ⟨a,ha⟩ := (Erdos66Explore.witness_infinite hc ht).nonempty
  filter_upwards [eventually_ge_atTop (a+1)] with N hN
  exact Finset.card_pos.mpr ⟨a,mem_cutoff.mpr ⟨by omega,ha⟩⟩

/-- Removing any automatic subset leaves asymptotically all the counting
mass of a hypothetical witness. -/
theorem automatic_complement_full {b : ℕ} {σ : Type*} [Fintype σ]
    (hb : 1 < b) (M : DFA (Fin b) σ) (A B : Set ℕ)
    (hrec : ∀ w, code w ∈ B ↔ w ∈ M.accepts) (hBA : B ⊆ A)
    (c : ℝ) (hc : c ≠ 0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun N ↦ (count (A \ B) N : ℝ)/count A N) atTop (𝓝 1) := by
  have hB := automatic_subset_negligible hb M A B hrec hBA c hc ht
  have hlim := hB.const_sub 1
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [count_positive_eventually hc ht] with N hN
  rw [count_difference hBA, Nat.cast_sub (count_mono_sets hBA N), sub_div,
    div_self (by exact_mod_cast (Nat.ne_of_gt hN))]

/-- An augmentation of an automatic set can be a witness only if the
augmenting set supplies asymptotically all of its counting mass. -/
theorem automatic_union_repair_full {b : ℕ} {σ : Type*} [Fintype σ]
    (hb : 1 < b) (M : DFA (Fin b) σ) (B D : Set ℕ)
    (hrec : ∀ w, code w ∈ B ↔ w ∈ M.accepts) (c : ℝ) (hc : c ≠ 0)
    (ht : Tendsto (fun n ↦ (sumRep (B ∪ D) n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun N ↦ (count D N : ℝ)/count (B ∪ D) N) atTop (𝓝 1) := by
  have hlow := automatic_complement_full hb M (B ∪ D) B hrec Set.subset_union_left c hc ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · apply Eventually.of_forall
    intro N
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast count_mono_sets (show (B ∪ D) \ B ⊆ D from
      fun x hx ↦ hx.1.resolve_left hx.2) N
  · filter_upwards [count_positive_eventually hc ht] with N hN
    have hpos : (0:ℝ) < count (B ∪ D) N := by exact_mod_cast hN
    apply (div_le_one hpos).mpr
    exact_mod_cast count_mono_sets Set.subset_union_right N

/-- In particular, an augmentation negligible relative to the resulting
set cannot repair an automatic core to a witness. -/
theorem no_negligible_automatic_repair {b : ℕ} {σ : Type*} [Fintype σ]
    (hb : 1 < b) (M : DFA (Fin b) σ) (B D : Set ℕ)
    (hrec : ∀ w, code w ∈ B ↔ w ∈ M.accepts)
    (hD : Tendsto (fun N ↦ (count D N : ℝ)/count (B ∪ D) N) atTop (𝓝 0))
    (c : ℝ) (hc : c ≠ 0) :
    ¬ Tendsto (fun n ↦ (sumRep (B ∪ D) n : ℝ)/Real.log n) atTop (𝓝 c) := by
  intro ht
  have hh := tendsto_nhds_unique hD (automatic_union_repair_full hb M B D hrec c hc ht)
  norm_num at hh

end Erdos66AutomaticCore
