import Submission.Explore

/-! At the midpoint between two consecutive blocks, all representations
are old/new. A sublogarithmic old/new cap at unbounded cutoffs is therefore
incompatible with a nonzero logarithmic representation limit. -/
namespace Erdos66NaturalBoundaryMixed
open Filter AdditiveCombinatorics
open scoped Topology Classical
set_option maxHeartbeats 1500000

noncomputable def boundaryMixed (A : Set ℕ) (M : ℕ) : ℕ :=
  ((Finset.range M).filter (fun a ↦ a∈A ∧ 2*M-1-a∈A)).card

/-- At the odd target immediately below twice the cutoff, every ordered
representation has exactly one endpoint below the cutoff. -/
theorem boundary_exact (A : Set ℕ) (M : ℕ) (hM : 0<M) :
    sumRep A (2*M-1)=2*boundaryMixed A M := by
  let S := (Finset.antidiagonal (2*M-1)).filter (fun p ↦ p.1∈A ∧ p.2∈A)
  have hlow : (S.filter (fun p ↦ p.1<M)).card=boundaryMixed A M := by
    apply Finset.card_bij (fun p _ ↦ p.1)
    · intro p hp
      obtain ⟨hp,hlow⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp,hA⟩ := Finset.mem_filter.mp hp
      have he := Finset.mem_antidiagonal.mp hp
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr hlow,hA.1,?_⟩
      convert hA.2 using 1
      omega
    · intro p hp q hq he
      have hp' := Finset.mem_antidiagonal.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
      have hq' := Finset.mem_antidiagonal.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
      exact Prod.ext he (by omega)
    · intro a ha
      obtain ⟨ha,hAa,hAb⟩ := Finset.mem_filter.mp ha
      have ha' := Finset.mem_range.mp ha
      refine ⟨(a,2*M-1-a),?_,rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr ?_,hAa,hAb⟩,ha'⟩
      dsimp only
      omega
  have hswap : (S.filter (fun p ↦ p.1<M)).card=(S.filter (fun p ↦ ¬p.1<M)).card := by
    apply Finset.card_bij (fun p _ ↦ p.swap)
    · intro p hp
      obtain ⟨hp,hlow⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp,hAa,hAb⟩ := Finset.mem_filter.mp hp
      have he := Finset.mem_antidiagonal.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_antidiagonal.mpr (by dsimp; omega),hAb,hAa⟩,by dsimp; omega⟩
    · intro p hp q hq he
      exact Prod.swap_injective he
    · intro p hp
      obtain ⟨hp,hlow⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp,hAa,hAb⟩ := Finset.mem_filter.mp hp
      have he := Finset.mem_antidiagonal.mp hp
      refine ⟨p.swap,?_,by simp⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_antidiagonal.mpr (by dsimp; omega),hAb,hAa⟩,by dsimp; omega⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s:=S) (fun p : ℕ×ℕ ↦ p.1<M)
  rw [sumRep_def]
  change S.card=2*boundaryMixed A M
  omega

lemma boundary_target_tendsto : Tendsto (fun M : ℕ ↦ 2*M-1) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b+1)] with M hM
  omega

/-- Every hypothetical witness has asymptotically c/2 logarithmic mixed
counts across every large cutoff, not merely across a selected subsequence. -/
theorem boundary_mixed_limit {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun M ↦ (boundaryMixed A M:ℝ)/Real.log ((2*M-1:ℕ):ℝ)) atTop (𝓝 (c/2)) := by
  have hh := (h.comp boundary_target_tendsto).div_const 2
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with M hM
  rw [Function.comp_apply,boundary_exact A M (by omega)]
  push_cast
  ring

/-- A uniform small mixed cap along unbounded cutoffs cannot be carried
from the finite-field construction to the natural-number setting. -/
theorem no_sublog_boundary_cap {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c))
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) (g : ℕ → ℝ)
    (hg : Tendsto (fun j ↦ g j/Real.log ((2*M j-1:ℕ):ℝ)) atTop (𝓝 0)) :
    ¬(∀ᶠ j in atTop, (boundaryMixed A (M j):ℝ)≤g j) := by
  intro hcap
  have hlim := (boundary_mixed_limit h).comp hM
  have hlogpos : ∀ᶠ j in atTop, 0<Real.log ((2*M j-1:ℕ):ℝ) := by
    filter_upwards [hM.eventually_ge_atTop 2] with j hj
    exact Real.log_pos (by exact_mod_cast (show 1<2*M j-1 by omega))
  have hle : c/2≤(0:ℝ) := le_of_tendsto_of_tendsto hlim hg (by
    filter_upwards [hcap,hlogpos] with j hj hp
    exact div_le_div_of_nonneg_right hj hp.le)
  have hcpos := Erdos66Explore.limit_pos hc h
  linarith


lemma root_log_ratio_tendsto_zero (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) (K : ℝ) :
    Tendsto (fun j ↦ K*Real.sqrt (Real.log ((2*M j-1:ℕ):ℝ))/
      Real.log ((2*M j-1:ℕ):ℝ)) atTop (𝓝 0) := by
  have ht := boundary_target_tendsto.comp hM
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp ht)
  have hs := Real.tendsto_sqrt_atTop.comp hl
  have hh := hs.inv_tendsto_atTop.const_mul K
  rw [mul_zero] at hh
  apply hh.congr'
  filter_upwards [hl.eventually_gt_atTop 0] with j hj
  change 0<Real.log ((2*M j-1:ℕ):ℝ) at hj
  have hs0 := (Real.sqrt_pos.mpr hj).ne'
  change K*(Real.sqrt (Real.log ((2*M j-1:ℕ):ℝ)))⁻¹=_
  symm
  calc
    _ = K*Real.sqrt (Real.log ((2*M j-1:ℕ):ℝ))/
        (Real.sqrt (Real.log ((2*M j-1:ℕ):ℝ))*Real.sqrt (Real.log ((2*M j-1:ℕ):ℝ))) := by
          rw [Real.mul_self_sqrt hj.le]
    _ = _ := by field_simp [hs0]

/-- In particular, a cap of the fresh-curve size O(sqrt(log M)) cannot
supply the natural transition at an unbounded sequence of cutoffs. -/
theorem no_root_boundary_cap {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c))
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) (K : ℝ) :
    ¬(∀ᶠ j in atTop, (boundaryMixed A (M j):ℝ)≤
      K*Real.sqrt (Real.log ((2*M j-1:ℕ):ℝ))) :=
  no_sublog_boundary_cap hc h M hM _ (root_log_ratio_tendsto_zero M hM K)

end Erdos66NaturalBoundaryMixed
