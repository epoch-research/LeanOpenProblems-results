import FormalConjecturesUtil

/-! A direct finite-support gliding-hump lemma. No assertion about prime factors
or natural density is made in this file. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

/-- For triangular real arrays, coordinatewise convergence and convergence
against every fixed sign test imply convergence of the row ℓ¹ norms. -/
theorem triangular_schur (f : ℕ → ℕ → ℝ)
    (hcoord : ∀ p, Tendsto (fun N => f N p) atTop (𝓝 0))
    (hweak : ∀ s : ℕ → ℝ, (∀ p, s p = 1 ∨ s p = -1) →
      Tendsto (fun N => ∑ p ∈ range N, s p*f N p) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ p ∈ range N, |f N p|) atTop (𝓝 0) := by
  classical
  have hpos (N : ℕ) : 0 ≤ ∑ p ∈ range N, |f N p| := sum_nonneg (fun p _ => abs_nonneg _)
  suffices hs : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (∑ p ∈ range N, |f N p|)<ε by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (hpos _)] using hs ε hε
  intro ε hε
  by_contra h
  have hbad : ∀ M : ℕ, ∃ N, M ≤ N ∧ ε ≤ ∑ p ∈ range N, |f N p| := by
    simpa only [not_lt] using frequently_atTop.mp (not_eventually.mp h)
  have hsmall (B : ℕ) : Tendsto (fun N => ∑ p ∈ range B, |f N p|) atTop (𝓝 0) := by
    simpa only [abs_zero,sum_const_zero] using tendsto_finset_sum (range B) (fun p _ => (hcoord p).abs)
  have hex (M : ℕ) : ∃ N : ℕ, M<N ∧ ε ≤ ∑ p ∈ range N, |f N p| ∧
      (∑ p ∈ range M, |f N p|)<ε/4 := by
    obtain ⟨T,hT⟩ := eventually_atTop.mp ((hsmall M).eventually_lt_const (by positivity : (0 : ℝ)<ε/4))
    obtain ⟨N,hN,hmass⟩ := hbad (max T (M+1))
    exact ⟨N,by omega,hmass,hT N (by omega)⟩
  choose pick hpick using hex
  let d : ℕ → ℕ := fun k => (pick^[k]) 0
  have hdstep (k : ℕ) : d (k+1)=pick (d k) := by simp [d,Function.iterate_succ_apply']
  have hd : StrictMono d := strictMono_nat_of_lt_succ (fun k => by rw [hdstep]; exact (hpick (d k)).1)
  have hdtop : Tendsto d atTop atTop := hd.tendsto_atTop
  have hexp (p : ℕ) : ∃ k : ℕ, p<d (k+1) := by
    obtain ⟨k,hk⟩ := (hdtop.eventually_gt_atTop p).exists
    exact ⟨k,hk.trans (hd (Nat.lt_succ_self k))⟩
  let block (p : ℕ) : ℕ := Nat.find (hexp p)
  have hblock (k p : ℕ) (hlo : d k ≤ p) (hhi : p<d (k+1)) : block p=k := by
    apply le_antisymm (Nat.find_min' (hexp p) hhi)
    by_contra hn
    change ¬k≤block p at hn
    have hlt : block p<k := by omega
    have hh := Nat.find_spec (hexp p)
    change p<d (block p+1) at hh
    have hh' := hd.monotone (show block p+1≤k by omega)
    omega
  let s (p : ℕ) : ℝ := if 0≤f (d (block p+1)) p then 1 else -1
  have hs (p : ℕ) : s p=1 ∨ s p = -1 := by unfold s; split_ifs <;> simp
  have hsgn (k p : ℕ) (hlo : d k≤p) (hhi : p<d (k+1)) :
      s p*f (d (k+1)) p=|f (d (k+1)) p| := by
    dsimp [s]
    rw [hblock k p hlo hhi]
    split_ifs with h
    · simp only [one_mul,abs_of_nonneg h]
    · simp only [neg_one_mul,abs_of_neg (lt_of_not_ge h)]
  have hbound (k : ℕ) : ε/2 ≤ ∑ p ∈ range (d (k+1)), s p*f (d (k+1)) p := by
    have hp := hpick (d k)
    rw [← hdstep] at hp
    have hpoint (p : ℕ) (hp' : p ∈ range (d (k+1))) :
        |f (d (k+1)) p|-2*(if p<d k then |f (d (k+1)) p| else 0) ≤
          s p*f (d (k+1)) p := by
      by_cases hlo : p<d k
      · rw [if_pos hlo]
        rcases hs p with h|h
        · rw [h,one_mul]; linarith [neg_abs_le (f (d (k+1)) p)]
        · rw [h,neg_one_mul]; linarith [le_abs_self (f (d (k+1)) p)]
      · rw [if_neg hlo,hsgn k p (not_lt.mp hlo) (mem_range.mp hp'),mul_zero,sub_zero]
    have hsum := sum_le_sum hpoint
    have hfilt : (range (d (k+1))).filter (fun p => p<d k) = range (d k) := by
      ext p
      simp only [mem_filter,mem_range]
      constructor
      · exact And.right
      · intro h; exact ⟨h.trans (hd (Nat.lt_succ_self k)),h⟩
    rw [sum_sub_distrib,← mul_sum,← sum_filter,hfilt] at hsum
    linarith [hp.2.1,hp.2.2]
  have ht : Tendsto (fun k => ∑ p ∈ range (d (k+1)), s p*f (d (k+1)) p) atTop (𝓝 0) :=
    (hweak s hs).comp (hdtop.comp (tendsto_add_atTop_nat 1))
  have hh := ge_of_tendsto ht (Eventually.of_forall hbound)
  linarith


/-- The coordinate limits in `triangular_schur` follow already from the sign
tests, by comparing the constant test with a one-coordinate sign flip. -/
theorem triangular_schur_of_sign_tests (f : ℕ → ℕ → ℝ)
    (hweak : ∀ s : ℕ → ℝ, (∀ p, s p = 1 ∨ s p = -1) →
      Tendsto (fun N => ∑ p ∈ range N, s p*f N p) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ p ∈ range N, |f N p|) atTop (𝓝 0) := by
  classical
  apply triangular_schur f _ hweak
  intro p
  let s (q : ℕ) : ℝ := if q=p then 1 else -1
  have hs := hweak s (fun q => by unfold s; split_ifs <;> simp)
  have h1 := hweak (fun _ => 1) (fun _ => Or.inl rfl)
  have ht := (hs.add h1).div_const 2
  simp only [zero_add,zero_div] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop p] with N hN
  rw [← sum_add_distrib]
  have he : (∑ q ∈ range N, (s q*f N q+1*f N q))=2*f N p := by
    rw [sum_eq_single p]
    · simp [s]; ring
    · intro q hq hqp
      simp [s,hqp]
    · intro hp
      exact False.elim (hp (mem_range.mpr hN))
  rw [he]
  ring

#print axioms triangular_schur_of_sign_tests

#print axioms triangular_schur
end Erdos371.FiniteInformation
