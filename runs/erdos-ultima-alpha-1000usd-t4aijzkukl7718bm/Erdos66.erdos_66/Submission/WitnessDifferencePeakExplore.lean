import Submission.ShortDifferenceMassExplore
import Submission.SidonColorWitnessExplore

/-! A hypothetical logarithmic witness has log-squared repeated short
positive differences. This is not a lower bound on its sum representations. -/
namespace Erdos66WitnessDifferencePeak
open Filter AdditiveCombinatorics Erdos66ShortDifferenceMass
  Erdos66SidonColorWitness Erdos66SidonColorAnnuli Erdos66Counting
  Erdos66TauberianProfile Erdos66Explore
open scoped Classical Topology
set_option maxHeartbeats 1800000

lemma differencePairs_card (S : Finset ℕ) (d : ℕ) (hd : 0<d) :
    (differencePairs S d).card=(S.filter (fun x ↦ x+d∈S)).card := by
  apply Finset.card_bij (fun ab _ ↦ ab.1)
  · intro ab hab
    obtain ⟨hab,hablt,he⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    exact Finset.mem_filter.mpr ⟨ha,by convert hb using 1; omega⟩
  · intro ab hab cd hcd he
    have hab' := (Finset.mem_filter.mp hab).2
    have hcd' := (Finset.mem_filter.mp hcd).2
    exact Prod.ext he (by omega)
  · intro x hx
    obtain ⟨hx,hxd⟩ := Finset.mem_filter.mp hx
    exact ⟨(x,x+d),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hxd⟩,
      by dsimp; omega,by dsimp; omega⟩,rfl⟩

noncomputable def shiftCount (A : Set ℕ) (N d : ℕ) : ℕ :=
  ((cutoff A N).filter (fun x ↦ x+d<N ∧ x+d∈A)).card

lemma cutoff_differencePairs_card (A : Set ℕ) (N d : ℕ) (hd : 0<d) :
    (differencePairs (cutoff A N) d).card=shiftCount A N d := by
  rw [differencePairs_card _ _ hd]
  simp only [shiftCount,mem_cutoff]

/-- The conclusion already follows from the positive sqrt(N log N)
counting profile. It does not need pointwise representation estimates. -/
theorem counting_profile_forces_difference_peaks (A : Set ℕ) (L : ℝ) (hL : 0<L)
    (hcount : Tendsto (fun N ↦ (count A N:ℝ)/Real.sqrt ((N:ℝ)*Real.log N)) atTop (𝓝 L)) :
    ∃ γ : ℝ, 0<γ ∧ ∃ K : ℕ, ∀ J : ℕ, K ≤ J →
      ∃ d : ℕ, 0<d ∧ d<4^J ∧ γ*(J:ℝ)^2 ≤ shiftCount A (4^(2*J)) d := by
  let D := L*Real.sqrt (Real.log 4)
  have hD : 0<D := mul_pos hL (Real.sqrt_pos.mpr (Real.log_pos (by norm_num)))
  have hgeo : Tendsto (fun k : ℕ ↦ (count A (4^k):ℝ)/((2:ℝ)^k*Real.sqrt k)) atTop (𝓝 D) :=
    geometric_count_limit hcount
  obtain ⟨K,hK1,hbounds⟩ := geometric_count_bounds hD hgeo
  let a := D/4
  let b := 5*D/2
  have ha : 0<a := by dsimp [a]; positivity
  have ha2 : 0<a^2 := sq_pos_of_pos ha
  obtain ⟨K',hK'⟩ := exists_nat_ge (6*b/a^2)
  refine ⟨a^2/12,by positivity,max K K',fun J hJ ↦ ?_⟩
  have hJK : K ≤ J := (le_max_left _ _).trans hJ
  have hJK' : K' ≤ J := (le_max_right _ _).trans hJ
  have hJ1 : 1 ≤ J := hK1.trans hJK
  have hJsize : 6*b ≤ a^2*(J:ℝ) := by
    have hr : 6*b/a^2 ≤ (J:ℝ) := hK'.trans (by exact_mod_cast hJK')
    simpa only [mul_comm] using (div_le_iff₀ ha2).mp hr
  obtain ⟨d,hd,hdu,hpeak⟩ := annular_difference_peak (cutoff A (4^(2*J))) J a b ha (by omega)
    (annulus_profile_of_bounds A D hD K hbounds J hJK)
    (cutoff_size_of_bounds A D hD K hbounds J hJK hJ1) hJsize
  rw [cutoff_differencePairs_card A _ d hd] at hpeak
  exact ⟨d,hd,hdu,hpeak⟩

/-- At N=4^(2J), some shift d<sqrt(N) occurs at least gamma*J^2 times.
The shift is allowed to vary with J; no fixed-shift conclusion is asserted. -/
theorem witness_forces_difference_peaks {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (h : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c)) :
    ∃ γ : ℝ, 0<γ ∧ ∃ K : ℕ, ∀ J : ℕ, K ≤ J →
      ∃ d : ℕ, 0<d ∧ d<4^J ∧ γ*(J:ℝ)^2 ≤ shiftCount A (4^(2*J)) d := by
  have hcpos := limit_pos hc h
  apply counting_profile_forces_difference_peaks A (2*Real.sqrt (c/Real.pi))
    (by positivity) (witness_counting_profile hc h)

/-- Uniform o(J^2) bounds for all these short-difference counts exclude a
witness. This does not assume such a bound for arbitrary sets. -/
theorem subquadratic_short_differences_exclude_witness (A : Set ℕ) (E : ℕ → ℝ)
    (hE : Tendsto (fun J : ℕ ↦ E J/(J:ℝ)^2) atTop (𝓝 0))
    (hbound : ∀ᶠ J in atTop, ∀ d : ℕ, 0<d → d<4^J → (shiftCount A (4^(2*J)) d:ℝ) ≤ E J)
    (c : ℝ) (hc : c≠0) :
    ¬Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c) := by
  intro h
  obtain ⟨γ,hγ,K,hK⟩ := witness_forces_difference_peaks hc h
  obtain ⟨J,hJ,hJE,hJ1,hJK⟩ := (hbound.and
    ((hE.eventually_lt_const hγ).and ((eventually_ge_atTop 1).and (eventually_ge_atTop K)))).exists
  obtain ⟨d,hd,hdu,hpeak⟩ := hK J hJK
  have hsq : 0<(J:ℝ)^2 := by positivity
  have hlt := (div_lt_iff₀ hsq).mp hJE
  have hb := hJ d hd hdu
  linarith

end Erdos66WitnessDifferencePeak
