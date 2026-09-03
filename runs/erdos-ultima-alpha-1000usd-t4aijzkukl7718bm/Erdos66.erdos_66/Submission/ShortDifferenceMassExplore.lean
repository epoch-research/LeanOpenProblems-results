import Submission.SidonColorAnnuliExplore

/-! Short positive differences forced by multiscale occupancy, without any
Sidon coloring assumption. These are finite counting inequalities. -/
namespace Erdos66ShortDifferenceMass
open Erdos66SidonColorBlockEnergy Erdos66SidonColorAnnuli
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def differencePairs (S : Finset ℕ) (d : ℕ) : Finset (ℕ×ℕ) :=
  (S×ˢS).filter (fun ab ↦ ab.1<ab.2 ∧ ab.2-ab.1=d)

noncomputable def shortPairs (S : Finset ℕ) (u : ℕ) : Finset (ℕ×ℕ) :=
  (S×ˢS).filter (fun ab ↦ ab.1<ab.2 ∧ ab.2-ab.1<u)

lemma differencePairs_zero (S : Finset ℕ) : differencePairs S 0=∅ := by
  apply Finset.filter_eq_empty_iff.mpr
  intro ab hab he
  omega

lemma shortPairs_sum (S : Finset ℕ) (u : ℕ) :
    (shortPairs S u).card=∑ d∈Finset.range u, (differencePairs S d).card := by
  let T := (S×ˢS).filter (fun ab ↦ ab.1<ab.2)
  have he := Finset.sum_card_fiberwise_eq_card_filter T (Finset.range u) (fun ab ↦ ab.2-ab.1)
  simpa only [T,Finset.filter_filter,Finset.mem_range,differencePairs,shortPairs] using he.symm

lemma block_energy_le_short_pairs (S : Finset ℕ) (u : ℕ) (hu : 0<u) (B : Finset ℕ) :
    (∑ b∈B, (binMass S u b:ℝ)^2) ≤ S.card+2*((shortPairs S u).card:ℝ) := by
  have hf := partial_fiber_square_sum S (fun a ↦ a/u) B
  have he : ((S×ˢS).filter (fun ab ↦ ab.1/u=ab.2/u))=sameCellPairs S (fun _ ↦ ()) u := by
    ext ab
    simp [sameCellPairs]
  rw [he,sameCellPairs_card] at hf
  have hsub : (sameCellPairs S (fun _ ↦ ()) u).filter (fun ab ↦ ab.1<ab.2) ⊆ shortPairs S u := by
    intro ab hab
    obtain ⟨hab,hablt⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha,hb,hcol,hbin⟩ := mem_sameCellPairs.mp hab
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩,
      hablt,same_bin_difference_lt hu hablt hbin⟩
  have hc := Finset.card_le_card hsub
  have hh : (∑ b∈B, (binMass S u b)^2) ≤ S.card+2*(shortPairs S u).card := by
    exact hf.trans (by omega)
  exact_mod_cast hh

/-- Short differences pay for every annulus, not just the largest one. -/
theorem annular_short_difference_mass (S : Finset ℕ) (J : ℕ) (a : ℝ)
    (hprofile : ∀ j∈Finset.Ico J (2*J), a^2*(4:ℝ)^j*J ≤ (shellMass S j:ℝ)^2) :
    a^2*(4:ℝ)^J*(J:ℝ)^2 ≤ 3*S.card+6*((shortPairs S (4^J)).card:ℝ) := by
  have hjbound (j : ℕ) (hj : j∈Finset.Ico J (2*J)) :
      a^2*(4:ℝ)^J*J ≤ 3*∑ b∈shellBins J j, (binMass S (4^J) b:ℝ)^2 := by
    have hjJ := (Finset.mem_Ico.mp hj).1
    have hl := (hprofile j hj).trans (shell_cauchy S hjJ)
    have he : (4:ℝ)^j=(4:ℝ)^J*(4:ℝ)^(j-J) := by
      rw [←pow_add,Nat.add_sub_of_le hjJ]
    rw [he] at hl
    apply le_of_mul_le_mul_right (a := (4:ℝ)^(j-J)) _ (by positivity)
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.Ico J (2*J)) (fun j hj ↦ hjbound j hj)
  have hc : (Finset.Ico J (2*J)).card=J := by simp only [Nat.card_Ico]; omega
  simp only [Finset.sum_const,hc,nsmul_eq_mul] at hs
  rw [←Finset.mul_sum,←Finset.sum_biUnion (shellBins_disjoint J)] at hs
  have he := block_energy_le_short_pairs S (4^J) (by positivity)
    ((Finset.Ico J (2*J)).biUnion (shellBins J))
  nlinarith

/-- Once the diagonal point mass is smaller than half the annular lower
bound, short-difference mass has quadratic logarithmic-scale size. -/
theorem annular_short_difference_mass_lower (S : Finset ℕ) (J : ℕ) (a b : ℝ)
    (hprofile : ∀ j∈Finset.Ico J (2*J), a^2*(4:ℝ)^j*J ≤ (shellMass S j:ℝ)^2)
    (hsize : (S.card:ℝ) ≤ b*(4:ℝ)^J*J) (hJ : 6*b ≤ a^2*(J:ℝ)) :
    (a^2/12)*(4:ℝ)^J*(J:ℝ)^2 ≤ (shortPairs S (4^J)).card := by
  have he := annular_short_difference_mass S J a hprofile
  have hm := mul_le_mul_of_nonneg_right hJ (show 0 ≤ (4:ℝ)^J*(J:ℝ) by positivity)
  nlinarith only [he,hsize,hm]

/-- Pigeonholing the short positive differences yields one repeated shift. -/
theorem annular_difference_peak (S : Finset ℕ) (J : ℕ) (a b : ℝ)
    (ha : 0<a) (hJpos : 0<J)
    (hprofile : ∀ j∈Finset.Ico J (2*J), a^2*(4:ℝ)^j*J ≤ (shellMass S j:ℝ)^2)
    (hsize : (S.card:ℝ) ≤ b*(4:ℝ)^J*J) (hJ : 6*b ≤ a^2*(J:ℝ)) :
    ∃ d : ℕ, 0<d ∧ d<4^J ∧ (a^2/12)*(J:ℝ)^2 ≤ (differencePairs S d).card := by
  have he := annular_short_difference_mass_lower S J a b hprofile hsize hJ
  rw [shortPairs_sum,Nat.cast_sum] at he
  have hh : (∑ _d∈Finset.range (4^J), (a^2/12)*(J:ℝ)^2) ≤
      ∑ d∈Finset.range (4^J), ((differencePairs S d).card:ℝ) := by
    simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,mul_comm,mul_left_comm,mul_assoc] using he
  obtain ⟨d,hd,hcount⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr (by positivity : 4^J≠0)) hh
  refine ⟨d,?_,Finset.mem_range.mp hd,hcount⟩
  by_contra hnot
  have hz : d=0 := by omega
  rw [hz,differencePairs_zero,Finset.card_empty,Nat.cast_zero] at hcount
  have hpos : 0<(a^2/12)*(J:ℝ)^2 := by positivity
  linarith

end Erdos66ShortDifferenceMass
