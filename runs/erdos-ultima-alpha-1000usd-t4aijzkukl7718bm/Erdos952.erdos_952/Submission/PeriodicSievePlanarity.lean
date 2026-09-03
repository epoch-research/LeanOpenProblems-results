import Submission.RipsCrossing
import Submission.PeriodicCurveCrossing
import Submission.RankTwoSieveNecessity

/-! Planarity and rotation symmetry of the finite Gaussian sieve.
These results concern finite sieves, not the infinite prime sieve. -/
namespace Erdos952Investigation.PeriodicSievePlanarity
open FiniteSieveReduction PeriodicSieveComponents RankTwoSieveNecessity RipsCrossing
open scoped unitInterval
set_option maxHeartbeats 0

lemma period_neg {N : ℕ} {d : GaussianInt} (hd : IsPeriod N d) : IsPeriod N (-d) :=
  ⟨by simpa using dvd_neg.mpr hd.1,by simpa using dvd_neg.mpr hd.2⟩

lemma period_int_mul {N : ℕ} {d : GaussianInt} (hd : IsPeriod N d) (n : ℤ) :
    IsPeriod N ((n : GaussianInt)*d) := by
  constructor
  · simpa using dvd_mul_of_dvd_right hd.1 n
  · simpa using dvd_mul_of_dvd_right hd.2 n

lemma reachable_int_multiples {C : ℤ} {N : ℕ} {z d : GaussianInt}
    (h : (sieveGraph C N).Reachable z (z+d)) (hd : IsPeriod N d) (n : ℤ) :
    (sieveGraph C N).Reachable z (z+(n : GaussianInt)*d) := by
  have hnat {a e : GaussianInt} (h : (sieveGraph C N).Reachable a (a+e))
      (he : IsPeriod N e) (k : ℕ) :
      (sieveGraph C N).Reachable a (a+(k : GaussianInt)*e) := by
    simpa only [add_sub_cancel_left] using reachable_multiples_of_period h
      (show IsPeriod N (a+e-a) by simpa using he) k
  have hneg : (sieveGraph C N).Reachable z (z+(-d)) := by
    have ht := reachable_add_period h (period_neg hd)
    simpa only [add_neg_cancel_right] using ht.symm
  cases n with
  | ofNat k => simpa using hnat h hd k
  | negSucc k =>
    convert hnat hneg (period_neg hd) (k+1) using 1 <;> push_cast <;> ring

lemma adj_add_period {C : ℤ} {N : ℕ} {a b d : GaussianInt}
    (h : (sieveGraph C N).Adj a b) (hd : IsPeriod N d) :
    (sieveGraph C N).Adj (a+d) (b+d) :=
  ⟨allowed_add_period h.1 hd,allowed_add_period h.2.1 hd,
    fun he => h.2.2.1 (add_right_cancel he),by simpa using h.2.2.2⟩

lemma trace_mono_reachable {G : SimpleGraph GaussianInt} {z w : GaussianInt}
    (h : G.Reachable z w) : Trace G w ⊆ Trace G z := by
  rintro p ⟨a,b,hwa,hab,hp⟩
  exact ⟨a,b,h.trans hwa,hab,hp⟩

lemma trace_add_period {C : ℤ} {N : ℕ} {z d : GaussianInt} {p : ℂ}
    (hp : p ∈ Trace (sieveGraph C N) z) (hd : IsPeriod N d) :
    p+(d : ℂ) ∈ Trace (sieveGraph C N) (z+d) := by
  obtain ⟨a,b,hza,hab,hp⟩ := hp
  refine ⟨a+d,b+d,reachable_add_period hza hd,adj_add_period hab hd,?_⟩
  simpa only [GaussianInt.toComplex_add,add_comm] using
    (mem_segment_translate ℝ (d : ℂ)).mpr hp

lemma reachable_ne_has_edge {G : SimpleGraph GaussianInt} {a b : GaussianInt}
    (h : G.Reachable a b) (hne : a ≠ b) : ∃ c, G.Adj a c := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact False.elim (hne rfl)
  | cons hab _ => exact ⟨_,hab⟩

lemma path_of_walk {G : SimpleGraph GaussianInt} (root : GaussianInt)
    {a b : GaussianInt} (p : G.Walk a b) :
    G.Reachable root a → (a : ℂ) ∈ Trace G root →
    ∃ q : Path (a : ℂ) (b : ℂ), Set.range q ⊆ Trace G root := by
  induction p with
  | nil =>
    intro _ ha
    refine ⟨Path.refl _,?_⟩
    simpa only [Path.refl_range,Set.singleton_subset_iff] using ha
  | @cons a b c hab p ih =>
    intro hroota _
    have hb : (b : ℂ) ∈ Trace G root := ⟨a,b,hroota,hab,right_mem_segment _ _ _⟩
    obtain ⟨q,hq⟩ := ih (hroota.trans hab.reachable) hb
    refine ⟨(Path.segment (a : ℂ) (b : ℂ)).trans q,?_⟩
    rw [Path.trans_range,Path.range_segment]
    exact Set.union_subset (fun _ hp => ⟨a,b,hroota,hab,hp⟩) hq

lemma curve_in_periodic_component {C : ℤ} {N : ℕ} {z d : GaussianInt}
    (hwrap : (sieveGraph C N).Reachable z (z+d)) (hd : IsPeriod N d) (hd0 : d ≠ 0) :
    ∃ f : ℝ → ℂ, Continuous f ∧
      (∃ B : ℝ, ∀ t : ℝ, ‖f t-(t : ℂ)*(d : ℂ)‖ ≤ B) ∧
      ∀ t, f t ∈ Trace (sieveGraph C N) z := by
  obtain ⟨v,hv⟩ := reachable_ne_has_edge hwrap (by intro he; apply hd0; abel_nf at he; simpa using he.symm)
  obtain ⟨p⟩ := hwrap
  have hztrace : (z : ℂ) ∈ Trace (sieveGraph C N) z :=
    ⟨z,v,SimpleGraph.Reachable.refl _,hv,left_mem_segment _ _ _⟩
  obtain ⟨q,hq⟩ := path_of_walk z p (SimpleGraph.Reachable.refl _) hztrace
  have hend : ((z+d : GaussianInt) : ℂ) = (z : ℂ)+(d : ℂ) := GaussianInt.toComplex_add _ _
  let q' : Path (z : ℂ) ((z : ℂ)+(d : ℂ)) := q.cast rfl hend.symm
  obtain ⟨f,hf,hB,hfmem⟩ := PeriodicCurveCrossing.path_drift_extension (z : ℂ) (d : ℂ) q'
  refine ⟨f,hf,hB,fun t => ?_⟩
  obtain ⟨n,s,he⟩ := hfmem t
  rw [he]
  have hs : q' s ∈ Trace (sieveGraph C N) z := hq ⟨s,rfl⟩
  have hh := trace_add_period hs (period_int_mul hd n)
  have hr := reachable_int_multiples p.reachable hd n
  have ht := trace_mono_reachable hr hh
  simpa only [GaussianInt.toComplex_mul,map_intCast] using ht

/-- Independent periods in two sieve components force the components to join. -/
theorem independent_periods_join {C : ℤ} {N : ℕ} {z w d e : GaussianInt}
    (hd : IsPeriod N d) (he : IsPeriod N e)
    (hzd : (sieveGraph C N).Reachable z (z+d))
    (hwe : (sieveGraph C N).Reachable w (w+e)) (hdet : det d e ≠ 0) :
    (sieveGraph C N).Reachable z w := by
  have hd0 : d ≠ 0 := by intro h; apply hdet; simp [h,det]
  have he0 : e ≠ 0 := by intro h; apply hdet; simp [h,det]
  obtain ⟨f,hf,⟨A,hA⟩,hfm⟩ := curve_in_periodic_component hzd hd hd0
  obtain ⟨g,hg,⟨B,hB⟩,hgm⟩ := curve_in_periodic_component hwe he he0
  have hdet' : (d : ℂ).re*(e : ℂ).im-(d : ℂ).im*(e : ℂ).re ≠ 0 := by
    rcases d with ⟨dr,di⟩
    rcases e with ⟨er,ei⟩
    simp only [GaussianInt.re_toComplex,GaussianInt.im_toComplex]
    exact_mod_cast hdet
  obtain ⟨s,t,hst⟩ := PeriodicCurveCrossing.bounded_drift_curves_intersect
    f g hf hg d e hdet' A B hA hB
  by_contra hn
  have hdis := sieve_component_traces_disjoint C N z w hn
  exact (Set.disjoint_left.mp hdis) (hfm s) (hst ▸ hgm t)

#print axioms independent_periods_join
end Erdos952Investigation.PeriodicSievePlanarity
