import Submission.AdditiveDeficitMassExplore
import Submission.BoundedReuseRepairExplore

/-! Necessary incidence concentration for monotone repair with unrestricted
sharing of points. No packets, designated pairs, or reuse bound are assumed.
These are conditional repair restrictions, not a solution of Erdős 66. -/
namespace Erdos66UnrestrictedRepairIncidence
open Filter AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66AdditiveDeficitMass
  Erdos66BoundedReuseRepair Erdos66Counting
open scoped Classical Topology
set_option maxHeartbeats 1600000

noncomputable def targetDegree (B T : Finset ℕ) (x : ℕ) : ℕ :=
  (B.filter (fun b ↦ x+b ∈ T)).card

lemma sum_pairs_eq_degrees (F B T : Finset ℕ) :
    (∑ n∈T, pairs F B n) = ∑ x∈F, targetDegree B T x := by
  rw [pairs_sum]
  simp only [targetDegree, Finset.card_filter, Finset.product_eq_sprod, Finset.sum_product]

/-- Counting all new-point incidences counts a new/new representation twice.
The extra term makes the exact accounting explicit. -/
lemma increment_incidence_identity (A F T : Finset ℕ) (h : Disjoint A F) :
    incrementMass A F T + ∑ n∈T, (pairs F F n:ℝ) =
      2*∑ x∈F, (targetDegree (A∪F) T x:ℝ) := by
  have he : (∑ n∈T, (pairs F (A∪F) n:ℝ)) =
      ∑ x∈F, (targetDegree (A∪F) T x:ℝ) := by
    exact_mod_cast sum_pairs_eq_degrees F (A∪F) T
  rw [←he, Finset.mul_sum, incrementMass, ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [increment_eq A F h n, pairs_union_right F A F n h, pairs_comm F A]
  push_cast
  ring

lemma increment_incidence_bound (A F T : Finset ℕ) (h : Disjoint A F) :
    incrementMass A F T ≤ 2*∑ x∈F, (targetDegree (A∪F) T x:ℝ) := by
  have hn : 0 ≤ ∑ n∈T, (pairs F F n:ℝ) := by positivity
  linarith [increment_incidence_identity A F T h]

/-- Total uniform gain costs incidences even when every new point is allowed
to participate in arbitrarily many target repairs. -/
theorem uniform_gain_incidence_bound (A F T : Finset ℕ) (h : Disjoint A F) (d : ℝ)
    (hgain : ∀ n∈T, (sumRep (A:Set ℕ) n:ℝ)+d ≤ sumRep (A∪F:Finset ℕ) n) :
    d*T.card ≤ 2*∑ x∈F, (targetDegree (A∪F) T x:ℝ) := by
  have hh : (∑ n∈T, d) ≤ incrementMass A F T := by
    apply Finset.sum_le_sum
    intro n hn
    exact le_sub_iff_add_le.mpr (by simpa only [add_comm] using hgain n hn)
  have he : (∑ _n∈T, d) = d*T.card := by simp [mul_comm]
  rw [he] at hh
  exact hh.trans (increment_incidence_bound A F T h)

/-- If every new point has at most H target incidences, the shared repair
needs at least d|T|/(2H) new points. No independence is required. -/
theorem uniform_degree_card_bound (A F T : Finset ℕ) (h : Disjoint A F) (d H : ℝ)
    (hgain : ∀ n∈T, (sumRep (A:Set ℕ) n:ℝ)+d ≤ sumRep (A∪F:Finset ℕ) n)
    (hdegree : ∀ x∈F, (targetDegree (A∪F) T x:ℝ) ≤ H) :
    d*T.card ≤ 2*H*F.card := by
  have hh := uniform_gain_incidence_bound A F T h d hgain
  have hs : (∑ x∈F, (targetDegree (A∪F) T x:ℝ)) ≤ H*F.card := by
    calc
      _ ≤ ∑ _x∈F, H := Finset.sum_le_sum hdegree
      _ = _ := by simp [mul_comm]
  linarith

/-- The number of target tests cancels from the budget when every new-point
degree is bounded by the target mass divided by the ambient counting scale. -/
theorem normalized_degree_card_bound (A F T : Finset ℕ) (h : Disjoint A F)
    (hT : T.Nonempty) (δ L R H : ℝ) (hL : 0<L) (hR : 0<R)
    (hgain : ∀ n∈T, (sumRep (A:Set ℕ) n:ℝ)+δ*L ≤ sumRep (A∪F:Finset ℕ) n)
    (hdegree : ∀ x∈F, R*(targetDegree (A∪F) T x:ℝ) ≤ H*T.card*L) :
    δ*R ≤ 2*H*F.card := by
  have hh := uniform_degree_card_bound A F T h (δ*L) (H*T.card*L/R) hgain
    (fun x hx ↦ (le_div_iff₀ hR).mpr (by simpa only [mul_comm] using hdegree x hx))
  have hc : (0:ℝ)<T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have hm := mul_le_mul_of_nonneg_right hh hR.le
  have he : 2*(H*T.card*L/R)*(F.card:ℝ)*R =
      (2*H*F.card)*((T.card:ℝ)*L) := by field_simp
  rw [he] at hm
  apply le_of_mul_le_mul_right (a := (T.card:ℝ)*L) _ (mul_pos hc hL)
  convert hm using 1 <;> ring

/-- A negligible monotone addition cannot fill persistent positive deficits
if all its points retain this normalized degree bound. -/
theorem negligible_repair_forces_empty_targets (A F T : ℕ → Finset ℕ)
    (R L : ℕ → ℝ) (δ H : ℝ) (hδ : 0<δ)
    (hsmall : Tendsto (fun k ↦ ((F k).card:ℝ)/R k) atTop (𝓝 0))
    (hdata : ∀ᶠ k in atTop, Disjoint (A k) (F k) ∧ 0<L k ∧ 0<R k ∧
      (∀ n∈T k, (sumRep (A k:Set ℕ) n:ℝ)+δ*L k ≤ sumRep ((A k)∪(F k):Finset ℕ) n) ∧
      (∀ x∈F k, R k*(targetDegree ((A k)∪(F k)) (T k) x:ℝ) ≤ H*(T k).card*L k)) :
    ∀ᶠ k in atTop, T k = ∅ := by
  have hlim : Tendsto (fun k ↦ 2*H*(((F k).card:ℝ)/R k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hsmall.const_mul (2*H)
  filter_upwards [hdata, hlim.eventually (gt_mem_nhds hδ)] with k hk hlt
  by_contra he
  have hT : (T k).Nonempty := Finset.nonempty_iff_ne_empty.mpr he
  obtain ⟨hd, hL, hR, hg, hdeg⟩ := hk
  have hh := normalized_degree_card_bound (A k) (F k) (T k) hd hT δ (L k) (R k) H hL hR hg hdeg
  have hl : δ ≤ 2*H*(((F k).card:ℝ)/R k) := by
    rw [←mul_div_assoc]
    exact (le_div_iff₀ hR).mpr hh
  linarith

lemma cutoff_union_diff (A B : Set ℕ) (hAB : A ⊆ B) (N : ℕ) :
    cutoff A N ∪ cutoff (B\A) N = cutoff B N := by
  ext x
  simp only [Finset.mem_union, mem_cutoff, Set.mem_diff]
  constructor
  · rintro (⟨hx, ha⟩ | ⟨hx, hb, ha⟩)
    · exact ⟨hx, hAB ha⟩
    · exact ⟨hx, hb⟩
  · rintro ⟨hx, hb⟩
    by_cases ha : x∈A
    · exact Or.inl ⟨hx, ha⟩
    · exact Or.inr ⟨hx, hb, ha⟩

lemma cutoff_disjoint_diff (A B : Set ℕ) (N : ℕ) :
    Disjoint (cutoff A N) (cutoff (B\A) N) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact (mem_cutoff.mp hy).2.2 (mem_cutoff.mp hx).2

lemma cutoff_sumRep (A : Set ℕ) {n N : ℕ} (hn : n<N) :
    sumRep (cutoff A N : Set ℕ) n = sumRep A n := by
  rw [←pairs_self]
  exact (sumRep_eq_fiber_card A N n hn).symm

/-- Set-level version. Both normalized counting limits are explicit; no
counting profile is assumed for an arbitrary base set. -/
theorem same_counting_completion_empty_targets (A B : Set ℕ) (hAB : A ⊆ B)
    (T : ℕ → Finset ℕ) (R L : ℕ → ℝ) (a δ H : ℝ) (hδ : 0<δ)
    (hA : Tendsto (fun N ↦ (count A N:ℝ)/R N) atTop (𝓝 a))
    (hB : Tendsto (fun N ↦ (count B N:ℝ)/R N) atTop (𝓝 a))
    (hdata : ∀ᶠ N in atTop, 0<L N ∧ 0<R N ∧
      (∀ n∈T N, n<N) ∧
      (∀ n∈T N, (sumRep A n:ℝ)+δ*L N ≤ sumRep B n) ∧
      (∀ x<N, x∈B\A → R N*(targetDegree (cutoff B N) (T N) x:ℝ) ≤ H*(T N).card*L N)) :
    ∀ᶠ N in atTop, T N = ∅ := by
  apply negligible_repair_forces_empty_targets
    (fun N ↦ cutoff A N) (fun N ↦ cutoff (B\A) N) T R L δ H hδ
    (added_count_limit_zero A B hAB R a hA hB)
  filter_upwards [hdata] with N hN
  obtain ⟨hL, hR, hs, hg, hd⟩ := hN
  refine ⟨cutoff_disjoint_diff A B N, hL, hR, ?_, ?_⟩
  · intro n hn
    rw [cutoff_union_diff A B hAB N, cutoff_sumRep A (hs n hn), cutoff_sumRep B (hs n hn)]
    exact hg n hn
  · intro x hx
    rw [cutoff_union_diff A B hAB N]
    exact hd x (mem_cutoff.mp hx).1 (mem_cutoff.mp hx).2

/-- Persistent deficits in a same-counting-mass completion require arbitrarily
large normalized incidence concentrations at newly added points. This allows
unrestricted sharing and includes all new/new contributions. -/
theorem same_counting_completion_frequent_concentration (A B : Set ℕ) (hAB : A ⊆ B)
    (T : ℕ → Finset ℕ) (R L : ℕ → ℝ) (a δ : ℝ) (hδ : 0<δ)
    (hA : Tendsto (fun N ↦ (count A N:ℝ)/R N) atTop (𝓝 a))
    (hB : Tendsto (fun N ↦ (count B N:ℝ)/R N) atTop (𝓝 a))
    (hdata : ∀ᶠ N in atTop, 0<L N ∧ 0<R N ∧
      (∀ n∈T N, n<N) ∧ (∀ n∈T N, (sumRep A n:ℝ)+δ*L N ≤ sumRep B n))
    (hT : ∃ᶠ N in atTop, (T N).Nonempty) (H : ℝ) :
    ∃ᶠ N in atTop, ∃ x<N, x∈B\A ∧
      H*(T N).card*L N < R N*(targetDegree (cutoff B N) (T N) x:ℝ) := by
  by_contra hh
  have hd := not_frequently.mp hh
  have he := same_counting_completion_empty_targets A B hAB T R L a δ H hδ hA hB
    (by
      filter_upwards [hdata, hd] with N hN hbad
      refine ⟨hN.1, hN.2.1, hN.2.2.1, hN.2.2.2, ?_⟩
      intro x hx hxb
      exact le_of_not_gt (fun hlt ↦ hbad ⟨x, hx, hxb, hlt⟩))
  obtain ⟨N, hN, hNe⟩ := (hT.and_eventually he).exists
  simpa only [hNe, Finset.not_nonempty_empty] using hN

/-- Specialization to a hypothetical logarithmic-limit completion. The base
is required to have the same necessary Tauberian counting profile. -/
theorem same_coefficient_completion_frequent_concentration (A B : Set ℕ)
    (hAB : A ⊆ B) (c : ℝ) (hc : c ≠ 0)
    (hB : Tendsto (fun n ↦ (sumRep B n:ℝ)/Real.log n) atTop (𝓝 c))
    (hA : Tendsto (fun N ↦ (count A N:ℝ)/Real.sqrt ((N:ℝ)*Real.log N))
      atTop (𝓝 (2*Real.sqrt (c/Real.pi))))
    (T : ℕ → Finset ℕ) (δ : ℝ) (hδ : 0<δ)
    (hdata : ∀ᶠ N in atTop, (∀ n∈T N, n<N) ∧
      (∀ n∈T N, (sumRep A n:ℝ)+δ*Real.log N ≤ sumRep B n))
    (hT : ∃ᶠ N in atTop, (T N).Nonempty) (H : ℝ) :
    ∃ᶠ N in atTop, ∃ x<N, x∈B\A ∧
      H*(T N).card*Real.log N <
        Real.sqrt ((N:ℝ)*Real.log N)*(targetDegree (cutoff B N) (T N) x:ℝ) := by
  apply same_counting_completion_frequent_concentration A B hAB T
    (fun N ↦ Real.sqrt ((N:ℝ)*Real.log N)) (fun N ↦ Real.log N)
    (2*Real.sqrt (c/Real.pi)) δ hδ hA
    (Erdos66TauberianProfile.witness_counting_profile hc hB) _ hT H
  filter_upwards [hdata, eventually_ge_atTop 2] with N hN hN2
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hlog : 0<Real.log (N:ℝ) := Real.log_pos hNr
  exact ⟨hlog, Real.sqrt_pos.mpr (mul_pos (by linarith) hlog), hN⟩

end Erdos66UnrestrictedRepairIncidence
