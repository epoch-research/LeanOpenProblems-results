import Submission.PeriodicSievePlanarity

/-! Every infinite component of a finite Gaussian sieve is rank two,
and there is at most one such component. This is not a proof that any cutoff
has only finite components for a given arbitrary jump bound. -/
namespace Erdos952Investigation.SieveInfiniteUniqueness
open FiniteSieveReduction PeriodicSieveComponents RankTwoSieveNecessity
open PeriodicSievePlanarity
set_option maxHeartbeats 0

def rotate (z : GaussianInt) : GaussianInt := ⟨-z.im,z.re⟩

lemma rotate_add (z w : GaussianInt) : rotate (z+w) = rotate z+rotate w := by
  apply Zsqrtd.ext <;> simp [rotate] <;> ring

lemma rotate_sub (z w : GaussianInt) : rotate (z-w) = rotate z-rotate w := by
  apply Zsqrtd.ext <;> simp [rotate] <;> ring

lemma rotate_injective : Function.Injective rotate := by
  intro z w h
  have hr := congrArg Zsqrtd.re h
  have hi := congrArg Zsqrtd.im h
  exact Zsqrtd.ext hi (neg_injective hr)

lemma rotate_norm (z : GaussianInt) : (rotate z).norm = z.norm := by
  simp [rotate,gaussian_norm_sq,add_comm]

lemma rotate_period {N : ℕ} {d : GaussianInt} (hd : IsPeriod N d) :
    IsPeriod N (rotate d) := ⟨dvd_neg.mpr hd.2,hd.1⟩

lemma rotate_allowed {N : ℕ} {z : GaussianInt} (hz : Allowed N z) :
    Allowed N (rotate z) := by
  intro p hpN hp hd
  rw [rotate_norm] at hd
  exact hz p hpN hp hd

lemma rotate_adj {C : ℤ} {N : ℕ} {z w : GaussianInt} (h : (sieveGraph C N).Adj z w) :
    (sieveGraph C N).Adj (rotate z) (rotate w) :=
  ⟨rotate_allowed h.1,rotate_allowed h.2.1,fun he => h.2.2.1 (rotate_injective he),by
    rw [← rotate_sub,rotate_norm]
    exact h.2.2.2⟩

lemma rotate_reachable {C : ℤ} {N : ℕ} {z w : GaussianInt}
    (h : (sieveGraph C N).Reachable z w) :
    (sieveGraph C N).Reachable (rotate z) (rotate w) :=
  h.map (⟨rotate,rotate_adj⟩ : sieveGraph C N →g sieveGraph C N)

lemma det_rotate_self (d : GaussianInt) : det d (rotate d) = d.norm := by
  simp [det,rotate,gaussian_norm_sq]
  ring

lemma nonzero_period_of_infinite {C : ℤ} {N : ℕ} {z : GaussianInt}
    (hz : {w | (sieveGraph C N).Reachable z w}.Infinite) :
    ∃ d : GaussianInt, IsPeriod N d ∧ d ≠ 0 ∧ (sieveGraph C N).Reachable z (z+d) := by
  have hh : ¬ Set.InjOn (residue N) {w | (sieveGraph C N).Reachable z w} :=
    fun h => hz ((component_finite_iff_residue_injective C N z).mpr h)
  simp only [Set.InjOn] at hh
  push_neg at hh
  obtain ⟨u,hu,v,hv,hres,hne⟩ := hh
  have hd := period_of_same_residue hres
  exact ⟨v-u,hd,fun h => hne (sub_eq_zero.mp h).symm,
    reachable_period_at_base hu hv hd⟩

/-- An infinite component contains a nonzero period and its quarter-turn. -/
theorem infinite_component_has_rotated_periods {C : ℤ} {N : ℕ} {z : GaussianInt}
    (hz : {w | (sieveGraph C N).Reachable z w}.Infinite) :
    ∃ d : GaussianInt, IsPeriod N d ∧ d ≠ 0 ∧
      (sieveGraph C N).Reachable z (z+d) ∧
      (sieveGraph C N).Reachable z (z+rotate d) := by
  obtain ⟨d,hd,hd0,hzd⟩ := nonzero_period_of_infinite hz
  have hr : (sieveGraph C N).Reachable (rotate z) (rotate z+rotate d) := by
    simpa only [rotate_add] using rotate_reachable hzd
  have hdet : det d (rotate d) ≠ 0 := by
    rw [det_rotate_self]
    exact mt GaussianInt.norm_eq_zero.mp hd0
  have hjoin := independent_periods_join hd (rotate_period hd) hzd hr hdet
  refine ⟨d,hd,hd0,hzd,?_⟩
  simpa only [add_sub_cancel_left] using reachable_period_at_base hjoin (hjoin.trans hr)
    (show IsPeriod N (rotate z+rotate d-rotate z) by simpa using rotate_period hd)

/-- At a fixed cutoff, an infinite component already forces the rank-two
condition; increasing the cutoff is not necessary for this implication. -/
theorem infinite_component_has_rank_two {C : ℤ} {N : ℕ} {z : GaussianInt}
    (hz : {w | (sieveGraph C N).Reachable z w}.Infinite) : HasRankTwoComponent C N := by
  obtain ⟨d,hd,hd0,hzd,hzrd⟩ := infinite_component_has_rotated_periods hz
  exact ⟨z,d,rotate d,hd,rotate_period hd,hzd,hzrd,by
    rw [det_rotate_self]; exact mt GaussianInt.norm_eq_zero.mp hd0⟩

lemma independent_of_one_rotation {d e : GaussianInt} (hd : d ≠ 0) (he : e ≠ 0) :
    det d e ≠ 0 ∨ det (rotate d) e ≠ 0 := by
  by_contra! hh
  have hid : (det d e)^2+(det (rotate d) e)^2 = d.norm*e.norm := by
    simp [det,rotate,gaussian_norm_sq]
    ring
  rw [hh.1,hh.2] at hid
  have hp := mul_pos (GaussianInt.norm_pos.mpr hd) (GaussianInt.norm_pos.mpr he)
  have hzero : d.norm*e.norm = 0 := by
    calc
      d.norm*e.norm = 0^2+0^2 := hid.symm
      _ = 0 := by norm_num
  exact hp.ne' hzero

/-- A finite Gaussian sieve has at most one infinite Rips component. -/
theorem infinite_components_unique {C : ℤ} {N : ℕ} {z w : GaussianInt}
    (hz : {v | (sieveGraph C N).Reachable z v}.Infinite)
    (hw : {v | (sieveGraph C N).Reachable w v}.Infinite) :
    (sieveGraph C N).Reachable z w := by
  obtain ⟨d,hd,hd0,hzd,hzrd⟩ := infinite_component_has_rotated_periods hz
  obtain ⟨e,he,he0,hwe⟩ := nonzero_period_of_infinite hw
  rcases independent_of_one_rotation hd0 he0 with hh | hh
  · exact independent_periods_join hd he hzd hwe hh
  · exact independent_periods_join (rotate_period hd) he hzrd hwe hh

/-- The unique infinite component is invariant under every sieve period,
not just under the period initially detected by a wrapping walk. -/
theorem infinite_component_reaches_all_periods {C : ℤ} {N : ℕ} {z : GaussianInt}
    (hz : {v | (sieveGraph C N).Reachable z v}.Infinite)
    (d : GaussianInt) (hd : IsPeriod N d) :
    (sieveGraph C N).Reachable z (z+d) :=
  infinite_components_unique hz (infinite_component_add_period hz hd)

/-- One specified nonzero period suffices to test infinitude of a component. -/
theorem infinite_iff_reachable_given_period (C : ℤ) (N : ℕ) (z d : GaussianInt)
    (hd : IsPeriod N d) (hd0 : d ≠ 0) :
    {v | (sieveGraph C N).Reachable z v}.Infinite ↔
      (sieveGraph C N).Reachable z (z+d) := by
  refine ⟨fun hz => infinite_component_reaches_all_periods hz d hd,fun hr => ?_⟩
  have hinj : Function.Injective (fun n : ℕ => z+(n : GaussianInt)*d) := by
    intro i j hij
    exact Nat.cast_injective (mul_right_cancel₀ hd0 (add_left_cancel hij))
  apply (Set.infinite_range_of_injective hinj).mono
  rintro v ⟨n,rfl⟩
  simpa only [add_sub_cancel_left] using reachable_multiples_of_period hr
    (show IsPeriod N (z+d-z) by simpa using hd) n

/-- At a fixed cutoff the ordinary sieve-ray and rank-two tests coincide. -/
theorem sieve_ray_iff_rank_two (C : ℤ) (N : ℕ) :
    HasSieveRay C N ↔ HasRankTwoComponent C N := by
  constructor
  · intro h
    obtain ⟨z,hz⟩ := (sieve_ray_iff_infinite_component C N).mp h
    exact infinite_component_has_rank_two hz
  · rintro ⟨z,d,e,hd,he,hrd,hre,hdet⟩
    have hd0 : d ≠ 0 := by intro h; apply hdet; simp [h,det]
    exact (sieve_ray_iff_infinite_component C N).mpr
      ⟨z,(infinite_iff_reachable_given_period C N z d hd hd0).mpr hrd⟩

#print axioms infinite_component_reaches_all_periods
#print axioms infinite_iff_reachable_given_period
#print axioms sieve_ray_iff_rank_two
#print axioms infinite_component_has_rank_two
#print axioms infinite_components_unique
end Erdos952Investigation.SieveInfiniteUniqueness
