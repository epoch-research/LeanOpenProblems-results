import Submission.PrimeFactorLocalMinima
import Submission.PrimeLoserWeightedRelativeCancellation

/-! Strict local minima supply opposite-sign loser incidences. Combined with
weighted Cauchy--Schwarz, this gives a genuine positive lower bound on the
weighted opposite-sign fraction, but not the conjectured limit one half. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma primeLocalMinima_incidence_data (N n : ℕ) (hn : n ∈ primeLocalMinima N) :
    (n-1 ∈ bothAboveSet 0 N ∧ n ∈ bothAboveSet 0 N) ∧
      primeLoser (n-1)=Nat.maxPrimeFac n ∧ primeLoser n=Nat.maxPrimeFac n ∧
      factorSign (n-1)= -1 ∧ factorSign n=1 := by
  obtain ⟨hnN,hnpos,hprev,hnext⟩ := mem_filter.mp hn
  have hsub : n-1+1=n := Nat.sub_add_cancel hnpos
  have hp : 0<Nat.maxPrimeFac n := maxPrimeFac_pos_of_pos n hnpos
  have hnot : ¬Nat.maxPrimeFac (n-1)<Nat.maxPrimeFac (n-1+1) := by
    rw [hsub]
    exact hprev.not_gt
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_⟩
  · exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hnN; omega),
      hp.trans hprev,by simpa only [hsub] using hp⟩
  · exact mem_filter.mpr ⟨hnN,hp,hp.trans hnext⟩
  · simp only [primeLoser,hsub,min_eq_right hprev.le]
  · simp only [primeLoser,min_eq_left hnext.le]
  · simp only [factorSign,predicateSign,hnot,if_false]
  · simp only [factorSign,predicateSign,hnext,if_true]

/-- Pair the fall into one local minimum with the rise out of another
minimum having the same prime label. The resulting opposite-sign ordered
collision retains that prime as its weight. -/
lemma localMinima_pair_maps_to_opposite (B N : ℕ) :
    ∀ nm ∈ ((primeLocalMinimaAbove B N) ×ˢ (primeLocalMinimaAbove B N)).filter
      (fun nm => Nat.maxPrimeFac nm.1=Nat.maxPrimeFac nm.2),
      (nm.1-1,nm.2) ∈ primeLoserOppositeCollisions 0 N := by
  intro nm hnm
  obtain ⟨hnm,he⟩ := mem_filter.mp hnm
  obtain ⟨hn,hm⟩ := mem_product.mp hnm
  have hnmin := (mem_filter.mp hn).1
  have hmmin := (mem_filter.mp hm).1
  have hd := primeLocalMinima_incidence_data N nm.1 hnmin
  have hd' := primeLocalMinima_incidence_data N nm.2 hmmin
  have hsign : factorSign (nm.1-1)≠factorSign nm.2 := by rw [hd.2.2.2.1,hd'.2.2.2.2]; norm_num
  have hne : nm.1-1≠nm.2 := fun h => hsign (congrArg factorSign h)
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_offDiag.mpr ⟨hd.1.1,hd'.1.2,hne⟩,
    by simpa only [hd.2.1,hd'.2.2.1] using he⟩,hsign⟩

lemma localMinima_pair_map_injective (B N : ℕ) :
    Set.InjOn (fun nm : ℕ × ℕ => (nm.1-1,nm.2))
      (((primeLocalMinimaAbove B N) ×ˢ (primeLocalMinimaAbove B N)).filter
        (fun nm => Nat.maxPrimeFac nm.1=Nat.maxPrimeFac nm.2)) := by
  intro nm hnm uv huv he
  have hn := (mem_filter.mp (mem_filter.mp (mem_product.mp (mem_filter.mp hnm).1).1).1).2.1
  have hu := (mem_filter.mp (mem_filter.mp (mem_product.mp (mem_filter.mp huv).1).1).1).2.1
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  apply Prod.ext <;> dsimp only at h1 h2 ⊢ <;> omega

lemma localMinima_weighted_same_pair_sum_le_opposite (B N : ℕ) :
    (∑ nm ∈ ((primeLocalMinimaAbove B N) ×ˢ (primeLocalMinimaAbove B N)).filter
      (fun nm => Nat.maxPrimeFac nm.1=Nat.maxPrimeFac nm.2), (Nat.maxPrimeFac nm.1 : ℝ)) ≤
        primeLoserWeightedOppositeMass N := by
  let U := ((primeLocalMinimaAbove B N) ×ˢ (primeLocalMinimaAbove B N)).filter
    (fun nm => Nat.maxPrimeFac nm.1=Nat.maxPrimeFac nm.2)
  let f := fun nm : ℕ × ℕ => (nm.1-1,nm.2)
  have hi : Set.InjOn f U := localMinima_pair_map_injective B N
  have hsub : U.image f ⊆ primeLoserOppositeCollisions 0 N := by
    intro nm hnm
    obtain ⟨uv,huv,rfl⟩ := mem_image.mp hnm
    exact localMinima_pair_maps_to_opposite B N uv huv
  have he : (∑ nm ∈ U, (Nat.maxPrimeFac nm.1 : ℝ)) =
      ∑ nm ∈ U.image f, (primeLoser nm.1 : ℝ) := by
    rw [sum_image hi]
    apply sum_congr rfl
    intro nm hnm
    have hn := (mem_filter.mp (mem_product.mp (mem_filter.mp hnm).1).1).1
    have hd := primeLocalMinima_incidence_data N nm.1 hn
    simp only [f,hd.2.1]
  rw [he]
  exact sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)

/-- Weighted Cauchy--Schwarz: local minima on few reciprocal prime labels
force positive opposite-sign collision mass. -/
theorem primeLocalMinimaAbove_sq_le_weightedOpposite (B N : ℕ) :
    ((primeLocalMinimaAbove B N).card : ℝ)^2 ≤
      (∑ p ∈ (primeWinnerLabels N).filter (B < ·), (1 : ℝ)/p)*
        primeLoserWeightedOppositeMass N := by
  let S := primeLocalMinimaAbove B N
  let T := (primeWinnerLabels N).filter (B < ·)
  let d (p : ℕ) := (S.filter fun n => Nat.maxPrimeFac n=p).card
  have hf : (S : Set ℕ).MapsTo Nat.maxPrimeFac T := by
    intro n hn
    change n ∈ (primeLocalMinima N).filter (fun n => B<Nat.maxPrimeFac n) at hn
    obtain ⟨hnmin,hpn⟩ := mem_filter.mp hn
    obtain ⟨hnN,hnpos,_,_⟩ := mem_filter.mp hnmin
    exact mem_filter.mpr ⟨primeWinnerLabels_mono (mem_range.mp hnN).le
      (maxPrimeFac_mem_labels_of_pos n (maxPrimeFac_pos_of_pos n hnpos)),hpn⟩
  have hsum : (∑ p ∈ T, (d p : ℝ))=S.card := by
    exact_mod_cast (card_eq_sum_card_fiberwise hf).symm
  have hsq : (∑ p ∈ T, (p : ℝ)*(d p : ℝ)^2) ≤ primeLoserWeightedOppositeMass N := by
    have he := label_weighted_fiber_square_sum S T Nat.maxPrimeFac
      (fun _ => (1 : ℝ)) (fun p => (p : ℝ)) (fun n hn => hf hn)
    simp only [sum_const,nsmul_eq_mul,mul_one] at he
    rw [he]
    exact localMinima_weighted_same_pair_sum_le_opposite B N
  have hcs := sum_sq_le_sum_mul_sum_of_sq_eq_mul T
    (r := fun p => (d p : ℝ)) (f := fun p => (1 : ℝ)/p)
    (g := fun p => (p : ℝ)*(d p : ℝ)^2)
    (by intros; positivity) (by intros; positivity) (fun p hp => by
      have hp0 : (p : ℝ)≠0 := by exact_mod_cast
        (primeWinnerLabel_pos N p (mem_filter.mp hp).1).ne'
      dsimp only
      field_simp)
  rw [hsum] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left hsq (by positivity))

/-- There is genuinely positive quadratic opposite-sign collision mass in
the actual largest-prime-factor sequence. This is not the sharp half bound. -/
theorem primeLoserWeightedOppositeMass_positive_quadratic :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop,
      c*(N : ℝ)^2 ≤ primeLoserWeightedOppositeMass N := by
  obtain ⟨u,c,hu,hc,hmass⟩ := primeLocalMinimaAbove_power_positive_mass
  refine ⟨u*c^2/2,by positivity,?_⟩
  filter_upwards [hmass,eventually_ge_atTop (4 : ℕ)] with N hm hN
  have hN0 : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hmass' := (le_div_iff₀ hN0).mp hm
  have hsq : c^2*(N : ℝ)^2 ≤ ((primeLocalMinimaAbove (ceilPowerCutoff u N) N).card : ℝ)^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hmass' 2
  have hO : 0≤primeLoserWeightedOppositeMass N := by unfold primeLoserWeightedOppositeMass; positivity
  have hraw := hsq.trans ((primeLocalMinimaAbove_sq_le_weightedOpposite (ceilPowerCutoff u N) N).trans
    (mul_le_mul_of_nonneg_right (high_primeWinnerLabels_reciprocal_bound u hu N hN) hO))
  have hh := mul_le_mul_of_nonneg_left hraw hu.le
  have hid : u*((2/u)*primeLoserWeightedOppositeMass N)=2*primeLoserWeightedOppositeMass N := by field_simp
  rw [hid] at hh
  nlinarith

/-- A positive lower bound for the actual weighted opposite-sign fraction.
The value one half would suffice for Erdős 371, but is not obtained here. -/
theorem primeLoserWeightedOppositeRatio_positive_lower :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop,
      c≤primeLoserWeightedOppositeRatio N := by
  obtain ⟨c,hc,hO⟩ := primeLoserWeightedOppositeMass_positive_quadratic
  refine ⟨c/2,by positivity,?_⟩
  filter_upwards [hO,primeLoserWeightedCollisionMass_eventually_lower,
    eventually_gt_atTop (0 : ℕ)] with N hON hQN hN
  have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
  have hQ0 : 0<primeLoserWeightedCollisionMass N := lt_of_lt_of_le (by positivity) hQN
  unfold primeLoserWeightedOppositeRatio
  apply (le_div_iff₀ hQ0).mpr
  have hh := mul_le_mul_of_nonneg_left (primeLoserWeightedCollisionMass_bound N) hc.le
  nlinarith

#print axioms primeLocalMinimaAbove_sq_le_weightedOpposite
#print axioms primeLoserWeightedOppositeMass_positive_quadratic
#print axioms primeLoserWeightedOppositeRatio_positive_lower
end Erdos371
