import Submission.QuadraticCountMomentObstruction
import Submission.PhaseUnionBennett
import Submission.IncrementCountConsequences

/-! Large new primes change every interval survivor count by at most their
number. Padding transfers an exact-cardinality high-moment bound to a
budget-uniform one, which the preceding file disproves. -/
namespace Erdos970.GapAverages
open Finset Real Erdos970.Resampling

lemma population_large_deletion_budget (S R : Finset ℕ) (m : ℕ)
    (hS : S ⊆ range m) (hR : ∀ p ∈ R, m ≤ p) (s : Phase R) :
    S.card ≤ (populationSurvivors S R s).card + R.card := by
  classical
  let U := populationSurvivors S R s
  let A (p : R) := S.filter (fun x => x % p.val = (s p).val)
  have hA (p : R) : (A p).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    obtain ⟨hxS,hx⟩ := mem_filter.mp hx
    obtain ⟨hyS,hy⟩ := mem_filter.mp hy
    have hxp : x < p.val := (mem_range.mp (hS hxS)).trans_le (hR p.val p.property)
    have hyp : y < p.val := (mem_range.mp (hS hyS)).trans_le (hR p.val p.property)
    rw [Nat.mod_eq_of_lt hxp] at hx
    rw [Nat.mod_eq_of_lt hyp] at hy
    exact hx.trans hy.symm
  have hsub : S \ U ⊆ (univ : Finset R).biUnion A := by
    intro x hx
    obtain ⟨hxS,hxU⟩ := mem_sdiff.mp hx
    have hex : ∃ p : R, x % p.val = (s p).val := by
      by_contra hh
      push_neg at hh
      exact hxU (mem_filter.mpr ⟨hxS,hh⟩)
    obtain ⟨p,hp⟩ := hex
    exact mem_biUnion.mpr ⟨p,mem_univ p,mem_filter.mpr ⟨hxS,hp⟩⟩
  have hu : U ⊆ S := filter_subset _ _
  have hc := (card_le_card hsub).trans (card_biUnion_le)
  have hs := sum_le_sum (s := (univ : Finset R)) (fun p _ => hA p)
  simp only [sum_const, card_univ, Fintype.card_coe, smul_eq_mul, mul_one] at hs
  rw [card_sdiff_of_subset hu] at hc
  have huc := card_le_card hu
  dsimp only [U] at hc huc
  omega

lemma joined_count_bounds (P R : Finset ℕ) (hdis : Disjoint P R)
    (m : ℕ) (hR : ∀ p ∈ R, m ≤ p) (r : Phase P) (s : Phase R) :
    intervalCount (P ∪ R) m (joinPhase P R r s) ≤ intervalCount P m r ∧
    intervalCount P m r ≤ intervalCount (P ∪ R) m (joinPhase P R r s) + R.card := by
  let S := populationSurvivors (range m) P r
  have hsub : S ⊆ range m := filter_subset _ _
  have hb := population_large_deletion_budget S R m hsub hR s
  have hc := card_le_card (show populationSurvivors S R s ⊆ S from filter_subset _ _)
  have he : (populationSurvivors S R s).card =
      (populationSurvivors (range m) (P ∪ R) (joinPhase P R r s)).card := by
    rw [populationSurvivors_union _ _ _ hdis]
  have hS : (S.card : ℝ) = intervalCount P m r := populationSurvivors_card (range m) P r
  have hT : ((populationSurvivors S R s).card : ℝ) =
      intervalCount (P ∪ R) m (joinPhase P R r s) := by
    rw [he, populationSurvivors_card]
    rfl
  constructor
  · have hh : ((populationSurvivors S R s).card : ℝ) ≤ S.card := by exact_mod_cast hc
    rwa [hS,hT] at hh
  · have hh : (S.card : ℝ) ≤ (populationSurvivors S R s).card + (R.card : ℝ) := by exact_mod_cast hb
    rwa [hS,hT] at hh

lemma joined_mean_bounds (P R : Finset ℕ) (hdis : Disjoint P R)
    (hP : ∀ p ∈ P, p.Prime) (hRprime : ∀ p ∈ R, p.Prime)
    (m : ℕ) (hR : ∀ p ∈ R, m ≤ p) :
    (m : ℝ)*density (P ∪ R) ≤ m*density P ∧
    (m : ℝ)*density P ≤ m*density (P ∪ R)+R.card := by
  have hPR : ∀ p ∈ P ∪ R, p.Prime := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact hP p hp
    · exact hRprime p hp
  have hmean := phaseMean_union P R hdis (intervalCount (P ∪ R) m)
  rw [phaseMean_count (P ∪ R) hPR] at hmean
  constructor
  · have hh := phaseMean_mono P (fun r => phaseMean_mono R
        (fun s => (joined_count_bounds P R hdis m hR r s).1))
    simp_rw [phaseMean_const R hRprime] at hh
    rw [phaseMean_count P hP, ← hmean] at hh
    exact hh
  · have hh := phaseMean_mono P (fun r => phaseMean_mono R
        (fun s => (joined_count_bounds P R hdis m hR r s).2))
    simp_rw [phaseMean_const R hRprime, phaseMean_add, phaseMean_const R hRprime] at hh
    rw [phaseMean_count P hP, phaseMean_const P hP, ← hmean] at hh
    exact hh

lemma joined_centered_abs_le (P R : Finset ℕ) (hdis : Disjoint P R)
    (hP : ∀ p ∈ P, p.Prime) (hRprime : ∀ p ∈ R, p.Prime)
    (m : ℕ) (hR : ∀ p ∈ R, m ≤ p) (r : Phase P) (s : Phase R) :
    |intervalCount P m r-(m : ℝ)*density P| ≤
      |intervalCount (P ∪ R) m (joinPhase P R r s)-(m : ℝ)*density (P ∪ R)| + R.card := by
  have hcount := joined_count_bounds P R hdis m hR r s
  have hmean := joined_mean_bounds P R hdis hP hRprime m hR
  have hd : |(intervalCount P m r-(m : ℝ)*density P) -
      (intervalCount (P ∪ R) m (joinPhase P R r s)-(m : ℝ)*density (P ∪ R))| ≤ R.card := by
    rw [abs_le]
    constructor <;> linarith only [hcount.1,hcount.2,hmean.1,hmean.2]
  have hh := abs_sub_le (intervalCount P m r-(m : ℝ)*density P)
    (intervalCount (P ∪ R) m (joinPhase P R r s)-(m : ℝ)*density (P ∪ R)) 0
  simpa only [sub_zero] using hh.trans (add_le_add hd le_rfl) |>.trans_eq (add_comm _ _)

lemma two_power_sum_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a+b)^n ≤ (2 : ℝ)^n*(a^n+b^n) := by
  have hab : a+b ≤ 2*max a b := by have := le_max_left a b; have := le_max_right a b; linarith
  have hh := pow_le_pow_left₀ (add_nonneg ha hb) hab n
  rw [mul_pow] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left (pow_nonneg ha n)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right (pow_nonneg hb n)

lemma centered_moment_padding (P R : Finset ℕ) (hdis : Disjoint P R)
    (hP : ∀ p ∈ P, p.Prime) (hRprime : ∀ p ∈ R, p.Prime)
    (m d : ℕ) (hR : ∀ p ∈ R, m ≤ p) :
    phaseMean P (fun r => |intervalCount P m r-(m : ℝ)*density P|^d) ≤
      (2 : ℝ)^d*(phaseMean (P ∪ R)
        (fun r => |intervalCount (P ∪ R) m r-(m : ℝ)*density (P ∪ R)|^d) + (R.card : ℝ)^d) := by
  have hpoint (r : Phase P) (s : Phase R) :
      |intervalCount P m r-(m : ℝ)*density P|^d ≤
        (2 : ℝ)^d*(|intervalCount (P ∪ R) m (joinPhase P R r s)-
          (m : ℝ)*density (P ∪ R)|^d + (R.card : ℝ)^d) := by
    exact (pow_le_pow_left₀ (abs_nonneg _) (joined_centered_abs_le P R hdis hP hRprime m hR r s) d).trans
      (two_power_sum_bound _ _ (abs_nonneg _) (Nat.cast_nonneg _) d)
  have hh := phaseMean_mono P (fun r => phaseMean_mono R (fun s => hpoint r s))
  simp_rw [phaseMean_const R hRprime, phaseMean_mul, phaseMean_add, phaseMean_const R hRprime] at hh
  rw [phaseMean_const P hP, ← phaseMean_union P R hdis
    (fun r => |intervalCount (P ∪ R) m r-(m : ℝ)*density (P ∪ R)|^d)] at hh
  exact hh

/-- The moment order now uses the ACTUAL cardinality, not a larger budget. -/
def UniformExactQuadraticCountMoment (C : ℝ) : Prop :=
  ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → 0 < P.card →
    ∀ m : ℕ, P.card^2 ≤ m →
      phaseMean P (fun r => |intervalCount P m r-(m : ℝ)*density P|^(2*P.card)) ≤
        (C*(P.card : ℝ)*m)^P.card

/-- Large-prime padding transfers exact-cardinality control to every smaller
core, at the same moment order and length, with only an absolute constant loss. -/
theorem exact_count_moment_to_budget (C : ℝ) (hC : 1 ≤ C)
    (hM : UniformExactQuadraticCountMoment C) : UniformQuadraticCountMoment (8*C) := by
  intro k hk P hP hPk m hkm
  obtain ⟨R,hRc,hdis,hR⟩ := IncrementReduction.exists_prime_set_above P m (k-P.card)
  have hRprime : ∀ p ∈ R, p.Prime := fun p hp => (hR p hp).1
  have hRlarge : ∀ p ∈ R, m ≤ p := fun p hp => (hR p hp).2.1
  have hPR : ∀ p ∈ P ∪ R, p.Prime := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact hP p hp
    · exact hRprime p hp
  have hcard : (P ∪ R).card = k := by rw [card_union_of_disjoint hdis,hRc]; omega
  have hm := hM (P ∪ R) hPR (by rwa [hcard]) m (by rwa [hcard])
  rw [hcard] at hm
  have hpad := centered_moment_padding P R hdis hP hRprime m (2*k) hRlarge
  have hRk : (R.card : ℝ) ≤ k := by rw [hRc]; exact_mod_cast Nat.sub_le k P.card
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hmk : (k : ℝ) ≤ m := by
    have hkk : k ≤ k^2 := Nat.le_self_pow (by omega : 2 ≠ 0) k
    exact_mod_cast hkk.trans hkm
  have hb : (R.card : ℝ)^2 ≤ C*(k : ℝ)*m := by
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg R.card) hRk 2
    have hkm' := mul_le_mul_of_nonneg_left hmk (Nat.cast_nonneg k)
    have hc := mul_le_mul_of_nonneg_right hC (show 0 ≤ (k : ℝ)*m by positivity)
    nlinarith only [hsq,hkm',hc]
  have hp : (R.card : ℝ)^(2*k) ≤ (C*(k : ℝ)*m)^k := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg _) hb k
  have hh := hpad.trans (mul_le_mul_of_nonneg_left (add_le_add hm hp) (by positivity))
  have htwo : (2 : ℝ) ≤ 2^k := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
  apply hh.trans
  calc
    (2 : ℝ)^(2*k)*((C*(k : ℝ)*m)^k+(C*(k : ℝ)*m)^k) =
        2*((4 : ℝ)*(C*(k : ℝ)*m))^k := by rw [pow_mul, mul_pow]; norm_num; ring
    _ ≤ (2 : ℝ)^k*((4 : ℝ)*(C*(k : ℝ)*m))^k :=
      mul_le_mul_of_nonneg_right htwo (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

/-- The full-centred Gaussian-shaped estimate fails even at order twice the
actual prime cardinality. The right side is still the more lenient density-free
one. This is not a statement about a truncated low-tail moment. -/
theorem not_uniformExactQuadraticCountMoment (C : ℝ) :
    ¬UniformExactQuadraticCountMoment C := by
  intro hM
  have hC0 : 0 ≤ C := by
    have hh := hM {2} (by norm_num) (by simp) 1 (by simp)
    simp only [Nat.cast_one] at hh
    have hn : 0 ≤ phaseMean {2}
        (fun r => |intervalCount {2} 1 r-(1 : ℝ)*density {2}|^(2*({2} : Finset ℕ).card)) := by
      unfold phaseMean
      positivity
    have hc := hn.trans hh
    simpa only [card_singleton, Nat.cast_one, mul_one, pow_one] using hc
  let D := max C 1
  have hD : 1 ≤ D := le_max_right _ _
  have hMD : UniformExactQuadraticCountMoment D := by
    intro P hP hk m hm
    exact (hM P hP hk m hm).trans (pow_le_pow_left₀ (by positivity)
      (by dsimp [D]; gcongr; exact le_max_left C 1) P.card)
  exact not_uniformQuadraticCountMoment (8*D) (exact_count_moment_to_budget D hD hMD)

#print axioms centered_moment_padding
#print axioms exact_count_moment_to_budget
#print axioms not_uniformExactQuadraticCountMoment
end Erdos970.GapAverages
