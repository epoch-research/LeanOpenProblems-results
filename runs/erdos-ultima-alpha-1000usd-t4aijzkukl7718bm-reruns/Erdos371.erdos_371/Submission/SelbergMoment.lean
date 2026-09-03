import FormalConjecturesUtil
import Submission.FiniteSelberg

/-! First-moment truncation of the optimal finite Selberg weights. -/

namespace Erdos371SelbergMoment

open Finset Erdos371FiniteSelberg

variable {ι : Type*} [DecidableEq ι]
attribute [local instance] Classical.propDecidable

noncomputable def mass (ν : ι → ℝ) (s : Finset ι) : ℝ := ∑ t ∈ s.powerset, oddsProd ν t
noncomputable def moment (ν l : ι → ℝ) (s : Finset ι) : ℝ :=
  ∑ t ∈ s.powerset, oddsProd ν t * ∑ p ∈ t, l p

lemma mass_product (ν : ι → ℝ) (s : Finset ι) :
    mass ν s = ∏ p ∈ s, (1+ν p/(1-ν p)) := by
  exact (prod_one_add s).symm

lemma mass_euler {ν : ι → ℝ} {s : Finset ι} (hν : ∀ p ∈ s, ν p < 1) :
    mass ν s * (∏ p ∈ s, (1-ν p)) = 1 := by
  rw [mass_product, ← prod_mul_distrib]
  apply prod_eq_one
  intro p hp
  have hh := (sub_pos.mpr (hν p hp)).ne'
  field_simp
  ring

lemma mass_pos {ν : ι → ℝ} {s : Finset ι}
    (hν : ∀ p ∈ s, 0 < ν p ∧ ν p < 1) : 0 < mass ν s := by
  apply sum_pos' (fun t ht => (oddsProd_pos (fun p hp => hν p (mem_powerset.mp ht hp))).le)
  exact ⟨∅, empty_mem_powerset _, by simp [oddsProd]⟩

lemma mass_insert (ν : ι → ℝ) {s : Finset ι} {p : ι} (hp : p ∉ s) :
    mass ν (insert p s) = (1+ν p/(1-ν p))*mass ν s := by
  simp only [mass_product, prod_insert hp]

lemma moment_insert (ν l : ι → ℝ) {s : Finset ι} {p : ι} (hp : p ∉ s) :
    moment ν l (insert p s) = moment ν l s +
      (ν p/(1-ν p))*(l p*mass ν s + moment ν l s) := by
  rw [moment, sum_powerset_insert hp]
  congr 1
  calc
    _ = ∑ t ∈ s.powerset, (ν p/(1-ν p))*oddsProd ν t*(l p+∑ q ∈ t, l q) := by
      apply sum_congr rfl
      intro t ht
      have hpt : p ∉ t := fun h => hp (mem_powerset.mp ht h)
      rw [oddsProd, prod_insert hpt, sum_insert hpt]
      rfl
    _ = ∑ t ∈ s.powerset, (((ν p/(1-ν p))*l p)*oddsProd ν t +
        (ν p/(1-ν p))*(oddsProd ν t*∑ q ∈ t, l q)) := by
      apply sum_congr rfl
      intro t ht
      ring
    _ = _ := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      dsimp [mass, moment]
      ring

lemma moment_identity {ν : ι → ℝ} (l : ι → ℝ) {s : Finset ι}
    (hν : ∀ p ∈ s, ν p < 1) :
    moment ν l s = mass ν s * ∑ p ∈ s, ν p*l p := by
  induction s using Finset.induction_on with
  | empty => simp [moment]
  | @insert p s hp ih =>
    have hps := hν p (mem_insert_self _ _)
    have hss : ∀ q ∈ s, ν q < 1 := fun q hq => hν q (mem_insert_of_mem hq)
    rw [moment_insert ν l hp, mass_insert ν hp, sum_insert hp, ih hss]
    have hn := (sub_pos.mpr hps).ne'
    field_simp
    ring

noncomputable def truncated (s : Finset ι) (q : ι → ℝ) (z : ℝ) : Finset (Finset ι) :=
  s.powerset.filter fun t => (∏ p ∈ t, q p) ≤ z
noncomputable def truncatedMass (ν q : ι → ℝ) (s : Finset ι) (z : ℝ) : ℝ :=
  ∑ t ∈ truncated s q z, oddsProd ν t

/-- Restricting to products at most `z` keeps at least half the total mass,
provided `log z` is at least twice its logarithmic first moment. -/
theorem truncatedMass_lower {ν q : ι → ℝ} {s : Finset ι}
    (hν : ∀ p ∈ s, 0 < ν p ∧ ν p < 1)
    (hq : ∀ p ∈ s, 1 ≤ q p) {z : ℝ} (hz : 1 < z)
    (hlarge : 2*(∑ p ∈ s, ν p * Real.log (q p)) ≤ Real.log z) :
    mass ν s / 2 ≤ truncatedMass ν q s z := by
  let U := s.powerset.filter fun t => ¬(∏ p ∈ t, q p) ≤ z
  let tail := ∑ t ∈ U, oddsProd ν t
  have hlog := Real.log_pos hz
  have htotal : truncatedMass ν q s z + tail = mass ν s := by
    exact sum_filter_add_sum_filter_not _ _ _
  have hw (t : Finset ι) (ht : t ⊆ s) : 0 ≤ oddsProd ν t :=
    (oddsProd_pos (fun p hp => hν p (ht hp))).le
  have hq0 (p : ι) (hp : p ∈ s) : 0 < q p := lt_of_lt_of_le zero_lt_one (hq p hp)
  have hterm (t : Finset ι) (ht : t ⊆ s) : 0 ≤ ∑ p ∈ t, Real.log (q p) :=
    sum_nonneg (fun p hp => Real.log_nonneg (hq p (ht hp)))
  have htail : tail * Real.log z ≤ moment ν (fun p => Real.log (q p)) s := by
    calc
      _ ≤ ∑ t ∈ U, oddsProd ν t * ∑ p ∈ t, Real.log (q p) := by
        rw [show tail = ∑ t ∈ U, oddsProd ν t from rfl, sum_mul]
        apply sum_le_sum
        intro t ht
        obtain ⟨hts, htz⟩ := mem_filter.mp ht
        have hts := mem_powerset.mp hts
        apply mul_le_mul_of_nonneg_left _ (hw t hts)
        rw [← Real.log_prod (fun p hp => (hq0 p (hts hp)).ne')]
        exact Real.log_le_log (lt_trans zero_lt_one hz) (not_le.mp htz).le
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun t ht _ => mul_nonneg (hw t (mem_powerset.mp ht)) (hterm t (mem_powerset.mp ht)))
  rw [moment_identity _ (fun p hp => (hν p hp).2)] at htail
  have hm := (mass_pos hν).le
  have hh := mul_le_mul_of_nonneg_left hlarge hm
  nlinarith

lemma inverse_truncatedMass_bound {ν q : ι → ℝ} {s : Finset ι}
    (hν : ∀ p ∈ s, 0 < ν p ∧ ν p < 1)
    (hq : ∀ p ∈ s, 1 ≤ q p) {z : ℝ} (hz : 1 < z)
    (hlarge : 2*(∑ p ∈ s, ν p * Real.log (q p)) ≤ Real.log z) :
    0 < truncatedMass ν q s z ∧
      1/truncatedMass ν q s z ≤ 2*(∏ p ∈ s, (1-ν p)) := by
  have hG := truncatedMass_lower hν hq hz hlarge
  have hm := mass_pos hν
  have hpos : 0 < truncatedMass ν q s z := lt_of_lt_of_le (by positivity) hG
  refine ⟨hpos, (div_le_iff₀ hpos).mpr ?_⟩
  have he := mass_euler (fun p hp => (hν p hp).2)
  have he0 : 0 ≤ ∏ p ∈ s, (1-ν p) := prod_nonneg (fun p hp => sub_nonneg.mpr (hν p hp).2.le)
  have hh := mul_le_mul_of_nonneg_right hG he0
  nlinarith

/-- A finite Selberg bound with a logarithmically truncated family. -/
theorem selberg_euler_upper {α : Type*} [DecidableEq α]
    (A : Finset α) (s : Finset ι) (b : ι → α → Prop)
    (ν ρ q : ι → ℝ) (hν : ∀ p ∈ s, 0 < ν p ∧ ν p < 1)
    (hρ : ∀ p ∈ s, 1 ≤ ρ p) (hq : ∀ p ∈ s, 2 ≤ q p)
    (heq : ∀ p ∈ s, ρ p/ν p=q p) (X : ℝ) (hX : 0 ≤ X)
    (hE : ∀ d ⊆ s, |Erdos371FiniteBrun.jointCount A b d-X*nuProd ν d| ≤ ∏ p ∈ d, ρ p)
    {z : ℝ} (hz : 1 < z) (hlarge : 2*(∑ p ∈ s, ν p * Real.log (q p)) ≤ Real.log z) :
    (Erdos371FiniteBrun.survivors A s b).card ≤ 2*X*(∏ p ∈ s, (1-ν p))+z^4 := by
  have hG := inverse_truncatedMass_bound hν (fun p hp => (hq p hp).trans' (by norm_num)) hz hlarge
  have hT (t : Finset ι) (ht : t ∈ truncated s q z) : t ⊆ s :=
    mem_powerset.mp (mem_filter.mp ht).1
  have hb := selberg_upper A s b ν hν (truncated s q z) hT hG.1 X (z^4) (by
    intro t ht u hu
    exact pair_error_modulus_bound (hT t ht) (hT u hu) ν ρ q
      (fun p hp => (hν p hp).1) hρ hq heq _ X hE (mem_filter.mp ht).2 (mem_filter.mp hu).2)
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hG.2 hX
  dsimp [truncatedMass] at hh
  rw [mul_one_div] at hh
  nlinarith

end Erdos371SelbergMoment

#print axioms Erdos371SelbergMoment.inverse_truncatedMass_bound

#print axioms Erdos371SelbergMoment.selberg_euler_upper
