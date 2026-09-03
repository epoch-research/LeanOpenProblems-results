import FormalConjecturesUtil
import Submission.RestrictedMoments

/-! Spreading the finite moment obstruction over many scales. The marginals
in this file are explicitly defined model marginals, not a claimed law of
largest prime factors. In particular this is not a disproof of Erdős 371. -/

namespace Erdos371DiffuseMomentObstruction


abbrev State (L : ℕ) := Erdos371RestrictedMoments.State × Fin L

def atom (L : ℕ) (t : Fin L) : ℕ := 10*L + t.val

def tail (L : ℕ) (t : Fin L) : ℕ := 5*(L-t.val)

def parts {L : ℕ} (i : State L) : List ℕ :=
  (Erdos371RestrictedMoments.parts i.1).map (fun k => k * atom L i.2) ++ [tail L i.2]

def value {L : ℕ} (i : State L) : ℕ := Erdos371RestrictedMoments.largest i.1 * atom L i.2

def weight {L : ℕ} (i j : State L) : ℤ := Erdos371RestrictedMoments.weight i.1 j.1

def base {L : ℕ} (i : State L) : ℤ := Erdos371RestrictedMoments.base i.1

def cmp (a b : ℕ) : ℤ := if a > b then 1 else if a < b then -1 else 0

lemma cmp_antisymm (a b : ℕ) : cmp a b = -cmp b a := by
  unfold cmp
  split_ifs <;> omega

lemma largest_bounds (i : Erdos371RestrictedMoments.State) : 1 ≤ Erdos371RestrictedMoments.largest i ∧ Erdos371RestrictedMoments.largest i ≤ 5 := by
  revert i
  decide +kernel

lemma parts_mass {L : ℕ} (i : State L) : (parts i).sum = 55*L := by
  have ht := i.2.isLt
  have hm := Erdos371RestrictedMoments.states_have_mass_five i.1
  have he : ((Erdos371RestrictedMoments.parts i.1).map (fun k => k * atom L i.2)).sum =
      (Erdos371RestrictedMoments.parts i.1).sum * atom L i.2 := by
    simpa using List.sum_map_mul_right (Erdos371RestrictedMoments.parts i.1) id (atom L i.2)
  simp only [parts, List.sum_append, List.sum_cons, List.sum_nil, add_zero, he, hm]
  unfold atom tail
  omega

lemma value_is_largest {L : ℕ} (i : State L) : (parts i).foldr max 0 = value i := by
  obtain ⟨i,t⟩ := i
  have ht := t.isLt
  have hL : 0 < L := by omega
  fin_cases i <;> simp [parts, Erdos371RestrictedMoments.parts, value, Erdos371RestrictedMoments.largest, atom, tail] <;> omega

lemma weight_nonneg {L : ℕ} (i j : State L) : 0 ≤ weight i j := Erdos371RestrictedMoments.weight_nonneg _ _

lemma value_lt_of_largest_lt {L : ℕ} (i j : State L)
    (h : Erdos371RestrictedMoments.largest i.1 < Erdos371RestrictedMoments.largest j.1) : value i < value j := by
  have hi := largest_bounds i.1
  have hj := largest_bounds j.1
  have ht := i.2.isLt
  have hs := j.2.isLt
  have hL : 0 < L := by omega
  have hib : Erdos371RestrictedMoments.largest i.1 * i.2.val < 5*L := by nlinarith
  have hjb : 0 ≤ Erdos371RestrictedMoments.largest j.1 * j.2.val := Nat.zero_le _
  have hh : (Erdos371RestrictedMoments.largest i.1 + 1) * L ≤ Erdos371RestrictedMoments.largest j.1 * L :=
    Nat.mul_le_mul_right L h
  unfold value atom
  nlinarith

lemma value_eq_iff {L : ℕ} (i j : State L) :
    value i = value j ↔ Erdos371RestrictedMoments.largest i.1 = Erdos371RestrictedMoments.largest j.1 ∧ i.2 = j.2 := by
  constructor
  · intro he
    have h : Erdos371RestrictedMoments.largest i.1 = Erdos371RestrictedMoments.largest j.1 := by
      by_contra hh
      rcases lt_or_gt_of_ne hh with hh | hh
      · exact (value_lt_of_largest_lt i j hh).ne he
      · exact (value_lt_of_largest_lt j i hh).ne he.symm
    refine ⟨h, ?_⟩
    have hp := (largest_bounds j.1).1
    have hm : atom L i.2 = atom L j.2 := by
      apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < Erdos371RestrictedMoments.largest j.1)
      simpa only [value, h] using he
    apply Fin.ext
    unfold atom at hm
    omega
  · rintro ⟨h,ht⟩
    simp [value, h, ht]

lemma cmp_value_of_ne {L : ℕ} (i j : State L)
    (h : Erdos371RestrictedMoments.largest i.1 ≠ Erdos371RestrictedMoments.largest j.1) :
    cmp (value i) (value j) = cmp (Erdos371RestrictedMoments.largest i.1) (Erdos371RestrictedMoments.largest j.1) := by
  rcases lt_or_gt_of_ne h with h | h
  · have hh := value_lt_of_largest_lt i j h
    simp [cmp, h, hh, not_lt_of_ge h.le, not_lt_of_ge hh.le]
  · have hh := value_lt_of_largest_lt j i h
    simp [cmp, h, hh]

lemma sum_cmp_self {α : Type*} [Fintype α] (f : α → ℕ) :
    (∑ a : α, ∑ b : α, cmp (f a) (f b)) = 0 := by
  have hh : (∑ a : α, ∑ b : α, cmp (f a) (f b)) =
      -(∑ a : α, ∑ b : α, cmp (f a) (f b)) := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun b hb => cmp_antisymm _ _)
  omega

lemma scale_comparison_sum (L : ℕ) (i j : Erdos371RestrictedMoments.State) :
    (∑ t : Fin L, ∑ s : Fin L, cmp (value (i,t)) (value (j,s))) =
      (L:ℤ)^2 * cmp (Erdos371RestrictedMoments.largest i) (Erdos371RestrictedMoments.largest j) := by
  by_cases h : Erdos371RestrictedMoments.largest i = Erdos371RestrictedMoments.largest j
  · have he : ∀ t s : Fin L, cmp (value (i,t)) (value (j,s)) =
        cmp (Erdos371RestrictedMoments.largest i * atom L t) (Erdos371RestrictedMoments.largest i * atom L s) := by
      intro t s
      simp [value, h]
    simp_rw [he]
    rw [sum_cmp_self]
    simp [cmp, h]
  · have he (t s : Fin L) : cmp (value (i,t)) (value (j,s)) =
        cmp (Erdos371RestrictedMoments.largest i) (Erdos371RestrictedMoments.largest j) := cmp_value_of_ne (i,t) (j,s) h
    simp_rw [he]
    simp [pow_two, mul_assoc]

lemma total_weight (L : ℕ) :
    (∑ i : State L, ∑ j : State L, weight i j) = 14400*(L:ℤ)^2 := by
  simp only [Fintype.sum_prod_type, weight]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  rw [Erdos371RestrictedMoments.total_weight]
  ring

lemma signed_comparison (L : ℕ) :
    (∑ i : State L, ∑ j : State L, weight i j * cmp (value i) (value j)) =
      2*(L:ℤ)^2 := by
  simp only [Fintype.sum_prod_type]
  have he (i : Erdos371RestrictedMoments.State) :
      (∑ t : Fin L, ∑ j : Erdos371RestrictedMoments.State, ∑ s : Fin L,
        weight (i,t) (j,s) * cmp (value (i,t)) (value (j,s))) =
      ∑ j : Erdos371RestrictedMoments.State, Erdos371RestrictedMoments.weight i j * ((L:ℤ)^2 * cmp (Erdos371RestrictedMoments.largest i) (Erdos371RestrictedMoments.largest j)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [weight, ← Finset.mul_sum, scale_comparison_sum]
  simp_rw [he]
  have hc : (∑ i : Erdos371RestrictedMoments.State, ∑ j : Erdos371RestrictedMoments.State,
      Erdos371RestrictedMoments.weight i j * cmp (Erdos371RestrictedMoments.largest i) (Erdos371RestrictedMoments.largest j)) = 2 := Erdos371RestrictedMoments.largest_comparison_biased
  calc
    _ = (L:ℤ)^2 * (∑ i : Erdos371RestrictedMoments.State, ∑ j : Erdos371RestrictedMoments.State,
        Erdos371RestrictedMoments.weight i j * cmp (Erdos371RestrictedMoments.largest i) (Erdos371RestrictedMoments.largest j)) := by
      simp only [Finset.mul_sum]
      congr 1
      funext i
      congr 1
      funext j
      ring
    _ = _ := by rw [hc]; ring

lemma equal_marginals {L : ℕ} (i : State L) :
    (∑ j : State L, weight i j) = 120*L*base i ∧
    (∑ j : State L, weight j i) = 120*L*base i := by
  constructor
  · simp only [Fintype.sum_prod_type, weight, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    rw [(Erdos371RestrictedMoments.equal_marginals i.1).1]
    simp only [base]
    ring
  · simp only [Fintype.sum_prod_type, weight, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    rw [(Erdos371RestrictedMoments.equal_marginals i.1).2]
    simp only [base]
    ring

/-- A type-conditioned factorial-selection feature. The scale label is kept
explicit, so no claim of a prime-factor distribution is hidden in the notation. -/
def typedFeature {L : ℕ} (t : Fin L) (u : List ℕ) (i : State L) : ℤ :=
  if t = i.2 then Erdos371RestrictedMoments.feature u i.1 else 0

lemma selection_budget {L : ℕ} (t s : Fin L) (u v : List ℕ)
    (h : atom L t * u.sum + atom L s * v.sum ≤ 55*L) : u.sum + v.sum ≤ 5 := by
  have hL : 0 < L := Nat.pos_of_ne_zero (fun he => by have := t.isLt; omega)
  have ht : 10*L ≤ atom L t := by unfold atom; omega
  have hs : 10*L ≤ atom L s := by unfold atom; omega
  have htu := Nat.mul_le_mul_right u.sum ht
  have hsv := Nat.mul_le_mul_right v.sum hs
  by_contra hh
  have hm := Nat.mul_le_mul_left (10*L) (show 6 ≤ u.sum + v.sum by omega)
  nlinarith

lemma typed_feature_sum {L : ℕ} (t : Fin L) (u : List ℕ) :
    (∑ i : State L, base i * typedFeature t u i) =
      ∑ i : Erdos371RestrictedMoments.State,
        Erdos371RestrictedMoments.base i * Erdos371RestrictedMoments.feature u i := by
  simp [Fintype.sum_prod_type, base, typedFeature, mul_ite]

/-- The specified subcritical mixed selection moments are exactly those of
the independent model with the same marginals, at every scale count `L`. -/
theorem typed_subcritical_moments {L : ℕ} (t s : Fin L) (u v : List ℕ)
    (hu : u ∈ Erdos371RestrictedMoments.selections)
    (hv : v ∈ Erdos371RestrictedMoments.selections)
    (h : atom L t * u.sum + atom L s * v.sum ≤ 55*L) :
    (∑ i : State L, ∑ j : State L,
      weight i j * typedFeature t u i * typedFeature s v j) =
      (∑ i : State L, base i * typedFeature t u i) *
      (∑ j : State L, base j * typedFeature s v j) := by
  rw [typed_feature_sum, typed_feature_sum]
  have hh := Erdos371RestrictedMoments.subcritical_moments u hu v hv (selection_budget t s u v h)
  simpa [Fintype.sum_prod_type, weight, typedFeature, mul_ite, ite_mul] using hh

def tieWeight (L : ℕ) : ℤ :=
  ∑ i : State L, ∑ j : State L, if value i = value j then weight i j else 0

lemma tieWeight_nonneg (L : ℕ) : 0 ≤ tieWeight L := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  split_ifs
  · exact weight_nonneg i j
  · exact le_rfl

lemma tieWeight_le (L : ℕ) : tieWeight L ≤ 14400*L := by
  have he (i j : Erdos371RestrictedMoments.State) :
      (∑ t : Fin L, ∑ s : Fin L,
        if value (i,t) = value (j,s) then weight (i,t) (j,s) else 0) =
      if Erdos371RestrictedMoments.largest i = Erdos371RestrictedMoments.largest j
      then (L:ℤ)*Erdos371RestrictedMoments.weight i j else 0 := by
    simp [value_eq_iff, weight, ite_and]
  have ht : tieWeight L =
      ∑ i : Erdos371RestrictedMoments.State, ∑ j : Erdos371RestrictedMoments.State,
        if Erdos371RestrictedMoments.largest i = Erdos371RestrictedMoments.largest j
        then (L:ℤ)*Erdos371RestrictedMoments.weight i j else 0 := by
    simp only [tieWeight, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    simp_rw [he]
  rw [ht]
  calc
    _ ≤ ∑ i : Erdos371RestrictedMoments.State, ∑ j : Erdos371RestrictedMoments.State,
        (L:ℤ)*Erdos371RestrictedMoments.weight i j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (Int.natCast_nonneg L) (Erdos371RestrictedMoments.weight_nonneg i j)
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [Erdos371RestrictedMoments.total_weight]
      ring

lemma normalized_signed_comparison {L : ℕ} (hL : 0 < L) :
    ((∑ i : State L, ∑ j : State L, weight i j * cmp (value i) (value j) : ℤ):ℝ) /
      ((∑ i : State L, ∑ j : State L, weight i j : ℤ):ℝ) = 1/7200 := by
  rw [signed_comparison, total_weight]
  push_cast
  have hl : (L:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  field_simp
  ring

lemma normalized_tie_bound {L : ℕ} (hL : 0 < L) :
    (tieWeight L : ℝ) / (14400*(L:ℝ)^2) ≤ 1/(L:ℝ) := by
  have hl : (0:ℝ) < L := Nat.cast_pos.mpr hL
  have ht : (tieWeight L : ℝ) ≤ 14400*(L:ℝ) := by exact_mod_cast tieWeight_le L
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 14400*(L:ℝ)^2)).mpr
  convert ht using 1
  field_simp

def closeWeight (L K : ℕ) : ℤ :=
  ∑ i : State L, ∑ j : State L,
    if Nat.dist (value i) (value j) ≤ K then weight i j else 0

lemma scale_close_count {L : ℕ} (i : State L)
    (j : Erdos371RestrictedMoments.State) (K : ℕ) :
    ((Finset.univ : Finset (Fin L)).filter
      (fun s => Nat.dist (value i) (value (j,s)) ≤ K)).card ≤ 2*K+1 := by
  let S := (Finset.univ : Finset (Fin L)).filter
    (fun s => Nat.dist (value i) (value (j,s)) ≤ K)
  have hc : S.card ≤ (Finset.Icc (value i-K) (value i+K)).card := by
    apply Finset.card_le_card_of_injOn (fun s : Fin L => value (j,s))
    · intro s hs
      change s ∈ S at hs
      dsimp [S] at hs
      have hd := (Finset.mem_filter.mp hs).2
      change value (j,s) ∈ Finset.Icc (value i-K) (value i+K)
      apply Finset.mem_Icc.mpr
      unfold Nat.dist at hd
      omega
    · intro s hs t ht he
      have hk := (largest_bounds j).1
      have hm : atom L s = atom L t := Nat.eq_of_mul_eq_mul_left
        (by omega : 0 < Erdos371RestrictedMoments.largest j) he
      apply Fin.ext
      unfold atom at hm
      omega
  rw [Nat.card_Icc] at hc
  change S.card ≤ _
  omega

lemma closeWeight_le (L K : ℕ) : closeWeight L K ≤ 14400*L*(2*K+1) := by
  have hs (i j : Erdos371RestrictedMoments.State) (t : Fin L) :
      (∑ s : Fin L, if Nat.dist (value (i,t)) (value (j,s)) ≤ K
        then weight (i,t) (j,s) else 0) ≤
      Erdos371RestrictedMoments.weight i j * (2*K+1) := by
    let S := (Finset.univ : Finset (Fin L)).filter
      (fun s => Nat.dist (value (i,t)) (value (j,s)) ≤ K)
    have he : (∑ s : Fin L, if Nat.dist (value (i,t)) (value (j,s)) ≤ K
        then weight (i,t) (j,s) else 0) =
        Erdos371RestrictedMoments.weight i j * (S.card : ℤ) := by
      dsimp [S]
      rw [← Finset.sum_boole, Finset.mul_sum]
      simp [weight, mul_ite]
    rw [he]
    have hh : (S.card : ℤ) ≤ 2*K+1 := by
      exact_mod_cast scale_close_count (i,t) j K
    exact mul_le_mul_of_nonneg_left hh (Erdos371RestrictedMoments.weight_nonneg i j)
  simp only [closeWeight, Fintype.sum_prod_type]
  calc
    _ ≤ ∑ i : Erdos371RestrictedMoments.State, ∑ t : Fin L,
        ∑ j : Erdos371RestrictedMoments.State, Erdos371RestrictedMoments.weight i j * (2*K+1) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro j hj
      exact hs i j t
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← Finset.sum_mul, ← Finset.mul_sum]
      rw [Erdos371RestrictedMoments.total_weight]
      ring

lemma close_probability_bound {L K : ℕ} (hL : 0 < L) :
    (closeWeight L K : ℝ) / (14400*(L:ℝ)^2) ≤ (2*(K:ℝ)+1)/L := by
  have hl : (0:ℝ) < L := Nat.cast_pos.mpr hL
  have ht : (closeWeight L K : ℝ) ≤ 14400*(L:ℝ)*(2*K+1) := by
    exact_mod_cast closeWeight_le L K
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 14400*(L:ℝ)^2)).mpr
  convert ht using 1
  field_simp

lemma normalized_close_bound {L : ℕ} (hL : 0 < L) {δ : ℝ} (hδ : 0 ≤ δ) :
    (closeWeight L ⌊δ*(55*L)⌋₊ : ℝ) / (14400*(L:ℝ)^2) ≤ 110*δ + 1/L := by
  have hl : (0:ℝ) < L := Nat.cast_pos.mpr hL
  have hf := Nat.floor_le (show 0 ≤ δ*(55*(L:ℝ)) by positivity)
  calc
    _ ≤ (2*(⌊δ*(55*L)⌋₊ : ℝ)+1)/L := close_probability_bound hL
    _ ≤ (2*(δ*(55*L))+1)/L := div_le_div_of_nonneg_right (by linarith) hl.le
    _ = _ := by field_simp; ring

open Filter
open scoped Topology

/-- The probability of a largest-part tie vanishes in this model family,
while the normalized signed comparison stays exactly `1/7200`. -/
theorem tie_probability_tendsto_zero :
    Tendsto (fun L : ℕ => (tieWeight L : ℝ) / (14400*(L:ℝ)^2)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_one_div_atTop_nhds_zero_nat
  · exact Eventually.of_forall (fun L => div_nonneg
      (show (0:ℝ) ≤ (tieWeight L : ℝ) by exact_mod_cast tieWeight_nonneg L) (by positivity))
  · filter_upwards [eventually_gt_atTop 0] with L hL
    exact normalized_tie_bound hL

/-- Even a uniform absence of concentration near equal normalized largest
parts is compatible with the biased comparison and the specified moments. -/
theorem no_diagonal_concentration :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ L : ℕ in atTop,
      (closeWeight L ⌊δ*(55*L)⌋₊ : ℝ) / (14400*(L:ℝ)^2) < ε := by
  intro ε hε
  refine ⟨ε/220, by positivity, ?_⟩
  have hh := tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const (show (0:ℝ) < ε/2 by positivity)
  filter_upwards [eventually_gt_atTop 0, hh] with L hL hsmall
  have hb := normalized_close_bound hL (show 0 ≤ ε/220 by positivity)
  linarith

end Erdos371DiffuseMomentObstruction

#print axioms Erdos371DiffuseMomentObstruction.parts_mass
#print axioms Erdos371DiffuseMomentObstruction.value_is_largest
#print axioms Erdos371DiffuseMomentObstruction.typed_subcritical_moments
#print axioms Erdos371DiffuseMomentObstruction.normalized_signed_comparison
#print axioms Erdos371DiffuseMomentObstruction.tie_probability_tendsto_zero
#print axioms Erdos371DiffuseMomentObstruction.no_diagonal_concentration
