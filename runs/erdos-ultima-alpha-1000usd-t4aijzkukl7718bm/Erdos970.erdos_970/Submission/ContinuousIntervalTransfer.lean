import Submission.ContinuousIntervalEnvelope

/-! Jensen transfer of interval-aware envelopes to dominating reference marginals.
Uniform quadratic positivity is not asserted. -/
namespace Erdos970.ContinuousInterval
open IntervalRescaling BlockSieve.SievePolynomial

theorem quotient_sandwich_sharp (m p c : ℕ) (hp : 0 < p)
    (hlo : m / p ≤ c) (hhi : c ≤ ceilQuotient m p) :
    ((m : ℝ) + 1) * (1 / (p : ℝ)) - 1 ≤ (c : ℝ) ∧
      (c : ℝ) ≤ 1 + ((m : ℝ) - 1) * (1 / (p : ℝ)) := by
  have hmod := Nat.mod_lt m hp
  have hdiv := Nat.mod_add_div m p
  have hlmul := Nat.mul_le_mul_left p hlo
  have hl : m + 1 ≤ p * c + p := by omega
  have hu : p * c + 1 ≤ m + p := by
    unfold ceilQuotient at hhi
    by_cases hm : m % p = 0
    · rw [if_pos hm] at hhi
      have hh := Nat.mul_le_mul_left p hhi
      nlinarith
    · rw [if_neg hm] at hhi
      have hmpos : 1 ≤ m % p := by omega
      have hh := Nat.mul_le_mul_left p hhi
      nlinarith
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hlR : (m : ℝ) + 1 ≤ (p : ℝ) * c + p := by exact_mod_cast hl
  have huR : (p : ℝ) * c + 1 ≤ (m : ℝ) + p := by exact_mod_cast hu
  constructor
  · have hh : ((m : ℝ) + 1) / p ≤ (c : ℝ) + 1 :=
      (div_le_iff₀ hpR).mpr (by nlinarith)
    simpa only [mul_one_div] using (sub_le_iff_le_add.mpr hh)
  · have hh : (c : ℝ) - 1 ≤ ((m : ℝ) - 1) / p :=
      (le_div_iff₀ hpR).mpr (by nlinarith)
    simpa only [mul_one_div, add_comm] using (sub_le_iff_le_add.mp hh : (c : ℝ) ≤ ((m : ℝ) - 1) / p + 1)

noncomputable def boost (q Q : ℝ) : ℝ := (Q - q) / (1 - q)

theorem boost_bounds (q Q : ℝ) (hq : q < 1) (hlo : q ≤ Q) (hhi : Q ≤ 1) :
    0 ≤ boost q Q ∧ boost q Q ≤ 1 := by
  have hd := sub_pos.mpr hq
  exact ⟨div_nonneg (sub_nonneg.mpr hlo) hd.le,
    (div_le_one hd).mpr (by linarith)⟩

theorem boost_identity (q Q : ℝ) (hq : q < 1) :
    boost q Q + (1 - boost q Q) * q = Q := by
  unfold boost
  have hd := (sub_pos.mpr hq).ne'
  field_simp
  ring

/-- The sharp endpoint errors transform with the boosted marginal itself. -/
theorem mixture_sandwich (n c q Q a : ℝ) (ha : a ≤ 1)
    (hprob : a + (1 - a) * q = Q)
    (hc : (n + 1) * q - 1 ≤ c ∧ c ≤ 1 + (n - 1) * q) :
    (n + 1) * Q - 1 ≤ a * n + (1 - a) * c ∧
      a * n + (1 - a) * c ≤ 1 + (n - 1) * Q := by
  have hl := mul_le_mul_of_nonneg_left hc.1 (sub_nonneg.mpr ha)
  have hu := mul_le_mul_of_nonneg_left hc.2 (sub_nonneg.mpr ha)
  rw [← hprob]
  constructor <;> nlinarith

noncomputable def normalization (p : ℕ → ℕ) (Q : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, (1 - boost (1 / (p i : ℝ)) (Q i))

theorem normalization_succ (p : ℕ → ℕ) (Q : ℕ → ℝ) (k : ℕ) :
    normalization p Q (k + 1) =
      normalization p Q k * (1 - boost (1 / (p k : ℝ)) (Q k)) := by
  exact Finset.prod_range_succ _ _

theorem normalization_nonneg (p : ℕ → ℕ) (Q : ℕ → ℝ) (k : ℕ)
    (hp : ∀ i < k, 1 < p i)
    (hQ : ∀ i < k, 1 / (p i : ℝ) ≤ Q i ∧ Q i ≤ 1) :
    0 ≤ normalization p Q k := by
  apply Finset.prod_nonneg
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hpR : (1 : ℝ) < p i := by exact_mod_cast hp i hi'
  have hq : 1 / (p i : ℝ) < 1 := (div_lt_one (by linarith)).mpr hpR
  exact sub_nonneg.mpr (boost_bounds _ _ hq (hQ i hi').1 (hQ i hi').2).2

/-- A real-valued, interval-aware envelope at larger marginals bounds the
normalized survivor count for arbitrary larger coprime moduli. -/
theorem envelope_normalized_bound (p : ℕ → ℕ) (Q : ℕ → ℝ) (k : ℕ)
    (hp : ∀ i < k, 1 < p i)
    (hcop : ∀ i < k, ∀ j < i, (p i).Coprime (p j))
    (hQ : ∀ i < k, 1 / (p i : ℝ) ≤ Q i ∧ Q i ≤ 1)
    (m : ℕ) (r : ℕ → ℕ) :
    (envelope Q k m).1 ≤ normalization p Q k * (count p r k m : ℝ) ∧
      normalization p Q k * (count p r k m : ℝ) ≤ (envelope Q k m).2 := by
  induction k generalizing m r with
  | zero => simp [envelope, normalization, count]
  | succ k ih =>
    have hpp : ∀ i < k, 1 < p i := fun i hi => hp i (by omega)
    have hQQ : ∀ i < k, 1 / (p i : ℝ) ≤ Q i ∧ Q i ≤ 1 := fun i hi => hQ i (by omega)
    have hcc : ∀ i < k, ∀ j < i, (p i).Coprime (p j) := fun i hi => hcop i (by omega)
    have hprev := ih hpp hcc hQQ m r
    have hreg := envelope_regular Q k (fun i hi =>
      ⟨(by positivity : 0 ≤ 1 / (p i : ℝ)).trans (hQQ i hi).1, (hQQ i hi).2⟩)
    have hpk : 1 < p k := hp k (by omega)
    have hpR : (1 : ℝ) < p k := by exact_mod_cast hpk
    have hq : 1 / (p k : ℝ) < 1 := (div_lt_one (by linarith)).mpr hpR
    let a := boost (1 / (p k : ℝ)) (Q k)
    have ha := boost_bounds _ _ hq (hQ k (by omega)).1 (hQ k (by omega)).2
    change 0 ≤ a ∧ a ≤ 1 at ha
    have hb : 0 ≤ 1 - a := sub_nonneg.mpr ha.2
    obtain ⟨c, s, hcl, hcu, he⟩ := firstHitCount_rescale p r k m (by omega)
      (fun j hj => by have := hpp j hj; omega) (hcop k (by omega))
    have hchild := ih hpp hcc hQQ c s
    let v := a * (m : ℝ) + (1 - a) * (c : ℝ)
    have hv : 0 ≤ v := add_nonneg (mul_nonneg ha.1 (Nat.cast_nonneg m))
      (mul_nonneg hb (Nat.cast_nonneg c))
    have hsand := mixture_sandwich (m : ℝ) c (1 / (p k : ℝ)) (Q k) a ha.2
      (boost_identity _ _ hq) (quotient_sandwich_sharp m (p k) c (by omega) hcl hcu)
    have hJlo := hreg.lower_convex.2 (Set.mem_univ (m : ℝ)) (Set.mem_univ (c : ℝ)) ha.1 hb
      (show a + (1 - a) = 1 by ring)
    have hJhi := hreg.upper_concave.2 (show (m : ℝ) ∈ Set.Ici 0 from (Nat.cast_nonneg m : (0 : ℝ) ≤ m))
      (show (c : ℝ) ∈ Set.Ici 0 from (Nat.cast_nonneg c : (0 : ℝ) ≤ c)) ha.1 hb
      (show a + (1 - a) = 1 by ring)
    simp only [smul_eq_mul] at hJlo hJhi
    have hlow : (envelope Q k (((m : ℝ) + 1) * Q k - 1)).1 ≤
        a * (normalization p Q k * (count p r k m : ℝ)) +
          (1 - a) * (normalization p Q k * (count p s k c : ℝ)) := by
      calc
        _ ≤ (envelope Q k v).1 := hreg.lower_mono hsand.1
        _ ≤ a * (envelope Q k m).1 + (1 - a) * (envelope Q k c).1 := hJlo
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hprev.1 ha.1)
          (mul_le_mul_of_nonneg_left hchild.1 hb)
    have hhigh : a * (normalization p Q k * (count p r k m : ℝ)) +
          (1 - a) * (normalization p Q k * (count p s k c : ℝ)) ≤
        (envelope Q k (1 + ((m : ℝ) - 1) * Q k)).2 := by
      calc
        _ ≤ a * (envelope Q k m).2 + (1 - a) * (envelope Q k c).2 :=
          add_le_add (mul_le_mul_of_nonneg_left hprev.2 ha.1)
            (mul_le_mul_of_nonneg_left hchild.2 hb)
        _ ≤ (envelope Q k v).2 := hJhi
        _ ≤ _ := hreg.upper_mono hv (hv.trans hsand.2) hsand.2
    have hpart : (count p r (k + 1) m : ℝ) + count p s k c = count p r k m := by
      have hh := count_succ_partition p r k m
      rw [he] at hh
      exact_mod_cast (show count p r (k + 1) m + count p s k c = count p r k m by omega)
    have hnorm := normalization_nonneg p Q (k + 1) hp hQ
    have hnonneg := mul_nonneg hnorm (Nat.cast_nonneg (count p r (k + 1) m))
    have hnormeq := normalization_succ p Q k
    change normalization p Q (k + 1) = normalization p Q k * (1 - a) at hnormeq
    have hscaled : normalization p Q (k + 1) * (count p r (k + 1) m : ℝ) =
        normalization p Q k * (count p r k m : ℝ) -
        (a * (normalization p Q k * (count p r k m : ℝ)) +
          (1 - a) * (normalization p Q k * (count p s k c : ℝ))) := by
      rw [hnormeq]
      nlinarith [congrArg (fun x : ℝ => normalization p Q k * (1 - a) * x) hpart]
    constructor
    · change clip (fun x => (envelope Q k x).1 -
        (envelope Q k (1 + (x - 1) * Q k)).2) m ≤ _
      rw [clip, max_eq_right (Nat.cast_nonneg m)]
      apply max_le hnonneg
      rw [hscaled]
      linarith [hprev.1]
    · change _ ≤ (envelope Q k m).2 - (envelope Q k (((m : ℝ) + 1) * Q k - 1)).1
      rw [hscaled]
      linarith [hprev.2]

/-- Positive reference envelopes force an actual survivor for arbitrary larger
coprime moduli. There is no unproved uniform positivity assumption hidden here. -/
theorem survivor_of_positive_envelope (p : ℕ → ℕ) (Q : ℕ → ℝ) (k : ℕ)
    (hp : ∀ i < k, 1 < p i)
    (hcop : ∀ i < k, ∀ j < i, (p i).Coprime (p j))
    (hQ : ∀ i < k, 1 / (p i : ℝ) ≤ Q i ∧ Q i ≤ 1)
    (m : ℕ) (hpos : 0 < (envelope Q k m).1) (r : ℕ → ℕ) :
    ∃ x < m, ∀ i < k, ¬x ≡ r i [MOD p i] := by
  have hh := hpos.trans_le (envelope_normalized_bound p Q k hp hcop hQ m r).1
  have hcount : 0 < count p r k m := by
    by_contra hn
    have hz : count p r k m = 0 := by omega
    simp [hz] at hh
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hcount
  exact ⟨x, Finset.mem_range.mp (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

#print axioms envelope_normalized_bound
#print axioms survivor_of_positive_envelope
end Erdos970.ContinuousInterval
