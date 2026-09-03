import FormalConjecturesUtil
import Submission.IrrationalSequenceDiagnostic
import Submission.PolynomialRateCriterion

/-! Stronger numerical diagnostics. These sequences are NOT identified as
extremal numbers of any fixed graph. -/
open Filter Asymptotics
open scoped Topology
namespace Erdos713DensitySequence

lemma concave_step {x t : ℝ} (hx : 1 ≤ x) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (x-1)*(x+1)^t ≤ (x-1+t)*x^t := by
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hB := rpow_one_add_le_one_add_mul_self
    (show -1 ≤ 1/x by
      have hh : 0 ≤ 1/x := by positivity
      linarith) ht0 ht1
  have he : x*(1+1/x) = x+1 := by field_simp
  have hfactor : (x-1)*(1+t*(1/x)) ≤ x-1+t := by
    have hdiv : t*(1/x)*x = t := by field_simp
    have hpos : 0 ≤ t*(1/x) := by positivity
    nlinarith
  calc
    (x-1)*(x+1)^t = ((x-1)*(1+1/x)^t)*x^t := by
      rw [← he,Real.mul_rpow hxp.le (by positivity)]
      ring
    _ ≤ ((x-1)*(1+t*(1/x)))*x^t :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr hx)) (Real.rpow_nonneg hxp.le _)
    _ ≤ (x-1+t)*x^t := mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hxp.le _)

lemma power_floor_margin {x r c : ℝ} (hx : 1 ≤ x) (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (hc : 0 ≤ c) (hcr : 1 ≤ c*(2-r)) :
    (x-1)*(c*(x+1)^r) ≤ (x+1)*(c*x^r-1) := by
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hp : 1 ≤ x^(r-1) := Real.one_le_rpow hx (sub_nonneg.mpr hr1)
  have hgap : 1 ≤ c*(2-r)*x^(r-1) := by nlinarith
  have hs := mul_le_mul_of_nonneg_left
    (concave_step hx (sub_nonneg.mpr hr1) (by linarith : r-1 ≤ 1)) hc
  have hh : c*(x-1)*(x+1)^(r-1) ≤ c*x*x^(r-1)-1 := by nlinarith
  have hex : x^r = x^(r-1)*x := by
    convert Real.rpow_add_one hxp.ne' (r-1) using 1 <;> congr 1 <;> ring
  have hex1 : (x+1)^r = (x+1)^(r-1)*(x+1) := by
    convert Real.rpow_add_one (by linarith : x+1 ≠ 0) (r-1) using 1 <;> congr 1 <;> ring
  calc
    (x-1)*(c*(x+1)^r) = (x+1)*(c*(x-1)*(x+1)^(r-1)) := by rw [hex1]; ring
    _ ≤ (x+1)*(c*x*x^(r-1)-1) := mul_le_mul_of_nonneg_left hh (by linarith)
    _ = (x+1)*(c*x^r-1) := by rw [hex]; ring

noncomputable def raw (c r : ℝ) (n : ℕ) : ℕ := ⌊c*(n : ℝ)^r⌋₊
noncomputable def seq (c r : ℝ) (n : ℕ) : ℕ := min (n.choose 2) (raw c r n)

lemma raw_density_antitone {r c : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (hc : 0 ≤ c) (hcr : 1 ≤ c*(2-r)) :
    AntitoneOn (fun n : ℕ => (raw c r n : ℝ)/(n.choose 2 : ℝ)) (Set.Ici 2) := by
  apply antitoneOn_nat_Ici_of_succ_le
  intro n hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0 : ℝ) < n := by linarith
  have hA := Nat.floor_le (mul_nonneg hc (Real.rpow_nonneg (by positivity : 0 ≤ ((n+1 : ℕ) : ℝ)) r))
  have hB := Nat.lt_floor_add_one (c*(n : ℝ)^r)
  change (raw c r (n+1) : ℝ) ≤ c*((n+1 : ℕ) : ℝ)^r at hA
  change c*(n : ℝ)^r < (raw c r n : ℝ)+1 at hB
  have hM := power_floor_margin (by linarith : (1 : ℝ) ≤ n) hr1 hr2 hc hcr
  rw [Nat.cast_add,Nat.cast_one] at hA
  have hAf := mul_le_mul_of_nonneg_left hA (show 0 ≤ (n : ℝ)-1 by linarith)
  have hBf := mul_le_mul_of_nonneg_left hB.le (show 0 ≤ (n : ℝ)+1 by linarith)
  have hcross : (n-1 : ℝ)*(raw c r (n+1) : ℝ) ≤ (n+1 : ℝ)*(raw c r n : ℝ) := by
    nlinarith
  have hnC : (0 : ℝ) < n.choose 2 := by exact_mod_cast Nat.choose_pos hn
  have hnC' : (0 : ℝ) < (n+1).choose 2 := by exact_mod_cast Nat.choose_pos (by omega : 2 ≤ n+1)
  rw [div_le_div_iff₀ hnC' hnC,Nat.cast_choose_two,Nat.cast_choose_two,Nat.cast_add,Nat.cast_one]
  nlinarith [mul_le_mul_of_nonneg_left hcross h0.le]

lemma density_formula (c r : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    (seq c r n : ℝ)/(n.choose 2 : ℝ) = min 1 ((raw c r n : ℝ)/(n.choose 2 : ℝ)) := by
  have hC : (0 : ℝ) < n.choose 2 := by exact_mod_cast Nat.choose_pos hn
  dsimp [seq]
  rw [Nat.cast_min,← min_div_div_right hC.le,div_self hC.ne']

lemma seq_density_antitone {r c : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (hc : 0 ≤ c) (hcr : 1 ≤ c*(2-r)) :
    AntitoneOn (fun n : ℕ => (seq c r n : ℝ)/(n.choose 2 : ℝ)) (Set.Ici 2) := by
  intro a ha b hb hab
  change (seq c r b : ℝ)/(b.choose 2 : ℝ) ≤ (seq c r a : ℝ)/(a.choose 2 : ℝ)
  rw [density_formula c r ha,density_formula c r hb]
  exact min_le_min (le_refl 1) (raw_density_antitone hr1 hr2 hc hcr ha hb hab)

lemma raw_monotone {r c : ℝ} (hr : 0 ≤ r) (hc : 0 ≤ c) : Monotone (raw c r) := by
  intro a b hab
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hab) hr) hc

lemma seq_monotone {r c : ℝ} (hr : 0 ≤ r) (hc : 0 ≤ c) : Monotone (seq c r) := by
  intro a b hab
  exact min_le_min (Nat.choose_mono 2 hab) (raw_monotone hr hc hab)

lemma raw_superadditive {r c : ℝ} (hr : 1 ≤ r) (hc : 0 ≤ c) (a b : ℕ) :
    raw c r a+raw c r b ≤ raw c r (a+b) := by
  apply Nat.le_floor
  have hA := Nat.floor_le (mul_nonneg hc (Real.rpow_nonneg (Nat.cast_nonneg a) r))
  have hB := Nat.floor_le (mul_nonneg hc (Real.rpow_nonneg (Nat.cast_nonneg b) r))
  have hh := mul_le_mul_of_nonneg_left
    (Real.add_rpow_le_rpow_add (Nat.cast_nonneg a) (Nat.cast_nonneg b) hr) hc
  simp only [Nat.cast_add]
  dsimp [raw]
  nlinarith

lemma choose_two_superadditive (a b : ℕ) : a.choose 2+b.choose 2 ≤ (a+b).choose 2 := by
  have hh : ((a.choose 2 : ℕ) : ℝ)+(b.choose 2 : ℝ) ≤ ((a+b).choose 2 : ℝ) := by
    simp only [Nat.cast_choose_two,Nat.cast_add]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) a) (Nat.cast_nonneg (α := ℝ) b)]
  exact_mod_cast hh

lemma seq_superadditive {r c : ℝ} (hr : 1 ≤ r) (hc : 0 ≤ c) (a b : ℕ) :
    seq c r a+seq c r b ≤ seq c r (a+b) := by
  apply le_min
  · exact (Nat.add_le_add (min_le_left _ _) (min_le_left _ _)).trans (choose_two_superadditive a b)
  · exact (Nat.add_le_add (min_le_right _ _) (min_le_right _ _)).trans (raw_superadditive hr hc a b)

lemma seq_eventually_raw {r c : ℝ} (hr : r < 2) (hc : 0 ≤ c) : seq c r =ᶠ[atTop] raw c r := by
  have hTop : Tendsto (fun n : ℕ => (n : ℝ)^(2-r)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 2-r)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hTop.eventually_ge_atTop (4*c),eventually_ge_atTop (2 : ℕ)] with n hn hn2
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  rw [Real.rpow_sub hnp,le_div_iff₀ (Real.rpow_pos_of_pos hnp r)] at hn
  have hsq : (n : ℝ)^(2 : ℝ) = (n : ℝ)^2 := by norm_cast
  rw [hsq] at hn
  have hF := Nat.floor_le (mul_nonneg hc (Real.rpow_nonneg hnp.le r))
  have hbound : (raw c r n : ℝ) ≤ (n.choose 2 : ℝ) := by
    rw [Nat.cast_choose_two]
    dsimp [raw]
    nlinarith
  apply min_eq_right
  exact_mod_cast hbound

lemma seq_asymptotic {r c : ℝ} (hr0 : 0 < r) (hr2 : r < 2) (hc : 0 < c) :
    IsEquivalent atTop (fun n : ℕ => (seq c r n : ℝ)) (fun n : ℕ => c*(n : ℝ)^r) := by
  have hraw : IsEquivalent atTop (fun n : ℕ => (raw c r n : ℝ)) (fun n : ℕ => c*(n : ℝ)^r) :=
    isEquivalent_nat_floor.comp_tendsto
      (Tendsto.const_mul_atTop hc ((tendsto_rpow_atTop hr0).comp tendsto_natCast_atTop_atTop))
  apply hraw.congr_left
  filter_upwards [seq_eventually_raw hr2 hc.le] with n hn
  exact congrArg (fun m : ℕ => (m : ℝ)) hn.symm

lemma exists_irrational_sequence_with_density :
    ∃ (r c : ℝ) (f : ℕ → ℕ), (6 : ℝ)/5 < r ∧ r < (5 : ℝ)/4 ∧ Irrational r ∧
      0 < c ∧ Monotone f ∧ (∀ a b, f a+f b ≤ f (a+b)) ∧
      (∀ n, f n ≤ n.choose 2) ∧
      AntitoneOn (fun n : ℕ => (f n : ℝ)/(n.choose 2 : ℝ)) (Set.Ici 2) ∧
      IsEquivalent atTop (fun n : ℕ => (f n : ℝ)) (fun n : ℕ => c*(n : ℝ)^r) := by
  let r := Erdos713IrrationalSequenceDiagnostic.index
  have hb := Erdos713IrrationalSequenceDiagnostic.index_bounds
  have hr1 : 1 ≤ r := by dsimp [r]; linarith [hb.1]
  have hr2 : r < 2 := by dsimp [r]; linarith [hb.2]
  refine ⟨r,2,seq 2 r,hb.1,hb.2,Erdos713IrrationalSequenceDiagnostic.index_irrational,
    by norm_num,seq_monotone (by linarith) (by norm_num),
    seq_superadditive hr1 (by norm_num),fun _ => min_le_left _ _,?_,?_⟩
  · apply seq_density_antitone hr1 hr2.le (by norm_num)
    dsimp [r]
    linarith [hb.2]
  · exact seq_asymptotic (by linarith) hr2 (by norm_num)


lemma seq_complete_prefix {r c : ℝ} {N : ℕ} (hr : 0 ≤ r) (hc : (N : ℝ)^2 ≤ c)
    {n : ℕ} (hn : n ≤ N) : seq c r n = n.choose 2 := by
  by_cases hz : n = 0
  · subst n
    simp [seq]
  have hn1 : 1 ≤ n := by omega
  have hp : 1 ≤ (n : ℝ)^r := Real.one_le_rpow (by exact_mod_cast hn1) hr
  have hc0 : 0 ≤ c := (sq_nonneg _).trans hc
  have hC : (n.choose 2 : ℝ) ≤ (N : ℝ)^2 := by
    rw [Nat.cast_choose_two]
    have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) n) hnR 2
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  apply min_eq_left
  apply Nat.le_floor
  exact hC.trans (hc.trans (by nlinarith))

/-- Even an arbitrarily long complete-graph prefix is compatible with all
these numerical properties and an irrational power index. -/
lemma exists_irrational_sequence_with_prefix (N : ℕ) :
    ∃ (r c : ℝ) (f : ℕ → ℕ), (6 : ℝ)/5 < r ∧ r < (5 : ℝ)/4 ∧ Irrational r ∧
      0 < c ∧ Monotone f ∧ (∀ a b, f a+f b ≤ f (a+b)) ∧
      (∀ n, f n ≤ n.choose 2) ∧ (∀ n ≤ N, f n = n.choose 2) ∧
      AntitoneOn (fun n : ℕ => (f n : ℝ)/(n.choose 2 : ℝ)) (Set.Ici 2) ∧
      IsEquivalent atTop (fun n : ℕ => (f n : ℝ)) (fun n : ℕ => c*(n : ℝ)^r) := by
  let r := Erdos713IrrationalSequenceDiagnostic.index
  let c : ℝ := (N : ℝ)^2+2
  have hb := Erdos713IrrationalSequenceDiagnostic.index_bounds
  have hr1 : 1 ≤ r := by dsimp [r]; linarith [hb.1]
  have hr2 : r < 2 := by dsimp [r]; linarith [hb.2]
  have hc2 : 2 ≤ c := by dsimp [c]; nlinarith [sq_nonneg (N : ℝ)]
  have hc : 0 < c := by linarith
  refine ⟨r,c,seq c r,hb.1,hb.2,Erdos713IrrationalSequenceDiagnostic.index_irrational,
    hc,seq_monotone (by linarith) hc.le,seq_superadditive hr1 hc.le,
    fun _ => min_le_left _ _,?_,?_,seq_asymptotic (by linarith) hr2 hc⟩
  · intro n hn
    exact seq_complete_prefix (by linarith) (by dsimp [c]; linarith) hn
  · apply seq_density_antitone hr1 hr2.le hc.le
    have hh : r < (5 : ℝ)/4 := hb.2
    nlinarith

lemma no_polynomial_relation (s : Finset (ℕ × ℕ)) (hs : s.Nonempty)
    (a : (ℕ × ℕ) → ℝ) (ha : ∀ p ∈ s, a p ≠ 0) :
    ∀ᶠ n : ℕ in atTop, ∑ p ∈ s, a p*(n : ℝ)^p.1*
      (seq 2 Erdos713IrrationalSequenceDiagnostic.index n : ℝ)^p.2 ≠ 0 := by
  classical
  by_contra hz
  change ∃ᶠ n : ℕ in atTop, ∑ p ∈ s, a p*(n : ℝ)^p.1*
    (seq 2 Erdos713IrrationalSequenceDiagnostic.index n : ℝ)^p.2 = 0 at hz
  have hb := Erdos713IrrationalSequenceDiagnostic.index_bounds
  have hf := seq_asymptotic (by linarith [hb.1]) (by linarith [hb.2]) (by norm_num : (0 : ℝ) < 2)
  exact Erdos713IrrationalSequenceDiagnostic.index_irrational
    (Erdos713PolynomialRate.rational_of_polynomial_relation (by norm_num) hf s hs a ha hz)

#print axioms exists_irrational_sequence_with_density
#print axioms exists_irrational_sequence_with_prefix
#print axioms no_polynomial_relation
end Erdos713DensitySequence
