import FormalConjecturesUtil
import Submission.SieveParameters

/-! Applying the two-linear-prime sieve to fixed cofactors of consecutive
  integers, and summing the exceptional weights over cofactor boxes. -/

namespace Erdos371CofactorSieve

open Finset Erdos371SieveParameters Erdos371SieveEulerProduct Erdos371TwoLinearSieve

attribute [local instance] Classical.propDecidable

noncomputable def cofactorInputs (k a b N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun n => a ∣ n ∧ b ∣ n+1 ∧
    (n/a).Prime ∧ ((n+1)/b).Prime ∧ cutoff k ≤ n/a ∧ cutoff k ≤ (n+1)/b

lemma coprime_of_consecutive_divisors {a b n : ℕ} (ha : a ∣ n) (hb : b ∣ n+1) :
    a.Coprime b := by
  have hd : a.gcd b ∣ n := (Nat.gcd_dvd_left _ _).trans ha
  have he : a.gcd b ∣ n+1 := (Nat.gcd_dvd_right _ _).trans hb
  have h1 : a.gcd b ∣ 1 := by
    have h := Nat.dvd_sub he hd
    simpa using h
  exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp h1)

lemma exists_progression_origin {a b : ℕ} (ha : 0<a) (hb : 0<b) (hab : a.Coprime b) :
    ∃ v, v < a*b ∧ a ∣ v ∧ b ∣ v+1 := by
  let v := Nat.chineseRemainder hab 0 (b-1)
  refine ⟨v.val, Nat.chineseRemainder_lt_mul hab _ _ (by omega) (by omega),
    Nat.modEq_zero_iff_dvd.mp v.property.1, ?_⟩
  have h := v.property.2.add_right 1
  have he : b-1+1=b := by omega
  rw [he] at h
  exact Nat.modEq_zero_iff_dvd.mp (h.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl b)))

lemma progression_remainder {a b v n : ℕ} (hab : a.Coprime b)
    (hv : v<a*b) (hav : a∣v) (hbv : b∣v+1) (han : a∣n) (hbn : b∣n+1) :
    n % (a*b) = v := by
  have hm1 : Nat.ModEq a n v :=
    (Nat.modEq_zero_iff_dvd.mpr han).trans (Nat.modEq_zero_iff_dvd.mpr hav).symm
  have hm2 : Nat.ModEq b n v := by
    apply Nat.ModEq.add_right_cancel' 1
    exact (Nat.modEq_zero_iff_dvd.mpr hbn).trans (Nat.modEq_zero_iff_dvd.mpr hbv).symm
  have hm := (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨hm1,hm2⟩
  change n%(a*b)=v%(a*b) at hm
  simpa only [Nat.mod_eq_of_lt hv] using hm

lemma progression_forms {a b v n : ℕ} (ha : 0<a) (hb : 0<b) (hab : a.Coprime b)
    (hv : v<a*b) (hav : a∣v) (hbv : b∣v+1) (han : a∣n) (hbn : b∣n+1) :
    n/a = b*(n/(a*b))+v/a ∧ (n+1)/b = a*(n/(a*b))+(v+1)/b := by
  have hr := progression_remainder hab hv hav hbv han hbn
  have hn := Nat.mod_add_div n (a*b)
  rw [hr] at hn
  have hna := Nat.mul_div_cancel' han
  have hnb := Nat.mul_div_cancel' hbn
  have hva := Nat.mul_div_cancel' hav
  have hvb := Nat.mul_div_cancel' hbv
  constructor
  · apply Nat.eq_of_mul_eq_mul_left ha
    nlinarith
  · apply Nat.eq_of_mul_eq_mul_left hb
    nlinarith

lemma progression_determinant {a b v : ℕ} (hav : a∣v) (hbv : b∣v+1) :
    determinantOne b (v/a) a ((v+1)/b) := by
  apply Or.inl
  have ha := Nat.mul_div_cancel' hav
  have hb := Nat.mul_div_cancel' hbv
  nlinarith

lemma cofactorInputs_card_le_primeInputs {a b v : ℕ} (ha : 0<a) (hb : 0<b)
    (hab : a.Coprime b) (hv : v<a*b) (hav : a∣v) (hbv : b∣v+1)
    (k N T : ℕ) (hT : N/(a*b)+1 ≤ T) :
    (cofactorInputs k a b N).card ≤
      (primeInputs (cutoff k).primesBelow b (v/a) a ((v+1)/b) T).card := by
  apply Finset.card_le_card_of_injOn (fun n => n/(a*b))
  · intro n hn
    change n ∈ cofactorInputs k a b N at hn
    obtain ⟨hnN, han, hbn, hp, hq, hpl, hql⟩ := Finset.mem_filter.mp hn
    have hnlt := Finset.mem_range.mp hnN
    have hforms := progression_forms ha hb hab hv hav hbv han hbn
    change n/(a*b) ∈ primeInputs (cutoff k).primesBelow b (v/a) a ((v+1)/b) T
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hforms.1 ▸ hp, hforms.2 ▸ hq, ?_⟩
    · have hh := Nat.div_le_div_right (by omega : n≤N) (c := a*b)
      omega
    · intro p hpm
      have hh := (Nat.mem_primesBelow.mp hpm).1
      constructor <;> omega
  · intro n hn m hm hnm
    change n ∈ cofactorInputs k a b N at hn
    change m ∈ cofactorInputs k a b N at hm
    obtain ⟨_, han, hbn, _⟩ := Finset.mem_filter.mp hn
    obtain ⟨_, ham, hbm, _⟩ := Finset.mem_filter.mp hm
    have hn := Nat.mod_add_div n (a*b)
    have hm := Nat.mod_add_div m (a*b)
    rw [progression_remainder hab hv hav hbv han hbn] at hn
    rw [progression_remainder hab hv hav hbv ham hbm] at hm
    change n/(a*b)=m/(a*b) at hnm
    rw [hnm] at hn
    omega

/-- Fixed-cofactor prime pairs are bounded by the two-linear-form sieve.
  The upper bound `T` for the progression length can be common to a box. -/
theorem cofactorInputs_card_le {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (k N T : ℕ) (hT : N/(a*b)+1 ≤ T) (hlarge : threshold k ≤ T) :
    (cofactorInputs k a b N).card ≤
      6*(T:ℝ)*weight (cutoff k).primesBelow a * weight (cutoff k).primesBelow b / (4:ℝ)^k := by
  by_cases hab : a.Coprime b
  · obtain ⟨v,hv,hav,hbv⟩ := exists_progression_origin ha hb hab
    have hc := cofactorInputs_card_le_primeInputs ha hb hab hv hav hbv k N T hT
    have hs := two_linear_prime_quantitative k T hlarge (progression_determinant hav hbv)
    calc
      _ ≤ ((primeInputs (cutoff k).primesBelow b (v/a) a ((v+1)/b) T).card:ℝ) := by exact_mod_cast hc
      _ ≤ _ := by convert hs using 1 <;> ring
  · have he : cofactorInputs k a b N = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hh := Finset.mem_filter.mp hn
      exact hab (coprime_of_consecutive_divisors hh.2.1 hh.2.2.1)
    rw [he, Finset.card_empty, Nat.cast_zero]
    apply div_nonneg
    · apply mul_nonneg
      · apply mul_nonneg (by positivity)
        exact weight_nonneg (fun p hp => (Nat.mem_primesBelow.mp hp).2) a
      · exact weight_nonneg (fun p hp => (Nat.mem_primesBelow.mp hp).2) b
    · positivity

lemma mean_weight_Icc {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (A : ℕ) :
    (∑ m ∈ Finset.Icc 1 A, weight s m) ≤ Real.exp 1 * A := by
  have he : (∑ m ∈ Finset.Icc 1 A, weight s m) =
      ∑ m ∈ Finset.range A, weight s (m+1) := by
    apply Finset.sum_bij (fun m _ => m-1)
    · intro m hm
      have hh := Finset.mem_Icc.mp hm
      exact Finset.mem_range.mpr (by omega)
    · intro m hm n hn he
      have hh := Finset.mem_Icc.mp hm
      have hh' := Finset.mem_Icc.mp hn
      omega
    · intro n hn
      refine ⟨n+1, Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hn; omega⟩, ?_⟩
      omega
    · intro m hm
      have he : m-1+1=m := by have := Finset.mem_Icc.mp hm; omega
      rw [he]
  rw [he]
  exact mean_weight_le hs A

lemma weight_box_sum_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (A B : ℕ) :
    (∑ a ∈ Finset.Icc 1 A, ∑ b ∈ Finset.Icc 1 B, weight s a * weight s b) ≤
      (Real.exp 1)^2 * A * B := by
  rw [← Finset.sum_mul_sum]
  calc
    _ ≤ (Real.exp 1 * A) * (Real.exp 1 * B) := by
      apply mul_le_mul (mean_weight_Icc hs A) (mean_weight_Icc hs B)
      · exact Finset.sum_nonneg (fun b _ => weight_nonneg hs b)
      · positivity
    _ = _ := by ring

noncomputable def cofactorBox (k A B N : ℕ) : Finset ℕ :=
  (Finset.Icc A B).biUnion fun a => (Finset.Icc A B).biUnion fun b => cofactorInputs k a b N

lemma cofactorBox_card_bound {A : ℕ} (hA : 0<A) (k B N T : ℕ)
    (hT : N/(A*A)+1 ≤ T) (hlarge : threshold k ≤ T) :
    (cofactorBox k A B N).card ≤
      6*(Real.exp 1)^2*(T:ℝ)*B^2/(4:ℝ)^k := by
  let s := (cutoff k).primesBelow
  have hs : ∀ p ∈ s, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
  have hc : (cofactorBox k A B N).card ≤
      ∑ a ∈ Finset.Icc A B, ∑ b ∈ Finset.Icc A B, (cofactorInputs k a b N).card :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le))
  have hcard : (cofactorBox k A B N).card ≤
      (6*(T:ℝ)/(4:ℝ)^k) *
        (∑ a ∈ Finset.Icc A B, ∑ b ∈ Finset.Icc A B, weight s a * weight s b) := by
    calc
      _ ≤ ∑ a ∈ Finset.Icc A B, ∑ b ∈ Finset.Icc A B, ((cofactorInputs k a b N).card:ℝ) := by
        exact_mod_cast hc
      _ ≤ ∑ a ∈ Finset.Icc A B, ∑ b ∈ Finset.Icc A B,
          6*(T:ℝ)*weight s a*weight s b/(4:ℝ)^k := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        have haA := (Finset.mem_Icc.mp ha).1
        have hbA := (Finset.mem_Icc.mp hb).1
        apply cofactorInputs_card_le (hA.trans_le haA) (hA.trans_le hbA) k N T _ hlarge
        have hden : A*A ≤ a*b := Nat.mul_le_mul haA hbA
        have hh := Nat.div_le_div_left hden (Nat.mul_pos hA hA) (a := N)
        omega
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
  have hsub : Finset.Icc A B ⊆ Finset.Icc 1 B := by
    intro a ha
    obtain ⟨ha,hb⟩ := Finset.mem_Icc.mp ha
    exact Finset.mem_Icc.mpr ⟨by omega,hb⟩
  have hsum : (∑ a ∈ Finset.Icc A B, ∑ b ∈ Finset.Icc A B, weight s a*weight s b) ≤
      (Real.exp 1)^2*(B:ℝ)*B := by
    calc
      _ ≤ ∑ a ∈ Finset.Icc 1 B, ∑ b ∈ Finset.Icc 1 B, weight s a*weight s b := by
        apply (Finset.sum_le_sum (fun a _ =>
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun b _ _ => mul_nonneg (weight_nonneg hs a) (weight_nonneg hs b)))).trans
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro a _ _
        exact Finset.sum_nonneg (fun b _ => mul_nonneg (weight_nonneg hs a) (weight_nonneg hs b))
      _ ≤ _ := weight_box_sum_le hs B B
  calc
    _ ≤ (6*(T:ℝ)/(4:ℝ)^k) *
        (∑ a ∈ Finset.Icc A B, ∑ b ∈ Finset.Icc A B, weight s a*weight s b) := hcard
    _ ≤ (6*(T:ℝ)/(4:ℝ)^k) * ((Real.exp 1)^2*(B:ℝ)*B) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- A box with bounded cofactor ratio costs a multiple of `N/4^k`, provided
  its available progression length exceeds the explicit sieve threshold. -/
theorem cofactorBox_scaled_bound {A N : ℕ} (hA : 0<A) (hAN : A*A ≤ N)
    (k C : ℕ) (hlarge : threshold k ≤ N/(A*A)+1) :
    (cofactorBox k A (C*A) N).card ≤
      12*(Real.exp 1)^2*(C:ℝ)^2*N/(4:ℝ)^k := by
  have hh := cofactorBox_card_bound hA k (C*A) N (N/(A*A)+1) le_rfl hlarge
  have hA' : (0:ℝ)<A := by exact_mod_cast hA
  have hdiv : ((N/(A*A)+1:ℕ):ℝ) ≤ 2*(N:ℝ)/(A:ℝ)^2 := by
    have hcast : ((N/(A*A):ℕ):ℝ) ≤ (N:ℝ)/(A:ℝ)^2 := by
      simpa [sq] using (Nat.cast_div_le (α := ℝ) (m := N) (n := A*A))
    have hunit : (1:ℝ) ≤ (N:ℝ)/(A:ℝ)^2 := by
      apply (le_div_iff₀ (by positivity)).mpr
      simpa [sq] using (Nat.cast_le.mpr hAN : ((A*A:ℕ):ℝ)≤N)
    push_cast
    simp only [div_eq_mul_inv] at *
    linarith
  calc
    _ ≤ 6*(Real.exp 1)^2*((N/(A*A)+1:ℕ):ℝ)*((C*A:ℕ):ℝ)^2/(4:ℝ)^k := hh
    _ ≤ 6*(Real.exp 1)^2*(2*(N:ℝ)/(A:ℝ)^2)*((C*A:ℕ):ℝ)^2/(4:ℝ)^k := by
      gcongr
    _ = _ := by push_cast; field_simp; ring

end Erdos371CofactorSieve

#print axioms Erdos371CofactorSieve.cofactorInputs_card_le
#print axioms Erdos371CofactorSieve.cofactorBox_scaled_bound
