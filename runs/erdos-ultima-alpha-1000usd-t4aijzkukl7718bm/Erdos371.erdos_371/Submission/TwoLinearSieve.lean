import Submission.CoprimeResidueSieve

/-! A finite two-linear-form sieve for determinant-one pairs. -/

namespace Erdos371
namespace FiniteSieve
open Finset

noncomputable def linearResidues (p a b : ℕ) : Finset ℕ :=
  (range p).filter fun n => p ∣ a*n+b

lemma linearResidues_card (p a b : ℕ) (hp : 0 < p) (ha : a.Coprime p) :
    (linearResidues p a b).card = 1 := by
  classical
  letI : NeZero p := ⟨hp.ne'⟩
  let u := ZMod.unitOfCoprime a ha
  let x : ZMod p := -(b : ZMod p) * (u⁻¹ : (ZMod p)ˣ)
  have hx : p ∣ a*x.val+b := by
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    push_cast
    rw [ZMod.natCast_zmod_val]
    change (a : ZMod p) * x + b = 0
    rw [← ZMod.coe_unitOfCoprime a ha]
    dsimp [x]
    change (u : ZMod p) * (-(b : ZMod p) * (u⁻¹ : (ZMod p)ˣ)) + b = 0
    rw [mul_left_comm, Units.mul_inv, mul_one, neg_add_cancel]
  apply card_eq_one.mpr
  refine ⟨x.val, ?_⟩
  ext n
  simp only [linearResidues, mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨hn, hd⟩
    have hm : Nat.ModEq p (a*n+b) (a*x.val+b) := hd.modEq_zero_nat.trans hx.zero_modEq_nat
    have he := (hm.add_right_cancel' b).cancel_left_of_coprime ha.symm
    exact he.eq_of_lt_of_lt hn (ZMod.val_lt x)
  · rintro rfl
    exact ⟨ZMod.val_lt x, hx⟩

lemma twoLinearResidues_disjoint (p a b c d : ℕ) (hp : 1 < p)
    (hdet : a*d+1=b*c ∨ b*c+1=a*d) :
    Disjoint (linearResidues p a b) (linearResidues p c d) := by
  classical
  apply disjoint_left.mpr
  intro n hn hn'
  have hab := (mem_filter.mp hn).2
  have hcd := (mem_filter.mp hn').2
  have hab' : p ∣ c*(a*n+b) := dvd_mul_of_dvd_right hab c
  have hcd' : p ∣ a*(c*n+d) := dvd_mul_of_dvd_right hcd a
  have h1 : p ∣ 1 := by
    rcases hdet with h | h
    · have he : c*(a*n+b) = a*(c*n+d)+1 := by nlinarith
      rw [he] at hab'
      exact (Nat.dvd_add_iff_right hcd').mpr hab'
    · have he : a*(c*n+d) = c*(a*n+b)+1 := by nlinarith
      rw [he] at hcd'
      exact (Nat.dvd_add_iff_right hab').mpr hcd'
  have := Nat.dvd_one.mp h1
  omega

noncomputable def twoLinearResidues (p a b c d : ℕ) : Finset ℕ :=
  linearResidues p a b ∪ linearResidues p c d

lemma twoLinearResidues_card (p a b c d : ℕ) (hp : 1 < p)
    (ha : a.Coprime p) (hc : c.Coprime p)
    (hdet : a*d+1=b*c ∨ b*c+1=a*d) :
    (twoLinearResidues p a b c d).card = 2 := by
  rw [twoLinearResidues, card_union_of_disjoint (twoLinearResidues_disjoint p a b c d hp hdet),
    linearResidues_card p a b (by omega) ha, linearResidues_card p c d (by omega) hc]

lemma twoLinearResidues_subset (p a b c d : ℕ) :
    twoLinearResidues p a b c d ⊆ range p :=
  union_subset (filter_subset _ _) (filter_subset _ _)

lemma mod_mem_twoLinearResidues (p a b c d n : ℕ) (hp : 0 < p) :
    n%p ∈ twoLinearResidues p a b c d ↔ p ∣ a*n+b ∨ p ∣ c*n+d := by
  have h (u v : ℕ) : p ∣ u*(n%p)+v ↔ p ∣ u*n+v := by
    simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod]
  simp [twoLinearResidues, linearResidues, Nat.mod_lt n hp, h]

/-- An explicit finite two-form sieve bound. The primes used here are
coprime to both slopes; the determinant assumption makes their two roots distinct. -/
theorem twoLinear_brun_upper_bound (S : Finset ℕ) (a b c d N k : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ p ∈ S, a.Coprime p)
    (hc : ∀ p ∈ S, c.Coprime p) (hdet : a*d+1=b*c ∨ b*c+1=a*d)
    (hk : 6 * (∑ p ∈ S, (1 : ℝ)/p) ≤ (2*k+1 : ℕ) * Real.log 2) :
    (avoidanceCount (range N) (fun p n => p ∣ a*n+b ∨ p ∣ c*n+d) S : ℝ) ≤
      2 * N * Real.exp (-2 * (∑ p ∈ S, (1 : ℝ)/p)) +
      ∑ T ∈ S.powerset, if T.card ≤ 2*k then ∏ p ∈ T, (p : ℝ) else 0 := by
  classical
  have hlocal : ∀ p ∈ S, (twoLinearResidues p a b c d).card = 2 :=
    fun p hp => twoLinearResidues_card p a b c d (hS p hp).one_lt (ha p hp) (hc p hp) hdet
  have hmass : (∑ p ∈ S, (twoLinearResidues p a b c d).card / (p : ℝ)) =
      2 * (∑ p ∈ S, (1 : ℝ)/p) := by
    rw [mul_sum]
    exact sum_congr rfl fun p hp => by rw [hlocal p hp]; push_cast; ring
  have havoid : avoidanceCount (range N) (fun p n => n%p ∈ twoLinearResidues p a b c d) S =
      avoidanceCount (range N) (fun p n => p ∣ a*n+b ∨ p ∣ c*n+d) S := by
    unfold avoidanceCount
    congr 1
    ext n
    simp only [mem_filter]
    apply and_congr_right
    intro hn
    exact forall₂_congr fun p hp => not_congr (mod_mem_twoLinearResidues p a b c d n (hS p hp).pos)
  have hcop : (↑S : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq
  have hk' : 3 * (∑ p ∈ S, (twoLinearResidues p a b c d).card / (p : ℝ)) ≤
      (2*k+1 : ℕ) * Real.log 2 := by rw [hmass]; linarith
  have h := residue_brun_upper_bound S id (fun p => twoLinearResidues p a b c d)
    (fun p hp => (hS p hp).ne_zero) hcop (fun p _ => twoLinearResidues_subset p a b c d) N k hk'
  simpa only [id_eq, havoid, hmass, neg_mul] using h

/-- A polynomial upper bound for the total CRT rounding error when all
sieving primes are at most `z` and there are at most `z` of them. -/
lemma prime_subset_error_le (S : Finset ℕ) (k z : ℕ) (hz : 1 ≤ z)
    (hcard : S.card ≤ z) (hS : ∀ p ∈ S, p ≤ z) :
    (∑ T ∈ S.powerset, if T.card ≤ 2*k then ∏ p ∈ T, (p : ℝ) else 0) ≤
      (2*k+1 : ℕ) * (z : ℝ)^(4*k) := by
  have hZ : (1 : ℝ) ≤ (z : ℝ)^2 := one_le_pow₀ (by exact_mod_cast hz)
  have hsum : (∑ p ∈ S, (p : ℝ)) ≤ (z : ℝ)^2 := by
    calc
      _ ≤ ∑ _p ∈ S, (z : ℝ) := sum_le_sum fun p hp => by exact_mod_cast hS p hp
      _ = (S.card : ℝ)*z := by simp
      _ ≤ (z : ℝ)*z := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = _ := by ring
  have h := truncated_subset_product_sum_le S (fun p => (p : ℝ)) (2*k)
    (fun _ _ => by positivity) ((z : ℝ)^2) hZ hsum
  simpa only [← pow_mul, ← Nat.mul_assoc, Nat.reduceMul, Nat.cast_add, Nat.cast_one] using h

/-- A bound on simultaneous prime values, with the small-prime exceptions
explicitly excluded. -/
theorem twoLinear_prime_count_le (S : Finset ℕ) (a b c d N k z : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ p ∈ S, a.Coprime p)
    (hc : ∀ p ∈ S, c.Coprime p) (hdet : a*d+1=b*c ∨ b*c+1=a*d)
    (hk : 6 * (∑ p ∈ S, (1 : ℝ)/p) ≤ (2*k+1 : ℕ) * Real.log 2)
    (hz : 1 ≤ z) (hcard : S.card ≤ z) (hSz : ∀ p ∈ S, p ≤ z) :
    (((range N).filter fun n =>
      (a*n+b).Prime ∧ (c*n+d).Prime ∧ z < a*n+b ∧ z < c*n+d).card : ℝ) ≤
      2*N*Real.exp (-2 * (∑ p ∈ S, (1 : ℝ)/p)) +
        (2*k+1 : ℕ) * (z : ℝ)^(4*k) := by
  classical
  have hcount : ((range N).filter fun n =>
      (a*n+b).Prime ∧ (c*n+d).Prime ∧ z < a*n+b ∧ z < c*n+d).card ≤
      avoidanceCount (range N) (fun p n => p ∣ a*n+b ∨ p ∣ c*n+d) S := by
    unfold avoidanceCount
    conv_rhs => rw [filter_congr_decidable]
    apply card_le_card
    intro n hn
    obtain ⟨hn, h1, h2, hz1, hz2⟩ := mem_filter.mp hn
    apply mem_filter.mpr ⟨hn, ?_⟩
    intro p hp hbad
    rcases hbad with hd | hd
    · rcases (Nat.dvd_prime h1).mp hd with he | he
      · exact (hS p hp).ne_one he
      · have := hSz p hp
        omega
    · rcases (Nat.dvd_prime h2).mp hd with he | he
      · exact (hS p hp).ne_one he
      · have := hSz p hp
        omega
  have hb := twoLinear_brun_upper_bound S a b c d N k hS ha hc hdet hk
  have he := prime_subset_error_le S k z hz hcard hSz
  exact (show (_ : ℝ) ≤ _ by exact_mod_cast hcount).trans
    (hb.trans (add_le_add le_rfl he))

#print axioms twoLinear_prime_count_le
#print axioms twoLinear_brun_upper_bound
end FiniteSieve
end Erdos371
