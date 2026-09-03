import Submission.CommonEndpointPrimeSkew

/-! A global bound for enlarging the cofactor-dependent prime endpoints.
Above the square-root threshold, uniqueness of the large prime divisors
bounds the entire overhang by one interval length, independently of the
number of primes or cofactor blocks. No prime-character cancellation is
asserted here. -/
namespace Erdos371
open Finset

private def endpointTriples (P S : Finset ℕ) (C M : ℕ) (F : ℕ → ℕ) (s : Bool) :
    Finset ((ℕ × ℕ) × ℕ) :=
  ((P ×ˢ S) ×ˢ ((Ioc C M).filter Nat.Prime)).filter fun z =>
    z.2 ≤ F z.1.2 ∧ z.1.1 ∣ if s then z.1.2*z.2-1 else z.1.2*z.2+1

private lemma mem_endpointTriples (P S : Finset ℕ) (C M : ℕ) (F : ℕ → ℕ) (s : Bool)
    (p b q : ℕ) :
    ((p,b),q) ∈ endpointTriples P S C M F s ↔
      p ∈ P ∧ b ∈ S ∧ C < q ∧ q ≤ M ∧ q.Prime ∧ q ≤ F b ∧
        p ∣ if s then b*q-1 else b*q+1 := by
  simp only [endpointTriples, mem_filter, mem_product, mem_Ioc]
  tauto

private lemma endpointTriples_card (P S : Finset ℕ) (C M : ℕ) (F : ℕ → ℕ) (s : Bool)
    (hF : ∀ b ∈ S, F b ≤ M) :
    (endpointTriples P S C M F s).card =
      ∑ p ∈ P, ∑ b ∈ S, oppositePrimeCount C (F b) p b s := by
  have he (p b : ℕ) (hb : b ∈ S) :
      oppositePrimeCount C (F b) p b s =
        (((Ioc C M).filter Nat.Prime).filter fun q =>
          q ≤ F b ∧ p ∣ if s then b*q-1 else b*q+1).card := by
    unfold oppositePrimeCount
    congr 1
    ext q
    simp only [mem_filter, mem_Ioc]
    have hq : q ≤ F b → q ≤ M := fun h => h.trans (hF b hb)
    tauto
  unfold endpointTriples
  rw [card_eq_sum_ones, sum_filter, sum_product]
  rw [sum_product]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro b hb
  rw [he p b hb, card_eq_sum_ones]
  simp only [sum_filter]

private lemma endpointTriples_mono (P S : Finset ℕ) (C M : ℕ) (F G : ℕ → ℕ)
    (s : Bool) (hFG : ∀ b ∈ S, G b ≤ F b) :
    endpointTriples P S C M G s ⊆ endpointTriples P S C M F s := by
  rintro ⟨⟨p,b⟩,q⟩ ht
  rw [mem_endpointTriples] at ht ⊢
  exact ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2.1,
    ht.2.2.2.2.2.1.trans (hFG b ht.2.1),ht.2.2.2.2.2.2⟩

private lemma endpointTriples_product_bounds (P S : Finset ℕ) (B C M : ℕ)
    (F : ℕ → ℕ) (s : Bool) (hB : 2 ≤ B) (hBC : B ≤ C)
    (hS : ∀ b ∈ S, 0 < b) (hF : ∀ b ∈ S, b*F b ≤ M)
    (p b q : ℕ) (ht : ((p,b),q) ∈ endpointTriples P S C M F s) :
    1 < b*q ∧ b*q ≤ M := by
  rw [mem_endpointTriples] at ht
  have hb := hS b ht.2.1
  have hq := ht.2.2.1
  have hFq := ht.2.2.2.2.2.1
  constructor
  · nlinarith
  · exact (Nat.mul_le_mul_left b hFq).trans (hF b ht.2.1)

/-- The product b*q determines all three coordinates of a triple at a fixed
orientation. This uses uniqueness for q dividing b*q and for p dividing
b*q-1 or b*q+1. -/
private lemma endpointTriples_product_injective (P S : Finset ℕ) (B C M : ℕ)
    (F : ℕ → ℕ) (s : Bool) (hB : 2 ≤ B) (hBC : B ≤ C)
    (hP : ∀ p ∈ P, p.Prime ∧ B < p) (hS : ∀ b ∈ S, 0 < b)
    (hF : ∀ b ∈ S, b*F b ≤ M) (hsize : M+1 ≤ B^2) :
    Set.InjOn (fun z : (ℕ × ℕ) × ℕ => z.1.2*z.2)
      (endpointTriples P S C M F s : Set ((ℕ × ℕ) × ℕ)) := by
  rintro ⟨⟨p,b⟩,q⟩ ht ⟨⟨p',b'⟩,q'⟩ ht' he
  have hnb := endpointTriples_product_bounds P S B C M F s hB hBC hS hF p b q ht
  have hnb' := endpointTriples_product_bounds P S B C M F s hB hBC hS hF p' b' q' ht'
  simp only [mem_coe] at ht ht'
  rw [mem_endpointTriples] at ht ht'
  dsimp only at he
  have hq := ht.2.2.2.2.1
  have hq' := ht'.2.2.2.2.1
  have hqq' : q=q' := prime_dvd_unique_above_sqrt B (b*q) q q'
    (by omega) (by omega) hq hq' (by omega) (by omega)
    (dvd_mul_left _ _) (by rw [he]; exact dvd_mul_left _ _)
  subst q'
  have hbb' : b=b' := Nat.mul_right_cancel (by omega : 0 < q) he
  subst b'
  have hp := hP p ht.1
  have hp' := hP p' ht'.1
  have hn0 : 0 < if s then b*q-1 else b*q+1 := by cases s <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
  have hnsize : (if s then b*q-1 else b*q+1) ≤ B^2 := by cases s <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
  have hpp' : p=p' := prime_dvd_unique_above_sqrt B _ p p' hn0 hnsize
    hp.1 hp'.1 hp.2 hp'.2 ht.2.2.2.2.2.2 ht'.2.2.2.2.2.2
  subst p'
  rfl

private lemma endpointTriples_overhang (P S : Finset ℕ) (B C N M : ℕ)
    (F : ℕ → ℕ) (s : Bool) (hB : 2 ≤ B) (hBC : B ≤ C)
    (hP : ∀ p ∈ P, p.Prime ∧ B < p) (hS : ∀ b ∈ S, 0 < b)
    (hF : ∀ b ∈ S, b*F b ≤ M) (hsize : M+1 ≤ B^2) :
    (endpointTriples P S C M F s \
      endpointTriples P S C M (fun b => N/b) s).card ≤ M-N := by
  calc
    _ ≤ (Ioc N M).card := by
      apply card_le_card_of_injOn (fun z : (ℕ × ℕ) × ℕ => z.1.2*z.2)
      · rintro ⟨⟨p,b⟩,q⟩ ht
        obtain ⟨ht,hn⟩ := mem_sdiff.mp ht
        have hnb := endpointTriples_product_bounds P S B C M F s hB hBC hS hF p b q ht
        rw [mem_endpointTriples] at ht hn
        have hb := hS b ht.2.1
        have hqN : ¬q ≤ N/b := by
          intro h
          exact hn ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2.1,h,ht.2.2.2.2.2.2⟩
        have hprod : N < b*q := by
          have heq : q ≤ N/b ↔ b*q ≤ N := by rw [Nat.le_div_iff_mul_le hb,mul_comm]
          rw [heq] at hqN
          omega
        exact mem_Ioc.mpr ⟨hprod,hnb.2⟩
      · exact (endpointTriples_product_injective P S B C M F s hB hBC hP hS hF hsize).mono
          (fun _ h => (mem_sdiff.mp h).1)
    _ = _ := Nat.card_Ioc N M

/-- Enlarging all prime endpoints costs at most M-N in each orientation,
not a separate error for each prime or cofactor. -/
theorem oppositePrimeCount_total_increment_bounds (P S : Finset ℕ) (B C N M : ℕ)
    (F : ℕ → ℕ) (s : Bool) (hB : 2 ≤ B) (hBC : B ≤ C)
    (hP : ∀ p ∈ P, p.Prime ∧ B < p) (hS : ∀ b ∈ S, 0 < b)
    (hlo : ∀ b ∈ S, N/b ≤ F b) (hhi : ∀ b ∈ S, b*F b ≤ M)
    (hsize : M+1 ≤ B^2) :
    0 ≤ (∑ p ∈ P, ∑ b ∈ S, (oppositePrimeCount C (F b) p b s : ℝ)) -
      (∑ p ∈ P, ∑ b ∈ S, (oppositePrimeCount C (N/b) p b s : ℝ)) ∧
    (∑ p ∈ P, ∑ b ∈ S, (oppositePrimeCount C (F b) p b s : ℝ)) -
      (∑ p ∈ P, ∑ b ∈ S, (oppositePrimeCount C (N/b) p b s : ℝ)) ≤ (M-N : ℕ) := by
  have hFM : ∀ b ∈ S, F b ≤ M := by
    intro b hb
    have := hS b hb
    have := hhi b hb
    nlinarith
  have hGM : ∀ b ∈ S, N/b ≤ M := fun b hb => (hlo b hb).trans (hFM b hb)
  have hsub := endpointTriples_mono P S C M F (fun b => N/b) s hlo
  have he := card_sdiff_of_subset hsub
  have hcard := card_le_card hsub
  have hu := endpointTriples_overhang P S B C N M F s hB hBC hP hS hhi hsize
  rw [he] at hu
  rw [endpointTriples_card P S C M F s hFM,
    endpointTriples_card P S C M (fun b => N/b) s hGM] at hu hcard
  constructor
  · have h := (Nat.cast_le (α := ℝ)).mpr hcard
    push_cast at h
    linarith
  · have h := (Nat.cast_le (α := ℝ)).mpr hu
    rw [Nat.cast_sub hcard] at h
    push_cast at h
    exact h

noncomputable def cutoffPrimeSkew (P S : Finset ℕ) (C : ℕ) (F : ℕ → ℕ) : ℝ :=
  ∑ p ∈ P, ∑ b ∈ S, ((oppositePrimeCount C (F b) p b true : ℝ) -
    oppositePrimeCount C (F b) p b false)

/-- Both orientation increments lie in the same interval [0,M-N], so their
signed difference is bounded by M-N, rather than twice that quantity. -/
theorem cutoffPrimeSkew_endpoint_bound (P S : Finset ℕ) (B C N M : ℕ)
    (F : ℕ → ℕ) (hB : 2 ≤ B) (hBC : B ≤ C)
    (hP : ∀ p ∈ P, p.Prime ∧ B < p) (hS : ∀ b ∈ S, 0 < b)
    (hlo : ∀ b ∈ S, N/b ≤ F b) (hhi : ∀ b ∈ S, b*F b ≤ M)
    (hsize : M+1 ≤ B^2) :
    |cutoffPrimeSkew P S C F - cutoffPrimeSkew P S C (fun b => N/b)| ≤ (M-N : ℕ) := by
  have ht := oppositePrimeCount_total_increment_bounds P S B C N M F true
    hB hBC hP hS hlo hhi hsize
  have hf := oppositePrimeCount_total_increment_bounds P S B C N M F false
    hB hBC hP hS hlo hhi hsize
  simp only [cutoffPrimeSkew,sum_sub_distrib]
  rw [abs_le]
  constructor <;> linarith

/-- Specialization to the actual common-endpoint prime-band kernel. -/
theorem commonEndpointPrimeSkew_endpoint_bound (B C N M : ℕ) (F : ℕ → ℕ)
    (hB : 2 ≤ B) (hBC : B ≤ C)
    (hlo : ∀ b ∈ Icc 1 (N/(C+1)), N/b ≤ F b)
    (hhi : ∀ b ∈ Icc 1 (N/(C+1)), b*F b ≤ M)
    (hsize : M+1 ≤ B^2) :
    |cutoffPrimeSkew ((range (N+2)).filter fun p => p.Prime ∧ B<p ∧ p≤C)
        (Icc 1 (N/(C+1))) C F - commonEndpointPrimeSkew B C N| ≤ (M-N : ℕ) := by
  apply cutoffPrimeSkew_endpoint_bound _ _ B C N M F hB hBC
  · intro p hp
    have h := (mem_filter.mp hp).2
    exact ⟨h.1,h.2.1⟩
  · intro b hb
    exact (mem_Icc.mp hb).1
  · exact hlo
  · exact hhi
  · exact hsize

/-- A cofactor rounding map gives a valid enlarged endpoint whenever the
cross-multiplied relative error is at most M/N. -/
lemma rounded_prime_endpoint_bounds (N M b d : ℕ) (hd : 0 < d) (hdb : d ≤ b)
    (hcross : b*N ≤ M*d) :
    N/b ≤ N/d ∧ b*(N/d) ≤ M := by
  refine ⟨Nat.div_le_div_left hdb hd,?_⟩
  apply Nat.le_of_mul_le_mul_right (c := d) _ hd
  calc
    b*(N/d)*d = b*(d*(N/d)) := by ring
    _ ≤ b*N := Nat.mul_le_mul_left b (Nat.mul_div_le N d)
    _ ≤ M*d := hcross

noncomputable def roundedPrimeSkew (P S : Finset ℕ) (C N : ℕ) (r : ℕ → ℕ) : ℝ :=
  ∑ d ∈ S.image r, ∑ p ∈ P, ∑ b ∈ S.filter (fun b => r b=d),
    ((oppositePrimeCount C (N/d) p b true : ℝ) - oppositePrimeCount C (N/d) p b false)

/-- The prime endpoint is constant on each cofactor block. This identity
keeps the actual finite block, without enlarging it to an interval. -/
lemma roundedPrimeSkew_eq_cutoff (P S : Finset ℕ) (C N : ℕ) (r : ℕ → ℕ) :
    roundedPrimeSkew P S C N r = cutoffPrimeSkew P S C (fun b => N/(r b)) := by
  unfold roundedPrimeSkew cutoffPrimeSkew
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  have hf := sum_fiberwise_of_maps_to (s := S) (t := S.image r) (g := r)
    (fun b hb => mem_image_of_mem r hb)
    (fun b => (oppositePrimeCount C (N/(r b)) p b true : ℝ) -
      oppositePrimeCount C (N/(r b)) p b false)
  rw [← hf]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro b hb
  rw [(mem_filter.mp hb).2]

/-- A finite rectangularization error for the original prime-band kernel.
There is no factor for the number of cofactor blocks or prime moduli. -/
theorem commonEndpointPrimeSkew_rounding_bound (B C N M : ℕ) (r : ℕ → ℕ)
    (hB : 2 ≤ B) (hBC : B ≤ C)
    (hr : ∀ b ∈ Icc 1 (N/(C+1)), 0 < r b ∧ r b ≤ b ∧ b*N ≤ M*r b)
    (hsize : M+1 ≤ B^2) :
    |roundedPrimeSkew ((range (N+2)).filter fun p => p.Prime ∧ B<p ∧ p≤C)
        (Icc 1 (N/(C+1))) C N r - commonEndpointPrimeSkew B C N| ≤ (M-N : ℕ) := by
  rw [roundedPrimeSkew_eq_cutoff]
  apply commonEndpointPrimeSkew_endpoint_bound B C N M _ hB hBC
  · intro b hb
    obtain ⟨hr0,hrb,hcross⟩ := hr b hb
    exact (rounded_prime_endpoint_bounds N M b (r b) hr0 hrb hcross).1
  · intro b hb
    obtain ⟨hr0,hrb,hcross⟩ := hr b hb
    exact (rounded_prime_endpoint_bounds N M b (r b) hr0 hrb hcross).2
  · exact hsize

/-- The entire smooth-cutoff skew is within M-N+1 of the rectangularized
prime sum, including its original endpoint correction. -/
theorem smoothCutoffSkew_rounding_bound (B C N M : ℕ) (r : ℕ → ℕ)
    (hB : 2 ≤ B) (hBC : B ≤ C) (hNM : N ≤ M)
    (hr : ∀ b ∈ Icc 1 (N/(C+1)), 0 < r b ∧ r b ≤ b ∧ b*N ≤ M*r b)
    (hsize : M+1 ≤ B^2) :
    |smoothCutoffSkew B C N -
      roundedPrimeSkew ((range (N+2)).filter fun p => p.Prime ∧ B<p ∧ p≤C)
        (Icc 1 (N/(C+1))) C N r| ≤ (M-N : ℕ)+1 := by
  have hrb := commonEndpointPrimeSkew_rounding_bound B C N M r hB hBC hr hsize
  have he := smoothCutoffSkew_odd_hyperbola_bound B C N (by omega) hBC (by omega)
  rw [← commonEndpointPrimeSkew_characters, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at he
  have ht := abs_sub_le (smoothCutoffSkew B C N) (commonEndpointPrimeSkew B C N)
    (roundedPrimeSkew ((range (N+2)).filter fun p => p.Prime ∧ B<p ∧ p≤C)
      (Icc 1 (N/(C+1))) C N r)
  rw [abs_sub_comm (commonEndpointPrimeSkew B C N)] at ht
  linarith

/-- Odd-character expansion for any positive cofactor block. In a rounded
block the prime endpoint X is independent of the cofactor b. -/
theorem cofactorSetOppositePrimeSkew_characters (C X p : ℕ) [NeZero p]
    (S : Finset ℕ) (hS : ∀ b ∈ S, 0 < b) :
    (p.totient : ℂ) * (∑ b ∈ S,
      ((oppositePrimeCount C X p b true : ℂ) - oppositePrimeCount C X p b false)) =
      2 * ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ p)).filter DirichletCharacter.Odd,
        (∑ b ∈ S, χ (b : ZMod p)) *
          (∑ q ∈ (Ioc C X).filter Nat.Prime, χ (q : ZMod p)) := by
  classical
  rw [mul_sum]
  calc
    _ = ∑ b ∈ S, 2 * ∑ χ : DirichletCharacter ℂ p, if χ.Odd then
        χ (b : ZMod p) * (∑ q ∈ (Ioc C X).filter Nat.Prime, χ (q : ZMod p)) else 0 := by
      apply sum_congr rfl
      intro b hb
      exact oppositePrimeCount_odd_characters C X p b (hS b hb)
    _ = _ := by
      simp_rw [← sum_filter, ← mul_sum]
      rw [sum_comm]
      simp only [sum_mul]

#print axioms oppositePrimeCount_total_increment_bounds
#print axioms cutoffPrimeSkew_endpoint_bound
#print axioms commonEndpointPrimeSkew_rounding_bound
#print axioms smoothCutoffSkew_rounding_bound
#print axioms cofactorSetOppositePrimeSkew_characters
end Erdos371
