import Submission.FourierSubsetObstruction

/-! Four-term cancellation and a necessary Fourier condition for odd covers.
These results do not establish the required universal frequency selection. -/
namespace Erdos7FourTermCancellation
open scoped BigOperators
open Erdos7SubsetFourier
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Four points of the unit circle summing to zero form opposite pairs. -/
theorem four_unit_zero_pairs (a b c d : ℂ)
    (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1) (hd : ‖d‖=1)
    (hz : a+b+c+d=0) :
    (a = -b ∧ c = -d) ∨ (a = -c ∧ b = -d) ∨ (a = -d ∧ b = -c) := by
  have hau : a*star a=1 := by simpa [ha] using Complex.mul_conj' a
  have hbu : b*star b=1 := by simpa [hb] using Complex.mul_conj' b
  have hcu : c*star c=1 := by simpa [hc] using Complex.mul_conj' c
  have hdu : d*star d=1 := by simpa [hd] using Complex.mul_conj' d
  have hstar : a*b*c*d*star (a+b+c+d)=0 := by rw [hz,star_zero,mul_zero]
  have he : a*b*c*d*star (a+b+c+d) = b*c*d+a*c*d+a*b*d+a*b*c := by
    simp only [star_add]
    calc
      _ = (a*star a)*b*c*d + a*(b*star b)*c*d +
          a*b*(c*star c)*d + a*b*c*(d*star d) := by ring
      _ = _ := by rw [hau,hbu,hcu,hdu]; ring
  rw [he] at hstar
  have hp : (a+b)*(a+c)*(a+d)=0 := by
    calc
      _ = a^2*(a+b+c+d)+(b*c*d+a*c*d+a*b*d+a*b*c) := by ring
      _ = 0 := by rw [hz,hstar]; ring
  rcases mul_eq_zero.mp hp with habc | had
  · rcases mul_eq_zero.mp habc with hab | hac
    · left
      exact ⟨eq_neg_of_add_eq_zero_left hab,eq_neg_of_add_eq_zero_left (by linear_combination hz-hab)⟩
    · right; left
      exact ⟨eq_neg_of_add_eq_zero_left hac,eq_neg_of_add_eq_zero_left (by linear_combination hz-hac)⟩
  · right; right
    exact ⟨eq_neg_of_add_eq_zero_left had,eq_neg_of_add_eq_zero_left (by linear_combination hz-had)⟩

/-- Odd powers preserve four-term vanishing on the unit circle. This is
special to four terms, not a rule for arbitrary finite vanishing sums. -/
theorem four_unit_zero_odd_pow (a b c d : ℂ)
    (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1) (hd : ‖d‖=1)
    (hz : a+b+c+d=0) (n : ℕ) (hn : Odd n) :
    a^n+b^n+c^n+d^n=0 := by
  rcases four_unit_zero_pairs a b c d ha hb hc hd hz with
    ⟨hab,hcd⟩ | ⟨hac,hbd⟩ | ⟨had,hbc⟩
  · rw [hab,hcd,hn.neg_pow,hn.neg_pow]; ring
  · rw [hac,hbd,hn.neg_pow,hn.neg_pow]; ring
  · rw [had,hbc,hn.neg_pow,hn.neg_pow]; ring

lemma signed_char_norm {N : ℕ} [NeZero N] (u : ZMod N) (t : ℕ) :
    ‖(-1 : ℂ)^t*ZMod.stdAddChar u‖=1 := by
  simp [norm_mul,ZMod.stdAddChar_apply]

lemma signed_char_odd_pow {N : ℕ} [NeZero N] (hN : Odd N)
    (u : ZMod N) (t : ℕ) :
    ((-1 : ℂ)^t*ZMod.stdAddChar u)^N=(-1 : ℂ)^t := by
  have hchi : ZMod.stdAddChar u ^ N=1 := by
    rw [← AddChar.map_nsmul_eq_pow]
    simp [nsmul_eq_mul]
  rw [mul_pow,hchi,mul_one,←pow_mul,mul_comm t N,pow_mul,hN.neg_one_pow]


/-- Opposite signed odd-order character values must have opposite signs
and identical phases; cancellation of equal signs is impossible. -/
theorem signed_char_opposite_iff {N : ℕ} [NeZero N] (hN : Odd N)
    (u v : ZMod N) (s t : ℕ) :
    (-1 : ℂ)^s*ZMod.stdAddChar u = -((-1 : ℂ)^t*ZMod.stdAddChar v) ↔
      (-1 : ℂ)^s = -(-1 : ℂ)^t ∧ u=v := by
  constructor
  · intro h
    have hsign := congrArg (fun z : ℂ => z^N) h
    simp only [hN.neg_pow,signed_char_odd_pow hN] at hsign
    refine ⟨hsign,?_⟩
    rw [hsign] at h
    have hmul : (-1 : ℂ)^t*ZMod.stdAddChar u = (-1 : ℂ)^t*ZMod.stdAddChar v := by
      simpa only [neg_mul,neg_inj] using h
    exact ZMod.injective_stdAddChar (mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) hmul)
  · rintro ⟨hs,rfl⟩
    rw [hs,neg_mul]

/-- All possibilities for four-term cancellation, retaining phase data. -/
theorem four_signed_char_pairs {N : ℕ} [NeZero N] (hN : Odd N)
    (u : Fin 4 → ZMod N) (t : Fin 4 → ℕ)
    (hz : (∑ j : Fin 4, (-1 : ℂ)^t j*ZMod.stdAddChar (u j))=0) :
    (((-1 : ℂ)^t 0 = -(-1 : ℂ)^t 1 ∧ u 0=u 1) ∧
      ((-1 : ℂ)^t 2 = -(-1 : ℂ)^t 3 ∧ u 2=u 3)) ∨
    (((-1 : ℂ)^t 0 = -(-1 : ℂ)^t 2 ∧ u 0=u 2) ∧
      ((-1 : ℂ)^t 1 = -(-1 : ℂ)^t 3 ∧ u 1=u 3)) ∨
    (((-1 : ℂ)^t 0 = -(-1 : ℂ)^t 3 ∧ u 0=u 3) ∧
      ((-1 : ℂ)^t 1 = -(-1 : ℂ)^t 2 ∧ u 1=u 2)) := by
  have h := four_unit_zero_pairs
    ((-1 : ℂ)^t 0*ZMod.stdAddChar (u 0))
    ((-1 : ℂ)^t 1*ZMod.stdAddChar (u 1))
    ((-1 : ℂ)^t 2*ZMod.stdAddChar (u 2))
    ((-1 : ℂ)^t 3*ZMod.stdAddChar (u 3))
    (signed_char_norm _ _) (signed_char_norm _ _) (signed_char_norm _ _)
    (signed_char_norm _ _) (by simpa [Fin.sum_univ_succ,add_assoc] using hz)
  simpa only [signed_char_opposite_iff hN] using h

/-- If a signed four-term sum of odd-order character values vanishes, its
four signs sum to zero: exactly two are positive and two negative. -/
theorem four_signed_char_balanced {N : ℕ} [NeZero N] (hN : Odd N)
    (u : Fin 4 → ZMod N) (t : Fin 4 → ℕ)
    (hz : (∑ j : Fin 4, (-1 : ℂ)^t j*ZMod.stdAddChar (u j))=0) :
    (∑ j : Fin 4, (-1 : ℂ)^t j)=0 := by
  have h := four_unit_zero_odd_pow
    ((-1 : ℂ)^t 0*ZMod.stdAddChar (u 0))
    ((-1 : ℂ)^t 1*ZMod.stdAddChar (u 1))
    ((-1 : ℂ)^t 2*ZMod.stdAddChar (u 2))
    ((-1 : ℂ)^t 3*ZMod.stdAddChar (u 3))
    (signed_char_norm _ _) (signed_char_norm _ _) (signed_char_norm _ _)
    (signed_char_norm _ _) (by simpa [Fin.sum_univ_succ,add_assoc] using hz) N hN
  simp only [signed_char_odd_pow hN] at h
  simpa [Fin.sum_univ_succ,add_assoc] using h

/-- A coefficient having precisely four distinct subset representations
must have balanced subset-cardinality signs in an odd-order kernel cover. -/
theorem cover_four_representations_balanced {ι : Type*} [Fintype ι]
    {N : ℕ} [NeZero N] (hN : Odd N) (k a : ι → ZMod N)
    (hc : ∀ x : ZMod N, ∃ i, k i*(x-a i)=0)
    (r : Fin 4 → Finset ι) (hr : Function.Injective r) (b : ZMod N)
    (hfreq : ∀ s : Finset ι, (∑ i ∈ s, k i=b) ↔ ∃ j, s=r j) :
    (∑ j : Fin 4, (-1 : ℂ)^(r j).card)=0 := by
  classical
  have hz := cover_coefficient_vanishes k a hc b
  rw [←Finset.sum_filter] at hz
  have hset : (Finset.univ : Finset ι).powerset.filter (fun s => ∑ i ∈ s, k i=b) =
      Finset.univ.image r := by
    ext s
    simp [hfreq,eq_comm]
  rw [hset,Finset.sum_image (by intro i _ j _ h; exact hr h)] at hz
  exact four_signed_char_balanced hN (fun j => -(∑ i ∈ r j, k i*a i))
    (fun j => (r j).card) hz

/-- An unbalanced four-representation coefficient rules out an odd kernel
cover independently of the phases/residues. -/
theorem not_cover_four_unbalanced {ι : Type*} [Fintype ι]
    {N : ℕ} [NeZero N] (hN : Odd N) (k a : ι → ZMod N)
    (r : Fin 4 → Finset ι) (hr : Function.Injective r) (b : ZMod N)
    (hfreq : ∀ s : Finset ι, (∑ i ∈ s, k i=b) ↔ ∃ j, s=r j)
    (hsign : (∑ j : Fin 4, (-1 : ℂ)^(r j).card) ≠ 0) :
    ¬ (∀ x : ZMod N, ∃ i, k i*(x-a i)=0) := by
  intro hc
  exact hsign (cover_four_representations_balanced hN k a hc r hr b hfreq)

/-- Arithmetic wrapper; exact frequency orders are not required. -/
theorem not_arithmetic_cover_four_unbalanced {ι : Type*} [Fintype ι]
    {N : ℕ} [NeZero N] (hN : Odd N) (m : ι → ℕ) (a : ι → ℤ)
    (k : ι → ZMod N) (horder : ∀ i, (m i : ZMod N)*k i=0)
    (r : Fin 4 → Finset ι) (hr : Function.Injective r) (b : ZMod N)
    (hfreq : ∀ s : Finset ι, (∑ i ∈ s, k i=b) ↔ ∃ j, s=r j)
    (hsign : (∑ j : Fin 4, (-1 : ℂ)^(r j).card) ≠ 0) :
    ¬ (∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i) := by
  intro hc
  apply not_cover_four_unbalanced hN k (fun i => (a i : ZMod N)) r hr b hfreq hsign
  intro x
  obtain ⟨i,z,hz⟩ := hc (x.val : ℤ)
  refine ⟨i,?_⟩
  have he : x-(a i : ZMod N)=(m i : ZMod N)*(z : ZMod N) := by
    have hh := congrArg (fun t : ℤ => (t : ZMod N)) hz
    simpa using hh
  rw [he,←mul_assoc,mul_comm (k i) (m i : ZMod N),horder i,zero_mul]

/-- The balance conclusion does not extend to arbitrary even numbers of
terms: six positive third roots already sum to zero. This is not a covering
system and makes no assertion about distinct arithmetic moduli. -/
theorem six_positive_vanishing :
    (∑ j : Fin 2 × ZMod 3, ZMod.stdAddChar j.2)=0 ∧
      (∑ _j : Fin 2 × ZMod 3, (1 : ℂ))=6 := by
  constructor
  · have hz : (∑ x : ZMod 3, ZMod.stdAddChar x)=0 := by
      have h := AddChar.sum_eq_zero_of_ne_one
        (ZMod.isPrimitive_stdAddChar 3 (show (1 : ZMod 3) ≠ 0 by decide))
      simpa using h
    rw [Fintype.sum_prod_type]
    simp [hz]
  · norm_num [Fintype.card_prod]

#print axioms four_unit_zero_pairs
#print axioms four_signed_char_pairs
#print axioms six_positive_vanishing
#print axioms four_signed_char_balanced
#print axioms not_arithmetic_cover_four_unbalanced
end Erdos7FourTermCancellation
