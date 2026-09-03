import FormalConjecturesUtil
import Submission.Independent126

/-!
# A binary-signature bound for Erdős problem 126

For a finite set of positive natural numbers, the number of elements is at most
`2 ^ S.card`, where `S` is the prime support of the ordered off-diagonal product
of pair sums. The color at an odd prime records the half containing the nonzero
residue of the prime-free part; at two it records the odd part modulo four.

Equal colors at all primes dividing a pair sum force that sum to divide twice
either entry, and hence force the entries to be equal. This is only an
exponential cardinality bound, not the conjectural superlogarithmic bound.
Neither statement from `Submission.Spec` is imported.
-/

namespace Signature126

/-- The exact prime support in the problem, including both orders of each pair. -/
def primeSupport (A : Finset ℕ) : Finset ℕ :=
  (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors

/-- A single bit at each prime. The exceptional bit at two uses modulus four. -/
def primeColor (p a : ℕ) : Bool :=
  if p = 2 then decide (ordCompl[2] a % 4 = 1)
  else decide (ordCompl[p] a % p ≤ p / 2)

private theorem same_half_not_dvd_add {p u v : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hu : ¬p ∣ u) (hv : ¬p ∣ v)
    (hc : decide (u % p ≤ p / 2) = decide (v % p ≤ p / 2)) :
    ¬p ∣ u + v := by
  intro hd
  have hru := Nat.mod_lt u hp.pos
  have hrv := Nat.mod_lt v hp.pos
  have hru0 : u % p ≠ 0 := fun h => hu (Nat.dvd_of_mod_eq_zero h)
  have hrv0 : v % p ≠ 0 := fun h => hv (Nat.dvd_of_mod_eq_zero h)
  have hsum : (u % p + v % p) % p = 0 := by
    rw [← Nat.add_mod]
    exact Nat.mod_eq_zero_of_dvd hd
  have hsum' : u % p + v % p = p := by
    by_cases hlt : u % p + v % p < p
    · rw [Nat.mod_eq_of_lt hlt] at hsum
      omega
    · rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt hlt),
        Nat.mod_eq_of_lt (show u % p + v % p - p < p by omega)] at hsum
      omega
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hiff := decide_eq_decide.mp hc
  omega

private theorem same_mod_four_not_four_dvd_add {u v : ℕ}
    (hu : ¬2 ∣ u) (hv : ¬2 ∣ v)
    (hc : decide (u % 4 = 1) = decide (v % 4 = 1)) :
    ¬4 ∣ u + v := by
  have hu0 : u % 2 ≠ 0 := fun h => hu (Nat.dvd_of_mod_eq_zero h)
  have hv0 : v % 2 ≠ 0 := fun h => hv (Nat.dvd_of_mod_eq_zero h)
  have hiff := decide_eq_decide.mp hc
  intro hd
  have hmod := Nat.mod_eq_zero_of_dvd hd
  omega

/-- Matching colors bound the valuation of the sum of the prime-free parts.
At odd primes it is zero; at two it is at most one. -/
theorem ordCompl_sum_factorization_le {p a b : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hc : primeColor p a = primeColor p b) :
    (ordCompl[p] a + ordCompl[p] b).factorization p ≤ (2 : ℕ).factorization p := by
  have hua := Nat.not_dvd_ordCompl hp ha.ne'
  have hub := Nat.not_dvd_ordCompl hp hb.ne'
  by_cases hp2 : p = 2
  · subst p
    have hc' : decide (ordCompl[2] a % 4 = 1) =
        decide (ordCompl[2] b % 4 = 1) := by
      simpa [primeColor] using hc
    have hnot := same_mod_four_not_four_dvd_add hua hub hc'
    have hnonzero : ordCompl[2] a + ordCompl[2] b ≠ 0 := by
      have := Nat.ordCompl_pos 2 ha.ne'
      omega
    have hle : (ordCompl[2] a + ordCompl[2] b).factorization 2 ≤ 1 := by
      by_contra h
      have hfac : 2 ≤ (ordCompl[2] a + ordCompl[2] b).factorization 2 := by omega
      have hd := (Nat.prime_two.pow_dvd_iff_le_factorization hnonzero).2 hfac
      exact hnot (by simpa using hd)
    simpa only [Nat.prime_two.factorization_self] using hle
  · have hc' : decide (ordCompl[p] a % p ≤ p / 2) =
        decide (ordCompl[p] b % p ≤ p / 2) := by
      simpa [primeColor, hp2] using hc
    have hnot := same_half_not_dvd_add hp hp2 hua hub hc'
    rw [Nat.factorization_eq_zero_of_not_dvd hnot]
    exact Nat.zero_le _

private theorem factorization_add_le_of_lt {p a b : ℕ}
    (hp : p.Prime) (ha : a ≠ 0) (hlt : a.factorization p < b.factorization p) :
    (a + b).factorization p ≤ a.factorization p := by
  have hs : a + b ≠ 0 := by omega
  by_contra h
  have hsdiv : p ^ (a.factorization p + 1) ∣ a + b :=
    (hp.pow_dvd_iff_le_factorization hs).2 (by omega)
  have hbdiv : p ^ (a.factorization p + 1) ∣ b :=
    (pow_dvd_pow p (by omega : a.factorization p + 1 ≤ b.factorization p)).trans
      (Nat.ordProj_dvd b p)
  exact Nat.pow_succ_factorization_not_dvd ha hp
    ((Nat.dvd_add_iff_left hbdiv).mpr hsdiv)

/-- For matching colors, every prime-power contribution to `a + b` occurs in `2*a`. -/
theorem same_color_factorization_add_le {p a b : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hc : primeColor p a = primeColor p b) :
    (a + b).factorization p ≤ (2 * a).factorization p := by
  rw [Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) ha.ne', Finsupp.add_apply]
  rcases lt_trichotomy (a.factorization p) (b.factorization p) with hlt | heq | hgt
  · have hle := factorization_add_le_of_lt hp ha.ne' hlt
    omega
  · have hsum : a + b = p ^ (a.factorization p) * (ordCompl[p] a + ordCompl[p] b) := by
      calc
        a + b = p ^ (a.factorization p) * ordCompl[p] a +
            p ^ (b.factorization p) * ordCompl[p] b := by
          rw [Nat.ordProj_mul_ordCompl_eq_self, Nat.ordProj_mul_ordCompl_eq_self]
        _ = p ^ (a.factorization p) * (ordCompl[p] a + ordCompl[p] b) := by
          rw [← heq, mul_add]
    have hu : ordCompl[p] a + ordCompl[p] b ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (Nat.ordCompl_pos p ha.ne') (Nat.le_add_right _ _))
    rw [hsum, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hu,
      Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same]
    have hle := ordCompl_sum_factorization_le hp ha hb hc
    omega
  · have hle := factorization_add_le_of_lt hp hb.ne' hgt
    rw [Nat.add_comm b a] at hle
    omega

/-- Matching colors on the prime support of a sum force the sum to divide `2*a`. -/
theorem sum_dvd_two_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : ∀ p ∈ (a + b).primeFactors, primeColor p a = primeColor p b) :
    a + b ∣ 2 * a := by
  apply (Nat.factorization_le_iff_dvd (by omega) (by positivity)).mp
  intro p
  by_cases hm : p ∈ (a + b).primeFactors
  · exact same_color_factorization_add_le (Nat.prime_of_mem_primeFactors hm) ha hb (hc p hm)
  · have hz : (a + b).factorization p = 0 := Finsupp.notMem_support_iff.mp hm
    rw [hz]
    exact Nat.zero_le _

/-- Positive integers with matching colors at every prime dividing their sum are equal. -/
theorem eq_of_prime_colors_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : ∀ p ∈ (a + b).primeFactors, primeColor p a = primeColor p b) :
    a = b := by
  have hd₁ := sum_dvd_two_mul ha hb hc
  have hd₂ : b + a ∣ 2 * b := sum_dvd_two_mul hb ha (by
    intro p hp
    exact (hc p (by simpa [Nat.add_comm] using hp)).symm)
  have hle₁ := Nat.le_of_dvd (by positivity : 0 < 2 * a) hd₁
  have hle₂ := Nat.le_of_dvd (by positivity : 0 < 2 * b) hd₂
  omega

/-- The binary signature, indexed by the primes occurring in pair sums of `A`. -/
def signature (A : Finset ℕ) (a : ℕ) : ↥(primeSupport A) → Bool :=
  fun p => primeColor p.1 a

/-- Signatures distinguish the elements of any finite set of positive naturals. -/
theorem signature_injective (A : Finset ℕ) (hpos : ∀ a ∈ A, 0 < a) :
    Function.Injective (fun a : A => signature A a) := by
  intro a b hab
  apply Subtype.ext
  by_contra hne
  apply hne
  apply eq_of_prime_colors_eq (hpos a a.property) (hpos b b.property)
  intro p hp
  have hs : p ∈ primeSupport A := by
    apply (Independent126.prime_mem_iff A p).mpr
    obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact ⟨hprime, a, a.property, b, b.property, hne, hdvd⟩
  exact congrFun hab ⟨p, hs⟩

/-- The positive-natural cardinality bound for the exact ordered product in the problem. -/
theorem card_le_two_pow_primeFactors_of_pos (A : Finset ℕ) (hpos : ∀ a ∈ A, 0 < a) :
    A.card ≤ 2 ^ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card := by
  classical
  have h := Fintype.card_le_of_injective (fun a : A => signature A a)
    (signature_injective A hpos)
  simpa [primeSupport] using h

/-- For arbitrary naturals, deleting zero costs at most one element and cannot
increase the prime support. -/
theorem card_le_two_pow_primeFactors_add_one (A : Finset ℕ) :
    A.card ≤ 2 ^ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card + 1 := by
  have hpos : ∀ a ∈ A.erase 0, 0 < a := by
    intro a ha
    exact Nat.pos_of_ne_zero (Finset.mem_erase.mp ha).1
  have hB := card_le_two_pow_primeFactors_of_pos (A.erase 0) hpos
  change (A.erase 0).card ≤ 2 ^ Independent126.factorCount (A.erase 0) at hB
  have hmono := Independent126.factorCount_mono (Finset.erase_subset 0 A)
  have hpow : 2 ^ Independent126.factorCount (A.erase 0) ≤
      2 ^ Independent126.factorCount A :=
    Nat.pow_le_pow_right (by decide) hmono
  have hcard : A.card ≤ (A.erase 0).card + 1 := by
    by_cases hz : 0 ∈ A
    · exact le_of_eq (Finset.card_erase_add_one hz).symm
    · simp [Finset.erase_eq_of_notMem hz]
  change A.card ≤ 2 ^ Independent126.factorCount A + 1
  omega

/-- The attained-minimum corollary for the exact extremal definition copied from
`Spec` in `Independent126`. This does not assert the conjectural asymptotic. -/
theorem maximal_card_bound {f : ℕ → ℕ}
    (hf : Independent126.IsMaximalAddFactorsCard f) (n : ℕ) :
    n ≤ 2 ^ (f n) + 1 := by
  obtain ⟨A, hA, hcost⟩ := Independent126.maximal_attained hf n
  have h := card_le_two_pow_primeFactors_add_one A
  change A.card ≤ 2 ^ Independent126.factorCount A + 1 at h
  simpa only [hA, hcost] using h

#print axioms ordCompl_sum_factorization_le
#print axioms same_color_factorization_add_le
#print axioms sum_dvd_two_mul
#print axioms eq_of_prime_colors_eq
#print axioms signature_injective
#print axioms card_le_two_pow_primeFactors_of_pos
#print axioms card_le_two_pow_primeFactors_add_one
#print axioms maximal_card_bound

end Signature126
