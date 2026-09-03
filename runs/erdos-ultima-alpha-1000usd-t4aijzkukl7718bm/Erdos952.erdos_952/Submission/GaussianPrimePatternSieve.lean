import Submission.GaussianWeightedSieve

/-! Applying the weighted Gaussian polynomial sieve to actual prime
translates, with the small-prime exceptions counted explicitly. This does
not supply growing-pattern estimates for the main term or weighted error. -/
namespace Erdos952Investigation.GaussianPrimePatternSieve
open GaussianIdealBoxCounts GaussianPolynomialBoxCounts GaussianWeightedSieve
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section

/-- The four possible Gaussian units, represented by their values. -/
def unitValues : Finset GaussianInt := {⟨1,0⟩,⟨-1,0⟩,⟨0,1⟩,⟨0,-1⟩}

lemma unitValues_card : unitValues.card = 4 := by decide +kernel

lemma unit_mem_unitValues (u : GaussianIntˣ) : (u : GaussianInt) ∈ unitValues := by
  have hn : (u : GaussianInt).norm = 1 :=
    (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) _).mpr u.isUnit
  generalize (u : GaussianInt) = z at hn ⊢
  rcases z with ⟨a,b⟩
  rw [gaussian_norm_sq] at hn
  change a^2+b^2 = 1 at hn
  have ha : -1 ≤ a ∧ a ≤ 1 := by constructor <;> nlinarith [sq_nonneg b]
  have hb : -1 ≤ b ∧ b ≤ 1 := by constructor <;> nlinarith [sq_nonneg a]
  obtain ⟨ha1,ha2⟩ := ha
  obtain ⟨hb1,hb2⟩ := hb
  interval_cases a <;> interval_cases b <;> norm_num [unitValues] at *

/-- Possible starts at which one translated prime is an associate of a
sieving prime. Overlaps only decrease the size of this set. -/
def exceptionSet {ι : Type*} [Fintype ι] (z : ι → GaussianInt)
    (Q : Finset GaussianInt) : Finset GaussianInt :=
  (((Finset.univ : Finset ι).product Q).product unitValues).image
    (fun x => x.1.2*x.2-z x.1.1)

theorem exceptionSet_card_le {ι : Type*} [Fintype ι]
    (z : ι → GaussianInt) (Q : Finset GaussianInt) :
    (exceptionSet z Q).card ≤ 4*Fintype.card ι*Q.card := by
  calc
    _ ≤ (((Finset.univ : Finset ι).product Q).product unitValues).card := Finset.card_image_le
    _ = _ := by
      change (((Finset.univ : Finset ι) ×ˢ Q) ×ˢ unitValues).card = _
      rw [Finset.card_product,Finset.card_product,Finset.card_univ,unitValues_card]
      ring

lemma mem_exceptionSet_of_dvd {ι : Type*} [Fintype ι]
    (z : ι → GaussianInt) (Q : Finset GaussianInt) (i : ι) (q t : GaussianInt)
    (hqQ : q ∈ Q) (hq : Prime q) (ht : Prime (t+z i)) (hd : q ∣ t+z i) :
    t ∈ exceptionSet z Q := by
  obtain ⟨u,hu⟩ := (hq.dvd_prime_iff_associated ht).mp hd
  apply Finset.mem_image.mpr
  refine ⟨⟨⟨i,q⟩,(u : GaussianInt)⟩,?_,?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ i,hqQ⟩,unit_mem_unitValues u⟩
  · dsimp
    rw [hu]
    abel

/-- Every nontrivial sieve modulus has a prime factor in the designated
finite family Q. This hypothesis must be checked for the selected support D. -/
def Supported (D Q : Finset GaussianInt) : Prop :=
  ∀ d ∈ D, d ≠ 1 → ∃ q ∈ Q, Prime q ∧ q ∣ d

lemma prime_pattern_sifted_or_exception {ι : Type*} [Fintype ι]
    (z : ι → GaussianInt) (D Q : Finset GaussianInt) (hD : Supported D Q)
    (t : GaussianInt) (ht : ∀ i, Prime (t+z i)) :
    Sifted D (patternPolynomial z) t ∨ t ∈ exceptionSet z Q := by
  by_cases hs : Sifted D (patternPolynomial z) t
  · exact Or.inl hs
  · right
    simp only [Sifted,not_forall,not_not] at hs
    obtain ⟨d,hdD,hd1,hd⟩ := hs
    obtain ⟨q,hqQ,hq,hqd⟩ := hD d hdD hd1
    have hqf := hqd.trans hd
    rw [patternPolynomial_eval,hq.dvd_finset_prod_iff] at hqf
    obtain ⟨i,_,hi⟩ := hqf
    exact mem_exceptionSet_of_dvd z Q i q t hqQ hq (ht i) hi

local instance boxPredFinite (p : GaussianInt → Prop) (a : GaussianInt) (R : ℕ) :
    Finite {t : GaussianInt // InBox a R t ∧ p t} := by
  let f : {t : GaussianInt // InBox a R t ∧ p t} → Box a R :=
    fun t => ⟨t.val,t.property.1⟩
  apply Finite.of_injective f
  intro t u he
  exact Subtype.ext (congrArg (fun t : Box a R => t.val) he)

lemma box_count_le_count_add_exception (p q : GaussianInt → Prop)
    (E : Finset GaussianInt) (a : GaussianInt) (R : ℕ)
    (h : ∀ t, p t → q t ∨ t ∈ E) :
    Nat.card {t : GaussianInt // InBox a R t ∧ p t} ≤
      Nat.card {t : GaussianInt // InBox a R t ∧ q t}+E.card := by
  let f : {t : GaussianInt // InBox a R t ∧ p t} →
      {t : GaussianInt // InBox a R t ∧ q t} ⊕ E := fun t =>
    if ht : q t.val then Sum.inl ⟨t.val,t.property.1,ht⟩
    else Sum.inr ⟨t.val,(h t.val t.property.2).resolve_left ht⟩
  let v : {t : GaussianInt // InBox a R t ∧ q t} ⊕ E → GaussianInt :=
    Sum.elim Subtype.val Subtype.val
  have hv (t) : v (f t) = t.val := by dsimp [f]; split_ifs <;> rfl
  have hf : Function.Injective f := by
    intro t u he
    apply Subtype.ext
    have hh := congrArg v he
    simpa only [hv] using hh
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_sum,Nat.card_eq_fintype_card,Fintype.card_coe] using hh

def primeTranslateCount {ι : Type*} [Fintype ι] (z : ι → GaussianInt)
    (a : GaussianInt) (R : ℕ) : ℕ :=
  Nat.card {t : GaussianInt // InBox a R t ∧ ∀ i, Prime (t+z i)}

/-- This bound includes every prime translate, including the ones whose
vertices equal small sieving primes up to a unit. No large-norm hypothesis
is used to discard exceptions. -/
theorem prime_translate_count_le_sifted_add {ι : Type*} [Fintype ι]
    (z : ι → GaussianInt) (D Q : Finset GaussianInt) (hD : Supported D Q)
    (a : GaussianInt) (R : ℕ) :
    primeTranslateCount z a R ≤ siftedCount D (patternPolynomial z) a R+
      4*Fintype.card ι*Q.card := by
  have hh := box_count_le_count_add_exception (fun t => ∀ i, Prime (t+z i))
    (Sifted D (patternPolynomial z)) (exceptionSet z Q) a R
    (prime_pattern_sifted_or_exception z D Q hD)
  exact hh.trans (Nat.add_le_add_left (exceptionSet_card_le z Q) _)

/-- The complete explicit weighted upper bound for actual prime translates.
The exceptional-set error is at most four times vertices times sieve primes. -/
theorem prime_translate_count_le_main_error {ι : Type*} [Fintype ι]
    (z : ι → GaussianInt) (D Q : Finset GaussianInt) (hD : Supported D Q)
    (hD1 : 1 ∈ D) (hD0 : ∀ d ∈ D, d ≠ 0)
    (w : GaussianInt → ℝ) (hw : w 1 = 1) (a : GaussianInt) (R : ℕ) :
    (primeTranslateCount z a R : ℝ) ≤
      (R : ℝ)^2*mainSum D w (patternPolynomial z)+errorSum D w (patternPolynomial z) R+
        4*(Fintype.card ι : ℝ)*(Q.card : ℝ) := by
  have hs := sifted_count_le_main_error D hD1 hD0 w hw (patternPolynomial z) a R
  have hp : (primeTranslateCount z a R : ℝ) ≤
      (siftedCount D (patternPolynomial z) a R : ℝ)+4*(Fintype.card ι : ℝ)*(Q.card : ℝ) := by
    exact_mod_cast prime_translate_count_le_sifted_add z D Q hD a R
  linarith

#print axioms exceptionSet_card_le
#print axioms prime_translate_count_le_sifted_add
#print axioms prime_translate_count_le_main_error
end
end Erdos952Investigation.GaussianPrimePatternSieve
