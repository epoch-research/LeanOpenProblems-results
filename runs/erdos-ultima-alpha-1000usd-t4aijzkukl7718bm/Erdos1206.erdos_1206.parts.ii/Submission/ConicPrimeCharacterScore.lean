import FormalConjecturesUtil

/-!
Finite prime-character scores for two pairs of quadratic norm forms.
The score cancels common dilations and normalizations. No sieve estimate,
positive-density source, or settlement of the original conjecture is asserted.
-/
namespace Erdos1206.ConicPrimeCharacterScore
open Finset

/-- A completely additive score supported on finitely many primes. -/
def score (P : Finset ℕ) (w : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ p ∈ P, w p * (n.factorization p : ℤ)

lemma score_mul (P : Finset ℕ) (w : ℕ → ℤ) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) :
    score P w (m*n) = score P w m + score P w n := by
  simp only [score, Nat.factorization_mul hm.ne' hn.ne', Finsupp.add_apply,
    Nat.cast_add, mul_add, sum_add_distrib]

/-- The signs are by norm-field pair, not by the signs in the cubic identity. -/
def contrast (P : Finset ℕ) (w : ℕ → ℤ) (a b c d : ℕ) : ℤ :=
  score P w a + score P w b - score P w c - score P w d

lemma contrast_dilation (P : Finset ℕ) (w : ℕ → ℤ) {a b c d t : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (ht : 0 < t) :
    contrast P w (t*a) (t*b) (t*c) (t*d) = contrast P w a b c d := by
  simp only [contrast, score_mul P w ht ha, score_mul P w ht hb,
    score_mul P w ht hc, score_mul P w ht hd]
  ring

lemma contrast_normalization (P : Finset ℕ) (w : ℕ → ℤ)
    {a b c d A B C D g : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hg : 0 < g)
    (hA : A=g*a) (hB : B=g*b) (hC : C=g*c) (hD : D=g*d) :
    contrast P w A B C D = contrast P w a b c d := by
  rw [hA,hB,hC,hD]
  exact contrast_dilation P w ha hb hc hd hg

/-- Valuations of the four coordinates at primes where the characters differ. -/
def mixedMass (P : Finset ℕ) (χ ψ : ℕ → ℤ) (a b c d : ℕ) : ℕ :=
  ∑ p ∈ P.filter (fun p => χ p ≠ ψ p),
    (a.factorization p + b.factorization p + c.factorization p + d.factorization p)

/-- The local algebra behind the score: a prime dividing a coordinate must
split in that coordinate's norm field. -/
lemma local_contrast {x y : ℤ} {a b c d : ℕ}
    (hx : x=1 ∨ x = -1) (hy : y=1 ∨ y = -1)
    (ha : a ≠ 0 → x=1) (hb : b ≠ 0 → x=1)
    (hc : c ≠ 0 → y=1) (hd : d ≠ 0 → y=1) :
    (x-y)*((a:ℤ)+b-c-d) =
      if x ≠ y then 2*((a:ℤ)+b+c+d) else 0 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · simp
  · have hc0 : c=0 := by by_contra hh; have := hc hh; omega
    have hd0 : d=0 := by by_contra hh; have := hd hh; omega
    simp [hc0,hd0]
  · have ha0 : a=0 := by by_contra hh; have := ha hh; omega
    have hb0 : b=0 := by by_contra hh; have := hb hh; omega
    simp [ha0,hb0]
    ring
  · simp

/-- Exact, nonnegative contrast, with no distributional assertion. -/
theorem contrast_eq_twice_mixedMass (P : Finset ℕ) (χ ψ : ℕ → ℤ)
    (a b c d : ℕ)
    (hχ : ∀ p ∈ P, χ p=1 ∨ χ p = -1)
    (hψ : ∀ p ∈ P, ψ p=1 ∨ ψ p = -1)
    (ha : ∀ p ∈ P, a.factorization p ≠ 0 → χ p=1)
    (hb : ∀ p ∈ P, b.factorization p ≠ 0 → χ p=1)
    (hc : ∀ p ∈ P, c.factorization p ≠ 0 → ψ p=1)
    (hd : ∀ p ∈ P, d.factorization p ≠ 0 → ψ p=1) :
    contrast P (fun p => χ p-ψ p) a b c d =
      2*(mixedMass P χ ψ a b c d : ℤ) := by
  classical
  simp only [contrast,score,←sum_add_distrib,←sum_sub_distrib]
  simp only [mixedMass,Nat.cast_sum,sum_filter,mul_sum]
  apply sum_congr rfl
  intro p hp
  have hh := local_contrast (hχ p hp) (hψ p hp)
    (ha p hp) (hb p hp) (hc p hp) (hd p hp)
  split_ifs at hh ⊢ with h
  all_goals push_cast at *
  all_goals nlinarith only [hh]

/-- A bounded score band can only contain dilated instances having small
mixed-prime mass. This conclusion is uniform in the dilation. -/
theorem mixedMass_le_of_bands (P : Finset ℕ) (χ ψ : ℕ → ℤ)
    {a b c d t : ℕ} {K : ℤ}
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hd0 : 0 < d) (ht : 0 < t)
    (hχ : ∀ p ∈ P, χ p=1 ∨ χ p = -1)
    (hψ : ∀ p ∈ P, ψ p=1 ∨ ψ p = -1)
    (ha : ∀ p ∈ P, a.factorization p ≠ 0 → χ p=1)
    (hb : ∀ p ∈ P, b.factorization p ≠ 0 → χ p=1)
    (hc : ∀ p ∈ P, c.factorization p ≠ 0 → ψ p=1)
    (hd : ∀ p ∈ P, d.factorization p ≠ 0 → ψ p=1)
    (hA : |score P (fun p => χ p-ψ p) (t*a)| ≤ K)
    (hB : |score P (fun p => χ p-ψ p) (t*b)| ≤ K)
    (hC : |score P (fun p => χ p-ψ p) (t*c)| ≤ K)
    (hD : |score P (fun p => χ p-ψ p) (t*d)| ≤ K) :
    (mixedMass P χ ψ a b c d : ℤ) ≤ 2*K := by
  have he := contrast_eq_twice_mixedMass P χ ψ a b c d hχ hψ ha hb hc hd
  have hscale := contrast_dilation P (fun p => χ p-ψ p) ha0 hb0 hc0 hd0 ht
  have hAu := (abs_le.mp hA).2
  have hBu := (abs_le.mp hB).2
  have hCl := (abs_le.mp hC).1
  have hDl := (abs_le.mp hD).1
  dsimp only [contrast] at he hscale
  omega

/-- A nonsingular zero of a binary quadratic gives a square discriminant. -/
lemma discriminant_square_of_zero {F : Type*} [Field F] {a b c x y : F}
    (ha : a ≠ 0) (hxy : x ≠ 0 ∨ y ≠ 0) (h : a*x^2+b*x*y+c*y^2=0) :
    IsSquare (b^2-4*a*c) := by
  have hy : y ≠ 0 := by
    intro hy
    have hx := hxy.resolve_right (not_not_intro hy)
    rw [hy] at h
    simp only [zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] at h
    exact mul_ne_zero ha (pow_ne_zero _ hx) h
  refine ⟨(2*a*x+b*y)/y, ?_⟩
  field_simp
  linear_combination -4*a*h

/-- Prime divisors of primitive quadratic-form values split in its
nondegenerate discriminant field, away from the leading coefficient. -/
theorem legendre_discriminant_of_dvd {p : ℕ} (hp : p.Prime)
    (a b c : ℤ) {s t : ℕ} (hst : Nat.Coprime s t)
    (ha : ¬ (p:ℤ) ∣ a) (hD : ¬ (p:ℤ) ∣ b^2-4*a*c)
    (hf : (p:ℤ) ∣ a*(s:ℤ)^2+b*s*t+c*(t:ℤ)^2) :
    letI : Fact p.Prime := ⟨hp⟩
    legendreSym p (b^2-4*a*c)=1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hxy : (s : ZMod p) ≠ 0 ∨ (t : ZMod p) ≠ 0 := by
    by_contra! hz
    have hs : p ∣ s := (CharP.cast_eq_zero_iff (ZMod p) p s).mp hz.1
    have ht : p ∣ t := (CharP.cast_eq_zero_iff (ZMod p) p t).mp hz.2
    exact hp.not_dvd_one (hst.gcd_eq_one ▸ Nat.dvd_gcd hs ht)
  have ha' : (a : ZMod p) ≠ 0 := by
    intro hz
    exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hz)
  have hD' : ((b^2-4*a*c : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    exact hD ((ZMod.intCast_zmod_eq_zero_iff_dvd (b^2-4*a*c) p).mp hz)
  apply (legendreSym.eq_one_iff p hD').mpr
  have hf' : (a : ZMod p)*(s:ZMod p)^2+(b:ZMod p)*s*t+(c:ZMod p)*(t:ZMod p)^2=0 := by
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hf
    simpa using hh
  have hh := discriminant_square_of_zero ha' hxy hf'
  simpa only [Int.cast_sub,Int.cast_pow,Int.cast_mul,Int.cast_ofNat] using hh

#print axioms contrast_eq_twice_mixedMass
#print axioms mixedMass_le_of_bands
#print axioms legendre_discriminant_of_dvd
end Erdos1206.ConicPrimeCharacterScore
