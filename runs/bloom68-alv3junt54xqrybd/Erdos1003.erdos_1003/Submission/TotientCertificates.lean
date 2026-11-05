import Mathlib

/-!
# Exact prime-support certificates for coprime totient collisions

These statements are necessary and sufficient support identities.  They do not
assert infinitely many adjacent collisions.
-/
namespace TotientCertificates
open scoped BigOperators

def radical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

def radicalPhi (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, (p - 1)

lemma radical_pos (n : ℕ) : 0 < radical n := by
  exact Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

lemma radicalPhi_pos (n : ℕ) : 0 < radicalPhi n := by
  exact Finset.prod_pos fun p hp => by have := (Nat.prime_of_mem_primeFactors hp).two_le; omega

lemma radical_dvd (n : ℕ) : radical n ∣ n := Nat.prod_primeFactors_dvd n

lemma totient_factorization (n : ℕ) : n.totient = (n / radical n) * radicalPhi n :=
  Nat.totient_eq_div_primeFactors_mul n

lemma primitive_cross_balance {F G x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hxy : Nat.Coprime x y) (heq : F * x = G * y) :
    F = y * Nat.gcd F G ∧ G = x * Nat.gcd F G := by
  have hyF : y ∣ F := hxy.symm.dvd_of_dvd_mul_right (by rw [heq]; exact dvd_mul_left y G)
  have hxG : x ∣ G := hxy.dvd_of_dvd_mul_right (by rw [← heq]; exact dvd_mul_left x F)
  obtain ⟨c, hF⟩ := hyF
  obtain ⟨d, hG⟩ := hxG
  have hcd : c = d := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hx hy)
    nlinarith only [heq, hF, hG]
  subst d
  have hg : Nat.gcd F G = c := by
    rw [hF, hG, Nat.gcd_mul_right, hxy.symm.gcd_eq_one, one_mul]
  exact ⟨by rw [hg, hF], by rw [hg, hG]⟩

lemma radical_quotient_pos {n : ℕ} (hn : 0 < n) : 0 < n / radical n := by
  exact Nat.div_pos (Nat.le_of_dvd hn (radical_dvd n)) (radical_pos n)

lemma radical_quotient_dvd (n : ℕ) : n / radical n ∣ n := by
  exact Nat.div_dvd_of_dvd (radical_dvd n)

/-- Once the two disjoint prime supports are given, coprimality and equal
    totients force both quotients, hence both integers. -/
theorem primitive_totient_pair_certificate {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hcop : Nat.Coprime n m)
    (heq : n.totient = m.totient) :
    n = radical n * (radicalPhi m / Nat.gcd (radicalPhi n) (radicalPhi m)) ∧
    m = radical m * (radicalPhi n / Nat.gcd (radicalPhi n) (radicalPhi m)) := by
  let x := n / radical n
  let y := m / radical m
  let g := Nat.gcd (radicalPhi n) (radicalPhi m)
  have hx : 0 < x := radical_quotient_pos hn
  have hy : 0 < y := radical_quotient_pos hm
  have hxy : Nat.Coprime x y := hcop.of_dvd (radical_quotient_dvd n) (radical_quotient_dvd m)
  have hbal : radicalPhi n * x = radicalPhi m * y := by
    simpa only [totient_factorization, Nat.mul_comm] using heq
  obtain ⟨hF, hG⟩ := primitive_cross_balance hx hy hxy hbal
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (radicalPhi_pos n)
  have hGdiv : radicalPhi m / g = x := by rw [hG]; exact Nat.mul_div_cancel _ hg
  have hFdiv : radicalPhi n / g = y := by rw [hF]; exact Nat.mul_div_cancel _ hg
  constructor
  · rw [hGdiv, Nat.mul_comm, Nat.div_mul_cancel (radical_dvd n)]
  · rw [hFdiv, Nat.mul_comm, Nat.div_mul_cancel (radical_dvd m)]

/-- Exact determinant identity for consecutive equal-totient integers. -/
theorem adjacent_support_determinant {n : ℕ}
    (heq : n.totient = (n + 1).totient) :
    radical (n + 1) * radicalPhi n =
      radical n * radicalPhi (n + 1) + Nat.gcd (radicalPhi n) (radicalPhi (n + 1)) := by
  have hn : 0 < n := by
    by_contra h
    have hz : n = 0 := by omega
    subst n
    norm_num at heq
  obtain ⟨h1, h2⟩ := primitive_totient_pair_certificate hn (by omega) (by simp) heq
  let g := Nat.gcd (radicalPhi n) (radicalPhi (n + 1))
  have hFn : g ∣ radicalPhi n := Nat.gcd_dvd_left _ _
  have hFm : g ∣ radicalPhi (n + 1) := Nat.gcd_dvd_right _ _
  have hleft : (n + 1) * g = radical (n + 1) * radicalPhi n := by
    calc
      (n + 1) * g = (radical (n + 1) * (radicalPhi n / g)) * g :=
        congrArg (fun t : ℕ => t * g) h2
      _ = radical (n + 1) * radicalPhi n := by rw [mul_assoc, Nat.div_mul_cancel hFn]
  have hright : n * g = radical n * radicalPhi (n + 1) := by
    calc
      n * g = (radical n * (radicalPhi (n + 1) / g)) * g :=
        congrArg (fun t : ℕ => t * g) h1
      _ = radical n * radicalPhi (n + 1) := by rw [mul_assoc, Nat.div_mul_cancel hFm]
  rw [← hleft, ← hright]
  ring

/-- The two finite prime products are the exact support and totient factors
    of any multiple whose quotient introduces no new primes. -/
lemma supported_product_totient (S : Finset ℕ) (x : ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (hx : 0 < x) (hxs : x.primeFactors ⊆ S) :
    ((∏ p ∈ S, p) * x).primeFactors = S ∧
    ((∏ p ∈ S, p) * x).totient = x * (∏ p ∈ S, (p - 1)) := by
  have hR : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp => (hS p hp).pos
  have hsupport : ((∏ p ∈ S, p) * x).primeFactors = S := by
    rw [Nat.primeFactors_mul hR.ne' hx.ne', Nat.primeFactors_prod hS]
    exact Finset.union_eq_left.mpr hxs
  refine ⟨hsupport, ?_⟩
  rw [Nat.totient_eq_div_primeFactors_mul, hsupport, Nat.mul_div_cancel_left x hR]

/-- A determinant-one certificate with the exact cross-supported quotients
    produces a consecutive equal-totient pair. -/
theorem support_certificate_sufficient (S T : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p)
    (hxs : ((∏ p ∈ T, (p - 1)) / Nat.gcd (∏ p ∈ S, (p - 1))
      (∏ p ∈ T, (p - 1))).primeFactors ⊆ S)
    (hyt : ((∏ p ∈ S, (p - 1)) / Nat.gcd (∏ p ∈ S, (p - 1))
      (∏ p ∈ T, (p - 1))).primeFactors ⊆ T)
    (hdet : (∏ p ∈ T, p) * (∏ p ∈ S, (p - 1)) =
      (∏ p ∈ S, p) * (∏ p ∈ T, (p - 1)) +
        Nat.gcd (∏ p ∈ S, (p - 1)) (∏ p ∈ T, (p - 1))) :
    ∃ n : ℕ, n.totient = (n + 1).totient ∧
      n.primeFactors = S ∧ (n + 1).primeFactors = T ∧
      n = (∏ p ∈ S, p) * ((∏ p ∈ T, (p - 1)) /
        Nat.gcd (∏ p ∈ S, (p - 1)) (∏ p ∈ T, (p - 1))) := by
  let R := ∏ p ∈ S, p
  let U := ∏ p ∈ T, p
  let F := ∏ p ∈ S, (p - 1)
  let G := ∏ p ∈ T, (p - 1)
  let g := Nat.gcd F G
  let x := G / g
  let y := F / g
  have hF : 0 < F := Finset.prod_pos fun p hp => by have := (hS p hp).two_le; omega
  have hG : 0 < G := Finset.prod_pos fun p hp => by have := (hT p hp).two_le; omega
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hF
  have hgF : g ∣ F := Nat.gcd_dvd_left _ _
  have hgG : g ∣ G := Nat.gcd_dvd_right _ _
  have hx : 0 < x := Nat.div_pos (Nat.le_of_dvd hG hgG) hg
  have hy : 0 < y := Nat.div_pos (Nat.le_of_dvd hF hgF) hg
  have hxG : x * g = G := Nat.div_mul_cancel hgG
  have hyF : y * g = F := Nat.div_mul_cancel hgF
  have hm : U * y = R * x + 1 := by
    apply Nat.eq_of_mul_eq_mul_right hg
    calc
      U * y * g = U * F := by rw [mul_assoc, hyF]
      _ = R * G + g := hdet
      _ = (R * x + 1) * g := by rw [add_mul, one_mul, mul_assoc, hxG]
  obtain ⟨hsupportN, hphiN⟩ := supported_product_totient S x hS hx hxs
  obtain ⟨hsupportM, hphiM⟩ := supported_product_totient T y hT hy hyt
  have hphi : (R * x).totient = (U * y).totient := by
    rw [hphiN, hphiM]
    change x * F = y * G
    calc
      x * F = x * (y * g) := congrArg (fun a : ℕ => x * a) hyF.symm
      _ = y * (x * g) := by ring
      _ = y * G := congrArg (fun a : ℕ => y * a) hxG
  refine ⟨R * x, ?_, hsupportN, ?_, rfl⟩
  · simpa only [hm] using hphi
  · change (U * y).primeFactors = T at hsupportM
    simpa only [hm] using hsupportM

/-- A finite, entirely arithmetic certificate for a unit-gap totient collision. -/
def SupportCertificate (S T : Finset ℕ) : Prop :=
  (∀ p ∈ S, Nat.Prime p) ∧ (∀ p ∈ T, Nat.Prime p) ∧
  (((∏ p ∈ T, (p - 1)) / Nat.gcd (∏ p ∈ S, (p - 1))
    (∏ p ∈ T, (p - 1))).primeFactors ⊆ S) ∧
  (((∏ p ∈ S, (p - 1)) / Nat.gcd (∏ p ∈ S, (p - 1))
    (∏ p ∈ T, (p - 1))).primeFactors ⊆ T) ∧
  ((∏ p ∈ T, p) * (∏ p ∈ S, (p - 1)) =
    (∏ p ∈ S, p) * (∏ p ∈ T, (p - 1)) +
      Nat.gcd (∏ p ∈ S, (p - 1)) (∏ p ∈ T, (p - 1)))

lemma adjacent_support_certificate {n : ℕ}
    (heq : n.totient = (n + 1).totient) :
    SupportCertificate n.primeFactors (n + 1).primeFactors := by
  have hn : 0 < n := by
    by_contra h
    have hz : n = 0 := by omega
    subst n
    norm_num at heq
  obtain ⟨h1, h2⟩ := primitive_totient_pair_certificate hn (by omega) (by simp) heq
  refine ⟨fun p hp => Nat.prime_of_mem_primeFactors hp,
    fun p hp => Nat.prime_of_mem_primeFactors hp, ?_, ?_, adjacent_support_determinant heq⟩
  · apply Nat.primeFactors_mono _ hn.ne'
    refine ⟨radical n, ?_⟩
    simpa only [Nat.mul_comm] using h1
  · apply Nat.primeFactors_mono _ (Nat.succ_ne_zero n)
    refine ⟨radical (n + 1), ?_⟩
    simpa only [Nat.mul_comm] using h2

/-- Necessary and sufficient support conditions, without any infinitude assumption. -/
theorem support_certificate_iff (S T : Finset ℕ) :
    SupportCertificate S T ↔ ∃ n : ℕ, n.totient = (n + 1).totient ∧
      n.primeFactors = S ∧ (n + 1).primeFactors = T := by
  constructor
  · rintro ⟨hS, hT, hxs, hyt, hdet⟩
    obtain ⟨n, ht, hnS, hnT, _⟩ := support_certificate_sufficient S T hS hT hxs hyt hdet
    exact ⟨n, ht, hnS, hnT⟩
  · rintro ⟨n, ht, rfl, rfl⟩
    exact adjacent_support_certificate ht



end TotientCertificates
