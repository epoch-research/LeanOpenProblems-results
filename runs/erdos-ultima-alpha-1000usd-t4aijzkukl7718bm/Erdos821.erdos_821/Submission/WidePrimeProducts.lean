import Submission.CompositeBelowHalfScales
import Submission.PrimeModulusReciprocals

/-!
# Products from two disjoint prime pools

Finite identities for wide modulus pools, with primitive conductors grouped
before applying the character mean estimate.  No distribution conclusion at
or above the square-root level is asserted here.
-/

open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 2000000

noncomputable def pairPrimeProducts (P Q : Finset ℕ) : Finset ℕ :=
  (P ×ˢ Q).image (fun z => z.1*z.2)

lemma pair_prime_product_inj (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hdis : Disjoint P Q) :
    Set.InjOn (fun z : ℕ × ℕ => z.1*z.2) (↑(P ×ˢ Q) : Set (ℕ × ℕ)) := by
  intro a ha b hb he
  obtain ⟨haP, haQ⟩ := mem_product.mp ha
  obtain ⟨hbP, hbQ⟩ := mem_product.mp hb
  change a.1*a.2 = b.1*b.2 at he
  have hd : a.1 ∣ b.1*b.2 := he ▸ dvd_mul_right a.1 a.2
  have hab : a.1 = b.1 := by
    rcases (hP _ haP).dvd_mul.mp hd with h | h
    · exact (prime_dvd_prime_iff_eq (hP _ haP) (hP _ hbP)).mp h
    · have heq := (prime_dvd_prime_iff_eq (hP _ haP) (hQ _ hbQ)).mp h
      exact False.elim (disjoint_left.mp hdis haP (heq ▸ hbQ))
  apply Prod.ext hab
  rw [hab] at he
  exact Nat.eq_of_mul_eq_mul_left (hP _ hbP).pos he

lemma sum_pairPrimeProducts (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hdis : Disjoint P Q) (F : ℕ → ℝ) :
    (∑ d ∈ pairPrimeProducts P Q, F d) = ∑ p ∈ P, ∑ q ∈ Q, F (p*q) := by
  rw [pairPrimeProducts, sum_image (pair_prime_product_inj P Q hP hQ hdis), sum_product]

lemma pair_prime_coprime {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hdis : Disjoint P Q) {p q : ℕ} (hp : p ∈ P) (hq : q ∈ Q) :
    p.Coprime q := by
  apply (hP _ hp).coprime_iff_not_dvd.mpr
  intro hd
  have he := (prime_dvd_prime_iff_eq (hP _ hp) (hQ _ hq)).mp hd
  exact disjoint_left.mp hdis hp (he ▸ hq)

lemma pairPrimeProducts_pos {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    {d : ℕ} (hd : d ∈ pairPrimeProducts P Q) : 0 < d := by
  obtain ⟨⟨p,q⟩, hpq, rfl⟩ := mem_image.mp hd
  obtain ⟨hp,hq⟩ := mem_product.mp hpq
  exact Nat.mul_pos (hP _ hp).pos (hQ _ hq).pos

noncomputable def poolTotientMass (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, (p.totient : ℝ)⁻¹

lemma poolTotientMass_nonneg (P : Finset ℕ) : 0 ≤ poolTotientMass P :=
  sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

lemma pairPrimeProducts_mass (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hdis : Disjoint P Q) :
    poolTotientMass (pairPrimeProducts P Q) = poolTotientMass P * poolTotientMass Q := by
  unfold poolTotientMass
  rw [sum_pairPrimeProducts P Q hP hQ hdis, sum_mul]
  apply sum_congr rfl
  intro p hp
  rw [mul_sum]
  apply sum_congr rfl
  intro q hq
  rw [Nat.totient_mul (pair_prime_coprime hP hQ hdis hp hq), Nat.cast_mul, mul_inv_rev, mul_comm]

lemma prime_pair_divisors {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {c : ℕ}
    (hc : c ∣ p*q) : c = 1 ∨ c = p ∨ c = q ∨ c = p*q := by
  obtain ⟨a, b, ha, hb, rfl⟩ := (Nat.dvd_mul.mp hc)
  rcases (Nat.dvd_prime hp).mp ha with rfl | rfl <;>
    rcases (Nat.dvd_prime hq).mp hb with rfl | rfl <;> simp

noncomputable def primitivePoolMean (P : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ d ∈ P, (∑ χ ∈ primitiveCharacters d, ‖twistedArithmeticSum χ vonMangoldt N‖) /
    (d.totient : ℝ)

lemma primitivePoolMean_nonneg (P : Finset ℕ) (N : ℕ) : 0 ≤ primitivePoolMean P N :=
  sum_nonneg (fun _ _ => div_nonneg (sum_nonneg (fun _ _ => norm_nonneg _)) (Nat.cast_nonneg _))

lemma pair_conductor_majorant_le (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hdis : Disjoint P Q) (N : ℕ) :
    (∑ d ∈ pairPrimeProducts P Q, primitiveConductorMangoldtMajorant d N / d.totient) ≤
      poolTotientMass Q * primitivePoolMean P N +
      poolTotientMass P * primitivePoolMean Q N + primitivePoolMean (pairPrimeProducts P Q) N := by
  let F : ℕ → ℝ := fun d => ∑ χ ∈ primitiveCharacters d, ‖twistedArithmeticSum χ vonMangoldt N‖
  have hF (d : ℕ) : 0 ≤ F d := sum_nonneg (fun _ _ => norm_nonneg _)
  have hloc (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ Q) :
      primitiveConductorMangoldtMajorant (p*q) N ≤ F p + F q + F (p*q) := by
    have hsub : (p*q).divisors.erase 1 ⊆ {p,q,p*q} := by
      intro c hc
      obtain ⟨hc1,hcd⟩ := mem_erase.mp hc
      rcases prime_pair_divisors (hP _ hp) (hQ _ hq) (Nat.dvd_of_mem_divisors hcd) with h | h | h | h
      · exact False.elim (hc1 h)
      · simp [h]
      · simp [h]
      · simp [h]
    have hs := sum_le_sum_of_subset_of_nonneg hsub (fun c _ _ => hF c)
    change (∑ c ∈ (p*q).divisors.erase 1, F c) ≤ _
    apply hs.trans
    have hne : p ≠ q := by
      intro h
      exact disjoint_left.mp hdis hp (h ▸ hq)
    have hpne : p ≠ p*q := by
      have := (hP _ hp).pos
      have := (hQ _ hq).two_le
      nlinarith
    have hqne : q ≠ p*q := by
      have := (hQ _ hq).pos
      have := (hP _ hp).two_le
      nlinarith
    simp only [sum_insert (by simp [hne, hpne] : p ∉ ({q,p*q} : Finset ℕ)),
      sum_insert (by simp [hqne] : q ∉ ({p*q} : Finset ℕ)), sum_singleton]
    ring_nf
    exact le_rfl
  have hpoint (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ Q) :
      primitiveConductorMangoldtMajorant (p*q) N / ((p*q).totient : ℝ) ≤
        (q.totient : ℝ)⁻¹ * (F p / (p.totient : ℝ)) +
        (p.totient : ℝ)⁻¹ * (F q / (q.totient : ℝ)) + F (p*q) / ((p*q).totient : ℝ) := by
    apply (div_le_div_of_nonneg_right (hloc p hp q hq) (Nat.cast_nonneg _)).trans_eq
    rw [Nat.totient_mul (pair_prime_coprime hP hQ hdis hp hq), Nat.cast_mul]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [sum_pairPrimeProducts P Q hP hQ hdis]
  calc
    _ ≤ ∑ p ∈ P, ∑ q ∈ Q, ((q.totient : ℝ)⁻¹ * (F p / (p.totient : ℝ)) +
        (p.totient : ℝ)⁻¹ * (F q / (q.totient : ℝ)) + F (p*q) / ((p*q).totient : ℝ)) :=
      sum_le_sum (fun p hp => sum_le_sum (fun q hq => hpoint p hp q hq))
    _ = _ := by
      simp only [sum_add_distrib, ← sum_mul, ← mul_sum]
      simp only [primitivePoolMean]
      rw [sum_pairPrimeProducts P Q hP hQ hdis]
      simp only [poolTotientMass, F]

/-- A primitive-conductor estimate for an arbitrary finite natural-number pool. -/
theorem primitivePoolMean_le_unbalanced (P : Finset ℕ) (L Q U V N B : ℕ)
    (hL : 0 < L) (hQ : 0 < Q)
    (hP : ∀ d ∈ P, 2 ≤ d ∧ L ≤ d ∧ d ≤ Q)
    (hB : 1 ≤ B) (hBU : B^2 ≤ U+1) (hBV : B^2 ≤ V) :
    primitivePoolMean P N ≤
      ((Q : ℝ)^2*vaughanShortMajorant U V N Q + unbalancedTypeIIMajorant N Q B)/(L : ℝ) := by
  let M : Finset ℕ+ := P.attach.image (fun d => ⟨d.val, by have := (hP d.val d.property).1; omega⟩)
  have hmem {d : ℕ+} : d ∈ M ↔ (d : ℕ) ∈ P := by
    constructor
    · intro hd
      obtain ⟨e, he, heq⟩ := mem_image.mp hd
      have hv := congrArg (fun x : ℕ+ => (x : ℕ)) heq
      change e.val = (d : ℕ) at hv
      exact hv ▸ e.property
    · intro hd
      exact mem_image.mpr ⟨⟨d,hd⟩, mem_attach _ _, Subtype.ext rfl⟩
  have hsum (F : ℕ → ℝ) : (∑ d ∈ M, F d) = ∑ d ∈ P, F d := by
    apply sum_bij (fun (d : ℕ+) _ => (d : ℕ))
    · intro d hd
      exact hmem.mp hd
    · intro d hd e he h
      exact PNat.coe_injective h
    · intro d hd
      have hd0 : 0 < d := by have := (hP d hd).1; omega
      exact ⟨⟨d,hd0⟩, hmem.mpr hd, rfl⟩
    · intros
      rfl
  have hmean := primitive_vonMangoldt_unbalanced_mean_bound M Q hQ
    (fun d hd => ⟨(hP d (hmem.mp hd)).1, (hP d (hmem.mp hd)).2.2⟩)
    (fun d => primitiveCharacters (d : ℕ))
    (fun _ _ _ hc => (mem_filter.mp hc).2) U V N B hB hBU hBV
    (fun _ _ => N) (fun _ _ _ _ => le_rfl)
  dsimp only at hmean
  rw [hsum (fun d => (d : ℝ)/(d.totient : ℝ) * ∑ χ ∈ primitiveCharacters d, ‖twistedArithmeticSum χ vonMangoldt N‖)] at hmean
  apply (le_div_iff₀ (by exact_mod_cast hL : (0 : ℝ) < L)).mpr
  rw [mul_comm, primitivePoolMean, mul_sum]
  apply (sum_le_sum (fun d hd => ?_)).trans hmean
  have hdL : (L : ℝ) ≤ d := by exact_mod_cast (hP d hd).2.1
  calc
    _ ≤ (d : ℝ)*((∑ χ ∈ primitiveCharacters d, ‖twistedArithmeticSum χ vonMangoldt N‖)/(d.totient : ℝ)) :=
      mul_le_mul_of_nonneg_right hdL (div_nonneg (sum_nonneg (fun _ _ => norm_nonneg _)) (Nat.cast_nonneg _))
    _ = _ := by ring

lemma pair_product_le_totient {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hdis : Disjoint P Q) {d : ℕ} (hd : d ∈ pairPrimeProducts P Q) :
    d ≤ 4*d.totient := by
  obtain ⟨⟨p,q⟩, hpq, rfl⟩ := mem_image.mp hd
  obtain ⟨hp,hq⟩ := mem_product.mp hpq
  rw [Nat.totient_mul (pair_prime_coprime hP hQ hdis hp hq),
    Nat.totient_prime (hP _ hp), Nat.totient_prime (hQ _ hq)]
  have hpp : p ≤ 2*(p-1) := by have := (hP _ hp).two_le; omega
  have hqq : q ≤ 2*(q-1) := by have := (hQ _ hq).two_le; omega
  nlinarith [Nat.mul_le_mul hpp hqq]

lemma pair_product_lift_error_le (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hdis : Disjoint P Q) (N H : ℕ) (hH : ∀ d ∈ pairPrimeProducts P Q, d ≤ H) :
    (∑ d ∈ pairPrimeProducts P Q, (((d : ℝ)+1)*characterLiftError d N)/(d.totient : ℝ)) ≤
      8*((pairPrimeProducts P Q).card : ℝ)*(Nat.log 2 N : ℝ)*Real.log H := by
  have hloc (d : ℕ) (hd : d ∈ pairPrimeProducts P Q) :
      (((d : ℝ)+1)*characterLiftError d N)/(d.totient : ℝ) ≤
        8*(Nat.log 2 N : ℝ)*Real.log H := by
    have hd0 := pairPrimeProducts_pos hP hQ hd
    have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd0
    have hratio : (d : ℝ)+1 ≤ 8*d.totient := by
      have h := pair_product_le_totient hP hQ hdis hd
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
      have hcast : (d : ℝ) ≤ 4*d.totient := by exact_mod_cast h
      linarith
    have hlift : characterLiftError d N ≤ (Nat.log 2 N : ℝ)*Real.log H :=
      mul_le_mul_of_nonneg_left (log_nat_mono (hH d hd)) (Nat.cast_nonneg _)
    apply (div_le_iff₀ hφ).mpr
    calc
      _ ≤ (8*(d.totient : ℝ))*((Nat.log 2 N : ℝ)*Real.log H) :=
        mul_le_mul hratio hlift (characterLiftError_nonneg d N) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ _d ∈ pairPrimeProducts P Q, 8*(Nat.log 2 N : ℝ)*Real.log H := sum_le_sum hloc
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

/-- All nontrivial conductors are retained, including the one-factor groups. -/
theorem pair_composite_error_le (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hdis : Disjoint P Q) (N H : ℕ) (hH : ∀ d ∈ pairPrimeProducts P Q, d ≤ H) :
    (∑ d ∈ pairPrimeProducts P Q, compositeProgressionError d N) ≤
      poolTotientMass Q * primitivePoolMean P N +
      poolTotientMass P * primitivePoolMean Q N + primitivePoolMean (pairPrimeProducts P Q) N +
      8*((pairPrimeProducts P Q).card : ℝ)*(Nat.log 2 N : ℝ)*Real.log H := by
  simp only [compositeProgressionError, add_div, sum_add_distrib]
  exact _root_.add_le_add (pair_conductor_majorant_le P Q hP hQ hdis N)
    (pair_product_lift_error_le P Q hP hQ hdis N H hH)

end Erdos821
