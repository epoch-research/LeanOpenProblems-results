import Submission.CoreTailSieve
import Submission.DoubleCoverQuadratic

/-! Selected-pair bounds for covers with no triple hit. The multiplicity
hypothesis is explicit; these results do not prove the unrestricted conjecture. -/
namespace Erdos970.DoubleCover
open Finset CoreTailSieve

lemma four_band_margin (a b c d : ℝ)
    (ha : 0 ≤ a) (ha' : a ≤ 184 / 1000)
    (hb : 0 ≤ b) (hb' : b ≤ 225 / 1000)
    (hc : 0 ≤ c) (hc' : c ≤ 184 / 1000)
    (hd : d ≤ 512 / 1000) :
    (24993 : ℝ) / 2000000 ≤ 1 - a - b - c - d + (a + b) ^ 2 / 2 + a * c := by
  have h1 : 0 ≤ (184 / 1000 - a) * (1 - (a + 184 / 1000 + 2 * b) / 2 - c) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (225 / 1000 - b) * (1 - (b + 225 / 1000 + 2 * (184 / 1000)) / 2) :=
    mul_nonneg (by linarith) (by linarith)
  have h3 : 0 ≤ (184 / 1000 - c) * (1 - (184 / 1000 : ℝ)) :=
    mul_nonneg (by linarith) (by norm_num)
  nlinarith only [h1, h2, h3, hd]

/-- CRT forces every triple product past the interval length. -/
lemma triple_product_gt {P : Finset ℕ} {r : ℕ → ℕ} {m p q s : ℕ}
    (hP : ∀ u ∈ P, u.Prime)
    (hdouble : ∀ x < m, (P.filter (fun u => x ≡ r u [MOD u])).card ≤ 2)
    (hp : p ∈ P) (hq : q ∈ P) (hs : s ∈ P)
    (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s) :
    m < p * q * s := by
  classical
  have hp' := hP p hp
  have hq' := hP q hq
  have hs' := hP s hs
  have hcop := (Nat.coprime_primes hp' hq').mpr hpq
  have hcop' : (p * q).Coprime s :=
    ((Nat.coprime_primes hp' hs').mpr hps).mul_left
      ((Nat.coprime_primes hq' hs').mpr hqs)
  let b := Nat.chineseRemainder hcop (r p) (r q)
  let x := Nat.chineseRemainder hcop' b.val (r s)
  have hxlt : x.val < p * q * s :=
    Nat.chineseRemainder_lt_mul hcop' _ _ (Nat.mul_ne_zero hp'.ne_zero hq'.ne_zero) hs'.ne_zero
  have hxp : x.val ≡ r p [MOD p] :=
    (x.property.1.of_dvd (dvd_mul_right p q)).trans b.property.1
  have hxq : x.val ≡ r q [MOD q] :=
    (x.property.1.of_dvd (dvd_mul_left q p)).trans b.property.2
  by_contra hn
  have hxm : x.val < m := by omega
  have hsub : ({p, q, s} : Finset ℕ) ⊆ P.filter (fun u => x.val ≡ r u [MOD u]) := by
    intro u hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact mem_filter.mpr ⟨hp, hxp⟩
    · exact mem_filter.mpr ⟨hq, hxq⟩
    · exact mem_filter.mpr ⟨hs, x.property.2⟩
  have hn3 : ({p, q, s} : Finset ℕ).card = 3 := by simp [hpq, hps, hqs]
  have hh := (card_le_card hsub).trans (hdouble x.val hxm)
  omega

lemma small_core_card_le_two {P : Finset ℕ} {r : ℕ → ℕ} {m t : ℕ}
    (hP : ∀ u ∈ P, u.Prime)
    (hdouble : ∀ x < m, (P.filter (fun u => x ≡ r u [MOD u])).card ≤ 2)
    (ht : t ^ 3 ≤ m) : (P.filter (fun p => p ≤ t)).card ≤ 2 := by
  classical
  by_contra hn
  have hthree : 2 < (P.filter (fun p => p ≤ t)).card := by omega
  obtain ⟨p, hp, q, hq, s, hs, hpq, hps, hqs⟩ := Finset.two_lt_card.mp hthree
  have hh := triple_product_gt hP hdouble (mem_filter.mp hp).1
    (mem_filter.mp hq).1 (mem_filter.mp hs).1 hpq hps hqs
  have hprod : p * q * s ≤ t ^ 3 := by
    have hmul := Nat.mul_le_mul (Nat.mul_le_mul (mem_filter.mp hp).2
      (mem_filter.mp hq).2) (mem_filter.mp hs).2
    nlinarith only [hmul]
  omega

lemma selected_pairs_pointwise (R : Finset ℕ) (F : Finset (Finset ℕ))
    (hF : F ⊆ R.powersetCard 2) (f : ℕ → Prop) [DecidablePred f]
    (hpos : 0 < (R.filter f).card) (htwo : (R.filter f).card ≤ 2) :
    (1 : ℝ) - (∑ p ∈ R, if f p then 1 else 0) +
      (∑ T ∈ F, if ∀ p ∈ T, f p then 1 else 0) ≤ 0 := by
  classical
  have hsub : F.filter (fun T => ∀ p ∈ T, f p) ⊆ (R.filter f).powersetCard 2 := by
    intro T hT
    obtain ⟨hTF, hf⟩ := mem_filter.mp hT
    obtain ⟨hTR, hcard⟩ := mem_powersetCard.mp (hF hTF)
    exact mem_powersetCard.mpr ⟨fun p hp => mem_filter.mpr ⟨hTR hp, hf p hp⟩, hcard⟩
  have hcard := card_le_card hsub
  rw [card_powersetCard] at hcard
  rw [sum_boole, sum_boole]
  have hcase : (R.filter f).card = 1 ∨ (R.filter f).card = 2 := by omega
  rcases hcase with h | h <;> rw [h] at hcard ⊢ <;> norm_num at hcard ⊢ <;>
    exact_mod_cast hcard

lemma selected_pairs_nonpos (Q R : Finset ℕ) (F : Finset (Finset ℕ))
    (hF : F ⊆ R.powersetCard 2) (r : ℕ → ℕ) (m : ℕ)
    (hcover : ∀ x < m, ∃ p ∈ Q ∪ R, x ≡ r p [MOD p])
    (hdouble : ∀ x < m, (R.filter (fun p => x ≡ r p [MOD p])).card ≤ 2) :
    siftCount Q ∅ r m - (∑ p ∈ R, siftCount Q {p} r m) +
      (∑ T ∈ F, siftCount Q T r m) ≤ 0 := by
  classical
  have hcount (T : Finset ℕ) : siftCount Q T r m =
      ∑ x ∈ range m, if (∀ q ∈ Q, ¬x ≡ r q [MOD q]) ∧
        (∀ p ∈ T, x ≡ r p [MOD p]) then (1 : ℝ) else 0 := by
    simp only [siftCount, siftSet, sum_boole]
  simp_rw [hcount]
  rw [sum_comm (s := R), sum_comm (s := F), ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_nonpos
  intro x hx
  have hxm := mem_range.mp hx
  by_cases hQ : ∀ q ∈ Q, ¬x ≡ r q [MOD q]
  · have hpos : 0 < (R.filter (fun p => x ≡ r p [MOD p])).card := by
      obtain ⟨p, hp, hpx⟩ := hcover x hxm
      have hpR : p ∈ R := (mem_union.mp hp).resolve_left (fun hpQ => hQ p hpQ hpx)
      exact card_pos.mpr ⟨p, mem_filter.mpr ⟨hpR, hpx⟩⟩
    have hh := selected_pairs_pointwise R F hF (fun p => x ≡ r p [MOD p]) hpos (hdouble x hxm)
    simp_all
  · simp only [hQ, false_and, if_false, sum_const_zero, sub_self, add_zero, le_refl]

/-- The error depends on the selected pair count, not on all tail pairs. -/
theorem cover_selected_pairs_bound (Q R : Finset ℕ) (F : Finset (Finset ℕ))
    (hQ : ∀ q ∈ Q, q.Prime) (hR : ∀ p ∈ R, p.Prime)
    (hdis : Disjoint Q R) (hF : F ⊆ R.powersetCard 2) (r : ℕ → ℕ) (m : ℕ)
    (hcover : ∀ x < m, ∃ p ∈ Q ∪ R, x ≡ r p [MOD p])
    (hdouble : ∀ x < m, (R.filter (fun p => x ≡ r p [MOD p])).card ≤ 2) :
    (m : ℝ) * density Q *
      (1 - (∑ p ∈ R, 1 / (p : ℝ)) + ∑ T ∈ F, 1 / ∏ p ∈ T, (p : ℝ)) ≤
      (2 : ℝ) ^ Q.card * (1 + R.card + F.card) := by
  classical
  have h0 := (abs_le.mp (siftCount_error Q ∅ hQ (by simp) (by simp) r m)).1
  simp only [prod_empty, div_one] at h0
  have hp (p : ℕ) (hp : p ∈ R) : siftCount Q {p} r m ≤
      (m : ℝ) * density Q * (1 / (p : ℝ)) + (2 : ℝ) ^ Q.card := by
    have hh := (abs_le.mp (siftCount_error Q {p} hQ (by simpa using hR p hp)
      (hdis.mono_right (singleton_subset_iff.mpr hp)) r m)).2
    simp only [prod_singleton, div_eq_mul_inv, one_div] at hh ⊢
    linarith
  have hT (T : Finset ℕ) (hT : T ∈ F) :
      (m : ℝ) * density Q * (1 / ∏ p ∈ T, (p : ℝ)) - (2 : ℝ) ^ Q.card ≤
        siftCount Q T r m := by
    have hTR := (mem_powersetCard.mp (hF hT)).1
    have hh := (abs_le.mp (siftCount_error Q T hQ (fun p hp => hR p (hTR hp))
      (hdis.mono_right hTR) r m)).1
    simp only [div_eq_mul_inv, one_div] at hh ⊢
    linarith
  have hs := sum_le_sum hp
  have ht := sum_le_sum hT
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at hs ht
  have hc := selected_pairs_nonpos Q R F hF r m hcover hdouble
  nlinarith only [h0, hs, ht, hc]

#print axioms four_band_margin
#print axioms triple_product_gt
#print axioms small_core_card_le_two
#print axioms cover_selected_pairs_bound
end Erdos970.DoubleCover
