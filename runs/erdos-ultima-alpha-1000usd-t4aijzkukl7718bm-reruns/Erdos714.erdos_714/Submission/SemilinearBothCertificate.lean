import FormalConjecturesUtil

/-! Polynomial certificate infrastructure for a refined auxiliary semilinear graph.
This file does not settle Erdős 714. -/

open Polynomial Matrix
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos714BothCertificate

abbrev R := Polynomial (ZMod 2)
def modulus : R := X^9 + X^4 + 1
lemma modulus_monic : modulus.Monic := by
  unfold modulus
  monicity <;> norm_num
lemma modulus_degree : modulus.degree = 9 := by
  unfold modulus
  compute_degree <;> norm_num <;> decide

lemma root_pow512 {K : Type*} [CommRing K] [CharP K 2]
    (z : K) (hz : z^9 + z^4 + 1 = 0) : z^512 = z := by
  have h0 : z^1 = z := by simp
  have step0 : (z)^2 = (z^2) := by
    ring
  have h1 : z^2 = (z^2) := by
    calc
      _ = (z^1)^2 := by ring
      _ = (z)^2 := by rw [h0]
      _ = _ := step0
  have step1 : (z^2)^2 = (z^4) := by
    ring
  have h2 : z^4 = (z^4) := by
    calc
      _ = (z^2)^2 := by ring
      _ = (z^2)^2 := by rw [h1]
      _ = _ := step1
  have step2 : (z^4)^2 = (z^8) := by
    ring
  have h3 : z^8 = (z^8) := by
    calc
      _ = (z^4)^2 := by ring
      _ = (z^4)^2 := by rw [h2]
      _ = _ := step2
  have step3 : (z^8)^2 = (z^2 + z^6 + z^7) := by
    have he : (z^8)^2 = (z^2 + z^6 + z^7) + (z^9 + z^4 + 1)*(z^2 + z^7) := by
      ring_nf
      reduce_mod_char!
    simpa only [hz, zero_mul, add_zero] using he
  have h4 : z^16 = (z^2 + z^6 + z^7) := by
    calc
      _ = (z^8)^2 := by ring
      _ = (z^8)^2 := by rw [h3]
      _ = _ := step3
  have step4 : (z^2 + z^6 + z^7)^2 = (1 + z^3 + z^5 + z^7) := by
    have he : (z^2 + z^6 + z^7)^2 = (1 + z^3 + z^5 + z^7) + (z^9 + z^4 + 1)*(1 + z^3 + z^5) := by
      ring_nf
      reduce_mod_char!
    simpa only [hz, zero_mul, add_zero] using he
  have h5 : z^32 = (1 + z^3 + z^5 + z^7) := by
    calc
      _ = (z^16)^2 := by ring
      _ = (z^2 + z^6 + z^7)^2 := by rw [h4]
      _ = _ := step4
  have step5 : (1 + z^3 + z^5 + z^7)^2 = (z + z^4 + z^6) := by
    have he : (1 + z^3 + z^5 + z^7)^2 = (z + z^4 + z^6) + (z^9 + z^4 + 1)*(1 + z + z^5) := by
      ring_nf
      reduce_mod_char!
    simpa only [hz, zero_mul, add_zero] using he
  have h6 : z^64 = (z + z^4 + z^6) := by
    calc
      _ = (z^32)^2 := by ring
      _ = (1 + z^3 + z^5 + z^7)^2 := by rw [h5]
      _ = _ := step5
  have step6 : (z + z^4 + z^6)^2 = (z^2 + z^3 + z^7 + z^8) := by
    have he : (z + z^4 + z^6)^2 = (z^2 + z^3 + z^7 + z^8) + (z^9 + z^4 + 1)*(z^3) := by
      ring_nf
      reduce_mod_char!
    simpa only [hz, zero_mul, add_zero] using he
  have h7 : z^128 = (z^2 + z^3 + z^7 + z^8) := by
    calc
      _ = (z^64)^2 := by ring
      _ = (z + z^4 + z^6)^2 := by rw [h6]
      _ = _ := step6
  have step7 : (z^2 + z^3 + z^7 + z^8)^2 = (1 + z^2 + z^5 + z^7) := by
    have he : (z^2 + z^3 + z^7 + z^8)^2 = (1 + z^2 + z^5 + z^7) + (z^9 + z^4 + 1)*(1 + z^2 + z^5 + z^7) := by
      ring_nf
      reduce_mod_char!
    simpa only [hz, zero_mul, add_zero] using he
  have h8 : z^256 = (1 + z^2 + z^5 + z^7) := by
    calc
      _ = (z^128)^2 := by ring
      _ = (z^2 + z^3 + z^7 + z^8)^2 := by rw [h7]
      _ = _ := step7
  have step8 : (1 + z^2 + z^5 + z^7)^2 = (z) := by
    have he : (1 + z^2 + z^5 + z^7)^2 = (z) + (z^9 + z^4 + 1)*(1 + z + z^5) := by
      ring_nf
      reduce_mod_char!
    simpa only [hz, zero_mul, add_zero] using he
  have h9 : z^512 = (z) := by
    calc
      _ = (z^256)^2 := by ring
      _ = (1 + z^2 + z^5 + z^7)^2 := by rw [h8]
      _ = _ := step8
  exact h9

lemma modulus_dvd : modulus ∣ (X^512 - X : R) := by
  let A := AdjoinRoot modulus
  letI : Nontrivial A := AdjoinRoot.nontrivial _ (by rw [modulus_degree]; decide)
  letI : CharP A 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) A).injective 2
  have hz : (AdjoinRoot.root modulus)^9 + (AdjoinRoot.root modulus)^4 + 1 = 0 := by
    simpa only [modulus, Polynomial.eval₂_add, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_one] using AdjoinRoot.eval₂_root modulus
  apply AdjoinRoot.mk_eq_zero.mp
  simp only [map_sub, map_pow, AdjoinRoot.mk_X]
  exact sub_eq_zero.mpr (root_pow512 _ hz)

abbrev F := GaloisField 2 9
lemma field_card : Nat.card F = 512 := by
  simpa using GaloisField.card 2 9 (by decide)
lemma field_pow (a : F) : a^512 = a := by
  classical
  letI := Fintype.ofFinite F
  have hc : Fintype.card F = 512 := by
    simpa only [Nat.card_eq_fintype_card] using field_card
  simpa only [hc] using FiniteField.pow_card a
lemma exists_modulus_root : ∃ z : F, eval₂ (algebraMap (ZMod 2) F) z modulus = 0 := by
  have hsplit := FiniteField.splits_X_pow_nat_card_sub_X (p := 2) (K := F)
  rw [field_card] at hsplit
  have hdvd := Polynomial.map_dvd (algebraMap (ZMod 2) F) modulus_dvd
  have hne : (X^512 - X : R).map (algebraMap (ZMod 2) F) ≠ 0 := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
    exact sub_ne_zero.mpr (by intro h; have := congrArg Polynomial.natDegree h; norm_num at this)
  have hs := hsplit.of_dvd hne hdvd
  have hdeg : ((modulus.map (algebraMap (ZMod 2) F))).degree ≠ 0 := by
    unfold modulus
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    have hd : (X^9 + X^4 + 1 : Polynomial F).degree = 9 := by
      compute_degree <;> norm_num <;> decide
    rw [hd]
    norm_num
  obtain ⟨z, hz⟩ := hs.exists_eval_eq_zero hdeg
  exact ⟨z, by simpa only [Polynomial.eval_map] using hz⟩

#print axioms root_pow512
#print axioms modulus_dvd
#print axioms exists_modulus_root
end Erdos714BothCertificate
