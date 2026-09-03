import Submission.SignedBlockMoments
import Submission.SmallSignJets

/-!
Primitive square collisions with a growing number of equal binary digit
moments. Primitivity here means common gcd one, not pairwise coprimality or
primality. This is an auxiliary obstruction, not a disproof of Erdos 773.
-/
namespace Erdos773.PrimitiveGrowingMoments
open Polynomial Finset
noncomputable section
set_option maxHeartbeats 1500000

private def BW (L : ℕ) (P : ℤ[X]) : Prop :=
  P ∈ binaryPolynomials ∧ ∀ i, L ≤ i → P.coeff i = 0

private lemma append_word {L H : ℕ} {P Q : ℤ[X]}
    (hP : BW L P) (hQ : BW H Q) : BW (L + H) (P + X ^ L * Q) := by
  constructor
  · intro i
    rw [coeff_add, coeff_X_pow_mul']
    by_cases hi : L ≤ i
    · simp only [if_pos hi, hP.2 i hi, zero_add]
      exact hQ.1 _
    · simpa only [if_neg hi, add_zero] using hP.1 i
  · intro i hi
    have hLi : L ≤ i := by omega
    have hHi : H ≤ i - L := by omega
    simp [coeff_add, coeff_X_pow_mul', hLi, hP.2 i hLi, hQ.2 _ hHi]

private lemma one_word {L : ℕ} (hL : 0 < L) : BW L (1 : ℤ[X]) := by
  constructor
  · intro i
    by_cases hi : i = 0 <;> simp [coeff_one, hi]
  · intro i hi
    simp [coeff_one, show i ≠ 0 by omega]

private lemma append_odd {L H : ℕ} (hL : 0 < L) {P Q : ℤ[X]}
    (hP : OddBinaryWord L P) (hQ : BW H Q) :
    OddBinaryWord (L + H) (P + X ^ L * Q) := by
  refine ⟨?_, append_word hP.2 hQ⟩
  rw [coeff_add, coeff_X_pow_mul']
  simp [show ¬L ≤ 0 by omega, hP.1]

private lemma pad_odd {L H : ℕ} {P : ℤ[X]} (h : OddBinaryWord L P) (hLH : L ≤ H) :
    OddBinaryWord H P := ⟨h.1, h.2.1, fun i hi => h.2.2 i (hLH.trans hi)⟩

private lemma word_bound {L : ℕ} (_hL : 0 < L) {P : ℤ[X]} (hP : BW L P) :
    0 ≤ P.eval 2 ∧ P.eval 2 < (2 : ℤ) ^ L := by
  have he : P = ∑ i ∈ range L, C (P.coeff i) * X ^ i := by
    ext i
    simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    by_cases hi : i < L
    · simp [hi]
    · simp [hi, hP.2 i (by omega)]
  have hev : P.eval 2 = ∑ i ∈ range L, P.coeff i * (2 : ℤ) ^ i := by
    conv_lhs => rw [he]
    simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  have hsum : (∑ i ∈ range L, (2 : ℤ) ^ i) = 2 ^ L - 1 := by
    have hh := onesPolynomial_eval_two L
    simpa [onesPolynomial] using hh
  rw [hev]
  constructor
  · apply sum_nonneg
    intro i hi
    have hc := hP.1 i
    rcases hc with hc | hc <;> simp [hc]
  · have hh : (∑ i ∈ range L, P.coeff i * (2 : ℤ) ^ i) ≤
        ∑ i ∈ range L, (2 : ℤ) ^ i := by
      apply sum_le_sum
      intro i hi
      rcases hP.1 i with hc | hc <;> simp [hc]
    rw [hsum] at hh
    omega

private def bitsWord : ℕ → ℕ → ℤ[X]
  | 0, _ => 0
  | L + 1, n => C ((n % 2 : ℕ) : ℤ) + X * bitsWord L (n / 2)

private lemma bitsWord_spec (L n : ℕ) (hn : n < 2 ^ L) :
    BW L (bitsWord L n) ∧ (bitsWord L n).eval 2 = n := by
  induction L generalizing n with
  | zero =>
    have hn0 : n = 0 := by simpa using hn
    subst n
    simp [bitsWord, BW, binaryPolynomials]
  | succ L ih =>
    have hn' : n / 2 < 2 ^ L := by rw [pow_succ] at hn; omega
    obtain ⟨hw, hv⟩ := ih (n / 2) hn'
    have hc : n % 2 = 0 ∨ n % 2 = 1 := by omega
    have hlow : BW 1 (C ((n % 2 : ℕ) : ℤ)) := by
      constructor
      · intro i
        rcases hc with hc | hc <;> by_cases hi : i = 0 <;> simp only [hc, Nat.cast_zero, Nat.cast_one, coeff_C, hi] <;> simp
      · intro i hi
        rw [coeff_C]; simp [show i ≠ 0 by omega]
    constructor
    · simpa [bitsWord, Nat.add_comm, pow_one] using append_word hlow hw
    · simp only [bitsWord, eval_add, eval_C, eval_mul, eval_X, hv]
      have hh := Nat.mod_add_div n 2
      exact_mod_cast hh

private lemma odd_word_of_int {L : ℕ} (hL : 0 < L) {n : ℤ}
    (hn : 0 ≤ n) (hnL : n < 2 ^ L) (hodd : n % 2 = 1) :
    ∃ P : ℤ[X], OddBinaryWord L P ∧ P.eval 2 = n := by
  have he : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
  have hn' : n.toNat < 2 ^ L := by
    have hh : (n.toNat : ℤ) < (2 : ℤ) ^ L := by rwa [he]
    exact_mod_cast hh
  obtain ⟨hw, hv⟩ := bitsWord_spec L n.toNat hn'
  refine ⟨bitsWord L n.toNat, ⟨?_, hw⟩, ?_⟩
  · obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
    simp only [bitsWord, coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero]
    have he : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
    have hh : ((n.toNat % 2 : ℕ) : ℤ) = 1 := by
      rw [Int.natCast_emod, he]
      exact hodd
    exact hh
  · simpa [Int.toNat_of_nonneg hn] using hv

private def rootA (u v : ℤ) := 1 + 3*u + 3*v + u*v
private def rootB (u v : ℤ) := 1 + 7*u + 7*v + 41*u*v
private def rootC (u v : ℤ) := 1 + 7*u + 3*v + 29*u*v
private def rootD (u v : ℤ) := 1 + 3*u + 7*v + 29*u*v

private lemma roots_collision (u v : ℤ) :
    rootA u v ^ 2 + rootB u v ^ 2 = rootC u v ^ 2 + rootD u v ^ 2 := by
  unfold rootA rootB rootC rootD
  ring

private lemma roots_primitive {u v : ℤ} (hu : u % 2 = 0) (hv : v % 2 = 0)
    {g : ℕ} (hA : (g : ℤ) ∣ rootA u v) (hB : (g : ℤ) ∣ rootB u v)
    (hC : (g : ℤ) ∣ rootC u v) (hD : (g : ℤ) ∣ rootD u v) : g = 1 := by
  have he : 29 * rootC u v + 29 * rootD u v - rootA u v - 41 * rootB u v = 16 := by
    unfold rootA rootB rootC rootD
    ring
  have hg : (g : ℤ) ∣ 16 := by
    rw [← he]
    exact dvd_sub (dvd_sub (dvd_add (dvd_mul_of_dvd_right hC 29)
      (dvd_mul_of_dvd_right hD 29)) hA) (dvd_mul_of_dvd_right hB 41)
  have hgN : g ∣ 16 := by exact_mod_cast hg
  have haodd : rootA u v % 2 = 1 := by
    simp [rootA, Int.add_emod, Int.mul_emod, hu, hv]
  have hgodd : ¬2 ∣ g := by
    intro hh
    have h2g : (2 : ℤ) ∣ g := by exact_mod_cast hh
    have h2a := h2g.trans hA
    have hzero := Int.emod_eq_zero_of_dvd h2a
    omega
  have hc : Nat.Coprime 2 g := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    exact hgodd
  have hc16 : Nat.Coprime 16 g := by simpa using hc.pow_left 4
  exact Nat.eq_one_of_dvd_coprimes hc16 hgN (dvd_refl g)


/-- Four distinct positive roots in binary, with equal first k moments and
common gcd one. No pairwise coprimality or primality is included. -/
def PrimitiveMomentCollision (L k : ℕ) : Prop :=
  ∃ P Q R S : ℤ[X],
    OddBinaryWord L P ∧ OddBinaryWord L Q ∧ OddBinaryWord L R ∧ OddBinaryWord L S ∧
    0 < P.eval 2 ∧ P.eval 2 < R.eval 2 ∧ R.eval 2 < S.eval 2 ∧ S.eval 2 < Q.eval 2 ∧
    P.eval 2 ^ 2 + Q.eval 2 ^ 2 = R.eval 2 ^ 2 + S.eval 2 ^ 2 ∧
    (∀ j < k, polynomialDigitMoment L P j = polynomialDigitMoment L Q j ∧
      polynomialDigitMoment L P j = polynomialDigitMoment L R j ∧
      polynomialDigitMoment L P j = polynomialDigitMoment L S j) ∧
    (∀ g : ℕ, (g : ℤ) ∣ P.eval 2 → (g : ℤ) ∣ Q.eval 2 →
      (g : ℤ) ∣ R.eval 2 → (g : ℤ) ∣ S.eval 2 → g = 1)

/-- Two levels of signed-block encoding retain a common unit constant, avoiding
the common-multiplier defect of the earlier moment construction. -/
theorem collision_from_signed_jet (D k : ℕ) (e : ℕ → ℤ)
    (he : ∀ i < D + 1, -1 ≤ e i ∧ e i ≤ 1) (hl : e D = 1)
    (hj : (X - 1 : ℤ[X]) ^ k ∣ ∑ i ∈ range (D + 1), C (e i) * X ^ i) :
    PrimitiveMomentCollision ((4 * (D + 2) + 6) * (D + 2)) k := by
  let p3 : ℤ[X] := ∑ i ∈ ({0,1} : Finset ℕ), X ^ i
  let p7 : ℤ[X] := ∑ i ∈ ({0,1,2} : Finset ℕ), X ^ i
  have hp3 : OddBinaryWord 4 p3 :=
    oddBinaryWord_sum _ (by simp) (by intro i hi; simp at hi; omega)
  have hp7 : OddBinaryWord 4 p7 :=
    oddBinaryWord_sum _ (by simp) (by intro i hi; simp at hi; omega)
  obtain ⟨M₁, E₁, hM₁, hw₁, hj₁⟩ :=
    SignedBlockMoments.exists_block_encoder D 4 k (by omega) e he hl hj
  let u : ℤ := 16 * M₁
  let H : ℕ := 4 * (D + 2)
  let T₀ : ℤ[X] := 1 + X ^ 4 * E₁ p3
  let T₁ : ℤ[X] := 1 + X ^ 4 * E₁ p7
  have hH : 0 < H := by dsimp [H]; omega
  have hT (P : ℤ[X]) (hP : OddBinaryWord 4 P) :
      OddBinaryWord H (1 + X ^ 4 * E₁ P) := by
    have hlen : 4 + 4 * (D + 1) = H := by dsimp [H]; omega
    rw [← hlen]
    exact append_odd (by omega) ⟨by simp, one_word (by omega)⟩
      ⟨(hw₁ P hP).1, (hw₁ P hP).2.1⟩
  have hT₀ : OddBinaryWord H T₀ := hT p3 hp3
  have hT₁ : OddBinaryWord H T₁ := hT p7 hp7
  have ht₀ : T₀.eval 2 = 1 + 3 * u := by
    simp only [T₀, eval_add, eval_one, eval_mul, eval_pow, eval_X, (hw₁ p3 hp3).2.2]
    norm_num [p3, u]
    ring
  have ht₁ : T₁.eval 2 = 1 + 7 * u := by
    simp only [T₁, eval_add, eval_one, eval_mul, eval_pow, eval_X, (hw₁ p7 hp7).2.2]
    norm_num [p7, u]
    ring
  have hu : 0 < u := by dsimp [u]; omega
  have hu2 : u % 2 = 0 := by simp [u, Int.mul_emod]
  have huH : u < (2 : ℤ) ^ H := by
    have hh := (word_bound hH hT₁.2).2
    rw [ht₁] at hh
    omega
  have hTjet : (X - 1 : ℤ[X]) ^ k ∣ T₀ - T₁ := by
    have hid : T₀ - T₁ = X ^ 4 * (E₁ p3 - E₁ p7) := by dsimp [T₀, T₁]; ring
    rw [hid]
    exact (hj₁ p3 p7).mul_left _
  let L : ℕ := H + 6
  have hL : 0 < L := by dsimp [L]; omega
  have hHL : H ≤ L := by dsimp [L]; omega
  have hpow : (2 : ℤ) ^ L = 64 * 2 ^ H := by
    dsimp [L]
    rw [pow_add]
    norm_num
    ring
  obtain ⟨R₀, hR₀, hr₀⟩ := odd_word_of_int hL
    (n := 3 + u) (by omega) (by rw [hpow]; omega)
    (by simp [Int.add_emod, hu2])
  obtain ⟨R₁, hR₁, hr₁⟩ := odd_word_of_int hL
    (n := 7 + 41*u) (by omega) (by rw [hpow]; omega)
    (by simp [Int.add_emod, Int.mul_emod, hu2])
  obtain ⟨R₂, hR₂, hr₂⟩ := odd_word_of_int hL
    (n := 3 + 29*u) (by omega) (by rw [hpow]; omega)
    (by simp [Int.add_emod, Int.mul_emod, hu2])
  obtain ⟨R₃, hR₃, hr₃⟩ := odd_word_of_int hL
    (n := 7 + 29*u) (by omega) (by rw [hpow]; omega)
    (by simp [Int.add_emod, Int.mul_emod, hu2])
  obtain ⟨M₂, E₂, hM₂, hw₂, hj₂⟩ :=
    SignedBlockMoments.exists_block_encoder D L k hL e he hl hj
  let v : ℤ := 2 ^ L * M₂
  have hv2 : v % 2 = 0 := by
    dsimp [v]
    rw [hpow]
    simp [Int.mul_emod]
  have huv : u < v := by
    have hp : (0 : ℤ) < 2 ^ H := by positivity
    have hm : 1 ≤ M₂ := by omega
    have hh := mul_le_mul_of_nonneg_left hm (show (0 : ℤ) ≤ 2 ^ L by positivity)
    dsimp [v]
    rw [mul_one] at hh
    rw [hpow] at hh ⊢
    omega
  have hv : 0 < v := hu.trans huv
  let P := T₀ + X ^ L * E₂ R₀
  let Q := T₁ + X ^ L * E₂ R₁
  let R := T₁ + X ^ L * E₂ R₂
  let S := T₀ + X ^ L * E₂ R₃
  have hW (T R' : ℤ[X]) (hT : OddBinaryWord H T) (hR : OddBinaryWord L R') :
      OddBinaryWord (L * (D + 2)) (T + X ^ L * E₂ R') := by
    have hlen : L + L * (D + 1) = L * (D + 2) := by ring
    rw [← hlen]
    exact append_odd hL (pad_odd hT hHL) ⟨(hw₂ R' hR).1, (hw₂ R' hR).2.1⟩
  have hP : OddBinaryWord (L * (D + 2)) P := hW T₀ R₀ hT₀ hR₀
  have hQ : OddBinaryWord (L * (D + 2)) Q := hW T₁ R₁ hT₁ hR₁
  have hR : OddBinaryWord (L * (D + 2)) R := hW T₁ R₂ hT₁ hR₂
  have hS : OddBinaryWord (L * (D + 2)) S := hW T₀ R₃ hT₀ hR₃
  have hp : P.eval 2 = rootA u v := by
    simp only [P, eval_add, eval_mul, eval_pow, eval_X, ht₀, (hw₂ R₀ hR₀).2.2, hr₀]
    dsimp [rootA, v]
    ring
  have hq : Q.eval 2 = rootB u v := by
    simp only [Q, eval_add, eval_mul, eval_pow, eval_X, ht₁, (hw₂ R₁ hR₁).2.2, hr₁]
    dsimp [rootB, v]
    ring
  have hr : R.eval 2 = rootC u v := by
    simp only [R, eval_add, eval_mul, eval_pow, eval_X, ht₁, (hw₂ R₂ hR₂).2.2, hr₂]
    dsimp [rootC, v]
    ring
  have hs : S.eval 2 = rootD u v := by
    simp only [S, eval_add, eval_mul, eval_pow, eval_X, ht₀, (hw₂ R₃ hR₃).2.2, hr₃]
    dsimp [rootD, v]
    ring
  have hJ {A B C D : ℤ[X]} (hAB : (X - 1 : ℤ[X]) ^ k ∣ A - B) :
      (X - 1 : ℤ[X]) ^ k ∣ (A + X ^ L * E₂ C) - (B + X ^ L * E₂ D) := by
    have hh := dvd_add hAB ((hj₂ C D).mul_left (X ^ L))
    convert hh using 1
    ring
  have hjQ : (X - 1 : ℤ[X]) ^ k ∣ P - Q := hJ hTjet
  have hjR : (X - 1 : ℤ[X]) ^ k ∣ P - R := hJ hTjet
  have hjS : (X - 1 : ℤ[X]) ^ k ∣ P - S := hJ (by simp)
  change PrimitiveMomentCollision (L * (D + 2)) k
  refine ⟨P, Q, R, S, hP, hQ, hR, hS, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp]
    dsimp [rootA]
    positivity
  · rw [hp, hr]
    dsimp [rootA, rootC]
    nlinarith [mul_pos hu hv]
  · rw [hr, hs]
    dsimp [rootC, rootD]
    omega
  · rw [hs, hq]
    dsimp [rootD, rootB]
    nlinarith [mul_pos hu hv]
  · rw [hp, hq, hr, hs]
    exact roots_collision u v
  · intro j hj'
    rw [polynomialDigitMoment_eq _ _ hP.2.2, polynomialDigitMoment_eq _ _ hQ.2.2,
      polynomialDigitMoment_eq _ _ hR.2.2, polynomialDigitMoment_eq _ _ hS.2.2]
    exact ⟨eulerIter_eval_one_of_jet hjQ hj', eulerIter_eval_one_of_jet hjR hj',
      eulerIter_eval_one_of_jet hjS hj'⟩
  · intro g hgP hgQ hgR hgS
    rw [hp] at hgP
    rw [hq] at hgQ
    rw [hr] at hgR
    rw [hs] at hgS
    exact roots_primitive hu2 hv2 hgP hgQ hgR hgS


/-- Polynomial-length primitive collisions with matching first k binary digit
moments. The common gcd of the four roots is one; the roots are not asserted
to be pairwise coprime or prime. -/
theorem matching_moment_collision_quartic_log (k : ℕ) (hk : 1 ≤ k) :
    ∃ L : ℕ, 0 < L ∧ L ≤ 1280 * k ^ 4 * (k.log2 + 1) ^ 2 ∧
      PrimitiveMomentCollision L k := by
  obtain ⟨V, hV, hdeg, hl, hc, hj⟩ := SmallSignJets.exists_signed_jet_quadratic_log k hk
  have hsum : (X - 1 : ℤ[X]) ^ k ∣
      ∑ i ∈ range (V.natDegree + 1), C (V.coeff i) * X ^ i := by
    rw [← V.as_sum_range_C_mul_X_pow]
    exact hj
  have hcol := collision_from_signed_jet V.natDegree k V.coeff
    (fun i hi => hc i) (by simpa only [coeff_natDegree] using hl) hsum
  let K : ℕ := k ^ 2 * (k.log2 + 1)
  have hK : 1 ≤ K := by dsimp [K]; nlinarith [sq_pos_of_pos (show 0 < k by omega)]
  have hD : V.natDegree + 2 ≤ 17 * K := by
    dsimp [K] at *
    nlinarith
  have hbound : (4 * (V.natDegree + 2) + 6) * (V.natDegree + 2) ≤ 1280 * K ^ 2 := by
    have hs := Nat.pow_le_pow_left hD 2
    nlinarith [sq_nonneg (K - 1 : ℤ)]
  refine ⟨(4 * (V.natDegree + 2) + 6) * (V.natDegree + 2), by positivity, ?_, hcol⟩
  calc
    _ ≤ 1280 * K ^ 2 := hbound
    _ = _ := by dsimp [K]; ring

/-- Each constructed primitive moment collision is genuinely non-Sidon. -/
theorem PrimitiveMomentCollision.not_sidon {L k : ℕ} (h : PrimitiveMomentCollision L k) :
    ∃ P Q R S : ℤ[X], OddBinaryWord L P ∧ OddBinaryWord L Q ∧
      OddBinaryWord L R ∧ OddBinaryWord L S ∧
      ¬ IsSidon ({P.eval 2 ^ 2, Q.eval 2 ^ 2, R.eval 2 ^ 2, S.eval 2 ^ 2} : Set ℤ) := by
  obtain ⟨P,Q,R,S,hP,hQ,hR,hS,hp,hpr,hrs,hsq,he,hm,hg⟩ := h
  refine ⟨P,Q,R,S,hP,hQ,hR,hS,?_⟩
  intro hsidon
  have hh := hsidon _ (by simp) _ (by simp) _ (by simp) _ (by simp) he
  rcases hh with hh | hh
  · nlinarith [sq_nonneg (R.eval 2 - P.eval 2)]
  · nlinarith [sq_nonneg (S.eval 2 - P.eval 2)]

#print axioms matching_moment_collision_quartic_log
#print axioms PrimitiveMomentCollision.not_sidon

#print axioms collision_from_signed_jet

end
end Erdos773.PrimitiveGrowingMoments
