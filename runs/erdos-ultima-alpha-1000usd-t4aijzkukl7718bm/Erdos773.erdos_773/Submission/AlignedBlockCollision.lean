import FormalConjecturesUtil

/-!
Aligned block constraints preserve square-sum collisions.  This module is a
method check, NOT a disproof of Erdős 773.  In particular, none of its statements
bounds the largest Sidon subset of the squares.
-/
namespace Erdos773.AlignedBlockCollision

open Finset

set_option maxHeartbeats 1000000

/-- Reversal of a collision is in the same norm-preserving plane. -/
theorem mix_collision {a b c d : ℕ} (h : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2)
    (u v : ℕ) :
    (a * u + d * v) ^ 2 + (b * u + c * v) ^ 2 =
      (c * u + b * v) ^ 2 + (d * u + a * v) ^ 2 := by
  calc
    _ = (a ^ 2 + b ^ 2) * u ^ 2 + (c ^ 2 + d ^ 2) * v ^ 2 +
      2 * (a * d + b * c) * u * v := by ring
    _ = (c ^ 2 + d ^ 2) * u ^ 2 + (a ^ 2 + b ^ 2) * v ^ 2 +
      2 * (a * d + b * c) * u * v := by rw [h]
    _ = _ := by ring

/-- Positions of the reversed blocks, with the initial block left unchanged. -/
def repeatWeight (W k : ℕ) : ℕ := W * ∑ i ∈ range k, W ^ i

/-- This is the value of the initial block `x i` followed by `k` reversed blocks. -/
def repeatedValue (x : Fin 4 → ℕ) (W k : ℕ) (i : Fin 4) : ℕ :=
  x i + x i.rev * repeatWeight W k

lemma repeated_collision {x : Fin 4 → ℕ}
    (h : x 0 ^ 2 + x 1 ^ 2 = x 2 ^ 2 + x 3 ^ 2) (W k : ℕ) :
    repeatedValue x W k 0 ^ 2 + repeatedValue x W k 1 ^ 2 =
      repeatedValue x W k 2 ^ 2 + repeatedValue x W k 3 ^ 2 := by
  simpa [repeatedValue] using mix_collision h 1 (repeatWeight W k)

lemma repeated_mod (x : Fin 4 → ℕ) (W k : ℕ) (i : Fin 4) :
    repeatedValue x W k i % W = x i % W := by
  simp [repeatedValue, repeatWeight, Nat.add_mod, Nat.mul_mod]

lemma repeated_injective {x : Fin 4 → ℕ} {W : ℕ}
    (hx : Function.Injective x) (hW : ∀ i, x i < W) (k : ℕ) :
    Function.Injective (repeatedValue x W k) := by
  intro i j hij
  apply hx
  have := congrArg (· % W) hij
  simpa only [repeated_mod, Nat.mod_eq_of_lt (hW i), Nat.mod_eq_of_lt (hW j)] using this

/-- The word is indexed by its aligned block and its position in the block. -/
def repeatedWord {L : ℕ} (w : Fin 4 → Fin L → ℕ) (i : Fin 4)
    (b : ℕ) (r : Fin L) : ℕ := if b = 0 then w i r else w i.rev r

lemma block_histogram {L : ℕ} (w : Fin 4 → Fin L → ℕ)
    (h : ∀ i, List.Perm (List.ofFn (w i)) (List.ofFn (w 0)))
    (i j : Fin 4) (b : ℕ) :
    List.Perm (List.ofFn (repeatedWord w i b))
      (List.ofFn (repeatedWord w j b)) := by
  change (List.ofFn (fun r => if b = 0 then w i r else w i.rev r)).Perm
    (List.ofFn (fun r => if b = 0 then w j r else w j.rev r))
  by_cases hb : b = 0
  · simpa only [hb, if_pos rfl] using (h i).trans (h j).symm
  · simpa only [if_neg hb] using (h i.rev).trans (h j.rev).symm

/-- Arbitrary digit statistics agree on EVERY union of aligned whole blocks. -/
theorem aligned_statistics {L : ℕ} {M : Type*} [AddCommMonoid M]
    (w : Fin 4 → Fin L → ℕ)
    (h : ∀ i, List.Perm (List.ofFn (w i)) (List.ofFn (w 0)))
    (i j : Fin 4) (blocks : Finset ℕ) (f : ℕ → M) :
    ∑ b ∈ blocks, ∑ r : Fin L, f (repeatedWord w i b r) =
      ∑ b ∈ blocks, ∑ r : Fin L, f (repeatedWord w j b r) := by
  apply Finset.sum_congr rfl
  intro b hb
  have hh := ((block_histogram w h i j b).map f).sum_eq
  simpa only [List.map_ofFn, List.sum_ofFn] using hh

lemma repeatedWord_value {L : ℕ} (w : Fin 4 → Fin L → ℕ)
    (B k : ℕ) (i : Fin 4) :
    (∑ b ∈ range (k + 1), ∑ r : Fin L,
        repeatedWord w i b r * B ^ (L * b + r.val)) =
      repeatedValue (fun j => ∑ r : Fin L, w j r * B ^ r.val) (B ^ L) k i := by
  rw [Finset.sum_range_succ']
  simp only [repeatedWord, mul_zero, zero_add, Nat.succ_ne_zero, if_false]
  have hs : (∑ b ∈ range k, ∑ r : Fin L,
      w i.rev r * B ^ (L * (b + 1) + r.val)) =
      (∑ r : Fin L, w i.rev r * B ^ r.val) * repeatWeight (B ^ L) k := by
    simp only [repeatWeight, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    rw [pow_add, Nat.mul_add, mul_one, pow_add, pow_mul]
    ring
  rw [hs]
  simp [repeatedValue, add_comm]

/-- A finite prime set has a common repetition period, even when some primes divide `W`. -/
lemma exists_repeat_period (W : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ K : ℕ, 0 < K ∧ ∀ k, K ∣ k → ∀ p ∈ S, p ∣ repeatWeight W k := by
  let K := ∏ p ∈ S, p * (p - 1)
  have hK : 0 < K := by
    apply Finset.prod_pos
    intro p hp
    have := (hS p hp).two_le
    exact Nat.mul_pos (by omega) (by omega)
  refine ⟨K, hK, ?_⟩
  intro k hk p hp
  have hpk : p * (p - 1) ∣ k :=
    (Finset.dvd_prod_of_mem (fun p => p * (p - 1)) hp).trans hk
  have hpdiv : p ∣ k := (dvd_mul_right p (p - 1)).trans hpk
  have hpred : p - 1 ∣ k := (dvd_mul_left (p - 1) p).trans hpk
  letI : Fact p.Prime := ⟨hS p hp⟩
  apply (ZMod.natCast_eq_zero_iff _ p).mp
  simp only [repeatWeight, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow]
  by_cases hz : (W : ZMod p) = 0
  · simp [hz]
  by_cases ho : (W : ZMod p) = 1
  · simpa [ho] using (ZMod.natCast_eq_zero_iff k p).mpr hpdiv
  have hpow : (W : ZMod p) ^ k = 1 := by
    obtain ⟨t, rfl⟩ := hpred
    rw [pow_mul, ZMod.pow_card_sub_one_eq_one hz, one_pow]
  have hs := geom_sum_mul (W : ZMod p) k
  rw [hpow, sub_self] at hs
  have he : ∑ j ∈ range k, (W : ZMod p) ^ j = 0 :=
    (mul_eq_zero.mp hs).resolve_right (sub_ne_zero.mpr ho)
  rw [he, mul_zero]

/-- The determinant of two affine forms, before choosing the repetition count. -/
def minor {α : Type*} (x : α → ℕ) (r : α → α) (i j : α) : ℤ :=
  (x i : ℤ) * x (r j) - (x j : ℤ) * x (r i)

lemma minor_ne_zero {α : Type*} {x : α → ℕ} {r : α → α}
    (hc : Pairwise (fun i j => (x i).Coprime (x j)))
    (hx : ∀ i, 1 < x i) (hr : ∀ i, r i ≠ i) {i j : α} (hij : i ≠ j) :
    minor x r i j ≠ 0 := by
  intro h
  have he : x i * x (r j) = x j * x (r i) := by
    have hh := sub_eq_zero.mp h
    exact_mod_cast hh
  have hd : x i ∣ x j * x (r i) := he ▸ dvd_mul_right (x i) (x (r j))
  have hone := ((hc hij).mul_right (hc (hr i).symm)).eq_one_of_dvd hd
  have := hx i
  omega

/-- Repetition can preserve pairwise coprimality, not merely the gcd of all roots. -/
theorem exists_coprime_period {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℕ) (r : α → α)
    (hc : Pairwise (fun i j => (x i).Coprime (x j)))
    (hx : ∀ i, 1 < x i) (hr : ∀ i, r i ≠ i) (W : ℕ) :
    ∃ K : ℕ, 0 < K ∧ ∀ k, K ∣ k →
      Pairwise (fun i j =>
        (x i + x (r i) * repeatWeight W k).Coprime
          (x j + x (r j) * repeatWeight W k)) := by
  let S : Finset ℕ := univ.biUnion (fun i : α =>
    univ.biUnion (fun j : α => (minor x r i j).natAbs.primeFactors))
  have hS : ∀ p ∈ S, p.Prime := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hi
    exact Nat.prime_of_mem_primeFactors hj
  obtain ⟨K, hK, hperiod⟩ := exists_repeat_period W S hS
  refine ⟨K, hK, ?_⟩
  intro k hk i j hij
  apply Nat.coprime_of_dvd
  intro p hp hpi hpj
  letI : Fact p.Prime := ⟨hp⟩
  have hai := (ZMod.natCast_eq_zero_iff _ p).mpr hpi
  have haj := (ZMod.natCast_eq_zero_iff _ p).mpr hpj
  simp only [Nat.cast_add, Nat.cast_mul] at hai haj
  have hdet : ((minor x r i j : ℤ) : ZMod p) = 0 := by
    simp only [minor, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    calc
      _ = ((x i : ZMod p) + x (r i) * repeatWeight W k) * x (r j) -
        ((x j : ZMod p) + x (r j) * repeatWeight W k) * x (r i) := by ring
      _ = 0 := by rw [hai, haj]; ring
  have hpdet : p ∣ (minor x r i j).natAbs :=
    Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hdet)
  have hmem : p ∈ S := by
    apply Finset.mem_biUnion.mpr
    refine ⟨i, mem_univ i, Finset.mem_biUnion.mpr ⟨j, mem_univ j, ?_⟩⟩
    exact hp.mem_primeFactors hpdet
      (Int.natAbs_eq_zero.not.mpr (minor_ne_zero hc hx hr hij))
  have hv : (repeatWeight W k : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ p).mpr (hperiod k hk p hmem)
  rw [hv, mul_zero, add_zero] at hai haj
  exact (Nat.Prime.not_coprime_iff_dvd.mpr
    ⟨p, hp, (ZMod.natCast_eq_zero_iff _ p).mp hai,
      (ZMod.natCast_eq_zero_iff _ p).mp haj⟩) (hc hij)

lemma coprime_injective {α : Type*} {x : α → ℕ}
    (hc : Pairwise (fun i j => (x i).Coprime (x j))) (hx : ∀ i, 1 < x i) :
    Function.Injective x := by
  intro i j hij
  by_contra hne
  have h := hc hne
  dsimp only at h
  rw [hij, Nat.coprime_self] at h
  have := hx j
  omega

/-- Arbitrarily long primitive block repetitions still have a square-sum collision. -/
theorem arbitrarily_long_coprime_repetitions {x : Fin 4 → ℕ} {W : ℕ}
    (hc : Pairwise (fun i j => (x i).Coprime (x j)))
    (hx : ∀ i, 1 < x i) (hW : ∀ i, x i < W)
    (hcol : x 0 ^ 2 + x 1 ^ 2 = x 2 ^ 2 + x 3 ^ 2) (n : ℕ) :
    ∃ k, n < k ∧
      Pairwise (fun i j => (repeatedValue x W k i).Coprime (repeatedValue x W k j)) ∧
      Function.Injective (repeatedValue x W k) ∧
      repeatedValue x W k 0 ^ 2 + repeatedValue x W k 1 ^ 2 =
        repeatedValue x W k 2 ^ 2 + repeatedValue x W k 3 ^ 2 := by
  have hr : ∀ i : Fin 4, i.rev ≠ i := by decide
  obtain ⟨K, hK, hperiod⟩ := exists_coprime_period x Fin.rev hc hx hr W
  refine ⟨K * (n + 1), ?_, hperiod _ (dvd_mul_right K _),
    repeated_injective (coprime_injective hc hx) hW _, repeated_collision hcol _ _⟩
  have : n + 1 ≤ K * (n + 1) := Nat.le_mul_of_pos_left _ hK
  omega

lemma repeated_not_sidon {x : Fin 4 → ℕ} {W : ℕ}
    (hx : Function.Injective x) (hW : ∀ i, x i < W)
    (hcol : x 0 ^ 2 + x 1 ^ 2 = x 2 ^ 2 + x 3 ^ 2) (k : ℕ) :
    ¬ IsSidon ((univ.image (fun i => repeatedValue x W k i ^ 2)) : Set ℕ) := by
  intro hs
  have h := hs (repeatedValue x W k 0 ^ 2) (by simp)
    (repeatedValue x W k 2 ^ 2) (by simp)
    (repeatedValue x W k 1 ^ 2) (by simp)
    (repeatedValue x W k 3 ^ 2) (by simp) (repeated_collision hcol W k)
  have hinj := (Nat.pow_left_injective (by decide : 2 ≠ 0)).comp
    (repeated_injective hx hW k)
  rcases h with h | h
  · have := hinj h.1
    exact (by decide : (0 : Fin 4) ≠ 2) this
  · have := hinj h.1
    exact (by decide : (0 : Fin 4) ≠ 3) this

#print axioms mix_collision
#print axioms aligned_statistics
#print axioms repeatedWord_value
#print axioms exists_repeat_period
#print axioms exists_coprime_period
#print axioms arbitrarily_long_coprime_repetitions
#print axioms repeated_not_sidon

end Erdos773.AlignedBlockCollision
