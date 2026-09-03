import FormalConjecturesUtil

/-! A finite cardinality bound for positive roots supported on a fixed prime set.
This bounds a proposed carrier, not the unrestricted square-Sidon maximum. -/
namespace Erdos773.PrimeSupportCardinality
open Finset
noncomputable section
set_option maxHeartbeats 1000000

def quotientPart (P : Finset ℕ) (k n : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ (n.factorization p / k)

def remainderPart (P : Finset ℕ) (k n : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ (n.factorization p % k)

lemma prod_factorization (P : Finset ℕ) {n : ℕ} (hn : n ≠ 0)
    (hP : n.primeFactors ⊆ P) : (∏ p ∈ P, p ^ n.factorization p) = n := by
  calc
    _ = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
      symm
      apply Finset.prod_subset hP
      intro p hp hpn
      have hz : n.factorization p = 0 := by
        apply Finsupp.notMem_support_iff.mp
        simpa only [Nat.support_factorization] using hpn
      simp [hz]
    _ = n := Nat.factorization_prod_pow_eq_self hn

lemma decomposition (P : Finset ℕ) (k : ℕ) {n : ℕ} (hn : n ≠ 0)
    (hP : n.primeFactors ⊆ P) :
    quotientPart P k n ^ k * remainderPart P k n = n := by
  rw [quotientPart, remainderPart, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  calc
    _ = ∏ p ∈ P, p ^ n.factorization p := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_mul, ← pow_add]
      congr 1
      simpa [Nat.mul_comm] using Nat.div_add_mod (n.factorization p) k
    _ = n := prod_factorization P hn hP

lemma quotientPart_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (k n : ℕ) :
    0 < quotientPart P k n := by
  exact Finset.prod_pos fun p hp => pow_pos (hP p hp).pos _

lemma remainderPart_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (k n : ℕ) :
    0 < remainderPart P k n := by
  exact Finset.prod_pos fun p hp => pow_pos (hP p hp).pos _

lemma quotientPart_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {k H n : ℕ} (hk : 0 < k) (hn : n ≠ 0) (hnH : n ≤ H^k)
    (hs : n.primeFactors ⊆ P) : quotientPart P k n ≤ H := by
  apply (Nat.pow_le_pow_iff_left hk.ne').mp
  calc
    quotientPart P k n ^ k ≤ quotientPart P k n ^ k * remainderPart P k n :=
      Nat.le_mul_of_pos_right _ (remainderPart_pos P hP k n)
    _ = n := decomposition P k hn hs
    _ ≤ H^k := hnH

def residues (P : Finset ℕ) (k : ℕ) (hk : 0 < k) (n : ℕ) : P → Fin k :=
  fun p => ⟨n.factorization p.val % k, Nat.mod_lt _ hk⟩

lemma remainderPart_eq_of_residues_eq (P : Finset ℕ) (k : ℕ) (hk : 0 < k)
    {m n : ℕ} (h : residues P k hk m = residues P k hk n) :
    remainderPart P k m = remainderPart P k n := by
  apply Finset.prod_congr rfl
  intro p hp
  have hh := congrArg Fin.val (congrFun h ⟨p,hp⟩)
  exact congrArg (fun e : ℕ => p^e) hh

/-- Every integer with prime support in P has a unique quotient/remainder
encoding, whose remainder component has only k^|P| possibilities. -/
lemma encoding_injective (P : Finset ℕ) (k : ℕ) (hk : 0 < k)
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmP : m.primeFactors ⊆ P) (hnP : n.primeFactors ⊆ P)
    (h : (quotientPart P k m, residues P k hk m) =
      (quotientPart P k n, residues P k hk n)) : m = n := by
  have hq : quotientPart P k m = quotientPart P k n := congrArg Prod.fst h
  have hr := remainderPart_eq_of_residues_eq P k hk (congrArg Prod.snd h)
  rw [← decomposition P k hm hmP, ← decomposition P k hn hnP, hq, hr]

/-- At height H^k, a carrier on r specified primes has at most k^r H members. -/
theorem card_le (P A : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {k H : ℕ} (hk : 0 < k)
    (hA : ∀ n ∈ A, 0 < n ∧ n ≤ H^k ∧ n.primeFactors ⊆ P) :
    A.card ≤ k^P.card * H := by
  let f : ℕ → ℕ × (P → Fin k) := fun n =>
    (quotientPart P k n, residues P k hk n)
  let T : Finset (ℕ × (P → Fin k)) := Icc 1 H ×ˢ univ
  have hf : Set.MapsTo f (A : Set ℕ) (T : Set (ℕ × (P → Fin k))) := by
    intro n hn
    obtain ⟨hn0,hnH,hnP⟩ := hA n hn
    change f n ∈ Icc 1 H ×ˢ (univ : Finset (P → Fin k))
    apply mem_product.mpr
    dsimp [f]
    exact ⟨mem_Icc.mpr
      ⟨quotientPart_pos P hP k n, quotientPart_le P hP hk hn0.ne' hnH hnP⟩,
      mem_univ _⟩
  have hinj : Set.InjOn f (A : Set ℕ) := by
    intro m hm n hn h
    exact encoding_injective P k hk (hA m hm).1.ne' (hA n hn).1.ne'
      (hA m hm).2.2 (hA n hn).2.2 h
  have hc := Finset.card_le_card_of_injOn (t := T) f hf hinj
  simpa [T, Finset.card_product, Fintype.card_fun, Nat.card_Icc, mul_comm] using hc

/-- In the range where the exponential rank cost is at most H, the entire
carrier has at most H² roots, independently of the much larger height H^k. -/
theorem card_le_sq (P A : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {k H : ℕ} (hk : 0 < k) (hrank : k^P.card ≤ H)
    (hA : ∀ n ∈ A, 0 < n ∧ n ≤ H^k ∧ n.primeFactors ⊆ P) :
    A.card ≤ H^2 := by
  calc
    A.card ≤ k^P.card * H := card_le P A hP hk hA
    _ ≤ H * H := Nat.mul_le_mul_right H hrank
    _ = H^2 := by ring

/-- The corresponding logarithmic tradeoff, with no asymptotic assumptions. -/
theorem log_card_bound (P A : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {k H : ℕ} (hk : 0 < k) (hH : 0 < H) (hcard : 0 < A.card)
    (hA : ∀ n ∈ A, 0 < n ∧ n ≤ H^k ∧ n.primeFactors ⊆ P) :
    Real.log (A.card : ℝ) ≤ (P.card : ℝ)*Real.log k + Real.log H := by
  have hc : (A.card : ℝ) ≤ (k : ℝ)^P.card * H := by
    exact_mod_cast card_le P A hP hk hA
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    Real.log (A.card : ℝ) ≤ Real.log ((k : ℝ)^P.card * H) :=
      Real.log_le_log (by exact_mod_cast hcard) hc
    _ = (P.card : ℝ)*Real.log k + Real.log H := by
      rw [Real.log_mul (pow_pos hkr _).ne' hHr.ne', Real.log_pow]

#print axioms decomposition
#print axioms encoding_injective
#print axioms card_le
#print axioms card_le_sq
#print axioms log_card_bound
end
end Erdos773.PrimeSupportCardinality
