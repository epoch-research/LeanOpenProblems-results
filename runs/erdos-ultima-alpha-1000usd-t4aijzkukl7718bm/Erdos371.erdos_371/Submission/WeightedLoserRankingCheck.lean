import FormalConjecturesUtil

/-!
A finite obstruction to a proposed prime-weighted loser-energy inequality
based only on max-under-multiplication. The weights are the original primes,
not their ranks. This changes the prime order and is NOT a counterexample to
Erdős 371 or to the same energy inequality for the natural prime order.
-/
namespace Erdos371.WeightedLoserRankingCheck
open Finset
set_option autoImplicit false

def rank (p : ℕ) : ℕ :=
  if p=11 then 1 else if p=2 then 2 else if p=23 then 3 else
  if p=3 then 4 else if p=31 then 5 else if p=41 then 6 else
  if p=37 then 7 else if p=19 then 8 else if p=5 then 9 else
  if p=29 then 10 else if p=7 then 11 else if p=17 then 12 else
  if p=13 then 13 else p+14

def decode (r : ℕ) : ℕ :=
  if r=0 then 1 else if r=1 then 11 else if r=2 then 2 else
  if r=3 then 23 else if r=4 then 3 else if r=5 then 31 else
  if r=6 then 41 else if r=7 then 37 else if r=8 then 19 else
  if r=9 then 5 else if r=10 then 29 else if r=11 then 7 else
  if r=12 then 17 else if r=13 then 13 else r-14

def label (n : ℕ) : ℕ := n.primeFactors.sup rank

def selectedPrime (n : ℕ) : ℕ := decode (label n)

lemma label_mul (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    label (a*b)=max (label a) (label b) := by
  simp only [label,Nat.primeFactors_mul ha hb,sup_union]

lemma rank_large (p : ℕ) (hp : 42 ≤ p) : rank p=p+14 := by
  simp only [rank,if_neg (show p ≠ 11 by omega),if_neg (show p ≠ 2 by omega),
    if_neg (show p ≠ 23 by omega),if_neg (show p ≠ 3 by omega),
    if_neg (show p ≠ 31 by omega),if_neg (show p ≠ 41 by omega),
    if_neg (show p ≠ 37 by omega),if_neg (show p ≠ 19 by omega),
    if_neg (show p ≠ 5 by omega),if_neg (show p ≠ 29 by omega),
    if_neg (show p ≠ 7 by omega),if_neg (show p ≠ 17 by omega),
    if_neg (show p ≠ 13 by omega)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rank_injective : Function.Injective rank := by
  have hs : Function.Injective (fun p : Fin 42 => rank p) := by decide +kernel
  have hb : ∀ p : Fin 42, rank p < 56 := by decide +kernel
  intro p q he
  by_cases hp : p < 42 <;> by_cases hq : q < 42
  · exact congrArg Fin.val (hs (a₁ := ⟨p,hp⟩) (a₂ := ⟨q,hq⟩) he)
  · have hh := hb ⟨p,hp⟩
    rw [rank_large q (by omega)] at he
    dsimp only at hh
    omega
  · have hh := hb ⟨q,hq⟩
    rw [rank_large p (by omega)] at he
    dsimp only at hh
    omega
  · rw [rank_large p (by omega),rank_large q (by omega)] at he
    omega

lemma decode_large (r : ℕ) (hr : 14 ≤ r) : decode r=r-14 := by
  simp only [decode,if_neg (show r ≠ 0 by omega),if_neg (show r ≠ 1 by omega),
    if_neg (show r ≠ 2 by omega),if_neg (show r ≠ 3 by omega),
    if_neg (show r ≠ 4 by omega),if_neg (show r ≠ 5 by omega),
    if_neg (show r ≠ 6 by omega),if_neg (show r ≠ 7 by omega),
    if_neg (show r ≠ 8 by omega),if_neg (show r ≠ 9 by omega),
    if_neg (show r ≠ 10 by omega),if_neg (show r ≠ 11 by omega),
    if_neg (show r ≠ 12 by omega),if_neg (show r ≠ 13 by omega)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma decode_rank (p : ℕ) : decode (rank p)=p := by
  by_cases hp : p < 42
  · have hh : ∀ p : Fin 42, decode (rank p)=p := by decide +kernel
    exact hh ⟨p,hp⟩
  · rw [rank_large p (by omega),decode_large (p+14) (by omega)]
    omega

/-- In particular the numerical weight attached to a ranked prime is that
prime itself, rather than its artificial rank. -/
lemma selectedPrime_of_prime (p : ℕ) (hp : p.Prime) : selectedPrime p=p := by
  simp only [selectedPrime,label,hp.primeFactors,sup_singleton,decode_rank]

/-- Indices n represent the positive consecutive pair (n+1,n+2). -/
def loser (n : ℕ) : ℕ :=
  if label (n+1) < label (n+2) then selectedPrime (n+1) else selectedPrime (n+2)

def sign (n : ℕ) : ℤ := if label (n+1) < label (n+2) then 1 else -1

def groupSum (p N : ℕ) : ℤ :=
  ∑ n ∈ range N, if loser n=p then sign n else 0

def energy (N : ℕ) : ℤ :=
  ∑ p ∈ insert 1 ((N+2).primesBelow), (p : ℤ)*(groupSum p N)^2

def diagonal (N : ℕ) : ℤ := ∑ n ∈ range N, (loser n : ℤ)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prefix_forty_values : energy 40=321 ∧ diagonal 40=319 := by
  decide +kernel

/-- A finite failure of the generic weighted-energy inequality. No claim
about the original numerical ordering of prime factors follows from it. -/
theorem weighted_loser_energy_exceeds_diagonal : diagonal 40 < energy 40 := by
  rw [prefix_forty_values.1,prefix_forty_values.2]
  norm_num

theorem not_weighted_loser_energy_le_diagonal : ¬ ∀ N, energy N ≤ diagonal N := by
  intro h
  exact (not_le_of_gt weighted_loser_energy_exceeds_diagonal) (h 40)

#print axioms rank_injective
#print axioms label_mul
#print axioms selectedPrime_of_prime
#print axioms prefix_forty_values
#print axioms not_weighted_loser_energy_le_diagonal
end Erdos371.WeightedLoserRankingCheck
