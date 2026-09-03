import FormalConjecturesUtil

/-! An inclusion–exclusion identity relevant to largest prime factors. -/

namespace Erdos371Exploration


/-- The Möbius-weighted contribution of a finite set, tagged at its least element. -/
def minWeight (f : ℕ → ℤ) (s : Finset ℕ) : ℤ :=
  if hs : s.Nonempty then (-1) ^ s.card * f (s.min' hs) else 0

lemma alladi_insert (f : ℕ → ℤ) (s : Finset ℕ) (a : ℕ)
    (ha : ∀ b ∈ s, b < a) :
    ∑ t ∈ (insert a s).powerset, minWeight f t = -f a := by
  classical
  have han : a ∉ s := fun h => (ha a h).false
  rw [Finset.sum_powerset_insert han, ← Finset.sum_add_distrib]
  have hpair (t : Finset ℕ) (ht : t ∈ s.powerset) :
      minWeight f t + minWeight f (insert a t) = if t = ∅ then -f a else 0 := by
    have hts : t ⊆ s := Finset.mem_powerset.mp ht
    have hat : a ∉ t := fun h => han (hts h)
    by_cases hne : t.Nonempty
    · have hmin : t.min' hne < a := ha _ (hts (t.min'_mem hne))
      simp [minWeight, hne, Finset.Nonempty.ne_empty hne, Finset.card_insert_of_notMem hat,
        Finset.min'_insert, min_eq_right hmin.le, pow_succ]
    · have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst t
      simp [minWeight]
  simp_rw [Finset.sum_congr rfl hpair]
  simp

lemma alladi_primeFactors (f : ℕ → ℤ) {n : ℕ} (hn : 1 < n) :
    ∑ t ∈ n.primeFactors.powerset, minWeight f t = -f (Nat.maxPrimeFac n) := by
  have hp : Nat.maxPrimeFac n ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨Nat.prime_maxPrimeFac_of_one_lt n hn, Nat.maxPrimeFac_dvd, by omega⟩
  have h := alladi_insert f (n.primeFactors.erase (Nat.maxPrimeFac n)) (Nat.maxPrimeFac n)
    (by
      intro b hb
      obtain ⟨hbne, hbmem⟩ := Finset.mem_erase.mp hb
      obtain ⟨hbp, hbd, hn0⟩ := Nat.mem_primeFactors.mp hbmem
      have hle := Nat.le_maxPrimeFac hn0 hbp hbd
      omega)
  rwa [Finset.insert_erase hp] at h

/-- Tag a prime according to which member of the consecutive pair it divides. -/
def primeTag (n p : ℕ) : ℤ := if p ∣ n then -1 else 1

lemma primeTag_max_product {n : ℕ} (hn : 0 < n) :
    primeTag n (Nat.maxPrimeFac (n * (n + 1))) =
      if Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) then 1 else -1 := by
  rw [Nat.maxPrimeFac_mul hn.ne' (by omega)]
  by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1)
  · have hnd : ¬Nat.maxPrimeFac (n + 1) ∣ n := by
      intro hd
      have hle := Nat.le_maxPrimeFac hn.ne'
        (Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)) hd
      omega
    simp [primeTag, max_eq_right h.le, hnd, h]
  · simp [primeTag, max_eq_left (Nat.le_of_not_gt h), Nat.maxPrimeFac_dvd, h]

/-- An exact inclusion–exclusion expansion of the signed comparison. -/
lemma comparison_eq_alladi_sum {n : ℕ} (hn : 0 < n) :
    (if Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) then (1 : ℤ) else -1) =
      -∑ t ∈ (n * (n + 1)).primeFactors.powerset, minWeight (primeTag n) t := by
  rw [alladi_primeFactors (primeTag n) (by nlinarith : 1 < n * (n + 1)), neg_neg]
  exact (primeTag_max_product hn).symm

end Erdos371Exploration
