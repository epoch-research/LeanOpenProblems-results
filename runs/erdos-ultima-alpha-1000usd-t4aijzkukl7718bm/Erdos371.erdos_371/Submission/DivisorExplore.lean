import FormalConjecturesUtil

namespace Erdos371

noncomputable def subsetMinTerm (f : ℕ → ℝ) (t : Finset ℕ) : ℝ :=
  if ht : t.Nonempty then (-1 : ℝ) ^ t.card * f (t.min' ht) else 0

theorem sum_subsetMinTerm (s : Finset ℕ) (hs : s.Nonempty) (f : ℕ → ℝ) :
    ∑ t ∈ s.powerset, subsetMinTerm f t = -f (s.max' hs) := by
  let p := s.max' hs
  have hp : p ∈ s := s.max'_mem hs
  have hpnot : p ∉ s.erase p := Finset.notMem_erase p s
  conv_lhs => rw [← Finset.insert_erase hp, Finset.sum_powerset_insert hpnot,
    ← Finset.sum_add_distrib]
  have hterm (t : Finset ℕ) (ht : t ∈ (s.erase p).powerset) :
      subsetMinTerm f t + subsetMinTerm f (insert p t) =
        if t = ∅ then -f p else 0 := by
    have hts := Finset.mem_powerset.mp ht
    have hpt : p ∉ t := fun h => hpnot (hts h)
    by_cases hte : t.Nonempty
    · have hm : t.min' hte ≤ p :=
        s.le_max' _ (Finset.mem_of_mem_erase (hts (t.min'_mem hte)))
      simp only [subsetMinTerm, dif_pos hte, dif_pos (Finset.insert_nonempty p t),
        Finset.card_insert_of_notMem hpt, Finset.min'_insert p t hte,
        min_eq_right hm, pow_succ, if_neg hte.ne_empty]
      ring
    · have hte' : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hte
      subst t
      simp [subsetMinTerm]
  calc
    _ = ∑ t ∈ (s.erase p).powerset, if t = ∅ then -f p else 0 :=
      Finset.sum_congr rfl hterm
    _ = -f (s.max' hs) := by simp [p]

/-- Finite-set form of the largest/least-prime-factor duality. -/
theorem alladi_maxPrimeFac (n : ℕ) (hn : 1 < n) (f : ℕ → ℝ) :
    ∑ t ∈ n.primeFactors.powerset, subsetMinTerm f t = -f (Nat.maxPrimeFac n) := by
  have hp : Nat.maxPrimeFac n ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_maxPrimeFac_of_one_lt n hn, Nat.maxPrimeFac_dvd, by omega⟩
  have hne : n.primeFactors.Nonempty := ⟨_, hp⟩
  have hm : n.primeFactors.max' hne = Nat.maxPrimeFac n := by
    apply le_antisymm
    · obtain ⟨hprime, hdvd, hn0⟩ := Nat.mem_primeFactors.mp
        (n.primeFactors.max'_mem hne)
      exact Nat.le_maxPrimeFac hn0 hprime hdvd
    · exact n.primeFactors.le_max' _ hp
  simpa only [hm] using sum_subsetMinTerm n.primeFactors hne f

/-- Exact inclusion-exclusion expansion of the signed comparison. -/
theorem comparison_as_subset_sum (n : ℕ) (hn : 1 < n) :
    (if Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) then (1 : ℝ) else -1) =
      -∑ t ∈ (n * (n + 1)).primeFactors.powerset,
        subsetMinTerm (fun p => if p ∣ n + 1 then 1 else -1) t := by
  have hpn : ¬ Nat.maxPrimeFac n ∣ n + 1 := by
    intro hd
    exact (Nat.prime_maxPrimeFac_of_one_lt n hn).not_dvd_one
      ((Nat.dvd_add_iff_right Nat.maxPrimeFac_dvd).mpr hd)
  rw [alladi_maxPrimeFac (n * (n + 1)) (by nlinarith), neg_neg,
    Nat.maxPrimeFac_mul (by omega) (by omega)]
  by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1)
  · simp only [if_pos h, max_eq_right h.le, if_pos Nat.maxPrimeFac_dvd]
  · simp only [if_neg h, max_eq_left (le_of_not_gt h), if_neg hpn]

#print axioms sum_subsetMinTerm
#print axioms alladi_maxPrimeFac
#print axioms comparison_as_subset_sum

end Erdos371
