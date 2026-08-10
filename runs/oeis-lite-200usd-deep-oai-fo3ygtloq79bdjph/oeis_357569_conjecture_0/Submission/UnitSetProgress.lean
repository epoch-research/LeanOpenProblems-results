import FormalConjectures.Util.ProblemImports

open scoped BigOperators
open Nat

def unitReps (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun i => Nat.Coprime i q)

lemma coprime_prime_pow_iff_not_dvd {p i k : ℕ} (hp : Nat.Prime p) (hk : 0 < k) :
    Nat.Coprime i (p ^ k) ↔ ¬ p ∣ i := by
  constructor
  · intro h hdiv
    have hpdvd : p ∣ p^k := dvd_pow_self p (Nat.ne_of_gt hk)
    have hpdvdg : p ∣ Nat.gcd i (p^k) := Nat.dvd_gcd hdiv hpdvd
    rw [h.gcd_eq_one] at hpdvdg
    exact hp.not_dvd_one hpdvdg
  · intro hnot
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr hnot

lemma prime_pow_one_lt {p r : ℕ} (hp : Nat.Prime p) (hr : 1 ≤ r) : 1 < p^r := by
  have hp2 : 2 ≤ p := hp.two_le
  exact one_lt_pow₀ (by omega) (Nat.ne_of_gt (by omega : 0 < r))

lemma unitReps_eq_Icc_filter_not_dvd (p r : ℕ) (hp : Nat.Prime p) (hr : 1 ≤ r) :
    unitReps (p^r) = (Finset.Icc 1 (p^r)).filter (fun i => ¬ p ∣ i) := by
  classical
  ext i
  simp only [unitReps, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · intro h
    rcases h with ⟨hi_lt, hcop⟩
    have hnot : ¬ p ∣ i := (coprime_prime_pow_iff_not_dvd hp (by omega : 0 < r)).mp hcop
    have hi_pos : 1 ≤ i := by
      by_contra hle
      have hi0 : i = 0 := by omega
      subst i
      have hq1 : 1 < p^r := prime_pow_one_lt hp hr
      have : ¬ Nat.Coprime 0 (p^r) := by
        intro hc
        rw [Nat.coprime_zero_left] at hc
        omega
      exact this hcop
    exact ⟨⟨hi_pos, le_of_lt hi_lt⟩, hnot⟩
  · intro h
    rcases h with ⟨⟨hi1, hi_le⟩, hnot⟩
    have hi_ne_q : i ≠ p^r := by
      intro hiq
      apply hnot
      rw [hiq]
      exact dvd_pow_self p (Nat.ne_of_gt (by omega : 0 < r))
    have hi_lt : i < p^r := lt_of_le_of_ne hi_le hi_ne_q
    have hcop : Nat.Coprime i (p^r) := (coprime_prime_pow_iff_not_dvd hp (by omega : 0 < r)).mpr hnot
    exact ⟨hi_lt, hcop⟩

lemma unitReps_q_sub_mem {q i : ℕ} (hq1 : 1 < q) (hi : i ∈ unitReps q) : q - i ∈ unitReps q := by
  classical
  rw [unitReps, Finset.mem_filter, Finset.mem_range] at hi ⊢
  rcases hi with ⟨hi_lt, hcop⟩
  have hi_pos : 0 < i := by
    by_contra hz
    have hi0 : i = 0 := by omega
    subst i
    simp at hcop
    omega
  have hsub_pos : 0 < q - i := Nat.sub_pos_of_lt hi_lt
  constructor
  · exact Nat.sub_lt (by omega : 0 < q) hi_pos
  · rw [Nat.coprime_comm]
    rw [Nat.coprime_comm] at hcop
    exact Nat.Coprime.symm ((Nat.coprime_self_sub_left (le_of_lt hi_lt)).mpr hcop.symm)

lemma unitReps_q_sub_involutive {q i : ℕ} (hi : i ∈ unitReps q) : q - (q - i) = i := by
  rw [unitReps, Finset.mem_filter, Finset.mem_range] at hi
  exact Nat.sub_sub_self (le_of_lt hi.1)
