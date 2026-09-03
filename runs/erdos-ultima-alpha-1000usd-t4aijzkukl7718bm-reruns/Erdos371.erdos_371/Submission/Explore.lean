import FormalConjecturesUtil

namespace Erdos371Exploration

lemma consecutive_maxPrimeFac_ne (n : ℕ) :
    Nat.maxPrimeFac (n + 1) ≠ Nat.maxPrimeFac n := by
  rcases n with _ | _ | n
  · simp
  · decide +kernel
  · intro h
    have hp := Nat.prime_maxPrimeFac_of_one_lt (n + 2) (by omega)
    have hd : Nat.maxPrimeFac (n + 2) ∣ n + 2 + 1 := by
      rw [← h]
      exact Nat.maxPrimeFac_dvd
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right Nat.maxPrimeFac_dvd).2 hd)

lemma decrease_set_eq_compl :
    {n : ℕ | Nat.maxPrimeFac (n + 1) < Nat.maxPrimeFac n} =
      {n : ℕ | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}ᶜ := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
  have h := consecutive_maxPrimeFac_ne n
  omega

lemma increase_before_prime {p : ℕ} (hp : p.Prime) :
    Nat.maxPrimeFac ((p - 1) + 1) > Nat.maxPrimeFac (p - 1) := by
  rw [Nat.sub_add_cancel hp.one_lt.le, hp.maxPrimeFac_eq_self]
  exact lt_of_le_of_lt Nat.maxPrimeFac_le (Nat.sub_lt hp.pos (by decide))

lemma decrease_after_odd_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    Nat.maxPrimeFac (p + 1) < Nat.maxPrimeFac p := by
  have hodd := hp.odd_of_ne_two h2
  have heven : Even (p + 1) := hodd.add_odd odd_one
  have hnprime : ¬(p + 1).Prime := by
    intro h
    have h' := h.even_iff.mp heven
    have hp2 := hp.two_le
    omega
  have hne : Nat.maxPrimeFac (p + 1) ≠ p + 1 := by
    simp only [ne_eq, Nat.maxPrimeFac_eq_self_iff, hnprime, or_false]
    have hp2 := hp.two_le
    omega
  have hle : Nat.maxPrimeFac (p + 1) ≤ p := by
    have := Nat.maxPrimeFac_le (n := p + 1)
    omega
  have hdiff := consecutive_maxPrimeFac_ne p
  rw [hp.maxPrimeFac_eq_self] at hdiff ⊢
  omega

lemma increase_unbounded (N : ℕ) :
    ∃ n ≥ N, Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 1)
  exact ⟨p - 1, by omega, increase_before_prime hp⟩

lemma decrease_unbounded (N : ℕ) :
    ∃ n ≥ N, Nat.maxPrimeFac (n + 1) < Nat.maxPrimeFac n := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 3)
  exact ⟨p, by omega, decrease_after_odd_prime hp (by omega)⟩

end Erdos371Exploration

open Filter
open scoped Topology

lemma partialDensity_compl (S : Set ℕ) {n : ℕ} (hn : n ≠ 0) :
    Sᶜ.partialDensity Set.univ n = 1 - S.partialDensity Set.univ n := by
  have hc : (S ∩ Set.Iio n).ncard + (Sᶜ ∩ Set.Iio n).ncard = n := by
    simpa [Set.diff_eq, Set.inter_comm] using
      Set.ncard_inter_add_ncard_diff_eq_ncard (Set.Iio n) S
  have hr : ((S ∩ Set.Iio n).ncard : ℝ) +
      ((Sᶜ ∩ Set.Iio n).ncard : ℝ) = n := by exact_mod_cast hc
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  apply (eq_sub_iff_add_eq).mpr
  rw [← add_div, add_comm, hr, div_self hn']

lemma hasDensity_compl {S : Set ℕ} {d : ℝ} (h : S.HasDensity d) :
    Sᶜ.HasDensity (1 - d) := by
  apply Tendsto.congr' _ (tendsto_const_nhds.sub h)
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (partialDensity_compl S (Nat.ne_of_gt hn)).symm

