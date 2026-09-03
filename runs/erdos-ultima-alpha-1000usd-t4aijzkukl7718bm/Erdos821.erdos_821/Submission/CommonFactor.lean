import Submission.Valuation

/-!
# Removing a common divisor from a finite totient fiber

This reduction identifies a possible amplification input, but does not prove
that sufficiently large common divisors occur in the families needed for
Erdős 821. It is not a proof or disproof of that conjecture.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

/-- Pairwise noncoprimality inside one fiber need not give a common prime. -/
lemma common_factor_obstruction :
    totient 21 = 12 ∧ totient 28 = 12 ∧ totient 36 = 12 ∧
      ¬Nat.Coprime 21 28 ∧ ¬Nat.Coprime 21 36 ∧ ¬Nat.Coprime 28 36 ∧
      Nat.gcd (Nat.gcd 21 28) 36 = 1 := by
  decide

lemma totient_div_of_common_factor_gcd {m n d c : ℕ} (hd : 0 < d) (hc : 0 < c)
    (hdm : d ∣ m) (hphi : totient m = n) (hgcd : Nat.gcd d (m / d) = c) :
    totient (m / d) = (totient c * n) / (totient d * c) := by
  have h := Nat.totient_gcd_mul_totient_mul d (m / d)
  rw [hgcd, Nat.mul_div_cancel' hdm, hphi] at h
  have hden : 0 < totient d * c := Nat.mul_pos (Nat.totient_pos.mpr hd) hc
  calc
    totient (m / d) = (totient (m / d) * (totient d * c)) / (totient d * c) :=
      (Nat.mul_div_cancel _ hden).symm
    _ = _ := by
      congr 1
      calc
        totient (m / d) * (totient d * c) = totient d * totient (m / d) * c := by ring
        _ = _ := h.symm

/-- If the overlap with the common factor is fixed, division maps injectively
into one smaller totient fiber. -/
lemma card_totient_fiber_le_g_div_of_fixed_gcd (S : Finset ℕ) (n d c : ℕ)
    (hd : 0 < d) (hc : 0 < c)
    (hS : ∀ m ∈ S, totient m = n ∧ d ∣ m ∧ Nat.gcd d (m / d) = c) :
    S.card ≤ g ((totient c * n) / (totient d * c)) := by
  have hinj : Set.InjOn (fun m : ℕ => m / d) (S : Set ℕ) := by
    intro a ha b hb hab
    change a ∈ S at ha
    change b ∈ S at hb
    change a / d = b / d at hab
    rw [← Nat.mul_div_cancel' (hS a ha).2.1,
      ← Nat.mul_div_cancel' (hS b hb).2.1, hab]
  have hsub : (S.image (fun m => m / d) : Set ℕ) ⊆
      {a : ℕ | totient a = (totient c * n) / (totient d * c)} := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
    exact totient_div_of_common_factor_gcd hd hc (hS m hm).2.1 (hS m hm).1 (hS m hm).2.2
  have hcard := Set.ncard_le_ncard hsub (finite_totient_fiber _)
  simpa only [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, g] using hcard

lemma card_totient_fiber_le_g_div_of_common_coprime_factor (S : Finset ℕ) (n d : ℕ)
    (hd : 0 < d)
    (hS : ∀ m ∈ S, totient m = n ∧ d ∣ m ∧ Nat.Coprime d (m / d)) :
    S.card ≤ g (n / totient d) := by
  simpa only [Nat.totient_one, one_mul, mul_one] using
    card_totient_fiber_le_g_div_of_fixed_gcd S n d 1 hd (by decide)
      (fun m hm => ⟨(hS m hm).1, (hS m hm).2.1, (hS m hm).2.2.gcd_eq_one⟩)

lemma common_factor_reduced_output_le (n d c : ℕ) (hd : 0 < d) (hc : 0 < c) :
    (totient c * n) / (totient d * c) ≤ n / totient d := by
  apply (Nat.le_div_iff_mul_le (Nat.totient_pos.mpr hd)).mpr
  apply Nat.le_of_mul_le_mul_right (c := c) _ hc
  calc
    ((totient c * n) / (totient d * c) * totient d) * c =
        ((totient c * n) / (totient d * c)) * (totient d * c) := by ring
    _ ≤ totient c * n := Nat.div_mul_le_self _ _
    _ ≤ c * n := Nat.mul_le_mul_right n (Nat.totient_le c)
    _ = n * c := Nat.mul_comm _ _

/-- A common divisor can be removed at the cost of at most its divisor count
in multiplicity. No coprimality assumption on the quotients is needed. -/
lemma exists_reduced_totient_fiber_of_common_factor (S : Finset ℕ) (n d : ℕ)
    (hd : 0 < d) (hS : ∀ m ∈ S, totient m = n ∧ d ∣ m) :
    ∃ n' : ℕ, n' ≤ n / totient d ∧ S.card ≤ d.divisors.card * g n' := by
  let f : ℕ → ℕ := fun c => (totient c * n) / (totient d * c)
  have hne : d.divisors.Nonempty := ⟨1, Nat.mem_divisors.mpr ⟨one_dvd d, hd.ne'⟩⟩
  obtain ⟨c, hcd, hmax⟩ := Finset.exists_max_image d.divisors (fun c => g (f c)) hne
  refine ⟨f c, common_factor_reduced_output_le n d c hd (Nat.pos_of_mem_divisors hcd), ?_⟩
  have hmaps : Set.MapsTo (fun m : ℕ => Nat.gcd d (m / d)) (S : Set ℕ) (d.divisors : Set ℕ) := by
    intro m _hm
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, hd.ne'⟩
  calc
    S.card = ∑ c ∈ d.divisors, (S.filter (fun m => Nat.gcd d (m / d) = c)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ c ∈ d.divisors, g (f c) := by
      apply Finset.sum_le_sum
      intro c hc
      apply card_totient_fiber_le_g_div_of_fixed_gcd _ n d c hd (Nat.pos_of_mem_divisors hc)
      intro m hm
      obtain ⟨hmS, hmc⟩ := Finset.mem_filter.mp hm
      exact ⟨(hS m hmS).1, (hS m hmS).2, hmc⟩
    _ ≤ ∑ _c ∈ d.divisors, g (f c) := Finset.sum_le_sum hmax
    _ = _ := by simp

#print axioms common_factor_obstruction
#print axioms card_totient_fiber_le_g_div_of_fixed_gcd
#print axioms card_totient_fiber_le_g_div_of_common_coprime_factor
#print axioms exists_reduced_totient_fiber_of_common_factor

end Erdos821
