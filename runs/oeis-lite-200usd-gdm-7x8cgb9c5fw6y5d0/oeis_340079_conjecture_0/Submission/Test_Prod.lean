import FormalConjectures.Util.ProblemImports

open List

lemma prime_dvd_prod_mem {p : ℕ} (hp : Nat.Prime p) {l : List ℕ} (hl : ∀ x ∈ l, Nat.Prime x) (h_dvd : p ∣ l.prod) : p ∈ l := by
  induction l with
  | nil =>
    simp at h_dvd
    have : p ≤ 1 := Nat.le_of_dvd (by omega) h_dvd
    have : p ≥ 2 := Nat.Prime.two_le hp
    omega
  | cons b l ih =>
    simp [prod_cons] at h_dvd
    rcases (Nat.Prime.dvd_mul hp).mp h_dvd with hp_dvd_b | hp_dvd_l
    · have hb_prime : Nat.Prime b := hl b (by simp)
      have hp_eq_b : p = b := Nat.Prime.eq_one_or_self_of_dvd hb_prime hp_dvd_b |>.resolve_left hp.ne_one
      subst hp_eq_b
      simp
    · have hl_prime : ∀ x ∈ l, Nat.Prime x := fun x hx => hl x (by simp [hx])
      have hp_in : p ∈ l := ih hl_prime hp_dvd_l
      simp [hp_in]
