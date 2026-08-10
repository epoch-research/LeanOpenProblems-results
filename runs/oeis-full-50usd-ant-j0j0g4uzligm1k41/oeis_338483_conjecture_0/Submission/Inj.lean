import Mathlib
open Finset

noncomputable def tau (n : ℕ) : ℕ := (Nat.divisors n).card
noncomputable def g4 (x : ℕ) : ℕ := ((Finset.Ico 1 x).filter (fun k => tau k = 4)).card

/-- τ of a product of two distinct primes is 4. -/
theorem tau_two_primes {r q : ℕ} (hr : r.Prime) (hq : q.Prime) (hrq : r ≠ q) :
    tau (r * q) = 4 := by
  unfold tau
  rw [Nat.Coprime.card_divisors_mul (Nat.coprime_primes hr hq |>.mpr hrq),
      Nat.Prime.divisors hr, Nat.Prime.divisors hq]
  rw [Finset.card_pair (fun h => hr.ne_one h.symm), Finset.card_pair (fun h => hq.ne_one h.symm)]

/-- The family injection lower bound for g4. -/
theorem g4_ge_fam (p : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) :
    ∑ r ∈ S, ((Finset.Ico (r+1) p).filter (fun q => q.Prime ∧ r*q < p)).card ≤ g4 p := by
  set f : ℕ → Finset ℕ := fun r =>
    ((Finset.Ico (r+1) p).filter (fun q => q.Prime ∧ r*q < p)).image (fun q => r*q) with hf
  have hcard : ∀ r ∈ S, (f r).card
      = ((Finset.Ico (r+1) p).filter (fun q => q.Prime ∧ r*q < p)).card := by
    intro r hr
    rw [hf]
    apply Finset.card_image_of_injOn
    intro a _ b _ hab
    have hrpos : 0 < r := (hS r hr).pos
    exact Nat.eq_of_mul_eq_mul_left hrpos hab
  -- disjointness
  have hdisj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (f x) (f y) := by
    intro x hx y hy hxy
    rw [Finset.disjoint_left]
    intro n hnx hny
    rw [hf] at hnx hny
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ico] at hnx hny
    obtain ⟨qx, ⟨⟨hqx1, _⟩, hqxp, _⟩, rfl⟩ := hnx
    obtain ⟨qy, ⟨⟨hqy1, _⟩, hqyp, _⟩, hqe⟩ := hny
    -- hqe : y * qy = x * qx ; x<qx, y<qy, all prime; derive x = y
    have hxp := hS x hx; have hyp := hS y hy
    have hxlt : x < qx := hqx1
    have hylt : y < qy := hqy1
    have hdvd : x ∣ y * qy := ⟨qx, hqe⟩
    rcases (hxp.dvd_mul.mp hdvd) with h | h
    · exact hxy ((Nat.prime_dvd_prime_iff_eq hxp hyp).mp h)
    · have hxqy : x = qy := (Nat.prime_dvd_prime_iff_eq hxp hqyp).mp h
      rw [← hxqy] at hqe
      -- hqe : y * x = x * qx
      have hxpos : 0 < x := hxp.pos
      have hyqx : y = qx := by
        have h2 : x * y = x * qx := by rw [mul_comm x y]; exact hqe
        exact Nat.eq_of_mul_eq_mul_left hxpos h2
      omega
  have hbu : (S.biUnion f).card = ∑ r ∈ S, (f r).card := Finset.card_biUnion hdisj
  have hsub : S.biUnion f ⊆ (Finset.Ico 1 p).filter (fun k => tau k = 4) := by
    intro n hn
    rw [Finset.mem_biUnion] at hn
    obtain ⟨r, hrS, hnr⟩ := hn
    rw [hf] at hnr
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ico] at hnr
    obtain ⟨q, ⟨⟨hq1, _⟩, hqp, hqpr⟩, rfl⟩ := hnr
    have hrp := hS r hrS
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨?_, hqpr⟩, ?_⟩
    · have := hrp.pos; nlinarith [hqp.pos]
    · exact tau_two_primes hrp hqp (by omega)
  calc ∑ r ∈ S, ((Finset.Ico (r+1) p).filter (fun q => q.Prime ∧ r*q < p)).card
      = ∑ r ∈ S, (f r).card := by rw [Finset.sum_congr rfl hcard]
    _ = (S.biUnion f).card := hbu.symm
    _ ≤ ((Finset.Ico 1 p).filter (fun k => tau k = 4)).card := Finset.card_le_card hsub
    _ = g4 p := rfl
