import Mathlib

lemma padicValNat_le_padicValNat_of_dvd (p x y : ℕ) (hp : p.Prime) (hx : x ≠ 0) (hy : y ≠ 0) (hdvd : x ∣ y) : padicValNat p x ≤ padicValNat p y := by
  obtain ⟨c, hc⟩ := hdvd
  have hc_nz : c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc
    exact hy hc
  rw [hc]
  have fact_p : Fact p.Prime := ⟨hp⟩
  rw [padicValNat.mul hx hc_nz]
  omega
