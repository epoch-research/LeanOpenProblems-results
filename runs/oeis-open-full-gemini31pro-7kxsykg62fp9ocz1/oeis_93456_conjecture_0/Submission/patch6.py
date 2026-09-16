with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    text = f.read()

# Insert the lemma before `theorem oeis_93456_conjecture_0.disproof`
lemma_text = """
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

theorem oeis_93456_conjecture_0.disproof"""

text = text.replace("theorem oeis_93456_conjecture_0.disproof", lemma_text)

# Also fix the end
old_end = """    have : padicValNat p (a (n - 1)) ≤ padicValNat p (a n) := padicValNat_le_padicValNat_of_dvd h_a_n_ne_zero hdvd
    omega
  
  refine ⟨Hn_gt1, H_not_dvd⟩"""
  
new_end = """    have h_a_n_minus_1_ne_zero : a (n - 1) ≠ 0 := by
      intro h
      have H_val : padicValNat p (a (n - 1)) = 0 := by rw [h, padicValNat_zero]
      omega
    have : padicValNat p (a (n - 1)) ≤ padicValNat p (a n) := padicValNat_le_padicValNat_of_dvd p (a (n - 1)) (a n) hp_prime h_a_n_minus_1_ne_zero h_a_n_ne_zero hdvd
    omega
  
  refine ⟨Hn_gtB, ⟨Hn_gt1, H_not_dvd⟩⟩"""

text = text.replace(old_end, new_end)

with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
    f.write(text)
