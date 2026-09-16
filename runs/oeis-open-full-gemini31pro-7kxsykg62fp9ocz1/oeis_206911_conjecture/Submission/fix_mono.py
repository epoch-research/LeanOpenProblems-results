with open('/workspace/leanproject/Submission/Complete.lean', 'r') as f:
    text = f.read()

mono_proof = """
lemma harm_mono : Monotone harmonic := by
  intro a b hab
  induction' b, hab using Nat.le_induction with k hk ih
  · rfl
  · have h_k : harmonic k ≤ harmonic (k + 1) := by
      rw [harmonic_succ]
      push_cast
      have : 0 ≤ (1 : ℝ) / (k + 1 : ℝ) := by positivity
      linarith
    exact ih.trans h_k

lemma A206911_mono : Monotone A206911 := by
  intro a b hab
  rw [A206911_eq, A206911_eq]
  apply add_le_add hab
  have h1 : harmonic a ≤ harmonic b := harm_mono hab
  have h2 : exp (harmonic a) ≤ exp (harmonic b) := Real.exp_monotone h1
  have h3 : exp (harmonic a) - 1 ≤ exp (harmonic b) - 1 := by linarith
  have ha_nonneg : (0 : ℝ) ≤ exp (harmonic a) - 1 := by
    have : 1 ≤ exp (harmonic a) := by
      have : exp 0 ≤ exp (harmonic a) := Real.exp_monotone (harm_nonneg a)
      rwa [Real.exp_zero] at this
    linarith
  have hb_nonneg : (0 : ℝ) ≤ exp (harmonic b) - 1 := by
    have : 1 ≤ exp (harmonic b) := by
      have : exp 0 ≤ exp (harmonic b) := Real.exp_monotone (harm_nonneg b)
      rwa [Real.exp_zero] at this
    linarith
  have h4 : ⌊exp (harmonic a) - 1⌋ ≤ ⌊exp (harmonic b) - 1⌋ := Int.floor_le_floor _ _ h3
  exact Int.toNat_le_toNat h4

"""

text = text.replace(
    'lemma sum_diff_eq',
    mono_proof + 'lemma sum_diff_eq'
)

text = text.replace(
    'have h1 : A206911 1 ≤ A206911 (N + 1) := by\n      -- we can just prove A206911 is monotone\n      sorry\n    have h2 : A206911 (N + 1) ≤ A206911 (N + 1 + 1) := by sorry',
    'have h1 : A206911 1 ≤ A206911 (N + 1) := A206911_mono (Nat.le_add_left 1 N)\n    have h2 : A206911 (N + 1) ≤ A206911 (N + 1 + 1) := A206911_mono (Nat.le_succ _)'
)

with open('/workspace/leanproject/Submission/Complete.lean', 'w') as f:
    f.write(text)
