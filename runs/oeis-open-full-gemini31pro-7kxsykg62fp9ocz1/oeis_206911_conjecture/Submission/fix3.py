with open('/workspace/leanproject/Submission/Complete.lean', 'r') as f:
    text = f.read()

text = text.replace(
    'have h_anti := exp_harmonic_div_n_anti k (by omega)\n    have h_cast : exp (harmonic (k + 1)) / (k + 1 : ℝ) ≤ exp (harmonic k) / (k : ℝ) := by\n      have hc : (k + 1 : ℝ) = (k : ℝ) + 1 := by push_cast; rfl\n      rwa [hc]\n    exact h_cast.trans ih',
    'have h_anti := exp_harmonic_div_n_anti k (by omega)\n    have hc : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; rfl\n    have h_cast : exp (harmonic (k + 1)) / ((k + 1 : ℕ) : ℝ) ≤ exp (harmonic k) / (k : ℝ) := by\n      rw [hc]\n      exact h_anti.le\n    exact h_cast.trans ih'
)

with open('/workspace/leanproject/Submission/Complete.lean', 'w') as f:
    f.write(text)
