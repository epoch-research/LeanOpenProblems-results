import re

with open('/workspace/leanproject/Submission/Complete.lean', 'r') as f:
    text = f.read()

text = text.replace(
    'have h_seq : eulerMascheroniSeq\' 600 = harmonic 600 - Real.log (600:ℝ) := by\n    dsimp [eulerMascheroniSeq\']\n    have : (600 : ℕ) ≠ 0 := by decide\n    simp [this]',
    'have h_seq : eulerMascheroniSeq\' 600 = harmonic 600 - Real.log (600:ℝ) := rfl'
)

text = text.replace(
    'have h_seq : eulerMascheroniSeq 296 = harmonic 296 - Real.log (297:ℝ) := by\n    change (harmonic 296 : ℝ) - Real.log (((296:ℕ):ℝ) + 1) = (harmonic 296 : ℝ) - Real.log (297:ℝ)\n    congr 1\n    norm_num',
    'have h_seq : eulerMascheroniSeq 296 = harmonic 296 - Real.log (297:ℝ) := by\n    change (harmonic 296 : ℝ) - Real.log (((296:ℕ):ℝ) + 1) = (harmonic 296 : ℝ) - Real.log (297:ℝ)\n    congr 1\n    norm_num'
)

text = text.replace(
    'have h_anti := exp_harmonic_div_n_anti k (by omega)\n    exact h_anti.le.trans ih',
    'have h_anti := exp_harmonic_div_n_anti k (by omega)\n    exact LE.le.trans h_anti.le ih'
)

text = text.replace(
    'apply exp_upper_bound_7 <;> norm_num',
    'exact exp_upper_bound_7 _ (by norm_num) (by norm_num)'
)
text = text.replace(
    'rw [exp_sub, exp_log] <;> norm_num',
    'rw [exp_sub, exp_log]; norm_num'
)

with open('/workspace/leanproject/Submission/Complete.lean', 'w') as f:
    f.write(text)

