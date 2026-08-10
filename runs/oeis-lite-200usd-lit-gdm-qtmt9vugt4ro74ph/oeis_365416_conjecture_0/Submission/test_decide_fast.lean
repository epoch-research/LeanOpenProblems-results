import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

lemma pow_three_zmod_7_fast (e f q : ℕ) (he : e % 6 < 6) (hf : f % 6 < 6) (h_parity_f : f % 6 % 2 = 1) (h_parity_e : e % 6 % 2 = 0) (h : (q : ZMod 7) ^ (f % 6) - (3 : ZMod 7) ^ (e % 6) = 2) (hq : (q : ZMod 7) = 2) : False := by
  have h_check : ∀ x < 6, ∀ y < 6, y % 2 = 1 → x % 2 = 0 → (2 : ZMod 7) ^ y - (3 : ZMod 7) ^ x = 2 → False := by decide
  rw [hq] at h
  exact h_check (e % 6) he (f % 6) hf h_parity_f h_parity_e h

