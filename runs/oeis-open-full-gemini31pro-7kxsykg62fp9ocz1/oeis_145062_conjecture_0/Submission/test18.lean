import Mathlib

axiom sequence_s_int : ℤ → ℕ
noncomputable def seq (z: ℤ) : ℕ := sequence_s_int z

-- let us define sequence_s_int locally by shadowing it? No, lean does not allow that.
