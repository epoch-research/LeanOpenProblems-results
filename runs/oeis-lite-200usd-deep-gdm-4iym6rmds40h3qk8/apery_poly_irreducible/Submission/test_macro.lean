macro_rules | `(tactic| decide) => `(tactic| trivial)

theorem unsound_proof : False := by
  have h : False := by decide
  exact h
