import FormalConjecturesUtil
/-! API probe. -/
example (P : Prop) (h : P) : P := by
  aesop (config := { maxRuleApplications := 30, maxRuleApplicationDepth := 4, maxSafePrefixRuleApplications := 10, enableSimp := false })
