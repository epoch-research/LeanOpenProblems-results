import Submission.WallDataPackedChecker

/-! Small positive and negative tests for length, endpoint, label and sentinel handling. -/
namespace Erdos952.WallData

-- Zero edges means exactly one black vertex; its direction is immaterial.
example : checkPacked ⟨146, -149⟩ 0 [48] ⟨146, -149⟩ = true := by decide +kernel
example : checkPacked ⟨146, -149⟩ 0 [51] ⟨146, -149⟩ = true := by decide +kernel
example : checkPacked ⟨0, 0⟩ 0 [48] ⟨0, 0⟩ = false := by decide +kernel
example : checkPacked ⟨146, -149⟩ 0 [] ⟨146, -149⟩ = false := by decide +kernel

-- Codes [8,24] are the first edge of the supplied path.
example : checkPacked ⟨147, -149⟩ 1 [2568] ⟨146, -149⟩ = true := by decide +kernel
-- Splitting a word has no effect on the decoded path.
example : checkPacked ⟨147, -149⟩ 1 [48, 64] ⟨146, -149⟩ = true := by decide +kernel
-- A real outgoing direction cannot be silently ignored.
example : checkPacked ⟨147, -149⟩ 1 [2569] ⟨146, -149⟩ = false := by decide +kernel
-- Changing ONLY the last dummy direction leaves this one-edge path unchanged.
example : checkPacked ⟨147, -149⟩ 1 [2688] ⟨146, -149⟩ = true := by decide +kernel
-- But the final vertex's label is checked.
example : checkPacked ⟨147, -149⟩ 1 [1608] ⟨146, -149⟩ = false := by decide +kernel
-- Wrong lengths and endpoints are rejected.
example : checkPacked ⟨147, -149⟩ 0 [2568] ⟨146, -149⟩ = false := by decide +kernel
example : checkPacked ⟨147, -149⟩ 2 [2568] ⟨146, -149⟩ = false := by decide +kernel
example : checkPacked ⟨147, -148⟩ 1 [2568] ⟨146, -149⟩ = false := by decide +kernel
-- Missing/incorrect sentinels and trailing malformed words are rejected.
example : checkPacked ⟨146, -149⟩ 0 [8] ⟨146, -149⟩ = false := by decide +kernel
example : checkPacked ⟨146, -149⟩ 0 [88] ⟨146, -149⟩ = false := by decide +kernel
example : checkPacked ⟨147, -149⟩ 1 [2568, 1] ⟨146, -149⟩ = false := by decide +kernel

#print axioms labelCheck_sound
#print axioms move_norm
#print axioms BlackPath.append
#print axioms BlackPath.toRTC
#print axioms checkPacked_sound

end Erdos952.WallData
