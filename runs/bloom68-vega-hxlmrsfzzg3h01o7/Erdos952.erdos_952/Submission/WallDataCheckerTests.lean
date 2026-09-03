import Submission.WallDataListChecker
namespace Erdos952.WallData
set_option maxRecDepth 100000
-- Empty input, wrong length, endpoint mismatch, and bad final label are rejected.
example : checkCodes ⟨0, 0⟩ 0 [] ⟨0, 0⟩ = false := by decide +kernel
example : checkCodes ⟨180, -139⟩ 63 [8, 24, 4, 13, 9, 21, 4, 8, 16, 24, 20, 4, 9, 12, 4, 0, 9, 5, 12, 8, 5, 1, 8, 13, 4, 24, 11, 16, 4, 8, 25, 5, 0, 32, 4, 1, 8, 4, 24, 13, 5, 0, 29, 9, 5, 12, 8, 1, 21, 8, 12, 27, 7, 16, 0, 8, 4, 3, 11, 7, 2, 11, 15, 7, 28] ⟨146, -149⟩ = false := by decide +kernel
example : checkCodes ⟨181, -139⟩ 64 [8, 24, 4, 13, 9, 21, 4, 8, 16, 24, 20, 4, 9, 12, 4, 0, 9, 5, 12, 8, 5, 1, 8, 13, 4, 24, 11, 16, 4, 8, 25, 5, 0, 32, 4, 1, 8, 4, 24, 13, 5, 0, 29, 9, 5, 12, 8, 1, 21, 8, 12, 27, 7, 16, 0, 8, 4, 3, 11, 7, 2, 11, 15, 7, 28] ⟨146, -149⟩ = false := by decide +kernel
example : checkCodes ⟨180, -139⟩ 64 [8, 24, 4, 13, 9, 21, 4, 8, 16, 24, 20, 4, 9, 12, 4, 0, 9, 5, 12, 8, 5, 1, 8, 13, 4, 24, 11, 16, 4, 8, 25, 5, 0, 32, 4, 1, 8, 4, 24, 13, 5, 0, 29, 9, 5, 12, 8, 1, 21, 8, 12, 27, 7, 16, 0, 8, 4, 3, 11, 7, 2, 11, 15, 7, 0] ⟨146, -149⟩ = false := by decide +kernel
-- Changing ONLY the final dummy direction leaves acceptance unchanged.
example : checkCodes ⟨180, -139⟩ 64 [8, 24, 4, 13, 9, 21, 4, 8, 16, 24, 20, 4, 9, 12, 4, 0, 9, 5, 12, 8, 5, 1, 8, 13, 4, 24, 11, 16, 4, 8, 25, 5, 0, 32, 4, 1, 8, 4, 24, 13, 5, 0, 29, 9, 5, 12, 8, 1, 21, 8, 12, 27, 7, 16, 0, 8, 4, 3, 11, 7, 2, 11, 15, 7, 31] ⟨146, -149⟩ = true := by decide +kernel
-- The next vertex's incorrect label is rejected even on the first edge.
example : checkCodes ⟨147, -149⟩ 1 [8, 0] ⟨146, -149⟩ = false := by decide +kernel
#print axioms checkCodes_sound
end Erdos952.WallData
