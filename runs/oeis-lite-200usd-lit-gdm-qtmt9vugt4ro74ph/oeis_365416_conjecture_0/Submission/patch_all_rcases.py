with open("/workspace/leanproject/Submission/generate_short_spec.py", "r") as f:
    code = f.read()

# 1. Replace the parent rcases lines
code = code.replace(
    "rcases hp_cases with rfl | rfl | rfl | rfl | hp_ge11",
    "rcases hp_cases with hp2 | hp3 | hp5 | hp7 | hp_ge11"
)
code = code.replace(
    "rcases hq_cases with rfl | rfl | rfl | rfl | hq_ge11",
    "rcases hq_cases with hq2 | hq3 | hq5 | hq7 | hq_ge11"
)

# 2. Add subst hp3, subst hp5, subst hp7
code = code.replace(
    "    · -- p = 3",
    "    · subst hp3"
)
code = code.replace(
    "    · -- p = 5",
    "    · subst hp5"
)
code = code.replace(
    "    · -- p = 7",
    "    · subst hp7"
)

# 3. Fix q_ne_p_of_diff_two uses (no longer rfl, now hq3/hq5/hq7)
code = code.replace(
    "exact (q_ne_p_of_diff_two 3 3 e f hp he h rfl).elim",
    "exact (q_ne_p_of_diff_two 3 3 e f hp he h hq3).elim"
)
code = code.replace(
    "exact (q_ne_p_of_diff_two 5 5 e f hp he h rfl).elim",
    "exact (q_ne_p_of_diff_two 5 5 e f hp he h hq5).elim"
)
code = code.replace(
    "exact (q_ne_p_of_diff_two 7 7 e f hp he h rfl).elim",
    "exact (q_ne_p_of_diff_two 7 7 e f hp he h hq7).elim"
)

# 4. Insert subst hq5 and subst hq7 in p = 3 subbranches
code = code.replace(
    "      · exact pillai_diff_two_3_5 e f (by omega) hf h",
    "      · subst hq5\n        exact pillai_diff_two_3_5 e f (by omega) hf h"
)
code = code.replace(
    "      · exact pillai_diff_two_3_7 e f (by omega) h",
    "      · subst hq7\n        exact pillai_diff_two_3_7 e f (by omega) h"
)

# 5. Insert subst hq3 and subst hq7 in p = 5 subbranches
code = code.replace(
    "      · have he_eq2 : e = 2 := (pillai_diff_two_5_3 e f he hf h).1\n        omega",
    "      · subst hq3\n        have he_eq2 : e = 2 := (pillai_diff_two_5_3 e f he hf h).1\n        omega"
)
code = code.replace(
    "      · exact pillai_diff_two_5_7 e f he h",
    "      · subst hq7\n        exact pillai_diff_two_5_7 e f he h"
)

# 6. Insert subst hq3 and subst hq5 in p = 7 subbranches
code = code.replace(
    "      · exact pillai_diff_two_7_3 e f he hf h",
    "      · subst hq3\n        exact pillai_diff_two_7_3 e f he hf h"
)
code = code.replace(
    "      · exact pillai_diff_two_7_5 e f h",
    "      · subst hq5\n        exact pillai_diff_two_7_5 e f h"
)

# 7. Insert subst hq3, hq5, hq7 in p >= 11 subbranches
code = code.replace(
    "      · -- q = 3\n        have he_eq2 : e = 2 := (pillai_diff_two_5_3 e f he hf h).1",
    "      · subst hq3\n        have he_eq2 : e = 2 := (pillai_diff_two_5_3 e f he hf h).1"
)
code = code.replace(
    "      · -- q = 5 => 5^f - p^e = 2 => mod 3 => (-1)^f - p^e = 2",
    "      · subst hq5\n        -- q = 5 => 5^f - p^e = 2 => mod 3 => (-1)^f - p^e = 2"
)
code = code.replace(
    "      · -- q = 7 => 7^f - p^e = 2 => mod 3 => 1^f - p^e = 2 => 1 - p^e = 2 => p^e = 2 mod 3 => p = 2 mod 3 and e is odd",
    "      · subst hq7\n        -- q = 7 => 7^f - p^e = 2 => mod 3 => 1^f - p^e = 2 => 1 - p^e = 2 => p^e = 2 mod 3 => p = 2 mod 3 and e is odd"
)

with open("/workspace/leanproject/Submission/generate_short_spec.py", "w") as f:
    f.write(code)

print("generate_short_spec.py rcases successfully patched!")
