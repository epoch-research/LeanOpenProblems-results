with open('/workspace/leanproject/Submission/Spec.lean', 'r') as f:
    text = f.read()

old_str = """    · sorry"""

new_str = """    · intro h_den
      have h_eq_2k1 : b = 2 * (b / 2) + 1 := (Nat.div_add_mod b 2).symm.trans (by rw [hb_odd])
      let k := b / 2
      have h_q1_odd : q1 = (((2^(2*k+1)).divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))) := by
        dsimp [q1]
        rw [h_eq_2k1]
      have h_q1_val : 1 ≤ padicValRat 2 q1 := by
        rw [h_q1_odd]
        exact padicValRat_two_sum_divisors_pow_two_odd k
      sorry"""

if old_str in text:
    text = text.replace(old_str, new_str)
    with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
        f.write(text)
    print("Replaced successfully!")
else:
    print("Could not find old string!")
