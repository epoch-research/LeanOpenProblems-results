import os
import re

def main():
    # Read generate_short_spec.py
    # We must read it from a clean state or rewrite it. Let's write a python script that will cleanly overwrite generate_short_spec.py with a perfect python code.
    
    # Let's read generate_short_spec.py and see if we can do the search and replace on the python file
    with open("/workspace/leanproject/Submission/generate_short_spec.py", "r") as f:
        content = f.read()

    # Define the new helper lemmas to insert
    helper_lemmas = """
lemma odd_sq_mod_eight (y : ℕ) (hy : y % 2 = 1) : 8 ∣ y ^ 2 - 1 := by
  have h_mod : y % 8 < 8 := Nat.mod_lt _ (by decide)
  set k := y / 8
  interval_cases y_mod : y % 8
  · have : y % 2 = 0 := by
      have : y = 8 * k + 0 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 1 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 2 * k) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 2 * k) + 1 - 1 = 8 * (8 * k ^ 2 + 2 * k) := by omega
    rw [this]
    exact dvd_mul_right 8 _
  · have : y % 2 = 0 := by
      have : y = 8 * k + 2 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 3 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 6 * k + 1) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 6 * k + 1) + 1 - 1 = 8 * (8 * k ^ 2 + 6 * k + 1) := by omega
    rw [this]
    exact dvd_mul_right 8 _
  · have : y % 2 = 0 := by
      have : y = 8 * k + 4 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 5 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 10 * k + 3) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 10 * k + 3) + 1 - 1 = 8 * (8 * k ^ 2 + 10 * k + 3) := by omega
    rw [this]
    exact dvd_mul_right 8 _
  · have : y % 2 = 0 := by
      have : y = 8 * k + 6 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 7 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 14 * k + 6) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 14 * k + 6) + 1 - 1 = 8 * (8 * k ^ 2 + 14 * k + 6) := by omega
    rw [this]
    exact dvd_mul_right 8 _

lemma pow_five_zmod_eight (e : ℕ) : (5 : ZMod 8) ^ e = 1 ∨ (5 : ZMod 8) ^ e = 5 := by
  induction e with
  | zero => left; rfl
  | succ e ih =>
    rcases ih with h1 | h2
    · right; rw [pow_succ, h1, one_mul]
    · left; rw [pow_succ, h2]
      decide

lemma hy_odd_proof (q f : ℕ) (hq : Nat.Prime q) (hq_ne_2 : q ≠ 2) (hf : f % 2 = 0) (hf_pos : f > 0) :
    (q ^ (f / 2)) % 2 = 1 := by
  set y := q ^ (f / 2)
  by_contra hc
  have hc_even : y % 2 = 0 := by omega
  have h_even_y : 2 ∣ y := Nat.dvd_of_mod_eq_zero hc_even
  have h_even_q : 2 ∣ q := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h_even_y
  rcases hq.eq_one_or_self_of_dvd 2 h_even_q with h1 | h2
  · contradiction
  · exact hq_ne_2 h2.symm

lemma f_even_contradiction (e f q : ℕ) (hq : Nat.Prime q) (hq_ne_2 : q ≠ 2) (h_sq : q ^ f = 5 ^ e + 2) (hf_even : f % 2 = 0) (hf_pos : f > 0) : False := by
  have hf_eq : f = (f / 2) * 2 := by omega
  set y := q ^ (f / 2)
  have h_fy : q ^ f = y ^ 2 := by
    rw [hf_eq, pow_mul]
  have h_sq_y : y ^ 2 = 5 ^ e + 2 := by
    rw [← h_fy, h_sq]
  have hy_odd : y % 2 = 1 := hy_odd_proof q f hq hq_ne_2 hf_even hf_pos
  have h_dvd : 8 ∣ y ^ 2 - 1 := odd_sq_mod_eight y hy_odd
  have h_dvd_five : 8 ∣ 5 ^ e + 1 := by
    have h_sub : y ^ 2 - 1 = 5 ^ e + 1 := by
      generalize 5 ^ e = V at h_sq_y ⊢
      rw [h_sq_y]
      omega
    rw [h_sub] at h_dvd
    exact h_dvd
  have h_cast : ((5 ^ e + 1 : ℕ) : ZMod 8) = 0 := by
    rcases h_dvd_five with ⟨c, hc⟩
    have hc_cast : ((5 ^ e + 1 : ℕ) : ZMod 8) = ((8 * c : ℕ) : ZMod 8) := congrArg Nat.cast hc
    rw [hc_cast]
    push_cast
    have : (8 : ZMod 8) = 0 := rfl
    rw [this, zero_mul]
  have h_five_zmod : (5 : ZMod 8) ^ e = -1 := by
    have h_cast_push : (5 : ZMod 8) ^ e + 1 = 0 := by
      calc (5 : ZMod 8) ^ e + 1 = ((5 ^ e + 1 : ℕ) : ZMod 8) := by push_cast; rfl
      _ = 0 := h_cast
    calc (5 : ZMod 8) ^ e = (5 : ZMod 8) ^ e + 1 - 1 := by ring
    _ = 0 - 1 := by rw [h_cast_push]
    _ = -1 := by ring
  have h_pow_cases := pow_five_zmod_eight e
  rcases h_pow_cases with h1 | h2
  · rw [h1] at h_five_zmod
    have : (1 : ZMod 8) = -1 := h_five_zmod
    revert this
    decide
  · rw [h2] at h_five_zmod
    have : (5 : ZMod 8) = -1 := h_five_zmod
    revert this
    decide

lemma pow_two_zmod_three_odd (e : ℕ) (he_odd : e % 2 = 1) : (2 : ZMod 3) ^ e = 2 := by
  have h_eq : e = 2 * (e / 2) + 1 := by omega
  rw [h_eq]
  have : (2 : ZMod 3) ^ (2 * (e / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (e / 2) * 2 := by
    rw [pow_succ, pow_mul]
  rw [this]
  have : (2 : ZMod 3) ^ 2 = 1 := rfl
  rw [this, one_pow, one_mul]

lemma q_mod_3_contradiction (e f q : ℕ) (hq_mod : q % 3 = 2) (he_odd : e % 2 = 1) (h : q ^ f = 5 ^ e + 2) : f % 2 = 0 := by
  by_contra hf_odd_hc
  have hf_odd : f % 2 = 1 := by omega
  have h_cast : ((q ^ f : ℕ) : ZMod 3) = ((5 ^ e + 2 : ℕ) : ZMod 3) := congrArg Nat.cast h
  push_cast at h_cast
  have hq_cast : (q : ZMod 3) = 2 := by
    have : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
    rw [this, hq_mod]
    rfl
  have h5_cast : (5 : ZMod 3) = 2 := rfl
  rw [hq_cast, h5_cast] at h_cast
  have hq_pow : (2 : ZMod 3) ^ f = 2 := pow_two_zmod_three_odd f hf_odd
  have h5_pow : (2 : ZMod 3) ^ e = 2 := pow_two_zmod_three_odd e he_odd
  rw [hq_pow, h5_pow] at h_cast
  have : (2 : ZMod 3) = 2 + 2 := h_cast
  revert this
  decide

lemma dvd_contradiction_eight (q : ℕ) (hq : Nat.Prime q) (hq_ne_2 : q ≠ 2) (h_dvd : 8 ∣ q) : False := by
  have : 2 ∣ q := dvd_trans (by decide) h_dvd
  rcases hq.eq_one_or_self_of_dvd 2 this with h1 | h2
  · contradiction
  · exact hq_ne_2 h2.symm

lemma dvd_contradiction_25 (q : ℕ) (hq : Nat.Prime q) (hq5_val : q % 5 = 2) (h_dvd : 25 ∣ q) : False := by
  have : 5 ∣ q := dvd_trans (by decide) h_dvd
  rcases hq.eq_one_or_self_of_dvd 5 this with h1 | h2
  · contradiction
  · subst h2
    revert hq5_val
    decide
"""

    # Ensure helper_lemmas string is correct, and we also correct the f_even_contradiction calls in pillai_diff_two_code
    # Let's find out how generate_short_spec.py is structured and apply these fixes
    # First, let's load generate_short_spec.py lines as a list
    with open("/workspace/leanproject/Submission/generate_short_spec.py", "r") as f:
        lines = f.readlines()

    # Let's write a python script that will completely regenerate generate_short_spec.py with our updated strings and functions
    # Wait, we can just replace the definition of pillai_diff_two_code inside generate_short_spec.py!
    # Let's do that. We can replace:
    # `exact f_even_contradiction e f q hp_ne_2 h hf_even hf`
    # etc.
    
    # We will join the lines back
    text = "".join(lines)
    
    # Replace the f_even_contradiction calls
    text = text.replace(
        "· exact f_even_contradiction e f q hp_ne_2 h hf_even hf",
        "· have h_sq : q ^ f = 5 ^ e + 2 := by omega\\n          exact f_even_contradiction e f q hq hq_ne_2 h_sq hf_even (by omega)"
    )
    text = text.replace(
        "exact f_even_contradiction e f q hp_ne_2 h hf_even2 hf",
        "have h_sq : q ^ f = 5 ^ e + 2 := by omega\\n            exact f_even_contradiction e f q hq hq_ne_2 h_sq hf_even2 (by omega)"
    )
    text = text.replace(
        "exact f_even_contradiction e f 5 hp_ne_2 h hf_even hf",
        "have h_sq : 5 ^ f = 5 ^ e + 2 := by omega\\n              exact f_even_contradiction e f 5 Nat.prime_five (by decide) h_sq hf_even (by omega)"
    )

    # Replace the divisibility contradictions
    text = text.replace(
        "· exfalso; have : 8 ∣ q := Nat.dvd_of_mod_eq_zero hq_mod; omega",
        "· exact dvd_contradiction_eight q hq hq_ne_2 (Nat.dvd_of_mod_eq_zero hq_mod)"
    )
    text = text.replace(
        "· exfalso; have : 25 ∣ q := Nat.dvd_of_mod_eq_zero hq25_val; omega",
        "· exact dvd_contradiction_25 q hq hq5_val (Nat.dvd_of_mod_eq_zero hq25_val)"
    )
    text = text.replace(
        "· exfalso; have : 8 ∣ q := Nat.dvd_of_mod_eq_zero hq8_val; omega",
        "· exact dvd_contradiction_eight q hq hq_ne_2 (Nat.dvd_of_mod_eq_zero hq8_val)"
    )
    text = text.replace(
        "· exfalso; have : 8 ∣ p := Nat.dvd_of_mod_eq_zero hp_mod; omega",
        "· exact dvd_contradiction_eight p hp hp_ne_2 (Nat.dvd_of_mod_eq_zero hp_mod)"
    )

    # Let's replace the helper_lemmas definition inside generate_short_spec.py to include our new helper lemmas
    # In generate_short_spec.py, there is a string `helper_lemmas = """..."""` that was inserted
    # Let's see: we want to replace the `lemma odd_sq_mod_eight` ... `decide` block
    # Actually, we can just replace the definition of `helper_lemmas` we inserted in generate_short_spec.py.
    # Let's find the start of our helper lemmas and replace up to the end of `decide`.
    # To be extremely clean, let's write a regex that updates helper_lemmas in generate_short_spec.py.
    
    # Let's overwrite generate_short_spec.py with this modified text
    with open("/workspace/leanproject/Submission/generate_short_spec.py", "w") as f:
        f.write(text)

if __name__ == "__main__":
    main()
