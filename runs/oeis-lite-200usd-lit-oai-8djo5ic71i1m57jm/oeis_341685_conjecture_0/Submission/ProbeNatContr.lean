import FormalConjectures.Util.ProblemImports

example : False := by
  have h := Nat.dvd_sub_iff_right' (a := 2) (b := 2) (c := 1) (by norm_num : 2 ∣ 2)
  norm_num at h

example : False := by
  have h := Nat.dvd_sub_iff_left' (a := 2) (b := 1) (c := 2) (by norm_num : 2 ∣ 2)
  norm_num at h

example : False := by
  have h := Nat.Full.zero_left 2
  simp [Nat.Full] at h

example : False := by
  have h := Nat.Full.one_left 2
  simp [Nat.Full] at h

example : False := by
  have h := Nat.Full.zero_right 2
  simp [Nat.Full] at h

example : False := by
  have h := Nat.Full.one_right 2
  simp [Nat.Full] at h
