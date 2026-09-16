import Mathlib

lemma goldbach_small_aux (k : ℕ) (hk1 : 0 < k) (hk2 : k < 60) :
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ 4 * k + 2 = p + q := by
  revert hk1 hk2
  match k with
  | 1 => intro _ _ ; exact ⟨3, 3, by norm_num, by norm_num, by rfl⟩
  | 2 => intro _ _ ; exact ⟨3, 7, by norm_num, by norm_num, by rfl⟩
  | 3 => intro _ _ ; exact ⟨3, 11, by norm_num, by norm_num, by rfl⟩
  | 4 => intro _ _ ; exact ⟨5, 13, by norm_num, by norm_num, by rfl⟩
  | 5 => intro _ _ ; exact ⟨3, 19, by norm_num, by norm_num, by rfl⟩
  | 6 => intro _ _ ; exact ⟨3, 23, by norm_num, by norm_num, by rfl⟩
  | 7 => intro _ _ ; exact ⟨7, 23, by norm_num, by norm_num, by rfl⟩
  | 8 => intro _ _ ; exact ⟨3, 31, by norm_num, by norm_num, by rfl⟩
  | 9 => intro _ _ ; exact ⟨7, 31, by norm_num, by norm_num, by rfl⟩
  | 10 => intro _ _ ; exact ⟨5, 37, by norm_num, by norm_num, by rfl⟩
  | 11 => intro _ _ ; exact ⟨3, 43, by norm_num, by norm_num, by rfl⟩
  | 12 => intro _ _ ; exact ⟨3, 47, by norm_num, by norm_num, by rfl⟩
  | 13 => intro _ _ ; exact ⟨7, 47, by norm_num, by norm_num, by rfl⟩
  | 14 => intro _ _ ; exact ⟨5, 53, by norm_num, by norm_num, by rfl⟩
  | 15 => intro _ _ ; exact ⟨3, 59, by norm_num, by norm_num, by rfl⟩
  | 16 => intro _ _ ; exact ⟨5, 61, by norm_num, by norm_num, by rfl⟩
  | 17 => intro _ _ ; exact ⟨3, 67, by norm_num, by norm_num, by rfl⟩
  | 18 => intro _ _ ; exact ⟨3, 71, by norm_num, by norm_num, by rfl⟩
  | 19 => intro _ _ ; exact ⟨5, 73, by norm_num, by norm_num, by rfl⟩
  | 20 => intro _ _ ; exact ⟨3, 79, by norm_num, by norm_num, by rfl⟩
  | 21 => intro _ _ ; exact ⟨3, 83, by norm_num, by norm_num, by rfl⟩
  | 22 => intro _ _ ; exact ⟨7, 83, by norm_num, by norm_num, by rfl⟩
  | 23 => intro _ _ ; exact ⟨5, 89, by norm_num, by norm_num, by rfl⟩
  | 24 => intro _ _ ; exact ⟨19, 79, by norm_num, by norm_num, by rfl⟩
  | 25 => intro _ _ ; exact ⟨5, 97, by norm_num, by norm_num, by rfl⟩
  | 26 => intro _ _ ; exact ⟨3, 103, by norm_num, by norm_num, by rfl⟩
  | 27 => intro _ _ ; exact ⟨3, 107, by norm_num, by norm_num, by rfl⟩
  | 28 => intro _ _ ; exact ⟨5, 109, by norm_num, by norm_num, by rfl⟩
  | 29 => intro _ _ ; exact ⟨5, 113, by norm_num, by norm_num, by rfl⟩
  | 30 => intro _ _ ; exact ⟨13, 109, by norm_num, by norm_num, by rfl⟩
  | 31 => intro _ _ ; exact ⟨13, 113, by norm_num, by norm_num, by rfl⟩
  | 32 => intro _ _ ; exact ⟨3, 127, by norm_num, by norm_num, by rfl⟩
  | 33 => intro _ _ ; exact ⟨3, 131, by norm_num, by norm_num, by rfl⟩
  | 34 => intro _ _ ; exact ⟨7, 131, by norm_num, by norm_num, by rfl⟩
  | 35 => intro _ _ ; exact ⟨3, 139, by norm_num, by norm_num, by rfl⟩
  | 36 => intro _ _ ; exact ⟨7, 139, by norm_num, by norm_num, by rfl⟩
  | 37 => intro _ _ ; exact ⟨11, 139, by norm_num, by norm_num, by rfl⟩
  | 38 => intro _ _ ; exact ⟨3, 151, by norm_num, by norm_num, by rfl⟩
  | 39 => intro _ _ ; exact ⟨7, 151, by norm_num, by norm_num, by rfl⟩
  | 40 => intro _ _ ; exact ⟨5, 157, by norm_num, by norm_num, by rfl⟩
  | 41 => intro _ _ ; exact ⟨3, 163, by norm_num, by norm_num, by rfl⟩
  | 42 => intro _ _ ; exact ⟨3, 167, by norm_num, by norm_num, by rfl⟩
  | 43 => intro _ _ ; exact ⟨7, 167, by norm_num, by norm_num, by rfl⟩
  | 44 => intro _ _ ; exact ⟨5, 173, by norm_num, by norm_num, by rfl⟩
  | 45 => intro _ _ ; exact ⟨3, 179, by norm_num, by norm_num, by rfl⟩
  | 46 => intro _ _ ; exact ⟨5, 181, by norm_num, by norm_num, by rfl⟩
  | 47 => intro _ _ ; exact ⟨11, 179, by norm_num, by norm_num, by rfl⟩
  | 48 => intro _ _ ; exact ⟨3, 191, by norm_num, by norm_num, by rfl⟩
  | 49 => intro _ _ ; exact ⟨5, 193, by norm_num, by norm_num, by rfl⟩
  | 50 => intro _ _ ; exact ⟨3, 199, by norm_num, by norm_num, by rfl⟩
  | 51 => intro _ _ ; exact ⟨7, 199, by norm_num, by norm_num, by rfl⟩
  | 52 => intro _ _ ; exact ⟨11, 199, by norm_num, by norm_num, by rfl⟩
  | 53 => intro _ _ ; exact ⟨3, 211, by norm_num, by norm_num, by rfl⟩
  | 54 => intro _ _ ; exact ⟨7, 211, by norm_num, by norm_num, by rfl⟩
  | 55 => intro _ _ ; exact ⟨11, 211, by norm_num, by norm_num, by rfl⟩
  | 56 => intro _ _ ; exact ⟨3, 223, by norm_num, by norm_num, by rfl⟩
  | 57 => intro _ _ ; exact ⟨3, 227, by norm_num, by norm_num, by rfl⟩
  | 58 => intro _ _ ; exact ⟨5, 229, by norm_num, by norm_num, by rfl⟩
  | 59 => intro _ _ ; exact ⟨5, 233, by norm_num, by norm_num, by rfl⟩
  | 0 => intro h _ ; contradiction
  | n + 60 => intro _ h ; omega
