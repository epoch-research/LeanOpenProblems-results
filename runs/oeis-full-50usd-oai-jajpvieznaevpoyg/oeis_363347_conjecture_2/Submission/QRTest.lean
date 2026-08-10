import FormalConjectures.Util.ProblemImports
open Rat Nat

example (p : ℕ) (hp : p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) :
    ∃ m : ℕ, 4 ≤ m ∧ m < p ∧ m*m ≡ 5 [MOD p] := by
  classical
  have hpprime : p.Prime := hp.1
  have hp_fact : Fact p.Prime := ⟨hpprime⟩
  have hp_ne2 : p ≠ 2 := by
    intro h; subst p
    rcases hp.2 with h | h <;> norm_num [Nat.ModEq] at h
  have hp_gt5 : 5 < p := by
    by_contra hle
    have hple : p ≤ 5 := by omega
    interval_cases p <;> try contradiction
    all_goals rcases hp.2 with h | h <;> norm_num [Nat.ModEq] at h
  have hpmod5 : p % 5 = 1 ∨ p % 5 = 4 := by
    rcases hp.2 with h | h
    · left
      rw [Nat.ModEq] at h
      omega
    · right
      rw [Nat.ModEq] at h
      omega
  have hp_gt9 : 9 < p := by
    by_contra hle
    have hple : p ≤ 9 := by omega
    interval_cases p <;> try contradiction
    all_goals rcases hp.2 with h | h <;> norm_num [Nat.ModEq] at h
  have hsq5 : IsSquare ((5 : ℕ) : ZMod p) := by
    letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hiff := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by norm_num) hp_ne2
    exact hiff.mp (by
      rcases hpmod5 with h1 | h4
      · refine ⟨(1 : ZMod 5), ?_⟩
        have : ((p : ℕ) : ZMod 5) = (1 : ZMod 5) := by
          exact (ZMod.natCast_eq_natCast_iff' p 1 5).2 h1
        rw [this]
        norm_num [pow_two]
      · refine ⟨(2 : ZMod 5), ?_⟩
        have : ((p : ℕ) : ZMod 5) = (4 : ZMod 5) := by
          exact (ZMod.natCast_eq_natCast_iff' p 4 5).2 h4
        rw [this]
        norm_num [pow_two])
  rcases hsq5 with ⟨a, ha⟩
  let m := a.val
  have hlt : m < p := a.val_lt
  have hsquare_val : (m * m) % p = 5 % p := by
    have hcast : ((m*m : ℕ) : ZMod p) = ((5:ℕ) : ZMod p) := by
      rw [Nat.cast_mul, show (m : ZMod p) = a by exact ZMod.natCast_zmod_val a]
      exact ha.symm
    exact (ZMod.natCast_eq_natCast_iff' (m*m) 5 p).1 hcast
  have h5mod : 5 % p = 5 := Nat.mod_eq_of_lt hp_gt5
  have h1mod : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  have h4mod : 4 % p = 4 := Nat.mod_eq_of_lt (by omega)
  have h9mod : 9 % p = 9 := Nat.mod_eq_of_lt hp_gt9
  have hnot0 : m ≠ 0 := by
    intro hm
    have : 0 = 5 := by simpa [hm, h5mod] using hsquare_val
    omega
  have hnot1 : m ≠ 1 := by
    intro hm
    have : 1 = 5 := by simpa [hm, h5mod, h1mod] using hsquare_val
    omega
  have hnot2 : m ≠ 2 := by
    intro hm
    have : 4 = 5 := by simpa [hm, h5mod, h4mod] using hsquare_val
    omega
  have hnot3 : m ≠ 3 := by
    intro hm
    have h9eq : 9 % p = 5 := by simpa [hm, h5mod] using hsquare_val
    have : 9 = 5 := by simpa [h9mod] using h9eq
    omega
  refine ⟨m, ?_, hlt, ?_⟩
  · omega
  · exact hsquare_val
