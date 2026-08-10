import Submission.Build
import Submission.Carlitz

open Nat Finset BigOperators

-- local copy for development (matches Spec.lean)
def A357674 (n : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ 4 * S2 ^ 3

namespace Wolst

variable {p : ℕ} [Fact p.Prime]

/-- The OEIS S2 summation as a natural number. -/
def S2seq (p : ℕ) : ℕ := ∑ k ∈ Finset.range (2*p+1), ((p+k-1).choose k)^2

/-- The OEIS S1 summation as a natural number. -/
def S1seq (p : ℕ) : ℕ := ∑ k ∈ Finset.range (2*p+1), (p+k-1).choose k

/-- The value `v = C(3p-1, p-1)` cast into `ZMod (p^5)`. -/
noncomputable def vval (p : ℕ) : ZMod (p^5) := (((3*p-1).choose (p-1) : ℕ) : ZMod (p^5))

/-- `vval` as a product (instance of `cval 2`). -/
lemma vval_prod :
    vval p = ∏ i ∈ Finset.Ico 1 p, (1 + (2:ZMod (p^5))*(p:ZMod (p^5)) * ((i:ZMod (p^5)))⁻¹) := by
  have h := cval (p := p) 2
  rw [show (2+1)*p - 1 = 3*p - 1 from by ring] at h
  rw [vval]; exact h

/-- THE HEART: `4·v + cast(S2seq) = 7` in `ZMod (p^5)`. -/
theorem heart (hp7 : 7 ≤ p) :
    4 * vval p + ((S2seq p : ℕ) : ZMod (p^5)) = 7 := by
  sorry

/-- `v - 1` is divisible by `p^3`. -/
theorem vsub1_dvd (hp7 : 7 ≤ p) :
    ∃ z : ZMod (p^5), vval p - 1 = (p:ZMod (p^5))^3 * z := by
  sorry

/-- Cast of `S1seq` equals `3·v`. -/
lemma cast_S1seq (hp1 : 1 ≤ p) :
    ((S1seq p : ℕ) : ZMod (p^5)) = 3 * vval p := by
  unfold S1seq
  rw [S1_telescope hp1, vval]
  push_cast
  ring

/-- The assembled congruence in `ZMod (p^5)` for `p ≥ 7`. -/
theorem main_zmod (hp7 : 7 ≤ p) :
    ((A357674 p : ℕ) : ZMod (p^5)) = 2187 := by
  have hp1 : 1 ≤ p := by omega
  have hAdef : A357674 p = (S1seq p)^4 * (S2seq p)^3 := rfl
  rw [hAdef]
  push_cast
  set v := vval p with hv
  rw [show (((S1seq p):ℕ):ZMod (p^5)) = 3 * v from cast_S1seq hp1]
  set s := ((S2seq p : ℕ) : ZMod (p^5)) with hs
  set A := 3*v - 3 with hA
  set B := s - 3 with hB
  have h3v : (3:ZMod (p^5))*v = 3 + A := by rw [hA]; ring
  have hsB : s = 3 + B := by rw [hB]; ring
  rw [h3v, hsB]
  obtain ⟨z, hz⟩ := vsub1_dvd (p := p) hp7
  have ha : A = (p:ZMod (p^5))^3 * (3*z) := by
    rw [hA, show 3*v-3 = 3*(v-1) from by ring, hv, hz]; ring
  have hheart : 4*v + s = 7 := heart (p := p) hp7
  have h4A3B : 4*A + 3*B = 0 := by rw [hA, hB]; linear_combination 3 * hheart
  have hp5 : (p:ZMod (p^5))^5 = 0 := by rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  have hA2 : A^2 = 0 := by
    rw [ha, mul_pow, show ((p:ZMod (p^5))^3)^2 = (p:ZMod (p^5))^5*p from by ring, hp5]; ring
  have hB3B : 3*B = -(4*A) := by linear_combination h4A3B
  have h3u : IsUnit (3:ZMod (p^5)) := by
    have h := isUnit_cast (p:=p) (k:=5) 3 (by norm_num) (by omega)
    simpa using h
  have h9u : IsUnit (9:ZMod (p^5)) := by
    rw [show (9:ZMod (p^5))=3*3 from by norm_num]; exact h3u.mul h3u
  have heB : (9:ZMod (p^5))*B^2 = 0 := by linear_combination (3*B-4*A)*hB3B + 16*hA2
  have hB2 : B^2 = 0 := (h9u.mul_right_eq_zero).mp heB
  have heAB : (3:ZMod (p^5))*(A*B) = 0 := by linear_combination A*hB3B - 4*hA2
  have hAB : A*B = 0 := (h3u.mul_right_eq_zero).mp heAB
  have e1 : (3+A)^4 = 81 + 108*A := by linear_combination (A^2 + 12*A + 54)*hA2
  have e2 : (3+B)^3 = 27 + 27*B := by linear_combination (B+9)*hB2
  rw [e1, e2]
  linear_combination 729*h4A3B + 2916*hAB

end Wolst

/-- Final theorem (development copy). -/
theorem final (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases h3 : p = 3
  · subst h3; decide
  by_cases h5 : p = 5
  · subst h5; decide
  have hp7 : 7 ≤ p := by
    rcases Nat.lt_or_ge p 7 with h | h
    · exfalso
      have : p = 4 ∨ p = 5 ∨ p = 6 := by omega
      rcases this with h'|h'|h' <;> subst h'
      · exact absurd hp (by decide)
      · exact h5 rfl
      · exact absurd hp (by decide)
    · exact h
  have h1 : A357674 1 = 2187 := by decide
  rw [h1]
  refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
  rw [Wolst.main_zmod hp7]
  norm_num
