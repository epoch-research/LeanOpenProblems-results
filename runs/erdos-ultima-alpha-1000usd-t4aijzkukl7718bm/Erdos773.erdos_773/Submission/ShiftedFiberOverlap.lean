import Submission.FullFiberOverlap

/-!
A modular gap match together with a coarse weighted-center match forces an
actual collision in two FULL shifted index intervals. No partial-fiber
claim and no bound for the original square-Sidon maximum is asserted.
-/
namespace Erdos773.ShiftedFiberOverlap

open Finset FullFiberOverlap

set_option maxHeartbeats 2000000

/-- The center used for quantization is five gap-scales above the interval start. -/
def center (q L r A : ℕ) : ℕ := q * (A + 5 * L) + r

/-- Close weighted centers put the modular collision inside both shifted intervals. -/
theorem close_center_collision {q L r s u v A B : ℕ} (hq : 0 < q) (hL : 0 < L)
    (hu : u ∈ Finset.Icc L (2 * L)) (hv : v ∈ Finset.Icc L (2 * L))
    (hcop : q.Coprime v) (hr : r < q) (hs : s < q)
    (he : r * u ≡ s * v [MOD q])
    (hclose₁ : u * center q L r A < v * center q L s B + q * L ^ 2)
    (hclose₂ : v * center q L s B < u * center q L r A + q * L ^ 2) :
    ∃ a c : ℕ, A ≤ a ∧ a + 2 * u ≤ A + 10 * L ∧
      B ≤ c ∧ c + 2 * v ≤ B + 10 * L ∧
      (q * (a + 2 * u) + r) ^ 2 + (q * c + s) ^ 2 =
        (q * a + r) ^ 2 + (q * (c + 2 * v) + s) ^ 2 := by
  obtain ⟨hu1, hu2⟩ := Finset.mem_Icc.mp hu
  obtain ⟨hv1, hv2⟩ := Finset.mem_Icc.mp hv
  have hu0 : 0 < u := by omega
  have hv0 : 0 < v := by omega
  obtain ⟨t, ht, hrt, hst⟩ := common_multiplier hq hcop hr hs he
  let k := (A + 5 * L) / v
  let a₀ := v * k + v * t / q
  let c₀ := u * k + u * t / q
  have htU : u * t / q < u := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
  have htV : v * t / q < v := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
  have hk₁ : v * k ≤ A + 5 * L := Nat.mul_div_le _ _
  have hk₂ : A + 5 * L < v * k + v := by
    have hh := Nat.mod_add_div (A + 5 * L) v
    have hm := Nat.mod_lt (A + 5 * L) hv0
    dsimp only [k]
    omega
  have ha₁ : a₀ < A + 5 * L + v := by dsimp only [a₀]; omega
  have ha₂ : A + 5 * L < a₀ + v :=
    hk₂.trans_le (Nat.add_le_add_right (Nat.le_add_right _ _) v)
  have haQ : q * a₀ + r = v * (q * k + t) := by
    have hh := Nat.mod_add_div (v * t) q
    rw [hrt] at hh
    dsimp only [a₀]
    nlinarith only [hh]
  have hcQ : q * c₀ + s = u * (q * k + t) := by
    have hh := Nat.mod_add_div (u * t) q
    rw [hst] at hh
    dsimp only [c₀]
    nlinarith only [hh]
  have hcore : u * (q * a₀ + r) = v * (q * c₀ + s) := by rw [haQ, hcQ]; ring
  have haQ₁ : q * a₀ + r < center q L r A + q * v := by
    have hh := Nat.mul_lt_mul_of_pos_left ha₁ hq
    dsimp only [center]
    nlinarith only [hh]
  have haQ₂ : center q L r A < q * a₀ + r + q * v := by
    have hh := Nat.mul_lt_mul_of_pos_left ha₂ hq
    dsimp only [center]
    nlinarith only [hh]
  have hbound : q * L ^ 2 + u * q * v ≤ 3 * q * L * v := by
    have hLsq := Nat.mul_le_mul_left L hv1
    have huv := Nat.mul_le_mul_right v hu2
    have hh := Nat.mul_le_mul_left q (show L ^ 2 + u * v ≤ 3 * L * v by
      nlinarith only [hLsq, huv])
    nlinarith only [hh]
  have hc₁ : c₀ < B + 5 * L + 3 * L := by
    have hh := Nat.mul_lt_mul_of_pos_left haQ₁ hu0
    have hmul : v * (q * c₀ + s) < v * (q * (B + 5 * L + 3 * L) + s) := by
      dsimp only [center] at hclose₁ hh
      nlinarith only [hh, hclose₁, hcore, hbound]
    have hh' := Nat.lt_of_mul_lt_mul_left hmul
    exact Nat.lt_of_mul_lt_mul_left (show q * c₀ < q * (B + 5 * L + 3 * L) by omega)
  have hc₂ : B + 5 * L < c₀ + 3 * L := by
    have hh := Nat.mul_lt_mul_of_pos_left haQ₂ hu0
    have hmul : v * (q * (B + 5 * L) + s) < v * (q * (c₀ + 3 * L) + s) := by
      dsimp only [center] at hclose₂ hh
      nlinarith only [hh, hclose₂, hcore, hbound]
    have hh' := Nat.lt_of_mul_lt_mul_left hmul
    exact Nat.lt_of_mul_lt_mul_left (show q * (B + 5 * L) < q * (c₀ + 3 * L) by omega)
  let a := a₀ - u
  let c := c₀ - v
  have ha : a + u = a₀ := Nat.sub_add_cancel (by omega)
  have hc : c + v = c₀ := Nat.sub_add_cancel (by omega)
  refine ⟨a, c, by omega, by omega, by omega, by omega, ?_⟩
  rw [← ha, ← hc] at hcore
  nlinarith only [congrArg (fun n => 4 * q * n) hcore]

/-- A bin match is a sufficient, not an assumed, bound on center separation. -/
lemma same_bin_close {x y D : ℕ} (hD : 0 < D) (h : x / D = y / D) :
    x < y + D ∧ y < x + D := by
  have hx := Nat.mod_add_div x D
  have hy := Nat.mod_add_div y D
  have hxm := Nat.mod_lt x hD
  have hym := Nat.mod_lt y hD
  rw [h] at hx
  omega

/-- The two-coordinate key: modular gap product and coarse weighted center. -/
def key (q L : ℕ) (starts : ℕ → ℕ) (z : ℕ × ℕ) : ℕ × ℕ :=
  (z.1 * z.2 % q, z.2 * center q L z.1 (starts z.1) / (q * L ^ 2))

lemma key_collision {q L : ℕ} {starts : ℕ → ℕ} {r s u v : ℕ}
    (hq : 0 < q) (hL : 0 < L)
    (hu : u ∈ Finset.Icc L (2 * L)) (hv : v ∈ Finset.Icc L (2 * L))
    (hcop : q.Coprime v) (hr : r < q) (hs : s < q)
    (he : key q L starts (r, u) = key q L starts (s, v)) :
    ∃ a c : ℕ, starts r ≤ a ∧ a + 2 * u ≤ starts r + 10 * L ∧
      starts s ≤ c ∧ c + 2 * v ≤ starts s + 10 * L ∧
      (q * (a + 2 * u) + r) ^ 2 + (q * c + s) ^ 2 =
        (q * a + r) ^ 2 + (q * (c + 2 * v) + s) ^ 2 := by
  have hmod := congrArg Prod.fst he
  have hbin := congrArg Prod.snd he
  change r * u ≡ s * v [MOD q] at hmod
  have hclose := same_bin_close (by positivity : 0 < q * L ^ 2) hbin
  exact close_center_collision hq hL hu hv hcop hr hs hmod hclose.1 hclose.2

#print axioms close_center_collision
#print axioms key_collision

end Erdos773.ShiftedFiberOverlap
