import FormalConjectures.Util.ProblemImports

open Nat

set_option maxHeartbeats 4000000
set_option maxRecDepth 25000

/--
A355898: $a(1) = a(2) = 1$; $a(n) = \gcd(a(n-1), a(n-2)) + \frac{a(n-1) + a(n-2)}{\gcd(a(n-1), a(n-2))}$.
-/
def A355898 : ℕ → ℕ
| 0 => 0 -- Sequence starts properly at A355898(1)
| 1 => 1
| 2 => 1
| n + 3 =>
  let an_minus_1 := A355898 (n + 2)
  let an_minus_2 := A355898 (n + 1)
  let g := Nat.gcd an_minus_1 an_minus_2
  g + (an_minus_1 + an_minus_2) / g

/-- All terms with positive index are positive. -/
theorem A355898_pos : ∀ n, 1 ≤ A355898 (n+1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | (m+2), ih =>
      have hdef : A355898 (m+3) = Nat.gcd (A355898 (m+2)) (A355898 (m+1)) +
          (A355898 (m+2) + A355898 (m+1)) / Nat.gcd (A355898 (m+2)) (A355898 (m+1)) := rfl
      have h1 : 1 ≤ A355898 (m+1) := ih m (by omega)
      have hg : 1 ≤ Nat.gcd (A355898 (m+2)) (A355898 (m+1)) :=
        Nat.one_le_iff_ne_zero.mpr (fun hz => by
          have := Nat.eq_zero_of_gcd_eq_zero_right hz; omega)
      show 1 ≤ A355898 (m+3)
      rw [hdef]
      exact le_trans hg (Nat.le_add_right _ _)

abbrev p : ℕ := 195318521017

@[ext] structure M2 where
  a : ZMod p
  b : ZMod p
  c : ZMod p
  d : ZMod p

namespace M2
def mul (x y : M2) : M2 :=
  ⟨x.a*y.a+x.b*y.c, x.a*y.b+x.b*y.d, x.c*y.a+x.d*y.c, x.c*y.b+x.d*y.d⟩
instance : Mul M2 := ⟨mul⟩
instance : One M2 := ⟨⟨1,0,0,1⟩⟩
theorem mul_def (x y : M2) : x * y = mul x y := rfl
theorem one_def : (1 : M2) = ⟨1,0,0,1⟩ := rfl
instance : Monoid M2 where
  mul_assoc x y z := by ext <;> · simp only [mul_def, mul]; ring
  one_mul x := by ext <;> · simp only [mul_def, mul, one_def]; ring
  mul_one x := by ext <;> · simp only [mul_def, mul, one_def]; ring
def act (m : M2) (v : ZMod p × ZMod p) : ZMod p × ZMod p :=
  (m.a * v.1 + m.b * v.2, m.c * v.1 + m.d * v.2)
theorem act_mul (m n : M2) (v) : act (m * n) v = act m (act n v) := by
  simp only [act, mul_def, mul, Prod.mk.injEq]; exact ⟨by ring, by ring⟩
theorem act_one (v) : act 1 v = v := by
  simp only [act, one_def, Prod.ext_iff]; exact ⟨by ring, by ring⟩
end M2

def MM : M2 := ⟨0,1,1,1⟩

-- Squaring chain: hpwj : MM ^ (2^j) = E_j
theorem hpw0 : MM ^ 1 = ⟨0,1,1,1⟩ := by rw [pow_one]; rfl
theorem hpw1 : MM ^ 2 = ⟨1,1,1,2⟩ := by
  have h : MM ^ 2 = MM ^ 1 * MM ^ 1 := by rw [← pow_add]
  rw [h, hpw0]; rfl
theorem hpw2 : MM ^ 4 = ⟨2,3,3,5⟩ := by
  have h : MM ^ 4 = MM ^ 2 * MM ^ 2 := by rw [← pow_add]
  rw [h, hpw1]; rfl
theorem hpw3 : MM ^ 8 = ⟨13,21,21,34⟩ := by
  have h : MM ^ 8 = MM ^ 4 * MM ^ 4 := by rw [← pow_add]
  rw [h, hpw2]; rfl
theorem hpw4 : MM ^ 16 = ⟨610,987,987,1597⟩ := by
  have h : MM ^ 16 = MM ^ 8 * MM ^ 8 := by rw [← pow_add]
  rw [h, hpw3]; rfl
theorem hpw5 : MM ^ 32 = ⟨1346269,2178309,2178309,3524578⟩ := by
  have h : MM ^ 32 = MM ^ 16 * MM ^ 16 := by rw [← pow_add]
  rw [h, hpw4]; rfl
theorem hpw6 : MM ^ 64 = ⟨111959126281,63009722805,63009722805,174968849086⟩ := by
  have h : MM ^ 64 = MM ^ 32 * MM ^ 32 := by rw [← pow_add]
  rw [h, hpw5]; rfl
theorem hpw7 : MM ^ 128 = ⟨109112207844,51417128957,51417128957,160529336801⟩ := by
  have h : MM ^ 128 = MM ^ 64 * MM ^ 64 := by rw [← pow_add]
  rw [h, hpw6]; rfl
theorem hpw8 : MM ^ 256 = ⟨75277332677,97012418887,97012418887,172289751564⟩ := by
  have h : MM ^ 256 = MM ^ 128 * MM ^ 128 := by rw [← pow_add]
  rw [h, hpw7]; rfl
theorem hpw9 : MM ^ 512 = ⟨110187394164,188588191927,188588191927,103457065074⟩ := by
  have h : MM ^ 512 = MM ^ 256 * MM ^ 256 := by rw [← pow_add]
  rw [h, hpw8]; rfl
theorem hpw10 : MM ^ 1024 = ⟨30161079904,5770458530,5770458530,35931538434⟩ := by
  have h : MM ^ 1024 = MM ^ 512 * MM ^ 512 := by rw [← pow_add]
  rw [h, hpw9]; rfl
theorem hpw11 : MM ^ 2048 = ⟨144552683616,192915565028,192915565028,142149727627⟩ := by
  have h : MM ^ 2048 = MM ^ 1024 * MM ^ 1024 := by rw [← pow_add]
  rw [h, hpw10]; rfl
theorem hpw12 : MM ^ 4096 = ⟨69667805911,24380517519,24380517519,94048323430⟩ := by
  have h : MM ^ 4096 = MM ^ 2048 * MM ^ 2048 := by rw [← pow_add]
  rw [h, hpw11]; rfl
theorem hpw13 : MM ^ 8192 = ⟨27700018719,5577243900,5577243900,33277262619⟩ := by
  have h : MM ^ 8192 = MM ^ 4096 * MM ^ 4096 := by rw [← pow_add]
  rw [h, hpw12]; rfl
theorem hpw14 : MM ^ 16384 = ⟨43074843587,168706442485,168706442485,16462765055⟩ := by
  have h : MM ^ 16384 = MM ^ 8192 * MM ^ 8192 := by rw [← pow_add]
  rw [h, hpw13]; rfl
theorem hpw15 : MM ^ 32768 = ⟨120168363434,177551683974,177551683974,102401526391⟩ := by
  have h : MM ^ 32768 = MM ^ 16384 * MM ^ 16384 := by rw [← pow_add]
  rw [h, hpw14]; rfl
theorem hpw16 : MM ^ 65536 = ⟨114955246228,66969999690,66969999690,181925245918⟩ := by
  have h : MM ^ 65536 = MM ^ 32768 * MM ^ 32768 := by rw [← pow_add]
  rw [h, hpw15]; rfl
theorem hpw17 : MM ^ 131072 = ⟨82118779510,175432384333,175432384333,62232642826⟩ := by
  have h : MM ^ 131072 = MM ^ 65536 * MM ^ 65536 := by rw [← pow_add]
  rw [h, hpw16]; rfl
theorem hpw18 : MM ^ 262144 = ⟨40736586663,68296258645,68296258645,109032845308⟩ := by
  have h : MM ^ 262144 = MM ^ 131072 * MM ^ 131072 := by rw [← pow_add]
  rw [h, hpw17]; rfl
theorem hpw19 : MM ^ 524288 = ⟨25291658413,148940966689,148940966689,174232625102⟩ := by
  have h : MM ^ 524288 = MM ^ 262144 * MM ^ 262144 := by rw [← pow_add]
  rw [h, hpw18]; rfl
theorem hpw20 : MM ^ 1048576 = ⟨115434376627,105187682578,105187682578,25303538188⟩ := by
  have h : MM ^ 1048576 = MM ^ 524288 * MM ^ 524288 := by rw [← pow_add]
  rw [h, hpw19]; rfl
theorem hpw21 : MM ^ 2097152 = ⟨102123116340,188279295794,188279295794,95083891117⟩ := by
  have h : MM ^ 2097152 = MM ^ 1048576 * MM ^ 1048576 := by rw [← pow_add]
  rw [h, hpw20]; rfl
theorem hpw22 : MM ^ 4194304 = ⟨52246199270,91536119839,91536119839,143782319109⟩ := by
  have h : MM ^ 4194304 = MM ^ 2097152 * MM ^ 2097152 := by rw [← pow_add]
  rw [h, hpw21]; rfl
theorem hpw23 : MM ^ 8388608 = ⟨34576922748,176548506382,176548506382,15806908113⟩ := by
  have h : MM ^ 8388608 = MM ^ 4194304 * MM ^ 4194304 := by rw [← pow_add]
  rw [h, hpw22]; rfl
theorem hpw24 : MM ^ 16777216 = ⟨128040991706,146300176125,146300176125,79022646814⟩ := by
  have h : MM ^ 16777216 = MM ^ 8388608 * MM ^ 8388608 := by rw [← pow_add]
  rw [h, hpw23]; rfl
theorem hpw25 : MM ^ 33554432 = ⟨130688711072,7013321801,7013321801,137702032873⟩ := by
  have h : MM ^ 33554432 = MM ^ 16777216 * MM ^ 16777216 := by rw [← pow_add]
  rw [h, hpw24]; rfl
theorem hpw26 : MM ^ 67108864 = ⟨101431712799,78203669006,78203669006,179635381805⟩ := by
  have h : MM ^ 67108864 = MM ^ 33554432 * MM ^ 33554432 := by rw [← pow_add]
  rw [h, hpw25]; rfl
theorem hpw27 : MM ^ 134217728 = ⟨192683405149,42895907439,42895907439,40260791571⟩ := by
  have h : MM ^ 134217728 = MM ^ 67108864 * MM ^ 67108864 := by rw [← pow_add]
  rw [h, hpw26]; rfl
theorem hpw28 : MM ^ 268435456 = ⟨101694691008,9523400993,9523400993,111218092001⟩ := by
  have h : MM ^ 268435456 = MM ^ 134217728 * MM ^ 134217728 := by rw [← pow_add]
  rw [h, hpw27]; rfl
theorem hpw29 : MM ^ 536870912 = ⟨135907267836,22055147896,22055147896,157962415732⟩ := by
  have h : MM ^ 536870912 = MM ^ 268435456 * MM ^ 268435456 := by rw [← pow_add]
  rw [h, hpw28]; rfl
theorem hpw30 : MM ^ 1073741824 = ⟨82622849268,63949767788,63949767788,146572617056⟩ := by
  have h : MM ^ 1073741824 = MM ^ 536870912 * MM ^ 536870912 := by rw [← pow_add]
  rw [h, hpw29]; rfl
theorem hpw31 : MM ^ 2147483648 = ⟨124496604184,29445893489,29445893489,153942497673⟩ := by
  have h : MM ^ 2147483648 = MM ^ 1073741824 * MM ^ 1073741824 := by rw [← pow_add]
  rw [h, hpw30]; rfl
theorem hpw32 : MM ^ 4294967296 = ⟨69527355682,151728037554,151728037554,25936872219⟩ := by
  have h : MM ^ 4294967296 = MM ^ 2147483648 * MM ^ 2147483648 := by rw [← pow_add]
  rw [h, hpw31]; rfl
theorem hpw33 : MM ^ 8589934592 = ⟨167649138019,95234564376,95234564376,67565181378⟩ := by
  have h : MM ^ 8589934592 = MM ^ 4294967296 * MM ^ 4294967296 := by rw [← pow_add]
  rw [h, hpw32]; rfl
theorem hpw34 : MM ^ 17179869184 = ⟨10156357443,42138100865,42138100865,52294458308⟩ := by
  have h : MM ^ 17179869184 = MM ^ 8589934592 * MM ^ 8589934592 := by rw [← pow_add]
  rw [h, hpw33]; rfl
theorem hpw35 : MM ^ 34359738368 = ⟨176491137404,81647376874,81647376874,62819993261⟩ := by
  have h : MM ^ 34359738368 = MM ^ 17179869184 * MM ^ 17179869184 := by rw [← pow_add]
  rw [h, hpw34]; rfl
theorem hpw36 : MM ^ 68719476736 = ⟨152478021259,6643576044,6643576044,159121597303⟩ := by
  have h : MM ^ 68719476736 = MM ^ 34359738368 * MM ^ 34359738368 := by rw [← pow_add]
  rw [h, hpw35]; rfl
theorem hpw37 : MM ^ 137438953472 = ⟨184726218105,130429264574,130429264574,119836961662⟩ := by
  have h : MM ^ 137438953472 = MM ^ 68719476736 * MM ^ 68719476736 := by rw [← pow_add]
  rw [h, hpw36]; rfl

theorem hpowK : MM ^ 249580073233 = ⟨117378126758,21827756563,21827756563,139205883321⟩ := by
  rw [show (249580073233:ℕ) = 1 + (16 + (256 + (4096 + (8192 + (32768 + (65536 + (2097152 + (67108864 + (134217728 + (268435456 + (8589934592 + (34359738368 + (68719476736 + (137438953472)))))))))))))) from rfl]
  simp only [pow_add]
  rw [hpw0, hpw4, hpw8, hpw12, hpw13, hpw15, hpw16, hpw21, hpw26, hpw27, hpw28, hpw33, hpw35, hpw36, hpw37]
  rfl

/-- If two positive numbers `x, y` share a common factor `≥ 2`, the value produced by the
A355898 recurrence, `gcd x y + (x+y)/gcd x y`, can never equal `1 + x + y`. -/
theorem recurrence_contradiction (x y z : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hg2 : 2 ≤ Nat.gcd x y)
    (hdef : z = Nat.gcd x y + (x + y) / Nat.gcd x y)
    (hf1 : z = 1 + x + y) : False := by
  set g := Nat.gcd x y with hgdef
  have hgpos : 0 < g := by omega
  have hgdvd : g ∣ (x + y) := Nat.dvd_add (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  obtain ⟨t, ht⟩ := hgdvd
  have hsdivg : (x + y) / g = t := by rw [ht]; exact Nat.mul_div_cancel_left t hgpos
  rw [hsdivg] at hdef
  have heq : g + t = 1 + g * t := by rw [← hdef, hf1]; linarith [ht]
  have ht1 : t = 1 := by
    have h0 : (g : ℤ) + (t : ℤ) = 1 + (g : ℤ) * (t : ℤ) := by exact_mod_cast heq
    have hz : ((t : ℤ) - 1) * ((g : ℤ) - 1) = 0 := by linear_combination -h0
    rcases mul_eq_zero.mp hz with hh | hh
    · have : (t : ℤ) = 1 := by linarith
      exact_mod_cast this
    · exfalso
      have hg1 : (g : ℤ) = 1 := by linarith
      have : g = 1 := by exact_mod_cast hg1
      omega
  have hsum : x + y = g := by rw [ht, ht1, mul_one]
  have hle : g ≤ y := Nat.le_of_dvd hy (Nat.gcd_dvd_right _ _)
  linarith [hsum, hle, hx]

theorem val3773 : (A355898 3773 : ZMod p) = 77940394258 := by rfl

theorem val3774 : (A355898 3774 : ZMod p) = 99768150821 := by rfl

/--
Disproof of the A355898 conjecture. Formula (1) forces gcd(a(n-1),a(n-2)) = 1 for all
n ≥ 3775. But modulo the prime p = 195318521017, the residue pair vanishes at
m = 3774 + K (K = 249580073233), so gcd(a(m),a(m-1)) > 1, contradicting formula (1).
-/
theorem oeis_a355898_conjecture.disproof :
    ¬ ∀ (n : ℕ), 3775 ≤ n →
      (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
      ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
      ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1) := by
  intro h
  have hrec : ∀ k, A355898 (3775 + k) = 1 + A355898 (3774 + k) + A355898 (3773 + k) := by
    intro k
    have hh := (h (3775 + k) (by omega)).1
    have e1 : 3775 + k - 1 = 3774 + k := by omega
    have e2 : 3775 + k - 2 = 3773 + k := by omega
    rw [e1, e2] at hh; exact hh
  have key : ∀ k, ((A355898 (3773 + k) : ZMod p) + 1, (A355898 (3774 + k) : ZMod p) + 1)
      = M2.act (MM ^ k) ((A355898 3773 : ZMod p) + 1, (A355898 3774 : ZMod p) + 1) := by
    intro k
    induction k with
    | zero => simp only [Nat.add_zero, pow_zero, M2.act_one]
    | succ k ih =>
      have i1 : 3773 + (k+1) = 3774 + k := by omega
      have i2 : 3774 + (k+1) = 3775 + k := by omega
      rw [i1, i2, pow_succ' MM k, M2.act_mul, ← ih]
      have hcast : (A355898 (3775 + k) : ZMod p)
          = 1 + (A355898 (3774 + k) : ZMod p) + (A355898 (3773 + k) : ZMod p) := by
        rw [hrec k]; push_cast; ring
      simp only [M2.act, MM, Prod.mk.injEq]
      exact ⟨by ring, by linear_combination hcast⟩
  -- Instantiate the evolution at k = K
  have hK := key 249580073233
  rw [hpowK] at hK
  have hact : M2.act ⟨117378126758,21827756563,21827756563,139205883321⟩ ((A355898 3773 : ZMod p) + 1, (A355898 3774 : ZMod p) + 1)
      = ((1 : ZMod p), (1 : ZMod p)) := by
    rw [val3773, val3774]; rfl
  rw [hact, Prod.mk.injEq] at hK
  obtain ⟨hK1, hK2⟩ := hK
  have z1 : (A355898 (3773 + 249580073233) : ZMod p) = 0 := add_eq_right.mp hK1
  have z2 : (A355898 (3774 + 249580073233) : ZMod p) = 0 := add_eq_right.mp hK2
  have d2 : p ∣ A355898 (3773 + 249580073233) := (ZMod.natCast_eq_zero_iff _ _).mp z1
  have d1 : p ∣ A355898 (3774 + 249580073233) := (ZMod.natCast_eq_zero_iff _ _).mp z2
  have pos1 : 1 ≤ A355898 (3774 + 249580073233) := by
    have hp := A355898_pos (3773 + 249580073233)
    have e : 3773 + 249580073233 + 1 = 3774 + 249580073233 := by omega
    rwa [e] at hp
  have pos2 : 1 ≤ A355898 (3773 + 249580073233) := by
    have hp := A355898_pos (3772 + 249580073233)
    have e : 3772 + 249580073233 + 1 = 3773 + 249580073233 := by omega
    rwa [e] at hp
  have hstep : ∀ n, A355898 (n+3) = Nat.gcd (A355898 (n+2)) (A355898 (n+1)) +
      (A355898 (n+2) + A355898 (n+1)) / Nat.gcd (A355898 (n+2)) (A355898 (n+1)) := fun n => rfl
  have hdef : A355898 (3775 + 249580073233) = Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233)) + (A355898 (3774 + 249580073233) + A355898 (3773 + 249580073233)) / Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233)) := by
    have hs := hstep (3772 + 249580073233)
    have e3 : 3772 + 249580073233 + 3 = 3775 + 249580073233 := by omega
    have e2 : 3772 + 249580073233 + 2 = 3774 + 249580073233 := by omega
    have e1 : 3772 + 249580073233 + 1 = 3773 + 249580073233 := by omega
    rw [e1, e2, e3] at hs; exact hs
  have hf1 : A355898 (3775 + 249580073233) = 1 + A355898 (3774 + 249580073233) + A355898 (3773 + 249580073233) := hrec 249580073233
  have hpg : p ∣ Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233)) := Nat.dvd_gcd d1 d2
  have hgpos : 0 < Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233)) := Nat.gcd_pos_iff.mpr (Or.inl pos1)
  have hg2 : 2 ≤ Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233)) := by
    have hpd := Nat.le_of_dvd hgpos hpg
    have hp2 : 2 ≤ p := by norm_num
    omega
  exact recurrence_contradiction _ _ _ pos1 pos2 hg2 hdef hf1

