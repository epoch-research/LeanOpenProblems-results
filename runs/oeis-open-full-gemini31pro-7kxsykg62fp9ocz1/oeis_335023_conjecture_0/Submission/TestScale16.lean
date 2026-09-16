import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0

def P16 (a : ℤ) : ℤ :=
  ((((((((((((((((1) * a + 120) * a + 6580) * a + 218400) * a + 4899622) * a + 78558480) * a + 928095740) * a + 8207628000) * a + 54631129553) * a + 272803210680) * a + 1009672107080) * a + 2706813345600) * a + 5056995703824) * a + 6165817614720) * a + 4339163001600) * a + 1307674368000) * a + 0

def F16_even (a : ℤ) : ℤ :=
  ((((((((((((((8) * a + 840) * a + 40096) * a + 1151640) * a + 22202544) * a + 303445800) * a + 3026649568) * a + 22340419080) * a + 122399846408) * a + 494509725360) * a + 1448487222336) * a + 2983207510080) * a + 4096543040640) * a + 3390612825600) * a + 1307674368000

def dc_fast (fuel a b : ℕ) : ℕ × ℤ :=
  match fuel with
  | 0 => (1, 0)
  | fuel' + 1 =>
    if b ≤ a then (1, 0)
    else if b = a + 16 then
      ((P16 a).toNat, if a % 2 = 0 then F16_even a else -F16_even a)
    else if b = a + 1 then (a, if a % 2 = 0 then (1:ℤ) else -1)
    else
      let m := (a + b) / 2
      let (p1, f1) := dc_fast fuel' a m
      let (p2, f2) := dc_fast fuel' m b
      (p1 * p2, f1 * (p2 : ℤ) + (p1 : ℤ) * f2)

theorem test10k : (dc_fast 30 2 10002).2 ≠ 0 := by decide
