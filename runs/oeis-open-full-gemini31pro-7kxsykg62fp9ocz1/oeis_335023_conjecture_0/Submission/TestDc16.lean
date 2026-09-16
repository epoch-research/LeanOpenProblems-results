import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def P16 (a : ℤ) : ℤ :=
  (a^16 + 120*a^15 + 6580*a^14 + 218400*a^13 + 4899622*a^12 + 78558480*a^11 + 928095740*a^10 + 8207628000*a^9 + 54631129553*a^8 + 272803210680*a^7 + 1009672107080*a^6 + 2706813345600*a^5 + 5056995703824*a^4 + 6165817614720*a^3 + 4339163001600*a^2 + 1307674368000*a)

def F16_even (a : ℤ) : ℤ :=
  (8*a^14 + 840*a^13 + 40096*a^12 + 1151640*a^11 + 22202544*a^10 + 303445800*a^9 + 3026649568*a^8 + 22340419080*a^7 + 122399846408*a^6 + 494509725360*a^5 + 1448487222336*a^4 + 2983207510080*a^3 + 4096543040640*a^2 + 3390612825600*a + 1307674368000)

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

theorem test : (dc_fast 30 2 (2 + 16 * 12500)).2 ≠ 0 := by decide
