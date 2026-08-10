import Submission.PiLower
open Finset
namespace PartA
set_option maxRecDepth 10000

/-- Binary modular exponentiation with structural `fuel` recursion (kernel-cheap). -/
def mpow : Nat → Nat → Nat → Nat → Nat
  | 0, _, n, _ => 1 % n
  | (fuel+1), b, n, e =>
    match e with
    | 0 => 1 % n
    | (e+1) =>
      let h := mpow fuel b n ((e+1)/2)
      let h2 := (h*h) % n
      if (e+1) % 2 = 1 then (h2 * b) % n else h2

theorem mpow_correct (fuel : ℕ) : ∀ b n e, e < 2^fuel → mpow fuel b n e = b^e % n := by
  induction fuel with
  | zero =>
    intro b n e he
    simp only [pow_zero] at he
    have he0 : e = 0 := by omega
    subst he0; simp [mpow]
  | succ fuel ih =>
    intro b n e he
    match e with
    | 0 => simp [mpow]
    | (e+1) =>
      have hhalf : (e+1)/2 < 2^fuel := by
        have h2 : (e+1) < 2*2^fuel := by rw [pow_succ] at he; omega
        omega
      have hrw : mpow (fuel+1) b n (e+1)
          = (let h := b^((e+1)/2) % n; let h2 := (h*h) % n;
             if (e+1) % 2 = 1 then (h2 * b) % n else h2) := by
        rw [mpow, ih b n ((e+1)/2) hhalf]
      rw [hrw]
      simp only
      set p := (e+1)/2 with hp
      rcases Nat.even_or_odd (e+1) with hev | hodd
      · have h0 : (e+1)%2 = 0 := Nat.even_iff.1 hev
        rw [if_neg (by omega)]
        show (b^p % n)*(b^p % n) ≡ b^(e+1) [MOD n]
        calc (b^p % n)*(b^p % n)
            ≡ b^p*b^p [MOD n] := (Nat.mod_modEq _ _).mul (Nat.mod_modEq _ _)
          _ = b^(e+1) := by rw [← pow_add]; congr 1; omega
      · have h1 : (e+1)%2 = 1 := Nat.odd_iff.1 hodd
        rw [if_pos h1]
        show ((b^p % n)*(b^p % n) % n) * b ≡ b^(e+1) [MOD n]
        calc ((b^p % n)*(b^p % n) % n) * b
            ≡ (b^p*b^p)*b [MOD n] :=
              Nat.ModEq.mul_right b
                ((Nat.mod_modEq _ _).trans ((Nat.mod_modEq _ _).mul (Nat.mod_modEq _ _)))
          _ = b^(e+1) := by rw [← pow_add, ← pow_succ]; congr 1; omega

/-- Per-class check: class `k0`. `c` is the canonical residue of `2^k0 - 270024 - k0` mod N. -/
def passes (k0 : ℕ) : Bool :=
  let c := (mpow 20 2 833782 k0 + 833782 - (270024 + k0)) % 833782
  (c % 34 != 0) || decide (2282 ≤ (11366 * (c / 34)) % 24523)

/-- Balanced divide-and-conquer scan with structural `fuel` recursion. -/
def chk : Nat → Nat → Nat → Bool
  | 0, lo, w => match w with | 0 => true | 1 => passes lo | _ => false
  | (fuel+1), lo, w =>
    match w with
    | 0 => true
    | 1 => passes lo
    | (w+2) => let h := (w+2)/2; chk fuel lo h && chk fuel (lo+h) (w+2-h)

theorem chk_spec : ∀ fuel lo w, chk fuel lo w = true →
    ∀ r, lo ≤ r → r < lo + w → passes r = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo w hchk r hlo hr
    match w with
    | 0 => omega
    | 1 => simp only [chk] at hchk
           have : r = lo := by omega
           rw [this]; exact hchk
    | (w+2) => simp only [chk] at hchk; exact absurd hchk (by decide)
  | succ fuel ih =>
    intro lo w hchk r hlo hr
    match w with
    | 0 => omega
    | 1 => simp only [chk] at hchk
           have : r = lo := by omega
           rw [this]; exact hchk
    | (w+2) =>
        simp only [chk] at hchk
        rw [Bool.and_eq_true] at hchk
        obtain ⟨h1, h2⟩ := hchk
        set hh := (w+2)/2 with hhdef
        by_cases hc : r < lo + hh
        · exact ih lo hh h1 r hlo hc
        · exact ih (lo+hh) (w+2-hh) h2 r (by omega) (by omega)

end PartA
