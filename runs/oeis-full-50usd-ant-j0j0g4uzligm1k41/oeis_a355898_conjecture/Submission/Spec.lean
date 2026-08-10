import FormalConjectures.Util.ProblemImports

open Nat
set_option maxRecDepth 1000000

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

/-- One step of the defining recurrence (holds by `rfl`). -/
theorem A355898_rec (n : ℕ) :
    A355898 (n+3) = Nat.gcd (A355898 (n+2)) (A355898 (n+1))
      + (A355898 (n+2) + A355898 (n+1)) / Nat.gcd (A355898 (n+2)) (A355898 (n+1)) := rfl

/-- The sequence is strictly positive (from index 1 on). -/
theorem A355898_pos : ∀ k, 0 < A355898 (k+1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => decide
    | 1 => decide
    | (j+2) =>
      rw [show j+2+1 = j+3 from rfl, A355898_rec]
      have h2 : 0 < A355898 (j+1) := ih j (by omega)
      have hg : 0 < Nat.gcd (A355898 (j+2)) (A355898 (j+1)) := Nat.gcd_pos_of_pos_right _ h2
      exact lt_of_lt_of_le hg (Nat.le_add_right _ _)

/-! ### Fast Fibonacci modulo `p` via binary fast-doubling -/

/-- Doubling step (mod `p`): from `(fib k % p, fib (k+1) % p)` produce the pair for `2k+b`. -/
def fstep (p : ℕ) (s : ℕ × ℕ) (b : Bool) : ℕ × ℕ :=
  let x := s.1; let y := s.2
  if b then ((y*y + x*x) % p, (y*(2*x+y)) % p)
  else ((x*(2*y + (p - x))) % p, (y*y + x*x) % p)

theorem fstep_spec (p k x y : ℕ) (hxp : x ≤ p)
    (hx : x ≡ fib k [MOD p]) (hy : y ≡ fib (k+1) [MOD p]) (b : Bool) :
    (fstep p (x,y) b).1 ≡ fib (2*k + (if b then 1 else 0)) [MOD p] ∧
    (fstep p (x,y) b).2 ≡ fib (2*k + (if b then 1 else 0) + 1) [MOD p] := by
  have hyy : y*y ≡ fib (k+1)^2 [MOD p] := by rw [pow_two]; exact hy.mul hy
  have hxx : x*x ≡ fib k^2 [MOD p] := by rw [pow_two]; exact hx.mul hx
  have hd : (y*y + x*x) ≡ fib (2*k+1) [MOD p] := by
    rw [fib_two_mul_add_one]; exact hyy.add hxx
  cases b with
  | true =>
    refine ⟨?_, ?_⟩
    · simp only [fstep, if_true]
      simpa using (Nat.mod_modEq _ _).trans hd
    · simp only [fstep, if_true]
      have hxy : (2*x+y) ≡ (2*fib k + fib (k+1)) [MOD p] := (hx.mul_left 2).add hy
      have : (y*(2*x+y)) ≡ fib (2*k+2) [MOD p] := by
        rw [fib_two_mul_add_two]; exact hy.mul hxy
      simpa using (Nat.mod_modEq _ _).trans this
  | false =>
    refine ⟨?_, ?_⟩
    · simp only [fstep]
      have hle : fib k ≤ 2 * fib (k+1) := le_trans fib_le_fib_succ (by omega)
      have e1 : (2*y + (p - x)) + x = 2*y + p := by omega
      have e2 : (2*fib (k+1) - fib k) + fib k = 2 * fib (k+1) := by omega
      have hsub : (2*y + (p - x)) ≡ (2*fib (k+1) - fib k) [MOD p] := by
        apply Nat.ModEq.add_right_cancel' x
        rw [e1]
        calc 2*y + p ≡ 2*y + 0 [MOD p] :=
                (Nat.ModEq.refl _).add (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
          _ = 2*y := by ring
          _ ≡ 2 * fib (k+1) [MOD p] := hy.mul_left 2
          _ = (2*fib (k+1) - fib k) + fib k := e2.symm
          _ ≡ (2*fib (k+1) - fib k) + x [MOD p] := (Nat.ModEq.refl _).add hx.symm
      have : (x*(2*y + (p - x))) ≡ fib (2*k) [MOD p] := by
        rw [fib_two_mul]; exact hx.mul hsub
      simpa using (Nat.mod_modEq _ _).trans this
    · simp only [fstep]
      simpa using (Nat.mod_modEq _ _).trans hd

/-- Value of a list of bits, most-significant first. -/
def bval : List Bool → ℕ := fun L => L.foldl (fun acc b => 2*acc + (if b then 1 else 0)) 0
/-- Fast-doubling fold giving `(fib (bval L) % p, fib (bval L + 1) % p)`. -/
def ffold (p : ℕ) : List Bool → ℕ × ℕ := fun L => L.foldl (fstep p) (0 % p, 1 % p)

theorem ffold_spec (p : ℕ) (hp : 2 ≤ p) (L : List Bool) :
    (ffold p L).1 ≤ p ∧ (ffold p L).2 ≤ p ∧
    (ffold p L).1 ≡ fib (bval L) [MOD p] ∧ (ffold p L).2 ≡ fib (bval L + 1) [MOD p] := by
  induction L using List.reverseRecOn with
  | nil =>
    simp only [ffold, bval, List.foldl_nil]
    refine ⟨?_, ?_, ?_, ?_⟩
    · show 0 % p ≤ p; rw [Nat.zero_mod]; exact Nat.zero_le p
    · show 1 % p ≤ p; exact le_of_lt (Nat.mod_lt 1 (by omega))
    · show 0 % p ≡ fib 0 [MOD p]; simpa using (Nat.mod_modEq 0 p)
    · show 1 % p ≡ fib (0+1) [MOD p]; simpa using (Nat.mod_modEq 1 p)
  | append_singleton L b ih =>
    obtain ⟨hx1, hx2, hmx, hmy⟩ := ih
    have hfold : ffold p (L ++ [b]) = fstep p (ffold p L) b := by
      simp only [ffold, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hbv : bval (L ++ [b]) = 2 * bval L + (if b then 1 else 0) := by
      simp only [bval, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hfold, hbv]
    have hpair : ffold p L = ((ffold p L).1, (ffold p L).2) := rfl
    rw [hpair]
    obtain ⟨s1, s2⟩ := fstep_spec p (bval L) (ffold p L).1 (ffold p L).2 hx1 hmx hmy b
    refine ⟨?_, ?_, s1, s2⟩
    · rcases b with _ | _ <;> simp only [fstep] <;> exact le_of_lt (Nat.mod_lt _ (by omega))
    · rcases b with _ | _ <;> simp only [fstep] <;> exact le_of_lt (Nat.mod_lt _ (by omega))

/-- Linear (Fibonacci) closed form for any sequence satisfying the Fibonacci recurrence. -/
theorem fib_lin (f : ℕ → ℕ) (hrec : ∀ j, f (j+2) = f (j+1) + f j) :
    ∀ j, f (j+1) = f 1 * fib (j+1) + f 0 * fib j := by
  intro j
  induction j using Nat.twoStepInduction with
  | zero => simp
  | one => simp [hrec 0, Nat.fib_two]
  | more j ih1 ih2 =>
      rw [hrec (j+1), ih2, ih1, fib_add_two (n := j+1), fib_add_two (n := j)]
      ring

/-- The bit-list (MSB first) of `249580073232`. -/
def Lwit : List Bool := [true, true, true, false, true, false, false, false, false, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, false, false, true, false, false, false, true, false, false, false, false]

/-- **Disproof.** The three closed forms do *not* all hold for every `n ≥ 3775`:
at `n = 249580077008` the gcd `gcd(a(n-1), a(n-2))` is divisible by the prime
`195318521017`, so it is `> 1` and the first formula `a(n) = 1 + a(n-1) + a(n-2)` fails. -/
theorem oeis_a355898_conjecture.disproof :
  ¬ ∀ (n : ℕ), 3775 ≤ n →
  (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
  ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
  ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1) := by
  intro H
  -- Closed form for the sequence in the "Fibonacci regime", assuming the conjecture.
  have hcf := fib_lin (fun j => A355898 (j + 3773) + 1) (by
    intro j
    show A355898 (j+2+3773) + 1 = (A355898 (j+1+3773) + 1) + (A355898 (j+3773) + 1)
    have hH := (H (j+3775) (by omega)).1
    rw [show j+2+3773 = j+3775 from by omega, hH,
        show j+3775-1 = j+1+3773 from by omega, show j+3775-2 = j+3773 from by omega]
    omega)
  have closed : ∀ j, A355898 (j+3774) + 1
      = (A355898 3774 + 1) * fib (j+1) + (A355898 3773 + 1) * fib j := by
    intro j
    have h := hcf j
    simp only [] at h
    rw [show j+1+3773 = j+3774 from by omega,
        show (1:ℕ)+3773 = 3774 from by norm_num,
        show (0:ℕ)+3773 = 3773 from by norm_num] at h
    exact h
  -- Fibonacci values modulo p from the fast-doubling fold.
  obtain ⟨_, _, hff1, hff2⟩ := ffold_spec 195318521017 (by norm_num) Lwit
  rw [show bval Lwit = 249580073232 from by rfl,
      show ffold 195318521017 Lwit = (117378126758, 21827756563) from by rfl] at hff1 hff2
  simp only [] at hff1 hff2
  have hfa : fib 249580073232 ≡ 117378126758 [MOD 195318521017] := hff1.symm
  have hfb : fib 249580073233 ≡ 21827756563 [MOD 195318521017] := by
    have := hff2.symm; rwa [show 249580073232+1 = 249580073233 from by norm_num] at this
  have hfc : fib 249580073234 ≡ 139205883321 [MOD 195318521017] := by
    have h := fib_add_two (n := 249580073232)
    rw [show 249580073232+2 = 249580073234 from by norm_num,
        show 249580073232+1 = 249580073233 from by norm_num] at h
    rw [h]
    calc fib 249580073232 + fib 249580073233
        ≡ 117378126758 + 21827756563 [MOD 195318521017] := hfa.add hfb
      _ = 139205883321 := by norm_num
  -- Seed values.
  have hV3774 : A355898 3774 = 58247620166949433924152349110387952083697979943894432862563828976040095229520447551846447106151838744759854302693877131497631690251007647345990824945923089962629840263458365713419764969401061223771086474022889794898006618157003102858034604369810330403334719184536749507414607510201847709900422830948846697746280327160364518807058513260008283 := by rfl
  have hV3773 : A355898 3773 = 7425763529563641656343950118919476361854496605895809221806730373403166836250554598912216231675893720246035801259006550047856708037120829047465510779038156824824471379179617511560002202519545851588002449939311799386981815701822134145342315490302441466084428121032068752422449560944883235622403419180199789756819086776097880710867416354388617 := by rfl
  -- p divides a(m) and a(m+1).
  have hdvd_m : 195318521017 ∣ A355898 249580077006 := by
    have hc := closed 249580073232
    rw [show (249580073232:ℕ)+3774 = 249580077006 from by norm_num,
        show (249580073232:ℕ)+1 = 249580073233 from by norm_num, hV3774, hV3773] at hc
    have hmod : A355898 249580077006 + 1 ≡ 1 [MOD 195318521017] := by
      rw [hc]
      calc (58247620166949433924152349110387952083697979943894432862563828976040095229520447551846447106151838744759854302693877131497631690251007647345990824945923089962629840263458365713419764969401061223771086474022889794898006618157003102858034604369810330403334719184536749507414607510201847709900422830948846697746280327160364518807058513260008283 + 1) * fib 249580073233 + (7425763529563641656343950118919476361854496605895809221806730373403166836250554598912216231675893720246035801259006550047856708037120829047465510779038156824824471379179617511560002202519545851588002449939311799386981815701822134145342315490302441466084428121032068752422449560944883235622403419180199789756819086776097880710867416354388617 + 1) * fib 249580073232
          ≡ (58247620166949433924152349110387952083697979943894432862563828976040095229520447551846447106151838744759854302693877131497631690251007647345990824945923089962629840263458365713419764969401061223771086474022889794898006618157003102858034604369810330403334719184536749507414607510201847709900422830948846697746280327160364518807058513260008283 + 1) * 21827756563 + (7425763529563641656343950118919476361854496605895809221806730373403166836250554598912216231675893720246035801259006550047856708037120829047465510779038156824824471379179617511560002202519545851588002449939311799386981815701822134145342315490302441466084428121032068752422449560944883235622403419180199789756819086776097880710867416354388617 + 1) * 117378126758 [MOD 195318521017] :=
            (hfb.mul_left _).add (hfa.mul_left _)
        _ ≡ 1 [MOD 195318521017] := by decide
    have : A355898 249580077006 + 1 ≡ 0 + 1 [MOD 195318521017] := by simpa using hmod
    exact (Nat.modEq_zero_iff_dvd).mp (Nat.ModEq.add_right_cancel' 1 this)
  have hdvd_m1 : 195318521017 ∣ A355898 249580077007 := by
    have hc := closed 249580073233
    rw [show (249580073233:ℕ)+3774 = 249580077007 from by norm_num,
        show (249580073233:ℕ)+1 = 249580073234 from by norm_num, hV3774, hV3773] at hc
    have hmod : A355898 249580077007 + 1 ≡ 1 [MOD 195318521017] := by
      rw [hc]
      calc (58247620166949433924152349110387952083697979943894432862563828976040095229520447551846447106151838744759854302693877131497631690251007647345990824945923089962629840263458365713419764969401061223771086474022889794898006618157003102858034604369810330403334719184536749507414607510201847709900422830948846697746280327160364518807058513260008283 + 1) * fib 249580073234 + (7425763529563641656343950118919476361854496605895809221806730373403166836250554598912216231675893720246035801259006550047856708037120829047465510779038156824824471379179617511560002202519545851588002449939311799386981815701822134145342315490302441466084428121032068752422449560944883235622403419180199789756819086776097880710867416354388617 + 1) * fib 249580073233
          ≡ (58247620166949433924152349110387952083697979943894432862563828976040095229520447551846447106151838744759854302693877131497631690251007647345990824945923089962629840263458365713419764969401061223771086474022889794898006618157003102858034604369810330403334719184536749507414607510201847709900422830948846697746280327160364518807058513260008283 + 1) * 139205883321 + (7425763529563641656343950118919476361854496605895809221806730373403166836250554598912216231675893720246035801259006550047856708037120829047465510779038156824824471379179617511560002202519545851588002449939311799386981815701822134145342315490302441466084428121032068752422449560944883235622403419180199789756819086776097880710867416354388617 + 1) * 21827756563 [MOD 195318521017] :=
            (hfc.mul_left _).add (hfb.mul_left _)
        _ ≡ 1 [MOD 195318521017] := by decide
    have : A355898 249580077007 + 1 ≡ 0 + 1 [MOD 195318521017] := by simpa using hmod
    exact (Nat.modEq_zero_iff_dvd).mp (Nat.ModEq.add_right_cancel' 1 this)
  -- positivity
  have hpos_m : 0 < A355898 249580077006 := by
    have := A355898_pos 249580077005; rwa [show 249580077005+1 = 249580077006 from by norm_num] at this
  have hpos_m1 : 0 < A355898 249580077007 := by
    have := A355898_pos 249580077006; rwa [show 249580077006+1 = 249580077007 from by norm_num] at this
  -- the recurrence at n = 249580077005
  have hreceq := A355898_rec 249580077005
  rw [show (249580077005:ℕ)+3 = 249580077008 from by norm_num,
      show (249580077005:ℕ)+2 = 249580077007 from by norm_num,
      show (249580077005:ℕ)+1 = 249580077006 from by norm_num] at hreceq
  -- the first conjectured formula at n = 249580077008
  have hP1 := (H 249580077008 (by norm_num)).1
  rw [show (249580077008:ℕ)-1 = 249580077007 from by norm_num,
      show (249580077008:ℕ)-2 = 249580077006 from by norm_num, hreceq] at hP1
  -- contradiction
  set am := A355898 249580077006 with ham
  set am1 := A355898 249580077007 with ham1
  set g := Nat.gcd am1 am with hgdef
  have hg_am : g ∣ am := Nat.gcd_dvd_right am1 am
  have hg_am1 : g ∣ am1 := Nat.gcd_dvd_left am1 am
  have hpg : 195318521017 ∣ g := Nat.dvd_gcd hdvd_m1 hdvd_m
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ hpos_m1
  have hg2 : 2 ≤ g := le_trans (by norm_num) (Nat.le_of_dvd hg_pos hpg)
  have hSdvd : g ∣ (am1 + am) := Nat.dvd_add hg_am1 hg_am
  obtain ⟨t, ht⟩ := hSdvd
  have hdiv : (am1 + am) / g = t := by rw [ht]; exact Nat.mul_div_cancel_left t hg_pos
  rw [hdiv] at hP1
  -- hP1 : g + t = 1 + am1 + am ; and am1 + am = g * t
  have ham_le : g ≤ am := Nat.le_of_dvd hpos_m hg_am
  have hge : g + 1 ≤ g * t := by rw [← ht]; omega
  have ht2 : 2 ≤ t := by omega
  have hgt2g : 2 * g ≤ g * t := by
    have := Nat.mul_le_mul_left g ht2; simpa [Nat.mul_comm] using this
  have hgt2t : 2 * t ≤ g * t := by
    have := Nat.mul_le_mul_right t hg2; simpa using this
  omega

