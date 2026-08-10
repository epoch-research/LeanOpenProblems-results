import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 8000

def A355898 : ℕ → ℕ
| 0 => 0
| 1 => 1
| 2 => 1
| n + 3 =>
  let an_minus_1 := A355898 (n + 2)
  let an_minus_2 := A355898 (n + 1)
  let g := Nat.gcd an_minus_1 an_minus_2
  g + (an_minus_1 + an_minus_2) / g

theorem A_rec (n : ℕ) :
    A355898 (n+3) = Nat.gcd (A355898 (n+2)) (A355898 (n+1))
      + (A355898 (n+2) + A355898 (n+1)) / Nat.gcd (A355898 (n+2)) (A355898 (n+1)) := rfl

/-! ## Positivity -/
theorem Apos : ∀ n, 1 ≤ A355898 (n+1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    match n with
    | 0 => decide
    | 1 => decide
    | k+2 =>
      rw [show k+2+1 = k+3 from rfl, A_rec]
      have h1 : 1 ≤ A355898 (k+2) := IH (k+1) (by omega)
      have h2 : 1 ≤ A355898 (k+1) := IH k (by omega)
      have hg : 0 < Nat.gcd (A355898 (k+2)) (A355898 (k+1)) := by
        rw [Nat.gcd_pos_iff]; left; omega
      exact le_trans hg (Nat.le_add_right _ _)

/-! ## Segmented evaluation of seeds a(3773), a(3774) -/
def Astep : ℕ × ℕ → ℕ × ℕ := fun p => (p.2, Nat.gcd p.2 p.1 + (p.2 + p.1) / Nat.gcd p.2 p.1)
def Aiter : ℕ → ℕ × ℕ
| 0 => (1,1)
| n+1 => Astep (Aiter n)
def AiterFrom (start : ℕ×ℕ) : ℕ → ℕ×ℕ
| 0 => start
| n+1 => Astep (AiterFrom start n)

theorem Aiter_add (a b : ℕ) : Aiter (a+b) = AiterFrom (Aiter a) b := by
  induction b with
  | zero => rfl
  | succ k ih => simp [Aiter, AiterFrom, ih]

theorem Aiter_correct (n : ℕ) : Aiter n = (A355898 (n+1), A355898 (n+2)) := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Aiter, ih, show k+1+2 = k+3 from rfl, A_rec]; rfl

theorem e1 : Aiter 1000 = (857849530606042011074830162029609056836142056053432234500214934736158102606870905673, 1649361868662090153303910549715102733645372464449722097662281114035603758181244349143) := by rfl
theorem e2 : Aiter 2000 = (3016310876544471039814211841161237135686166051819283926749201012500251985148689641005382234349889873473817198348083105332892079916102889196339987199121080815445028636362301568083905, 4870834809367087528565680855621871407973482199145088253299489849442888968616012834682202004063575402331653573094937185350034208679117333937383628437168745003888235439238959915061193) := by
  rw [show (2000:ℕ)=1000+1000 from rfl, Aiter_add, e1]; rfl
theorem e3 : Aiter 3000 = (2252100851515924337420712023090535791161228994963661906941246563757272408118701810882083719598383517894888766401650207550025252428618651916349548698397556216037468735105831539127884356365207584345983877997538910998006627494516449528278950666649538557693616077518388252436853, 3620515055665532360422328989354131977678080686610645643700783568117573724781138066905221475268276464450806379641167737675956330738667559167750992362425808603769007003161571941034766362295332703286037883775794573756031657645003290528249711652420438045833994511757700259945673) := by
  rw [show (3000:ℕ)=2000+1000 from rfl, Aiter_add, e2]; rfl
theorem e4 : Aiter 3772 = (7425763529563641656343950118919476361854496605895809221806730373403166836250554598912216231675893720246035801259006550047856708037120829047465510779038156824824471379179617511560002202519545851588002449939311799386981815701822134145342315490302441466084428121032068752422449560944883235622403419180199789756819086776097880710867416354388617, 58247620166949433924152349110387952083697979943894432862563828976040095229520447551846447106151838744759854302693877131497631690251007647345990824945923089962629840263458365713419764969401061223771086474022889794898006618157003102858034604369810330403334719184536749507414607510201847709900422830948846697746280327160364518807058513260008283) := by
  rw [show (3772:ℕ)=3000+772 from rfl, Aiter_add, e3]; rfl

theorem a3773_val : A355898 3773 = 7425763529563641656343950118919476361854496605895809221806730373403166836250554598912216231675893720246035801259006550047856708037120829047465510779038156824824471379179617511560002202519545851588002449939311799386981815701822134145342315490302441466084428121032068752422449560944883235622403419180199789756819086776097880710867416354388617 := by
  have h := Aiter_correct 3772; rw [e4] at h; simpa using (congrArg Prod.fst h).symm
theorem a3774_val : A355898 3774 = 58247620166949433924152349110387952083697979943894432862563828976040095229520447551846447106151838744759854302693877131497631690251007647345990824945923089962629840263458365713419764969401061223771086474022889794898006618157003102858034604369810330403334719184536749507414607510201847709900422830948846697746280327160364518807058513260008283 := by
  have h := Aiter_correct 3772; rw [e4] at h; simpa using (congrArg Prod.snd h).symm

/-! ## Fast doubling Fibonacci in a CommRing -/
def fibPair {R : Type*} [CommRing R] (fuel : ℕ) (n : ℕ) : R × R :=
  match fuel with
  | 0 => (0,1)
  | fuel+1 =>
    if n = 0 then (0,1)
    else
      let k := n / 2
      let p := fibPair fuel k
      let a := p.1
      let b := p.2
      let c := a*(2*b - a)
      let d := a*a + b*b
      if n % 2 = 0 then (c, d) else (d, c+d)

theorem fibPair_correct {R : Type*} [CommRing R] (fuel : ℕ) :
    ∀ n : ℕ, n < 2^fuel →
      fibPair fuel n = ((Nat.fib n : R), (Nat.fib (n+1) : R)) := by
  induction fuel with
  | zero => intro n hn; simp only [pow_zero, Nat.lt_one_iff] at hn; subst hn; simp [fibPair]
  | succ f ih =>
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [fibPair]
    · have hn0 : ¬ n = 0 := by omega
      have hk : n / 2 < 2^f := by apply Nat.div_lt_of_lt_mul; rw [pow_succ] at hn; omega
      have ihk := ih (n/2) hk
      have hle : Nat.fib (n/2) ≤ 2 * Nat.fib (n/2+1) := by
        have := Nat.fib_le_fib_succ (n := n/2); omega
      have h2k : ((Nat.fib (2*(n/2)) : R)) = (Nat.fib (n/2)) * (2 * (Nat.fib (n/2+1)) - (Nat.fib (n/2))) := by
        rw [Nat.fib_two_mul]; push_cast [Nat.cast_sub hle]; ring
      have h2k1 : ((Nat.fib (2*(n/2)+1) : R)) = (Nat.fib (n/2))*(Nat.fib (n/2)) + (Nat.fib (n/2+1))*(Nat.fib (n/2+1)) := by
        rw [Nat.fib_two_mul_add_one]; push_cast; ring
      rw [fibPair]
      simp only [if_neg hn0, ihk]
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · have hev : n % 2 = 0 := by omega
        have he2 : 2*(n/2) = n := by omega
        rw [he2] at h2k h2k1
        rw [if_pos hev, Prod.mk.injEq]
        exact ⟨h2k.symm, h2k1.symm⟩
      · have hod : ¬ n % 2 = 0 := by omega
        have ho : 2*(n/2)+1 = n := by omega
        rw [if_neg hod, Prod.mk.injEq]
        refine ⟨?_, ?_⟩
        · rw [← h2k1, ho]
        · have e : n+1 = (2*(n/2))+2 := by omega
          rw [e, Nat.fib_add_two]; push_cast; rw [h2k, h2k1]

abbrev pp : ℕ := 195318521017

/-- The hypothesis `f1` extracted from the conjecture. -/
private abbrev F1 : Prop :=
  ∀ n, 3775 ≤ n → A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2)

/-- Under `f1`, the sequence (plus one) follows the Fibonacci recurrence,
with seeds at indices 3773 and 3774. -/
theorem clf (f1 : F1) :
    ∀ j, A355898 (3774 + j) + 1
      = (A355898 3774 + 1) * Nat.fib (j + 1) + (A355898 3773 + 1) * Nat.fib j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IH =>
    rcases j with _ | _ | i
    · simp [Nat.fib_one, Nat.fib_zero]
    · have h := f1 3775 (by norm_num)
      simp only [show (3775:ℕ)-1=3774 from rfl, show (3775:ℕ)-2=3773 from rfl] at h
      show A355898 3775 + 1 = _
      rw [Nat.fib_two, Nat.fib_one]; omega
    · have hi1 := IH (i+1) (by omega)
      have hi0 := IH i (by omega)
      have hf := f1 (3776+i) (by omega)
      simp only [show 3776+i-1 = 3775+i from by omega, show 3776+i-2=3774+i from by omega] at hf
      rw [show 3774+(i+2) = 3776+i from by omega]
      rw [show 3774+(i+1) = 3775+i from by omega, show i+1+1 = i+2 from by omega] at hi1
      have gA : Nat.fib (i+2+1) = Nat.fib (i+1) + Nat.fib (i+2) := by
        rw [show i+2+1 = (i+1)+2 from by omega, Nat.fib_add_two]
      have gB : Nat.fib (i+2) = Nat.fib i + Nat.fib (i+1) := Nat.fib_add_two
      rw [gB] at hi1
      rw [gA, gB]
      ring_nf at hi1 hi0 ⊢
      linarith [hi1, hi0, hf]

/-- The prime `pp = 195318521017` divides `a(n*-1)` where `n* = 249580077008`. -/
theorem dvd_N1 (f1 : F1) : pp ∣ A355898 249580077007 := by
  have Eq1 := clf f1 249580073233
  rw [show (3774+249580073233:ℕ)=249580077007 from by norm_num] at Eq1
  have corr1 := fibPair_correct (R := ZMod pp) 40 249580073233 (by norm_num)
  have ev1 : fibPair (R := ZMod pp) 40 249580073233 = (21827756563, 139205883321) := by decide
  rw [ev1] at corr1
  have hf_a : (Nat.fib 249580073233 : ZMod pp) = 21827756563 := (congrArg Prod.fst corr1).symm
  have hf_b : (Nat.fib (249580073233+1) : ZMod pp) = 139205883321 := (congrArg Prod.snd corr1).symm
  have hm74 : A355898 3774 % pp = 99768150821 := by rw [a3774_val]; rfl
  have hm73 : A355898 3773 % pp = 77940394258 := by rw [a3773_val]; rfl
  have hr74 : (A355898 3774 : ZMod pp) = 99768150821 := by
    rw [← ZMod.natCast_mod (A355898 3774) pp, hm74]; norm_cast
  have hr73 : (A355898 3773 : ZMod pp) = 77940394258 := by
    rw [← ZMod.natCast_mod (A355898 3773) pp, hm73]; norm_cast
  have C1 : ((A355898 249580077007 + 1 : ℕ) : ZMod pp)
      = (((A355898 3774 + 1) * Nat.fib (249580073233+1)
          + (A355898 3773 + 1) * Nat.fib 249580073233 : ℕ) : ZMod pp) := congrArg _ Eq1
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at C1
  rw [hr74, hr73, hf_b, hf_a] at C1
  have hR1 : ((99768150821 : ZMod pp) + 1) * 139205883321
      + ((77940394258 : ZMod pp) + 1) * 21827756563 = 1 := by rfl
  rw [hR1] at C1
  have z1 : (A355898 249580077007 : ZMod pp) = 0 := by rw [add_eq_right] at C1; exact C1
  exact (CharP.cast_eq_zero_iff (ZMod pp) pp _).mp z1

/-- The prime `pp = 195318521017` divides `a(n*-2)` where `n* = 249580077008`. -/
theorem dvd_N2 (f1 : F1) : pp ∣ A355898 249580077006 := by
  have Eq2 := clf f1 249580073232
  rw [show (3774+249580073232:ℕ)=249580077006 from by norm_num] at Eq2
  have corr2 := fibPair_correct (R := ZMod pp) 40 249580073232 (by norm_num)
  have ev2 : fibPair (R := ZMod pp) 40 249580073232 = (117378126758, 21827756563) := by decide
  rw [ev2] at corr2
  have hf_c : (Nat.fib 249580073232 : ZMod pp) = 117378126758 := (congrArg Prod.fst corr2).symm
  have hf_d : (Nat.fib (249580073232+1) : ZMod pp) = 21827756563 := (congrArg Prod.snd corr2).symm
  have hm74 : A355898 3774 % pp = 99768150821 := by rw [a3774_val]; rfl
  have hm73 : A355898 3773 % pp = 77940394258 := by rw [a3773_val]; rfl
  have hr74 : (A355898 3774 : ZMod pp) = 99768150821 := by
    rw [← ZMod.natCast_mod (A355898 3774) pp, hm74]; norm_cast
  have hr73 : (A355898 3773 : ZMod pp) = 77940394258 := by
    rw [← ZMod.natCast_mod (A355898 3773) pp, hm73]; norm_cast
  have C2 : ((A355898 249580077006 + 1 : ℕ) : ZMod pp)
      = (((A355898 3774 + 1) * Nat.fib (249580073232+1)
          + (A355898 3773 + 1) * Nat.fib 249580073232 : ℕ) : ZMod pp) := congrArg _ Eq2
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at C2
  rw [hr74, hr73, hf_d, hf_c] at C2
  have hR2 : ((99768150821 : ZMod pp) + 1) * 21827756563
      + ((77940394258 : ZMod pp) + 1) * 117378126758 = 1 := by rfl
  rw [hR2] at C2
  have z2 : (A355898 249580077006 : ZMod pp) = 0 := by rw [add_eq_right] at C2; exact C2
  exact (CharP.cast_eq_zero_iff (ZMod pp) pp _).mp z2

theorem oeis_a355898_conjecture.disproof :
  ¬ ∀ (n : ℕ), 3775 ≤ n →
    (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
    ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
    ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1) := by
  intro H
  have f1 : F1 := fun n h => (H n h).1
  have dvd1 : pp ∣ A355898 249580077007 := dvd_N1 f1
  have dvd2 : pp ∣ A355898 249580077006 := dvd_N2 f1
  have arec := A_rec 249580077005
  rw [show (249580077005+3:ℕ)=249580077008 from by norm_num,
      show (249580077005+2:ℕ)=249580077007 from by norm_num,
      show (249580077005+1:ℕ)=249580077006 from by norm_num] at arec
  have hf1 := f1 249580077008 (by norm_num)
  rw [show (249580077008-1:ℕ)=249580077007 from by norm_num,
      show (249580077008-2:ℕ)=249580077006 from by norm_num] at hf1
  set g := Nat.gcd (A355898 249580077007) (A355898 249580077006) with hgdef
  have hN1pos : 1 ≤ A355898 249580077007 := by have := Apos 249580077006; simpa using this
  have hN2pos : 1 ≤ A355898 249580077006 := by have := Apos 249580077005; simpa using this
  have hgpos : 0 < g := by rw [hgdef, Nat.gcd_pos_iff]; left; omega
  have hgN1 : g ≤ A355898 249580077007 := Nat.le_of_dvd hN1pos (Nat.gcd_dvd_left _ _)
  have hppg : pp ∣ g := Nat.dvd_gcd dvd1 dvd2
  set q := (A355898 249580077007 + A355898 249580077006) / g with hqdef
  have hq : g * q = A355898 249580077007 + A355898 249580077006 :=
    Nat.mul_div_cancel' (Nat.dvd_add (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _))
  have heq0 : g + q = 1 + A355898 249580077007 + A355898 249580077006 := arec.symm.trans hf1
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with h | h
    · exfalso; interval_cases q
      · simp only [Nat.mul_zero] at hq; omega
      · simp only [Nat.mul_one] at hq; omega
    · exact h
  have hgge : pp ≤ g := Nat.le_of_dvd hgpos hppg
  have hge2 : 2 ≤ g := by simp only [pp] at hgge; omega
  have hle := Nat.add_le_mul hge2 hq2
  omega

#print axioms oeis_a355898_conjecture.disproof

