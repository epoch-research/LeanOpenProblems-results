import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A361713: The sequence defined by
$$a(n) = \sum_{k = 0}^{n-1} \binom{n}{k}^2 \binom{n+k-1}{k}^2$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k => (n.choose k) ^ 2 * ((n + k - 1).choose k) ^ 2

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace Disp

def split7 : ℕ → ℕ → (ℕ × ℕ)
  | 0, x => (0, x)
  | fuel+1, x => if x % 7 = 0 then (match split7 fuel (x/7) with | (v,c) => (v+1,c)) else (0,x)

-- split7 correctness
theorem split7_spec : ∀ (fuel x : ℕ), x ≠ 0 → x.factorization 7 ≤ fuel →
    split7 fuel x = (x.factorization 7, ordCompl[7] x) := by
  intro fuel
  induction fuel with
  | zero =>
    intro x hx hle
    have : x.factorization 7 = 0 := Nat.le_zero.mp hle
    rw [split7]
    have hnd : ¬ (7 ∣ x) := by
      intro hd
      have := (Nat.Prime.factorization_pos_of_dvd (by norm_num) hx hd)
      omega
    simp only [this, pow_zero, Nat.div_one]
  | succ f ih =>
    intro x hx hle
    rw [split7]
    by_cases h7 : x % 7 = 0
    · -- 7 ∣ x
      simp only [h7, if_true]
      have hd : 7 ∣ x := Nat.dvd_of_mod_eq_zero h7
      have hx7 : x / 7 ≠ 0 := by
        intro hc; apply hx; omega
      -- factorization x = factorization (x/7) + 1
      have hxeq : x = 7 * (x / 7) := by omega
      have hfac : x.factorization 7 = (x/7).factorization 7 + 1 := by
        conv_lhs => rw [hxeq]
        rw [Nat.factorization_mul (by norm_num) hx7]
        simp only [Finsupp.add_apply, Nat.Prime.factorization_self (by norm_num : Nat.Prime 7)]
        omega
      have hle' : (x/7).factorization 7 ≤ f := by omega
      have hrec := ih (x/7) hx7 hle'
      rw [hrec]
      -- ordCompl[7] (x/7) = ordCompl[7] x
      have h71 : ordCompl[7] (7:ℕ) = 1 := by
        have := Nat.ordCompl_self_pow (p:=7) (k:=1) (by norm_num : Nat.Prime 7)
        simpa using this
      have hoc : ordCompl[7] (x/7) = ordCompl[7] x := by
        conv_rhs => rw [hxeq]
        rw [Nat.ordCompl_mul, h71, one_mul]
      rw [hoc, hfac]
    · -- ¬ 7 ∣ x
      simp only [h7, if_false]
      have hnd : ¬ (7 ∣ x) := by rw [Nat.dvd_iff_mod_eq_zero]; exact h7
      have hf0 : x.factorization 7 = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
      rw [hf0]; simp

def hinv (pb m : ℕ) : ℕ :=
  let x0 := (pb^5) % 7
  let f := fun x => (x * ((2 + m - (pb*x) % m) % m)) % m
  f (f (f (f (f x0)))) % m

-- bridge helper: (n % m : ℤ) ≡ n [ZMOD m]
theorem cast_mod_modEq (n mm : ℕ) : ((n % mm : ℕ) : ℤ) ≡ (n : ℤ) [ZMOD (mm : ℤ)] := by
  rw [Int.natCast_mod]; exact Int.mod_modEq _ _

theorem hinv_spec (pb : ℕ) (hpb : ¬ (7 ∣ pb)) :
    pb * hinv pb (7^25) ≡ 1 [MOD 7^25] := by
  suffices key : ∀ (m : ℕ), m = 7^25 → pb * hinv pb m ≡ 1 [MOD m] from key _ rfl
  intro m hm
  have hm0 : (0:ℕ) < m := by rw [hm]; positivity
  set nf : ℕ → ℕ := fun x => (x * ((2 + m - (pb*x) % m) % m)) % m with hnf
  -- nf congruence in ℤ
  have hnfmod : ∀ x : ℕ, ((nf x : ℤ)) ≡ (x:ℤ)*(2 - (pb:ℤ)*x) [ZMOD (m:ℤ)] := by
    intro x
    have h1 : ((nf x : ℕ):ℤ) ≡ (x:ℤ) * ((2 + m - (pb*x) % m) % m : ℕ) [ZMOD (m:ℤ)] := by
      have := cast_mod_modEq (x * ((2 + m - (pb*x) % m) % m)) m
      simpa [hnf, Nat.cast_mul] using this
    refine h1.trans ?_
    apply Int.ModEq.mul_left
    -- ↑((2 + m - (pb*x)%m) % m) ≡ 2 - pb*x  [ZMOD m]
    refine (cast_mod_modEq (2 + m - (pb*x) % m) m).trans ?_
    have hle : (pb*x) % m ≤ 2 + m := le_trans (Nat.le_of_lt (Nat.mod_lt _ hm0)) (by omega)
    have hcast : ((2 + m - (pb*x) % m : ℕ):ℤ) = 2 + (m:ℤ) - ((pb*x) % m : ℕ) := by
      push_cast [Nat.cast_sub hle]; ring
    rw [hcast]
    have hmm : (m:ℤ) ≡ 0 [ZMOD (m:ℤ)] := (Int.modEq_zero_iff_dvd).mpr dvd_rfl
    have ht : (((pb*x) % m : ℕ):ℤ) ≡ (pb:ℤ)*x [ZMOD (m:ℤ)] := by
      have := cast_mod_modEq (pb*x) m; push_cast at this ⊢; exact this
    calc (2 + (m:ℤ) - ((pb*x) % m : ℕ)) ≡ 2 + 0 - (pb:ℤ)*x [ZMOD (m:ℤ)] := by
            exact (Int.ModEq.refl 2).add hmm |>.sub ht
      _ = 2 - (pb:ℤ)*x := by ring
  -- the Newton step
  have step : ∀ (a c x : ℕ), c ≤ 2*a → c ≤ 25 →
      (↑pb * ↑x : ℤ) ≡ 1 [ZMOD ((7:ℤ)^a)] → (↑pb * ↑(nf x) : ℤ) ≡ 1 [ZMOD ((7:ℤ)^c)] := by
    intro a c x hca hc25 hx
    have h7cm : ((7:ℤ)^c) ∣ (m:ℤ) := by rw [hm]; push_cast; exact pow_dvd_pow 7 hc25
    have hnf_c : (↑(nf x):ℤ) ≡ ↑x*(2-↑pb*↑x) [ZMOD ((7:ℤ)^c)] := (hnfmod x).of_dvd h7cm
    have key : (↑pb * ↑(nf x):ℤ) ≡ ↑pb*(↑x*(2-↑pb*↑x)) [ZMOD ((7:ℤ)^c)] := hnf_c.mul_left _
    -- divisibility of the square
    have hdvd : ((7:ℤ)^a) ∣ (1 - ↑pb*↑x) := Int.modEq_iff_dvd.mp hx
    have hdvd2 : ((7:ℤ)^c) ∣ (1 - ↑pb*↑x)^2 := by
      have h1 : ((7:ℤ)^a)^2 ∣ (1 - ↑pb*↑x)^2 := pow_dvd_pow_of_dvd hdvd 2
      have h2 : ((7:ℤ)^c) ∣ ((7:ℤ)^a)^2 := by rw [← pow_mul]; exact pow_dvd_pow 7 (by omega)
      exact dvd_trans h2 h1
    refine key.trans ?_
    have hid : (↑pb*(↑x*(2-↑pb*↑x)) : ℤ) = 1 - (1 - ↑pb*↑x)^2 := by ring
    rw [hid]
    exact (Int.modEq_iff_dvd.mpr (by simpa using hdvd2))
  -- seed
  have hcop : Nat.Coprime pb 7 := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hpb))
  have hseedN : pb * (pb^5 % 7) ≡ 1 [MOD 7] := by
    have h1 : pb^5 % 7 ≡ pb^5 [MOD 7] := Nat.mod_modEq _ _
    have h2 : pb * (pb^5 % 7) ≡ pb^6 [MOD 7] := by
      calc pb * (pb^5 % 7) ≡ pb * pb^5 [MOD 7] := (Nat.ModEq.refl pb).mul h1
        _ = pb^6 := by ring
    have h3 : pb^6 ≡ 1 [MOD 7] := by
      have := Nat.ModEq.pow_totient hcop
      simpa using this
    exact h2.trans h3
  have hseed : ((pb:ℤ) * ((pb^5 % 7 : ℕ):ℤ)) ≡ 1 [ZMOD ((7:ℤ)^1)] := by
    have h : ((pb * (pb^5 % 7) : ℕ) : ℤ) ≡ ((1:ℕ):ℤ) [ZMOD ((7:ℕ):ℤ)] := Int.natCast_modEq_iff.mpr hseedN
    rw [Nat.cast_mul] at h
    simpa only [Nat.cast_one, Nat.cast_ofNat, pow_one] using h
  -- chain
  have c1 := step 1 2 (pb^5 % 7) (by norm_num) (by norm_num) hseed
  have c2 := step 2 4 (nf (pb^5 % 7)) (by norm_num) (by norm_num) c1
  have c3 := step 4 8 (nf (nf (pb^5 % 7))) (by norm_num) (by norm_num) c2
  have c4 := step 8 16 (nf (nf (nf (pb^5 % 7)))) (by norm_num) (by norm_num) c3
  have c5 := step 16 25 (nf (nf (nf (nf (pb^5 % 7))))) (by norm_num) (by norm_num) c4
  -- hinv = nf^5 x0
  have hhinv : hinv pb m = nf (nf (nf (nf (nf (pb^5 % 7))))) := by
    have hh : hinv pb m = nf (nf (nf (nf (nf (pb^5 % 7))))) % m := rfl
    rw [hh, Nat.mod_eq_of_lt (Nat.mod_lt _ hm0)]
  rw [hhinv, hm]
  refine Int.natCast_modEq_iff.mp ?_
  push_cast
  exact c5

theorem modeq_to_eq {a b m : ℕ} (h : a ≡ b [MOD m]) (ha : a < m) : a = b % m := by
  have : a % m = a := Nat.mod_eq_of_lt ha
  rw [← this]; exact h

theorem step_u (u A P Bn Q ib m : ℕ) (hu : u ≡ A [MOD m]) (heq : A*P = Bn*Q)
    (hib : Q*ib ≡ 1 [MOD m]) : (u*P % m)*ib % m ≡ Bn [MOD m] := by
  calc (u*P % m)*ib % m ≡ (u*P % m)*ib [MOD m] := Nat.mod_modEq _ _
    _ ≡ (u*P)*ib [MOD m] := (Nat.mod_modEq _ _).mul_right ib
    _ ≡ (A*P)*ib [MOD m] := (hu.mul_right P).mul_right ib
    _ = (Bn*Q)*ib := by rw [heq]
    _ = Bn*(Q*ib) := by ring
    _ ≡ Bn*1 [MOD m] := (Nat.ModEq.refl Bn).mul hib
    _ = Bn := by ring

theorem split7_ok (x : ℕ) (hx : 0 < x) (hxlt : x < 7^7) :
    split7 10 x = (x.factorization 7, ordCompl[7] x) := by
  apply split7_spec
  · omega
  · by_contra h
    push_neg at h
    have h7 : (7:ℕ)^7 ∣ x := by
      have : (7:ℕ)^7 ∣ 7^(x.factorization 7) := pow_dvd_pow 7 (by omega)
      exact dvd_trans this (Nat.ordProj_dvd x 7)
    have := Nat.le_of_dvd hx h7
    omega

theorem factmul (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a*b).factorization 7 = a.factorization 7 + b.factorization 7 := by
  rw [Nat.factorization_mul ha hb]; simp

def tt (N k : ℕ) : ℕ := (N.choose k) ^ 2 * ((N + k - 1).choose k) ^ 2

def arun (N m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ×ℕ×ℕ×ℕ×ℕ)
  | 0, _, e1, u1, e2, u2, acc => (e1,u1,e2,u2,acc)
  | (len+1), k, e1, u1, e2, u2, acc =>
    let c1 := ((7^e1 % m) * u1) % m
    let c2 := ((7^e2 % m) * u2) % m
    let term := ((c1*c1 % m) * (c2*c2 % m)) % m
    let pa := split7 10 (N - k)
    let pa2 := split7 10 (N + k)
    let pbb := split7 10 (k+1)
    let ib := hinv pbb.2 m
    arun N m len (k+1) (e1 + pa.1 - pbb.1) ((u1 * pa.2 % m) * ib % m)
      (e2 + pa2.1 - pbb.1) ((u2 * pa2.2 % m) * ib % m) ((acc + term) % m)

theorem hDrec (N k : ℕ) (hN1 : 1 ≤ N) :
    (N+k).choose (k+1) * (k+1) = (N+k-1).choose k * (N+k) := by
  have h := Nat.succ_mul_choose_eq (N+k-1) k
  have e1 : (N+k-1).succ = N+k := by omega
  rw [e1] at h
  rw [Nat.succ_eq_add_one] at h
  rw [mul_comm ((N+k-1).choose k) (N+k)]
  exact h.symm

theorem step_c (e u B m : ℕ) (hu : u ≡ ordCompl[7] B [MOD m]) :
    ((7^e % m) * u) % m ≡ 7^e * ordCompl[7] B [MOD m] := by
  calc ((7^e % m)*u)%m ≡ (7^e % m)*u [MOD m] := Nat.mod_modEq _ _
    _ ≡ 7^e * u [MOD m] := (Nat.mod_modEq _ _).mul_right u
    _ ≡ 7^e * ordCompl[7] B [MOD m] := (Nat.ModEq.refl _).mul hu

theorem arun_succ (N m len k e1 u1 e2 u2 acc : ℕ) :
    arun N m (len+1) k e1 u1 e2 u2 acc
      = arun N m len (k+1)
          (e1 + (split7 10 (N-k)).1 - (split7 10 (k+1)).1)
          ((u1 * (split7 10 (N-k)).2 % m) * hinv (split7 10 (k+1)).2 m % m)
          (e2 + (split7 10 (N+k)).1 - (split7 10 (k+1)).1)
          ((u2 * (split7 10 (N+k)).2 % m) * hinv (split7 10 (k+1)).2 m % m)
          ((acc + (((((7^e1 % m) * u1) % m)*(((7^e1 % m) * u1) % m) % m)
                   * (((((7^e2 % m) * u2) % m)*(((7^e2 % m) * u2) % m) % m)) % m)) % m) := rfl

theorem arun_add (N m : ℕ) : ∀ (a b k e1 u1 e2 u2 acc : ℕ),
    arun N m (a + b) k e1 u1 e2 u2 acc
      = arun N m b (k + a) (arun N m a k e1 u1 e2 u2 acc).1 (arun N m a k e1 u1 e2 u2 acc).2.1
          (arun N m a k e1 u1 e2 u2 acc).2.2.1 (arun N m a k e1 u1 e2 u2 acc).2.2.2.1
          (arun N m a k e1 u1 e2 u2 acc).2.2.2.2 := by
  intro a
  induction a with
  | zero => intro b k e1 u1 e2 u2 acc; simp [arun]
  | succ A ih =>
    intro b k e1 u1 e2 u2 acc
    have h1 : A + 1 + b = (A + b) + 1 := by omega
    rw [h1, arun_succ, ih b (k+1) _ _ _ _ _, arun_succ]
    have hi : k + 1 + A = k + (A + 1) := by omega
    rw [hi]

theorem arun_acc_lt (N m : ℕ) (hm : 0 < m) :
    ∀ (len k e1 u1 e2 u2 acc : ℕ), (arun N m (len+1) k e1 u1 e2 u2 acc).2.2.2.2 < m := by
  intro len
  induction len with
  | zero => intro k e1 u1 e2 u2 acc; rw [arun_succ]; simp only [arun]; exact Nat.mod_lt _ hm
  | succ L ih => intro k e1 u1 e2 u2 acc; rw [arun_succ]; exact ih _ _ _ _ _ _

theorem term_tt (c1 c2 B D m : ℕ) (h1 : c1 ≡ B [MOD m]) (h2 : c2 ≡ D [MOD m]) :
    ((c1*c1 % m)*(c2*c2 % m)) % m ≡ B^2 * D^2 [MOD m] := by
  calc ((c1*c1%m)*(c2*c2%m))%m ≡ (c1*c1%m)*(c2*c2%m) [MOD m] := Nat.mod_modEq _ _
    _ ≡ (c1*c1)*(c2*c2) [MOD m] := (Nat.mod_modEq _ _).mul (Nat.mod_modEq _ _)
    _ ≡ (B*B)*(D*D) [MOD m] := (h1.mul h1).mul (h2.mul h2)
    _ = B^2 * D^2 := by ring

theorem arun_spec (N m : ℕ) (hm : m = 7^25) (hN1 : 1 ≤ N) (hNle : N ≤ 7^6) :
    ∀ (len k acc : ℕ), k + len ≤ N →
      ((arun N m len k ((N.choose k).factorization 7) (ordCompl[7] (N.choose k) % m)
            (((N+k-1).choose k).factorization 7) (ordCompl[7] ((N+k-1).choose k) % m) acc).1
          = (N.choose (k+len)).factorization 7)
    ∧ ((arun N m len k ((N.choose k).factorization 7) (ordCompl[7] (N.choose k) % m)
            (((N+k-1).choose k).factorization 7) (ordCompl[7] ((N+k-1).choose k) % m) acc).2.1
          = ordCompl[7] (N.choose (k+len)) % m)
    ∧ ((arun N m len k ((N.choose k).factorization 7) (ordCompl[7] (N.choose k) % m)
            (((N+k-1).choose k).factorization 7) (ordCompl[7] ((N+k-1).choose k) % m) acc).2.2.1
          = ((N+(k+len)-1).choose (k+len)).factorization 7)
    ∧ ((arun N m len k ((N.choose k).factorization 7) (ordCompl[7] (N.choose k) % m)
            (((N+k-1).choose k).factorization 7) (ordCompl[7] ((N+k-1).choose k) % m) acc).2.2.2.1
          = ordCompl[7] ((N+(k+len)-1).choose (k+len)) % m)
    ∧ ((arun N m len k ((N.choose k).factorization 7) (ordCompl[7] (N.choose k) % m)
            (((N+k-1).choose k).factorization 7) (ordCompl[7] ((N+k-1).choose k) % m) acc).2.2.2.2
          ≡ acc + ∑ i ∈ Finset.range len, tt N (k+i) [MOD m]) := by
  have hp7 : Nat.Prime 7 := by norm_num
  have h76 : (7:ℕ)^6 = 117649 := by norm_num
  have h77 : (7:ℕ)^7 = 823543 := by norm_num
  intro len
  induction len with
  | zero =>
    intro k acc hk
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arun, Finset.range_zero, Finset.sum_empty, add_zero]
    exact Nat.ModEq.refl _
  | succ L ih =>
    intro k acc hk
    have hkN : k < N := by omega
    -- split7 facts
    have hsa : split7 10 (N-k) = ((N-k).factorization 7, ordCompl[7] (N-k)) :=
      split7_ok _ (by omega) (by omega)
    have hsb : split7 10 (k+1) = ((k+1).factorization 7, ordCompl[7] (k+1)) :=
      split7_ok _ (by omega) (by omega)
    have hsa2 : split7 10 (N+k) = ((N+k).factorization 7, ordCompl[7] (N+k)) :=
      split7_ok _ (by omega) (by omega)
    -- nonzero facts
    have hBk : N.choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hBk1 : N.choose (k+1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hNk : N - k ≠ 0 := by omega
    have hk1 : k + 1 ≠ 0 := by omega
    have hDk : (N+k-1).choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hDk1 : (N+k).choose (k+1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hNpk : N + k ≠ 0 := by omega
    -- factorization equations
    have hfeq1 : (N.choose (k+1)).factorization 7 + (k+1).factorization 7
               = (N.choose k).factorization 7 + (N-k).factorization 7 := by
      have h := congrArg (fun t => t.factorization 7) (Nat.choose_succ_right_eq N k)
      simp only [factmul _ _ hBk1 hk1, factmul _ _ hBk hNk] at h
      exact h
    have hfeq2 : ((N+k).choose (k+1)).factorization 7 + (k+1).factorization 7
               = ((N+k-1).choose k).factorization 7 + (N+k).factorization 7 := by
      have h := congrArg (fun t => t.factorization 7) (hDrec N k hN1)
      simp only [factmul _ _ hDk1 hk1, factmul _ _ hDk hNpk] at h
      exact h
    -- ordCompl equations
    have hoc1 : ordCompl[7] (N.choose k) * ordCompl[7] (N-k)
              = ordCompl[7] (N.choose (k+1)) * ordCompl[7] (k+1) := by
      have h := congrArg (ordCompl[7] ·) (Nat.choose_succ_right_eq N k)
      simp only [Nat.ordCompl_mul] at h
      omega
    have hoc2 : ordCompl[7] ((N+k-1).choose k) * ordCompl[7] (N+k)
              = ordCompl[7] ((N+k).choose (k+1)) * ordCompl[7] (k+1) := by
      have h := congrArg (ordCompl[7] ·) (hDrec N k hN1)
      simp only [Nat.ordCompl_mul] at h
      omega
    -- hinv fact
    have hibok : ordCompl[7] (k+1) * hinv (ordCompl[7] (k+1)) m ≡ 1 [MOD m] := by
      rw [hm]
      exact hinv_spec (ordCompl[7] (k+1)) (Nat.not_dvd_ordCompl hp7 hk1)
    -- step equalities for the four arun args
    have he1eq : (N.choose k).factorization 7 + (N-k).factorization 7 - (k+1).factorization 7
               = (N.choose (k+1)).factorization 7 := by omega
    have hu1eq : ((ordCompl[7] (N.choose k) % m) * ordCompl[7] (N-k) % m)
                   * hinv (ordCompl[7] (k+1)) m % m
               = ordCompl[7] (N.choose (k+1)) % m := by
      apply modeq_to_eq _ (Nat.mod_lt _ (by rw [hm]; positivity))
      exact step_u _ _ _ _ _ _ _ (Nat.mod_modEq _ _) hoc1 hibok
    have he2eq : ((N+k-1).choose k).factorization 7 + (N+k).factorization 7 - (k+1).factorization 7
               = ((N+(k+1)-1).choose (k+1)).factorization 7 := by
      have : (N+(k+1)-1).choose (k+1) = (N+k).choose (k+1) := rfl
      rw [this]; omega
    have hu2eq : ((ordCompl[7] ((N+k-1).choose k) % m) * ordCompl[7] (N+k) % m)
                   * hinv (ordCompl[7] (k+1)) m % m
               = ordCompl[7] ((N+(k+1)-1).choose (k+1)) % m := by
      have hrw : (N+(k+1)-1).choose (k+1) = (N+k).choose (k+1) := rfl
      rw [hrw]
      apply modeq_to_eq _ (Nat.mod_lt _ (by rw [hm]; positivity))
      exact step_u _ _ _ _ _ _ _ (Nat.mod_modEq _ _) hoc2 hibok
    -- term modeq
    have hc1 : ((7^((N.choose k).factorization 7) % m) * (ordCompl[7] (N.choose k) % m)) % m
             ≡ N.choose k [MOD m] := by
      refine (step_c _ _ (N.choose k) _ (Nat.mod_modEq _ _)).trans ?_
      have : (7:ℕ)^((N.choose k).factorization 7) * ordCompl[7] (N.choose k) = N.choose k :=
        Nat.ordProj_mul_ordCompl_eq_self _ _
      rw [this]
    have hc2 : ((7^(((N+k-1).choose k).factorization 7) % m) * (ordCompl[7] ((N+k-1).choose k) % m)) % m
             ≡ (N+k-1).choose k [MOD m] := by
      refine (step_c _ _ ((N+k-1).choose k) _ (Nat.mod_modEq _ _)).trans ?_
      have : (7:ℕ)^(((N+k-1).choose k).factorization 7) * ordCompl[7] ((N+k-1).choose k) = (N+k-1).choose k :=
        Nat.ordProj_mul_ordCompl_eq_self _ _
      rw [this]
    rw [arun_succ]
    simp only [hsa, hsb, hsa2]
    rw [he1eq, hu1eq, he2eq, hu2eq]
    set c1 := ((7 ^ (N.choose k).factorization 7 % m) * (ordCompl[7] (N.choose k) % m)) % m with hc1def
    set c2 := ((7 ^ ((N + k - 1).choose k).factorization 7 % m) * (ordCompl[7] ((N + k - 1).choose k) % m)) % m with hc2def
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (k+1) _ (by omega)
    have hkk : k + 1 + L = k + (L+1) := by omega
    have hterm : ((c1*c1 % m)*(c2*c2 % m)) % m ≡ tt N k [MOD m] := by
      have h := term_tt c1 c2 (N.choose k) ((N+k-1).choose k) m hc1 hc2
      rw [show (N.choose k)^2 * ((N+k-1).choose k)^2 = tt N k from rfl] at h
      exact h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h1, hkk]
    · rw [h2, hkk]
    · rw [h3, hkk]
    · rw [h4, hkk]
    · refine h5.trans ?_
      rw [Finset.sum_range_succ']
      have hSeq : (∑ i ∈ Finset.range L, tt N (k+1+i)) = ∑ i ∈ Finset.range L, tt N (k+(i+1)) := by
        apply Finset.sum_congr rfl; intro i _; congr 1; omega
      rw [hSeq, Nat.add_zero]
      have hR : acc + ((∑ i ∈ Finset.range L, tt N (k+(i+1))) + tt N k)
              = (acc + tt N k) + (∑ i ∈ Finset.range L, tt N (k+(i+1))) := by ring
      rw [hR]
      exact (((Nat.mod_modEq _ _).trans ((Nat.ModEq.refl acc).add hterm)).add_right _)


theorem aMod (N : ℕ) (hN1 : 1 ≤ N) (hNle : N ≤ 7^6) :
    (∑ k ∈ Finset.range N, tt N k) % (7^25) = (arun N (7^25) N 0 0 1 0 1 0).2.2.2.2 := by
  set m : ℕ := 7^25 with hm
  have hm0 : 0 < m := by rw [hm]; positivity
  -- initial args are 0,1,0,1
  have h1m : (1:ℕ) < m := by rw [hm]; exact Nat.one_lt_pow (by norm_num) (by norm_num)
  have hoc1 : ordCompl[7] (N.choose 0) % m = 1 := by
    rw [Nat.choose_zero_right, show ordCompl[7] (1:ℕ) = 1 by simp [Nat.factorization_one]]
    exact Nat.mod_eq_of_lt h1m
  have hoc2 : ordCompl[7] ((N+0-1).choose 0) % m = 1 := by
    rw [Nat.choose_zero_right, show ordCompl[7] (1:ℕ) = 1 by simp [Nat.factorization_one]]
    exact Nat.mod_eq_of_lt h1m
  have hf1 : (N.choose 0).factorization 7 = 0 := by rw [Nat.choose_zero_right, Nat.factorization_one]; rfl
  have hf2 : ((N+0-1).choose 0).factorization 7 = 0 := by rw [Nat.choose_zero_right, Nat.factorization_one]; rfl
  have key := (arun_spec N m hm hN1 hNle N 0 0 (by omega)).2.2.2.2
  rw [hoc1, hoc2, hf1, hf2] at key
  -- key : (arun N m N 0 0 1 0 1 0).2.2.2.2 ≡ 0 + ∑ i ∈ range N, tt N (0+i) [MOD m]
  simp only [Nat.zero_add] at key
  -- lt
  have hlt : (arun N m N 0 0 1 0 1 0).2.2.2.2 < m := by
    have h := arun_acc_lt N m hm0 (N-1) 0 0 1 0 1 0
    rwa [Nat.sub_add_cancel hN1] at h
  exact (modeq_to_eq key hlt).symm

end Disp

theorem s6_s0 : Disp.arun 117649 (7^25) 343 0 0 1 0 1 0 = (3,687843876034320749108,3,902522019511674612289,551076796170696751852) := by rfl
theorem s6_s1 : Disp.arun 117649 (7^25) 343 343 3 687843876034320749108 3 902522019511674612289 551076796170696751852 = (3,1219663972324357079096,3,426507929425418769338,40769893373183237194) := by rfl
theorem s6_s2 : Disp.arun 117649 (7^25) 343 686 3 1219663972324357079096 3 426507929425418769338 40769893373183237194 = (3,68793879830137568419,3,565213276705932892056,1013353305520025371497) := by rfl
theorem s6_s3 : Disp.arun 117649 (7^25) 343 1029 3 68793879830137568419 3 565213276705932892056 1013353305520025371497 = (3,1219021433766825930603,3,1311661256272797974196,427540824636435020442) := by rfl
theorem s6_s4 : Disp.arun 117649 (7^25) 343 1372 3 1219021433766825930603 3 1311661256272797974196 427540824636435020442 = (3,1039626253192599878809,3,1280646931357401056263,1029076554173697220325) := by rfl
theorem s6_s5 : Disp.arun 117649 (7^25) 343 1715 3 1039626253192599878809 3 1280646931357401056263 1029076554173697220325 = (3,51544946519567379446,3,987443114735406241142,1230712469793538122490) := by rfl
theorem s6_s6 : Disp.arun 117649 (7^25) 343 2058 3 51544946519567379446 3 987443114735406241142 1230712469793538122490 = (2,150941942414299175196,2,57320838784838356862,78196334352884457123) := by rfl
theorem s6_s7 : Disp.arun 117649 (7^25) 343 2401 2 150941942414299175196 2 57320838784838356862 78196334352884457123 = (3,1245071362813592380695,3,1191051242167027476971,1096265209628194880492) := by rfl
theorem s6_s8 : Disp.arun 117649 (7^25) 343 2744 3 1245071362813592380695 3 1191051242167027476971 1096265209628194880492 = (3,90078468004214639499,3,1270341202918376488407,1069411118606992289241) := by rfl
theorem s6_s9 : Disp.arun 117649 (7^25) 343 3087 3 90078468004214639499 3 1270341202918376488407 1069411118606992289241 = (3,1086049373877897747250,3,979383174582226449677,377633130830572839755) := by rfl
theorem s6_s10 : Disp.arun 117649 (7^25) 343 3430 3 1086049373877897747250 3 979383174582226449677 377633130830572839755 = (3,939522389194202614761,3,416117099917593106069,811553718672183766077) := by rfl
theorem s6_s11 : Disp.arun 117649 (7^25) 343 3773 3 939522389194202614761 3 416117099917593106069 811553718672183766077 = (3,880409664531227717492,3,930428623566339315106,45967446507574591217) := by rfl
theorem s6_s12 : Disp.arun 117649 (7^25) 343 4116 3 880409664531227717492 3 930428623566339315106 45967446507574591217 = (3,198994904548099032673,3,1177165824075289425845,878784587035238101625) := by rfl
theorem s6_s13 : Disp.arun 117649 (7^25) 343 4459 3 198994904548099032673 3 1177165824075289425845 878784587035238101625 = (2,527749988428974657293,2,653011441757198116758,893358679276337407442) := by rfl
theorem s6_s14 : Disp.arun 117649 (7^25) 343 4802 2 527749988428974657293 2 653011441757198116758 893358679276337407442 = (3,38603342118300162183,3,1106499439545657640127,846441009176007288688) := by rfl
theorem s6_s15 : Disp.arun 117649 (7^25) 343 5145 3 38603342118300162183 3 1106499439545657640127 846441009176007288688 = (3,793973234892083640677,3,809431443451975572001,962453379122682503421) := by rfl
theorem s6_s16 : Disp.arun 117649 (7^25) 343 5488 3 793973234892083640677 3 809431443451975572001 962453379122682503421 = (3,265231419042721748433,3,817068750979548731207,995693077445025581175) := by rfl
theorem s6_s17 : Disp.arun 117649 (7^25) 343 5831 3 265231419042721748433 3 817068750979548731207 995693077445025581175 = (3,387085178131660867017,3,292097598483212147432,836884229962347700575) := by rfl
theorem s6_s18 : Disp.arun 117649 (7^25) 343 6174 3 387085178131660867017 3 292097598483212147432 836884229962347700575 = (3,517598928768395453542,3,477137282273868155929,583577396939935537021) := by rfl
theorem s6_s19 : Disp.arun 117649 (7^25) 343 6517 3 517598928768395453542 3 477137282273868155929 583577396939935537021 = (3,1131186596708439174583,3,620183840581702020378,909436749797145935954) := by rfl
theorem s6_s20 : Disp.arun 117649 (7^25) 343 6860 3 1131186596708439174583 3 620183840581702020378 909436749797145935954 = (2,1318141762523998581909,2,77873453347969728937,337975805035398218767) := by rfl
theorem s6_s21 : Disp.arun 117649 (7^25) 343 7203 2 1318141762523998581909 2 77873453347969728937 337975805035398218767 = (3,670189137411284383528,3,706900085621746396108,1309655523474205020569) := by rfl
theorem s6_s22 : Disp.arun 117649 (7^25) 343 7546 3 670189137411284383528 3 706900085621746396108 1309655523474205020569 = (3,597057720594278716735,3,661728804178229548457,49222045603715980507) := by rfl
theorem s6_s23 : Disp.arun 117649 (7^25) 343 7889 3 597057720594278716735 3 661728804178229548457 49222045603715980507 = (3,896809642618983789425,3,582026545627512215879,1067877272200453693560) := by rfl
theorem s6_s24 : Disp.arun 117649 (7^25) 343 8232 3 896809642618983789425 3 582026545627512215879 1067877272200453693560 = (3,930517691570142379713,3,1220877569132597673418,463274298830733183823) := by rfl
theorem s6_s25 : Disp.arun 117649 (7^25) 343 8575 3 930517691570142379713 3 1220877569132597673418 463274298830733183823 = (3,656993141551310246057,3,498572070891286677925,1081919249262809533724) := by rfl
theorem s6_s26 : Disp.arun 117649 (7^25) 343 8918 3 656993141551310246057 3 498572070891286677925 1081919249262809533724 = (3,270749732791302488884,3,568522086236994619078,1323338026252057737573) := by rfl
theorem s6_s27 : Disp.arun 117649 (7^25) 343 9261 3 270749732791302488884 3 568522086236994619078 1323338026252057737573 = (2,860052123623736754436,2,1025141928328109655345,168808975404140683067) := by rfl
theorem s6_s28 : Disp.arun 117649 (7^25) 343 9604 2 860052123623736754436 2 1025141928328109655345 168808975404140683067 = (3,286743065708758124880,3,114528605409731586165,961806440453043639350) := by rfl
theorem s6_s29 : Disp.arun 117649 (7^25) 343 9947 3 286743065708758124880 3 114528605409731586165 961806440453043639350 = (3,297180757953847922101,3,869157647923561462141,1323846563066175194236) := by rfl
theorem s6_s30 : Disp.arun 117649 (7^25) 343 10290 3 297180757953847922101 3 869157647923561462141 1323846563066175194236 = (3,1127043048553611256905,3,936103112244767043281,438028832455059773558) := by rfl
theorem s6_s31 : Disp.arun 117649 (7^25) 343 10633 3 1127043048553611256905 3 936103112244767043281 438028832455059773558 = (3,1114727749503533584354,3,696565683488488350133,1164358886137697325027) := by rfl
theorem s6_s32 : Disp.arun 117649 (7^25) 343 10976 3 1114727749503533584354 3 696565683488488350133 1164358886137697325027 = (3,421854992434666939326,3,2293022504199788672,917253041535226016902) := by rfl
theorem s6_s33 : Disp.arun 117649 (7^25) 343 11319 3 421854992434666939326 3 2293022504199788672 917253041535226016902 = (3,1124770197481180240810,3,1041929654337942203238,375709537187207178656) := by rfl
theorem s6_s34 : Disp.arun 117649 (7^25) 343 11662 3 1124770197481180240810 3 1041929654337942203238 375709537187207178656 = (2,149757218028327919292,2,878536251335294870664,855496157477003031669) := by rfl
theorem s6_s35 : Disp.arun 117649 (7^25) 343 12005 2 149757218028327919292 2 878536251335294870664 855496157477003031669 = (3,876438941251343474521,3,800689307087766842831,140110180107258932033) := by rfl
theorem s6_s36 : Disp.arun 117649 (7^25) 343 12348 3 876438941251343474521 3 800689307087766842831 140110180107258932033 = (3,407845693585122485179,3,527838781225434218404,406980878276315902105) := by rfl
theorem s6_s37 : Disp.arun 117649 (7^25) 343 12691 3 407845693585122485179 3 527838781225434218404 406980878276315902105 = (3,39392278533245709528,3,786284851834909997981,730011989277903424107) := by rfl
theorem s6_s38 : Disp.arun 117649 (7^25) 343 13034 3 39392278533245709528 3 786284851834909997981 730011989277903424107 = (3,1131982467941576327526,3,515040383355701128277,1099943022457649298468) := by rfl
theorem s6_s39 : Disp.arun 117649 (7^25) 343 13377 3 1131982467941576327526 3 515040383355701128277 1099943022457649298468 = (3,209935717457740091206,3,436266036774214487802,1243296802523960381695) := by rfl
theorem s6_s40 : Disp.arun 117649 (7^25) 343 13720 3 209935717457740091206 3 436266036774214487802 1243296802523960381695 = (3,624209434588727324273,3,343892143419006588195,565246907015968773345) := by rfl
theorem s6_s41 : Disp.arun 117649 (7^25) 343 14063 3 624209434588727324273 3 343892143419006588195 565246907015968773345 = (2,1155438908825828169831,2,486692699433517295746,1167461358978198323705) := by rfl
theorem s6_s42 : Disp.arun 117649 (7^25) 343 14406 2 1155438908825828169831 2 486692699433517295746 1167461358978198323705 = (3,443053607397517948014,3,869938254596606661908,1184839154729857552192) := by rfl
theorem s6_s43 : Disp.arun 117649 (7^25) 343 14749 3 443053607397517948014 3 869938254596606661908 1184839154729857552192 = (3,851430368967532455426,3,1207738234124173467888,827055489129964267377) := by rfl
theorem s6_s44 : Disp.arun 117649 (7^25) 343 15092 3 851430368967532455426 3 1207738234124173467888 827055489129964267377 = (3,418036360015284155360,3,1277967187322780955131,1113120770365485253912) := by rfl
theorem s6_s45 : Disp.arun 117649 (7^25) 343 15435 3 418036360015284155360 3 1277967187322780955131 1113120770365485253912 = (3,455947466389503145160,3,1053712637109822226441,1330840584131832216171) := by rfl
theorem s6_s46 : Disp.arun 117649 (7^25) 343 15778 3 455947466389503145160 3 1053712637109822226441 1330840584131832216171 = (3,127640055842949049095,3,754498206587754276707,1074310246950948434127) := by rfl
theorem s6_s47 : Disp.arun 117649 (7^25) 343 16121 3 127640055842949049095 3 754498206587754276707 1074310246950948434127 = (3,624976193127525882826,3,627422644928273058941,1175734619201115879207) := by rfl
theorem s6_s48 : Disp.arun 117649 (7^25) 343 16464 3 624976193127525882826 3 627422644928273058941 1175734619201115879207 = (1,250682943662213745446,1,89846240798014862155,689710024495785018615) := by rfl
theorem s6_s49 : Disp.arun 117649 (7^25) 343 16807 1 250682943662213745446 1 89846240798014862155 689710024495785018615 = (3,1170467558225757008503,3,1286819131857509911935,882856758682892012818) := by rfl
theorem s6_s50 : Disp.arun 117649 (7^25) 343 17150 3 1170467558225757008503 3 1286819131857509911935 882856758682892012818 = (3,318826659332766945168,3,584653884995716777406,529443946051140874909) := by rfl
theorem s6_s51 : Disp.arun 117649 (7^25) 343 17493 3 318826659332766945168 3 584653884995716777406 529443946051140874909 = (3,130936805473861681471,3,1011953604894787872651,1227797631207746540453) := by rfl
theorem s6_s52 : Disp.arun 117649 (7^25) 343 17836 3 130936805473861681471 3 1011953604894787872651 1227797631207746540453 = (3,939496994992914279420,3,431304349732216830207,903374249431910753407) := by rfl
theorem s6_s53 : Disp.arun 117649 (7^25) 343 18179 3 939496994992914279420 3 431304349732216830207 903374249431910753407 = (3,351704394635956446550,3,81740941697478918536,309365818254744574884) := by rfl
theorem s6_s54 : Disp.arun 117649 (7^25) 343 18522 3 351704394635956446550 3 81740941697478918536 309365818254744574884 = (3,1169791340116692844340,3,1057735648713650104491,938665502429661095895) := by rfl
theorem s6_s55 : Disp.arun 117649 (7^25) 343 18865 3 1169791340116692844340 3 1057735648713650104491 938665502429661095895 = (2,652992312247592459981,2,1309144239586714338221,570272944696549130317) := by rfl
theorem s6_s56 : Disp.arun 117649 (7^25) 343 19208 2 652992312247592459981 2 1309144239586714338221 570272944696549130317 = (3,1208561507862274829915,3,226024487481782740990,1278814537345957520938) := by rfl
theorem s6_s57 : Disp.arun 117649 (7^25) 343 19551 3 1208561507862274829915 3 226024487481782740990 1278814537345957520938 = (3,1157534283125895391734,3,1015632625785454754158,1108776792924387988906) := by rfl
theorem s6_s58 : Disp.arun 117649 (7^25) 343 19894 3 1157534283125895391734 3 1015632625785454754158 1108776792924387988906 = (3,773228459137821733212,3,569378246103938736141,693824776165078635820) := by rfl
theorem s6_s59 : Disp.arun 117649 (7^25) 343 20237 3 773228459137821733212 3 569378246103938736141 693824776165078635820 = (3,834867975508530372190,3,625638414149281821318,24976443609107710455) := by rfl
theorem s6_s60 : Disp.arun 117649 (7^25) 343 20580 3 834867975508530372190 3 625638414149281821318 24976443609107710455 = (3,1022693995748578526817,3,1075976599226230992314,781236624117194951028) := by rfl
theorem s6_s61 : Disp.arun 117649 (7^25) 343 20923 3 1022693995748578526817 3 1075976599226230992314 781236624117194951028 = (3,280279446638240623981,3,1083516781252450314566,436032686620753775176) := by rfl
theorem s6_s62 : Disp.arun 117649 (7^25) 343 21266 3 280279446638240623981 3 1083516781252450314566 436032686620753775176 = (2,1325940205989865057883,2,343850291026238153364,1270624637189747548178) := by rfl
theorem s6_s63 : Disp.arun 117649 (7^25) 343 21609 2 1325940205989865057883 2 343850291026238153364 1270624637189747548178 = (3,194813878651403946654,3,736758037258869909977,862089982829833510558) := by rfl
theorem s6_s64 : Disp.arun 117649 (7^25) 343 21952 3 194813878651403946654 3 736758037258869909977 862089982829833510558 = (3,753725665173533748427,3,411335442909636841607,123269222652664514525) := by rfl
theorem s6_s65 : Disp.arun 117649 (7^25) 343 22295 3 753725665173533748427 3 411335442909636841607 123269222652664514525 = (3,198192622445232525154,3,430737688720415520358,220108791815687096113) := by rfl
theorem s6_s66 : Disp.arun 117649 (7^25) 343 22638 3 198192622445232525154 3 430737688720415520358 220108791815687096113 = (3,71768111654060588839,3,604390370342037229414,289010544728331609086) := by rfl
theorem s6_s67 : Disp.arun 117649 (7^25) 343 22981 3 71768111654060588839 3 604390370342037229414 289010544728331609086 = (3,816323275075703991516,3,420959555583694002410,1193085227257236476612) := by rfl
theorem s6_s68 : Disp.arun 117649 (7^25) 343 23324 3 816323275075703991516 3 420959555583694002410 1193085227257236476612 = (3,579260003286308011114,3,502128876904133068386,85658290712939975164) := by rfl
theorem s6_s69 : Disp.arun 117649 (7^25) 343 23667 3 579260003286308011114 3 502128876904133068386 85658290712939975164 = (2,555963522565663419321,2,798340369734065910841,162411943839145073207) := by rfl
theorem s6_s70 : Disp.arun 117649 (7^25) 343 24010 2 555963522565663419321 2 798340369734065910841 162411943839145073207 = (3,405128729024883230067,3,1203356912955639298662,357092610948105081001) := by rfl
theorem s6_s71 : Disp.arun 117649 (7^25) 343 24353 3 405128729024883230067 3 1203356912955639298662 357092610948105081001 = (3,1147883549103635509000,3,1095583425907884246869,913507298268310347561) := by rfl
theorem s6_s72 : Disp.arun 117649 (7^25) 343 24696 3 1147883549103635509000 3 1095583425907884246869 913507298268310347561 = (3,94962586788471709368,3,510657895891447500040,591690857481335736986) := by rfl
theorem s6_s73 : Disp.arun 117649 (7^25) 343 25039 3 94962586788471709368 3 510657895891447500040 591690857481335736986 = (3,1156274683175943225606,3,1266201955021084678095,1103690521882544277634) := by rfl
theorem s6_s74 : Disp.arun 117649 (7^25) 343 25382 3 1156274683175943225606 3 1266201955021084678095 1103690521882544277634 = (3,995797094524875363234,3,881743798774211946002,1184675997783472357983) := by rfl
theorem s6_s75 : Disp.arun 117649 (7^25) 343 25725 3 995797094524875363234 3 881743798774211946002 1184675997783472357983 = (3,789733115710830678570,3,1217920041245024738466,602069183044108187864) := by rfl
theorem s6_s76 : Disp.arun 117649 (7^25) 343 26068 3 789733115710830678570 3 1217920041245024738466 602069183044108187864 = (2,1185229143978850067463,2,543249749342110583453,974502363180203290777) := by rfl
theorem s6_s77 : Disp.arun 117649 (7^25) 343 26411 2 1185229143978850067463 2 543249749342110583453 974502363180203290777 = (3,655126397143078579816,3,704256131902253774663,621750950903577243274) := by rfl
theorem s6_s78 : Disp.arun 117649 (7^25) 343 26754 3 655126397143078579816 3 704256131902253774663 621750950903577243274 = (3,611438204244777217354,3,112501753244845610447,408206216600023946952) := by rfl
theorem s6_s79 : Disp.arun 117649 (7^25) 343 27097 3 611438204244777217354 3 112501753244845610447 408206216600023946952 = (3,257632332866704955168,3,1238632718638357412263,518391971103598149811) := by rfl
theorem s6_s80 : Disp.arun 117649 (7^25) 343 27440 3 257632332866704955168 3 1238632718638357412263 518391971103598149811 = (3,126303903384071558483,3,1280289211275816203786,561048801512328528106) := by rfl
theorem s6_s81 : Disp.arun 117649 (7^25) 343 27783 3 126303903384071558483 3 1280289211275816203786 561048801512328528106 = (3,1021001427147166857697,3,714855164387871685125,1188357529274506738463) := by rfl
theorem s6_s82 : Disp.arun 117649 (7^25) 343 28126 3 1021001427147166857697 3 714855164387871685125 1188357529274506738463 = (3,648625448067642446302,3,415931142361062555681,599324162394966561274) := by rfl
theorem s6_s83 : Disp.arun 117649 (7^25) 343 28469 3 648625448067642446302 3 415931142361062555681 599324162394966561274 = (2,839487347159287581381,2,711936197930143615838,192493436316737872877) := by rfl
theorem s6_s84 : Disp.arun 117649 (7^25) 343 28812 2 839487347159287581381 2 711936197930143615838 192493436316737872877 = (3,859804890804137210059,3,62957690645469284274,289162663561808006601) := by rfl
theorem s6_s85 : Disp.arun 117649 (7^25) 343 29155 3 859804890804137210059 3 62957690645469284274 289162663561808006601 = (3,626201552150371863403,3,1163310901924274980041,397064332173382117700) := by rfl
theorem s6_s86 : Disp.arun 117649 (7^25) 343 29498 3 626201552150371863403 3 1163310901924274980041 397064332173382117700 = (3,1283448156589248951908,3,896130526714842890693,1153119397220785157570) := by rfl
theorem s6_s87 : Disp.arun 117649 (7^25) 343 29841 3 1283448156589248951908 3 896130526714842890693 1153119397220785157570 = (3,650920936721968061644,3,1190823295286166231958,734085090067566043136) := by rfl
theorem s6_s88 : Disp.arun 117649 (7^25) 343 30184 3 650920936721968061644 3 1190823295286166231958 734085090067566043136 = (3,482543509336840688124,3,1007093567632715214116,1107880383885864190715) := by rfl
theorem s6_s89 : Disp.arun 117649 (7^25) 343 30527 3 482543509336840688124 3 1007093567632715214116 1107880383885864190715 = (3,186292149194001486483,3,863171737571840548032,292132712837444354380) := by rfl
theorem s6_s90 : Disp.arun 117649 (7^25) 343 30870 3 186292149194001486483 3 863171737571840548032 292132712837444354380 = (2,1076333504034051436655,2,1248523579403242147613,162427272926837670389) := by rfl
theorem s6_s91 : Disp.arun 117649 (7^25) 343 31213 2 1076333504034051436655 2 1248523579403242147613 162427272926837670389 = (3,247715934816110733636,3,1335999597829216541285,227691448257350392344) := by rfl
theorem s6_s92 : Disp.arun 117649 (7^25) 343 31556 3 247715934816110733636 3 1335999597829216541285 227691448257350392344 = (3,959775503805076451231,3,174074000450436491941,340963333569578870396) := by rfl
theorem s6_s93 : Disp.arun 117649 (7^25) 343 31899 3 959775503805076451231 3 174074000450436491941 340963333569578870396 = (3,765279858810005124238,3,1167331248046752177800,248774559581420751271) := by rfl
theorem s6_s94 : Disp.arun 117649 (7^25) 343 32242 3 765279858810005124238 3 1167331248046752177800 248774559581420751271 = (3,239795594347708824763,3,1016513565324503745074,998136246520979018531) := by rfl
theorem s6_s95 : Disp.arun 117649 (7^25) 343 32585 3 239795594347708824763 3 1016513565324503745074 998136246520979018531 = (3,198271568428530013274,3,1164902220263228939551,235211520122922633207) := by rfl
theorem s6_s96 : Disp.arun 117649 (7^25) 343 32928 3 198271568428530013274 3 1164902220263228939551 235211520122922633207 = (3,1334346679077728906043,3,953212997387624044847,1331269588659569543447) := by rfl
theorem s6_s97 : Disp.arun 117649 (7^25) 343 33271 3 1334346679077728906043 3 953212997387624044847 1331269588659569543447 = (1,709633021594898681717,1,642850582735398853414,1300949595003434934594) := by rfl
theorem s6_s98 : Disp.arun 117649 (7^25) 343 33614 1 709633021594898681717 1 642850582735398853414 1300949595003434934594 = (3,1222378749202164814023,3,304177555253421881403,824286970356133505285) := by rfl
theorem s6_s99 : Disp.arun 117649 (7^25) 343 33957 3 1222378749202164814023 3 304177555253421881403 824286970356133505285 = (3,523186537209546047176,3,662121407460399191666,611638695904919362450) := by rfl
theorem s6_s100 : Disp.arun 117649 (7^25) 343 34300 3 523186537209546047176 3 662121407460399191666 611638695904919362450 = (3,560677798383114115359,3,1096443276797644327263,84797872940990505080) := by rfl
theorem s6_s101 : Disp.arun 117649 (7^25) 343 34643 3 560677798383114115359 3 1096443276797644327263 84797872940990505080 = (3,1059976910877101531109,3,506316293756346605373,1133120983051923371983) := by rfl
theorem s6_s102 : Disp.arun 117649 (7^25) 343 34986 3 1059976910877101531109 3 506316293756346605373 1133120983051923371983 = (3,426996658482702599756,3,907967891960095188050,159132747868867714565) := by rfl
theorem s6_s103 : Disp.arun 117649 (7^25) 343 35329 3 426996658482702599756 3 907967891960095188050 159132747868867714565 = (3,1194865341204752958693,3,1262523163118085826796,858451049452183337746) := by rfl
theorem s6_s104 : Disp.arun 117649 (7^25) 343 35672 3 1194865341204752958693 3 1262523163118085826796 858451049452183337746 = (2,99218854847007164914,2,748634788215217853055,1100203902226905286574) := by rfl
theorem s6_s105 : Disp.arun 117649 (7^25) 343 36015 2 99218854847007164914 2 748634788215217853055 1100203902226905286574 = (3,633670419586457260398,3,152739839165607110649,442674676565814433077) := by rfl
theorem s6_s106 : Disp.arun 117649 (7^25) 343 36358 3 633670419586457260398 3 152739839165607110649 442674676565814433077 = (3,130138327259196534163,3,744438468309020553009,1263483189344521615961) := by rfl
theorem s6_s107 : Disp.arun 117649 (7^25) 343 36701 3 130138327259196534163 3 744438468309020553009 1263483189344521615961 = (3,250738224251293672224,3,1336831227696818841300,172230137805497375143) := by rfl
theorem s6_s108 : Disp.arun 117649 (7^25) 343 37044 3 250738224251293672224 3 1336831227696818841300 172230137805497375143 = (3,611783502939398394635,3,1215984824189144690249,224557834528308615272) := by rfl
theorem s6_s109 : Disp.arun 117649 (7^25) 343 37387 3 611783502939398394635 3 1215984824189144690249 224557834528308615272 = (3,1032636902545584937024,3,738716701862623175863,571967069365234938599) := by rfl
theorem s6_s110 : Disp.arun 117649 (7^25) 343 37730 3 1032636902545584937024 3 738716701862623175863 571967069365234938599 = (3,781368433062052196353,3,1075356163910825754488,134436466935883418930) := by rfl
theorem s6_s111 : Disp.arun 117649 (7^25) 343 38073 3 781368433062052196353 3 1075356163910825754488 134436466935883418930 = (2,526912302991069203715,2,919499886179791209535,768603262378936109126) := by rfl
theorem s6_s112 : Disp.arun 117649 (7^25) 343 38416 2 526912302991069203715 2 919499886179791209535 768603262378936109126 = (3,691346053645641580915,3,114627580878388742088,789656712918180887564) := by rfl
theorem s6_s113 : Disp.arun 117649 (7^25) 343 38759 3 691346053645641580915 3 114627580878388742088 789656712918180887564 = (3,404332313967770139052,3,1056006310714565598259,1138811402973080997469) := by rfl
theorem s6_s114 : Disp.arun 117649 (7^25) 343 39102 3 404332313967770139052 3 1056006310714565598259 1138811402973080997469 = (3,402418951863216300661,3,1147648609003186038180,752729549784483024069) := by rfl
theorem s6_s115 : Disp.arun 117649 (7^25) 343 39445 3 402418951863216300661 3 1147648609003186038180 752729549784483024069 = (3,835503480024385799492,3,345797009471927355225,985363562073982353613) := by rfl
theorem s6_s116 : Disp.arun 117649 (7^25) 343 39788 3 835503480024385799492 3 345797009471927355225 985363562073982353613 = (3,830690236935415719187,3,1031615918423687829333,578816746098119178644) := by rfl
theorem s6_s117 : Disp.arun 117649 (7^25) 343 40131 3 830690236935415719187 3 1031615918423687829333 578816746098119178644 = (3,456525782103256478691,3,712488741834277055570,571509389196603698730) := by rfl
theorem s6_s118 : Disp.arun 117649 (7^25) 343 40474 3 456525782103256478691 3 712488741834277055570 571509389196603698730 = (2,61010106840325759401,2,1063377944192012211621,31512933436256909456) := by rfl
theorem s6_s119 : Disp.arun 117649 (7^25) 343 40817 2 61010106840325759401 2 1063377944192012211621 31512933436256909456 = (3,639133074333616322732,3,808529355213205228590,434706823955251806169) := by rfl
theorem s6_s120 : Disp.arun 117649 (7^25) 343 41160 3 639133074333616322732 3 808529355213205228590 434706823955251806169 = (3,722470125228953285510,3,669968972174562536655,469128176537656357226) := by rfl
theorem s6_s121 : Disp.arun 117649 (7^25) 343 41503 3 722470125228953285510 3 669968972174562536655 469128176537656357226 = (3,1008281684792812334991,3,1119602878024698170339,122047727567696151894) := by rfl
theorem s6_s122 : Disp.arun 117649 (7^25) 343 41846 3 1008281684792812334991 3 1119602878024698170339 122047727567696151894 = (3,478975740640423321010,3,375262669015116890737,165671921594137567904) := by rfl
theorem s6_s123 : Disp.arun 117649 (7^25) 343 42189 3 478975740640423321010 3 375262669015116890737 165671921594137567904 = (3,795957517274428331183,3,83649365803057091124,322644101907745300880) := by rfl
theorem s6_s124 : Disp.arun 117649 (7^25) 343 42532 3 795957517274428331183 3 83649365803057091124 322644101907745300880 = (3,1316836500818879373248,3,241825794366707671196,585675079043884692262) := by rfl
theorem s6_s125 : Disp.arun 117649 (7^25) 343 42875 3 1316836500818879373248 3 241825794366707671196 585675079043884692262 = (2,768107112475173600365,2,204118777161730641324,236718704252949506162) := by rfl
theorem s6_s126 : Disp.arun 117649 (7^25) 343 43218 2 768107112475173600365 2 204118777161730641324 236718704252949506162 = (3,984677135260595478906,3,333134879098066765105,154604776081354411163) := by rfl
theorem s6_s127 : Disp.arun 117649 (7^25) 343 43561 3 984677135260595478906 3 333134879098066765105 154604776081354411163 = (3,926073856623157794625,3,236703537357723242846,482834507975746069130) := by rfl
theorem s6_s128 : Disp.arun 117649 (7^25) 343 43904 3 926073856623157794625 3 236703537357723242846 482834507975746069130 = (3,607130960361601556424,3,1278704842490774147727,132997421229302092891) := by rfl
theorem s6_s129 : Disp.arun 117649 (7^25) 343 44247 3 607130960361601556424 3 1278704842490774147727 132997421229302092891 = (3,1247939011374395378085,3,400404741603102635989,522371028925463275706) := by rfl
theorem s6_s130 : Disp.arun 117649 (7^25) 343 44590 3 1247939011374395378085 3 400404741603102635989 522371028925463275706 = (3,1121656430874392897179,3,9708767576113654366,1214712721019927801085) := by rfl
theorem s6_s131 : Disp.arun 117649 (7^25) 343 44933 3 1121656430874392897179 3 9708767576113654366 1214712721019927801085 = (3,936072142495107277766,3,1041185577773157861232,385043586712998843421) := by rfl
theorem s6_s132 : Disp.arun 117649 (7^25) 343 45276 3 936072142495107277766 3 1041185577773157861232 385043586712998843421 = (2,898436631060887402291,2,624803482673763808677,991115676853030338142) := by rfl
theorem s6_s133 : Disp.arun 117649 (7^25) 343 45619 2 898436631060887402291 2 624803482673763808677 991115676853030338142 = (3,683590921929283580792,3,698247364249650764634,110721972276560410627) := by rfl
theorem s6_s134 : Disp.arun 117649 (7^25) 343 45962 3 683590921929283580792 3 698247364249650764634 110721972276560410627 = (3,251637051084367900214,3,1317921750025860984666,477672211839956299356) := by rfl
theorem s6_s135 : Disp.arun 117649 (7^25) 343 46305 3 251637051084367900214 3 1317921750025860984666 477672211839956299356 = (3,648474993470234099514,3,377978524965801231484,1100792623328834485848) := by rfl
theorem s6_s136 : Disp.arun 117649 (7^25) 343 46648 3 648474993470234099514 3 377978524965801231484 1100792623328834485848 = (3,979065741551623088407,3,292105284920154119080,849967953336882331855) := by rfl
theorem s6_s137 : Disp.arun 117649 (7^25) 343 46991 3 979065741551623088407 3 292105284920154119080 849967953336882331855 = (3,1166654970950917467954,3,751274157530719132159,417736110094436244504) := by rfl
theorem s6_s138 : Disp.arun 117649 (7^25) 343 47334 3 1166654970950917467954 3 751274157530719132159 417736110094436244504 = (3,1324094019028561926445,3,286988647373495800375,48284301669892364189) := by rfl
theorem s6_s139 : Disp.arun 117649 (7^25) 343 47677 3 1324094019028561926445 3 286988647373495800375 48284301669892364189 = (2,729602723427281199392,2,432920833090033206092,380004477216662028788) := by rfl
theorem s6_s140 : Disp.arun 117649 (7^25) 343 48020 2 729602723427281199392 2 432920833090033206092 380004477216662028788 = (3,389438847863976305004,3,315467072646540308782,826719675106332061209) := by rfl
theorem s6_s141 : Disp.arun 117649 (7^25) 343 48363 3 389438847863976305004 3 315467072646540308782 826719675106332061209 = (3,639507622222514358526,3,1276981741455175622080,998337761380314152372) := by rfl
theorem s6_s142 : Disp.arun 117649 (7^25) 343 48706 3 639507622222514358526 3 1276981741455175622080 998337761380314152372 = (3,333588378337370501693,3,1169927726533721076591,30854918406220408431) := by rfl
theorem s6_s143 : Disp.arun 117649 (7^25) 343 49049 3 333588378337370501693 3 1169927726533721076591 30854918406220408431 = (3,887209012730216222884,3,1264131355177578720751,230147418065490769180) := by rfl
theorem s6_s144 : Disp.arun 117649 (7^25) 343 49392 3 887209012730216222884 3 1264131355177578720751 230147418065490769180 = (3,491743403887554199566,3,161560969357995170960,1311022542449353352704) := by rfl
theorem s6_s145 : Disp.arun 117649 (7^25) 343 49735 3 491743403887554199566 3 161560969357995170960 1311022542449353352704 = (3,824338857707459511075,3,1010232076454538270178,409148875251118695288) := by rfl
theorem s6_s146 : Disp.arun 117649 (7^25) 343 50078 3 824338857707459511075 3 1010232076454538270178 409148875251118695288 = (1,345914931324913199737,1,410489464889564925821,1158312404966529299761) := by rfl
theorem s6_s147 : Disp.arun 117649 (7^25) 343 50421 1 345914931324913199737 1 410489464889564925821 1158312404966529299761 = (3,1339637301740512115305,3,988941188291249840704,120086424151649680747) := by rfl
theorem s6_s148 : Disp.arun 117649 (7^25) 343 50764 3 1339637301740512115305 3 988941188291249840704 120086424151649680747 = (3,800700500507328377044,3,403251556675724213790,1743684405020375952) := by rfl
theorem s6_s149 : Disp.arun 117649 (7^25) 343 51107 3 800700500507328377044 3 403251556675724213790 1743684405020375952 = (3,1114094416565411013546,3,806623128755462847540,394363950241708754077) := by rfl
theorem s6_s150 : Disp.arun 117649 (7^25) 343 51450 3 1114094416565411013546 3 806623128755462847540 394363950241708754077 = (3,116090331746338854823,3,788394921451545080066,507876351684544731246) := by rfl
theorem s6_s151 : Disp.arun 117649 (7^25) 343 51793 3 116090331746338854823 3 788394921451545080066 507876351684544731246 = (3,1282565615589254047888,3,896947633567891984046,807141876448116929504) := by rfl
theorem s6_s152 : Disp.arun 117649 (7^25) 343 52136 3 1282565615589254047888 3 896947633567891984046 807141876448116929504 = (3,1115589721290841680442,3,589465955003197073192,552111770476059897188) := by rfl
theorem s6_s153 : Disp.arun 117649 (7^25) 343 52479 3 1115589721290841680442 3 589465955003197073192 552111770476059897188 = (2,79212833160926550455,2,75377369344497154488,1037318767682309904310) := by rfl
theorem s6_s154 : Disp.arun 117649 (7^25) 343 52822 2 79212833160926550455 2 75377369344497154488 1037318767682309904310 = (3,715147471935083603613,3,543410238378495683126,17154187176524665618) := by rfl
theorem s6_s155 : Disp.arun 117649 (7^25) 343 53165 3 715147471935083603613 3 543410238378495683126 17154187176524665618 = (3,1081575642119154054806,3,1154695730379441489495,565083348335968308344) := by rfl
theorem s6_s156 : Disp.arun 117649 (7^25) 343 53508 3 1081575642119154054806 3 1154695730379441489495 565083348335968308344 = (3,41664000991564487023,3,931377932312015147370,980627668557763187543) := by rfl
theorem s6_s157 : Disp.arun 117649 (7^25) 343 53851 3 41664000991564487023 3 931377932312015147370 980627668557763187543 = (3,293475387745617606037,3,664896907588720541695,798321347103240912071) := by rfl
theorem s6_s158 : Disp.arun 117649 (7^25) 343 54194 3 293475387745617606037 3 664896907588720541695 798321347103240912071 = (3,422510616900959501064,3,384151139815860407490,1124276994432207879250) := by rfl
theorem s6_s159 : Disp.arun 117649 (7^25) 343 54537 3 422510616900959501064 3 384151139815860407490 1124276994432207879250 = (3,662149268588163069617,3,217924837563915699216,1159804618316509616571) := by rfl
theorem s6_s160 : Disp.arun 117649 (7^25) 343 54880 3 662149268588163069617 3 217924837563915699216 1159804618316509616571 = (2,1160425210072364664698,2,114020494092556142900,348855812533298539610) := by rfl
theorem s6_s161 : Disp.arun 117649 (7^25) 343 55223 2 1160425210072364664698 2 114020494092556142900 348855812533298539610 = (3,46427847536038536651,3,497565197483740568575,477384493904048389072) := by rfl
theorem s6_s162 : Disp.arun 117649 (7^25) 343 55566 3 46427847536038536651 3 497565197483740568575 477384493904048389072 = (3,372125877597873450629,3,533041405276111030429,254796201668739404451) := by rfl
theorem s6_s163 : Disp.arun 117649 (7^25) 343 55909 3 372125877597873450629 3 533041405276111030429 254796201668739404451 = (3,693397722790282630836,3,1014609550254871723234,62299175610949195668) := by rfl
theorem s6_s164 : Disp.arun 117649 (7^25) 343 56252 3 693397722790282630836 3 1014609550254871723234 62299175610949195668 = (3,502187668016387113854,3,786466863680358522069,1077450388834162785709) := by rfl
theorem s6_s165 : Disp.arun 117649 (7^25) 343 56595 3 502187668016387113854 3 786466863680358522069 1077450388834162785709 = (3,2491428399987748162,3,1322378029730870632663,117267278108593117219) := by rfl
theorem s6_s166 : Disp.arun 117649 (7^25) 343 56938 3 2491428399987748162 3 1322378029730870632663 117267278108593117219 = (3,41355164925711258348,3,590694428162132430597,143185885069274332377) := by rfl
theorem s6_s167 : Disp.arun 117649 (7^25) 343 57281 3 41355164925711258348 3 590694428162132430597 143185885069274332377 = (2,807538709769513812820,2,1239997587430630667238,755331015102551531351) := by rfl
theorem s6_s168 : Disp.arun 117649 (7^25) 343 57624 2 807538709769513812820 2 1239997587430630667238 755331015102551531351 = (3,270974223040882111661,3,44812823276674380124,1061724833285165086164) := by rfl
theorem s6_s169 : Disp.arun 117649 (7^25) 343 57967 3 270974223040882111661 3 44812823276674380124 1061724833285165086164 = (3,884075411407395278256,3,1302722808809355502762,763099605692399064650) := by rfl
theorem s6_s170 : Disp.arun 117649 (7^25) 343 58310 3 884075411407395278256 3 1302722808809355502762 763099605692399064650 = (3,719734107958896622247,3,1002303269253429509581,1174389098020459231478) := by rfl
theorem s6_s171 : Disp.arun 117649 (7^25) 343 58653 3 719734107958896622247 3 1002303269253429509581 1174389098020459231478 = (3,719734107958896622247,3,193292911637315706687,334366764170207362231) := by rfl
theorem s6_s172 : Disp.arun 117649 (7^25) 343 58996 3 719734107958896622247 3 193292911637315706687 334366764170207362231 = (3,884075411407395278256,3,500273883816332087304,1236292045002445635009) := by rfl
theorem s6_s173 : Disp.arun 117649 (7^25) 343 59339 3 884075411407395278256 3 500273883816332087304 1236292045002445635009 = (3,270974223040882111661,3,1185239789042623628978,388340772174963612425) := by rfl
theorem s6_s174 : Disp.arun 117649 (7^25) 343 59682 3 270974223040882111661 3 1185239789042623628978 388340772174963612425 = (2,807538709769513812820,2,911638371242174621103,909620746666576474951) := by rfl
theorem s6_s175 : Disp.arun 117649 (7^25) 343 60025 2 807538709769513812820 2 911638371242174621103 909620746666576474951 = (3,41355164925711258348,3,835000084988093742985,757848478176961361688) := by rfl
theorem s6_s176 : Disp.arun 117649 (7^25) 343 60368 3 41355164925711258348 3 835000084988093742985 757848478176961361688 = (3,2491428399987748162,3,1240773247773438245759,1101965351565880711750) := by rfl
theorem s6_s177 : Disp.arun 117649 (7^25) 343 60711 3 2491428399987748162 3 1240773247773438245759 1101965351565880711750 = (3,502187668016387113854,3,95338653229246561475,356264690087691624051) := by rfl
theorem s6_s178 : Disp.arun 117649 (7^25) 343 61054 3 502187668016387113854 3 95338653229246561475 356264690087691624051 = (3,693397722790282630836,3,1261263298077695548939,525972382039944561779) := by rfl
theorem s6_s179 : Disp.arun 117649 (7^25) 343 61397 3 693397722790282630836 3 1261263298077695548939 525972382039944561779 = (3,372125877597873450629,3,708925773713626154899,316830067157965300164) := by rfl
theorem s6_s180 : Disp.arun 117649 (7^25) 343 61740 3 372125877597873450629 3 708925773713626154899 316830067157965300164 = (3,46427847536038536651,3,745631478616908623382,1138025163157270847964) := by rfl
theorem s6_s181 : Disp.arun 117649 (7^25) 343 62083 3 46427847536038536651 3 745631478616908623382 1138025163157270847964 = (2,1160425210072364664698,2,178131950585483473477,368535578837067529707) := by rfl
theorem s6_s182 : Disp.arun 117649 (7^25) 343 62426 2 1160425210072364664698 2 178131950585483473477 368535578837067529707 = (3,662149268588163069617,3,1297765146325720190133,995106516237798577474) := by rfl
theorem s6_s183 : Disp.arun 117649 (7^25) 343 62769 3 662149268588163069617 3 1297765146325720190133 995106516237798577474 = (3,422510616900959501064,3,1278245472043049721334,1103493210654136068131) := by rfl
theorem s6_s184 : Disp.arun 117649 (7^25) 343 63112 3 422510616900959501064 3 1278245472043049721334 1103493210654136068131 = (3,293475387745617606037,3,879231182140182682592,733398754960473440483) := by rfl
theorem s6_s185 : Disp.arun 117649 (7^25) 343 63455 3 293475387745617606037 3 879231182140182682592 733398754960473440483 = (3,41664000991564487023,3,65271284756599147249,768152984575991119512) := by rfl
theorem s6_s186 : Disp.arun 117649 (7^25) 343 63798 3 41664000991564487023 3 65271284756599147249 768152984575991119512 = (3,1081575642119154054806,3,287049855092484965841,789081344440448525215) := by rfl
theorem s6_s187 : Disp.arun 117649 (7^25) 343 64141 3 1081575642119154054806 3 287049855092484965841 789081344440448525215 = (3,715147471935083603613,3,1186623605964740867601,1296854662081548127986) := by rfl
theorem s6_s188 : Disp.arun 117649 (7^25) 343 64484 3 715147471935083603613 3 1186623605964740867601 1296854662081548127986 = (2,79212833160926550455,2,386027143532324518055,359874824062327951028) := by rfl
theorem s6_s189 : Disp.arun 117649 (7^25) 343 64827 2 79212833160926550455 2 386027143532324518055 359874824062327951028 = (3,1115589721290841680442,3,867128368597170676928,1038349085410301916805) := by rfl
theorem s6_s190 : Disp.arun 117649 (7^25) 343 65170 3 1115589721290841680442 3 867128368597170676928 1038349085410301916805 = (3,1282565615589254047888,3,499413173126745910365,706452117482815277778) := by rfl
theorem s6_s191 : Disp.arun 117649 (7^25) 343 65513 3 1282565615589254047888 3 499413173126745910365 706452117482815277778 = (3,116090331746338854823,3,110630045528806497762,84359735710465655182) := by rfl
theorem s6_s192 : Disp.arun 117649 (7^25) 343 65856 3 116090331746338854823 3 110630045528806497762 84359735710465655182 = (3,1114094416565411013546,3,1027247679959573308161,888088062241059630532) := by rfl
theorem s6_s193 : Disp.arun 117649 (7^25) 343 66199 3 1114094416565411013546 3 1027247679959573308161 888088062241059630532 = (3,800700500507328377044,3,21694348623371099469,1029328383042449751766) := by rfl
theorem s6_s194 : Disp.arun 117649 (7^25) 343 66542 3 800700500507328377044 3 21694348623371099469 1029328383042449751766 = (3,1339637301740512115305,3,396766405766406654614,1284100617764481715899) := by rfl
theorem s6_s195 : Disp.arun 117649 (7^25) 343 66885 3 1339637301740512115305 3 396766405766406654614 1284100617764481715899 = (1,345914931324913199737,1,1326242041598476389193,1159973539277806548821) := by rfl
theorem s6_s196 : Disp.arun 117649 (7^25) 343 67228 1 345914931324913199737 1 1326242041598476389193 1159973539277806548821 = (3,824338857707459511075,3,853397808683171672950,846569266488618101318) := by rfl
theorem s6_s197 : Disp.arun 117649 (7^25) 343 67571 3 824338857707459511075 3 853397808683171672950 846569266488618101318 = (3,491743403887554199566,3,205891604232339921466,735706164082943330488) := by rfl
theorem s6_s198 : Disp.arun 117649 (7^25) 343 67914 3 491743403887554199566 3 205891604232339921466 735706164082943330488 = (3,887209012730216222884,3,815282538945560784390,1151457904007550484066) := by rfl
theorem s6_s199 : Disp.arun 117649 (7^25) 343 68257 3 887209012730216222884 3 815282538945560784390 1151457904007550484066 = (3,333588378337370501693,3,1284874730577720004340,503692560044956306361) := by rfl
theorem s6_s200 : Disp.arun 117649 (7^25) 343 68600 3 333588378337370501693 3 1284874730577720004340 503692560044956306361 = (3,639507622222514358526,3,545191098243988889325,1190281939189763909644) := by rfl
theorem s6_s201 : Disp.arun 117649 (7^25) 343 68943 3 639507622222514358526 3 545191098243988889325 1190281939189763909644 = (3,389438847863976305004,3,23705349112079221432,231376177840593905001) := by rfl
theorem s6_s202 : Disp.arun 117649 (7^25) 343 69286 3 389438847863976305004 3 23705349112079221432 231376177840593905001 = (2,729602723427281199392,2,828567519999631286358,621386099157422242358) := by rfl
theorem s6_s203 : Disp.arun 117649 (7^25) 343 69629 2 729602723427281199392 2 828567519999631286358 621386099157422242358 = (3,1324094019028561926445,3,913728318599724856572,1080008988712186109732) := by rfl
theorem s6_s204 : Disp.arun 117649 (7^25) 343 69972 3 1324094019028561926445 3 913728318599724856572 1080008988712186109732 = (3,1166654970950917467954,3,699183104718286980775,1319641386447879669539) := by rfl
theorem s6_s205 : Disp.arun 117649 (7^25) 343 70315 3 1166654970950917467954 3 699183104718286980775 1319641386447879669539 = (3,979065741551623088407,3,461497316284980291587,999147903379713014705) := by rfl
theorem s6_s206 : Disp.arun 117649 (7^25) 343 70658 3 979065741551623088407 3 461497316284980291587 999147903379713014705 = (3,648474993470234099514,3,65633720138250958444,953258754971488452341) := by rfl
theorem s6_s207 : Disp.arun 117649 (7^25) 343 71001 3 648474993470234099514 3 65633720138250958444 953258754971488452341 = (3,251637051084367900214,3,483978262995665776096,442829010971526657899) := by rfl
theorem s6_s208 : Disp.arun 117649 (7^25) 343 71344 3 251637051084367900214 3 483978262995665776096 442829010971526657899 = (3,683590921929283580792,3,397721052541665001932,432745897863326866617) := by rfl
theorem s6_s209 : Disp.arun 117649 (7^25) 343 71687 3 683590921929283580792 3 397721052541665001932 432745897863326866617 = (2,898436631060887402291,2,1014518090106286090952,880022089999905833107) := by rfl
theorem s6_s210 : Disp.arun 117649 (7^25) 343 72030 2 898436631060887402291 2 1014518090106286090952 880022089999905833107 = (3,936072142495107277766,3,278475646896534455397,485056298150492333350) := by rfl
theorem s6_s211 : Disp.arun 117649 (7^25) 343 72373 3 936072142495107277766 3 278475646896534455397 485056298150492333350 = (3,1121656430874392897179,3,1040072085813108793344,205731115042047246835) := by rfl
theorem s6_s212 : Disp.arun 117649 (7^25) 343 72716 3 1121656430874392897179 3 1040072085813108793344 205731115042047246835 = (3,1247939011374395378085,3,955637158558684944585,121798886703463597048) := by rfl
theorem s6_s213 : Disp.arun 117649 (7^25) 343 73059 3 1247939011374395378085 3 955637158558684944585 121798886703463597048 = (3,607130960361601556424,3,124493735074632959576,527000801689695998127) := by rfl
theorem s6_s214 : Disp.arun 117649 (7^25) 343 73402 3 607130960361601556424 3 124493735074632959576 527000801689695998127 = (3,926073856623157794625,3,1057863277012999790637,1196636118097844231599) := by rfl
theorem s6_s215 : Disp.arun 117649 (7^25) 343 73745 3 926073856623157794625 3 1057863277012999790637 1196636118097844231599 = (3,984677135260595478906,3,784832403921413684815,306219895338859584027) := by rfl
theorem s6_s216 : Disp.arun 117649 (7^25) 343 74088 3 984677135260595478906 3 784832403921413684815 306219895338859584027 = (2,768107112475173600365,2,784023851859391127052,183727368853349201434) := by rfl
theorem s6_s217 : Disp.arun 117649 (7^25) 343 74431 2 768107112475173600365 2 784023851859391127052 183727368853349201434 = (3,1316836500818879373248,3,102062698436329931140,950716010084798661068) := by rfl
theorem s6_s218 : Disp.arun 117649 (7^25) 343 74774 3 1316836500818879373248 3 102062698436329931140 950716010084798661068 = (3,795957517274428331183,3,370572314180206365385,1174796703152891322491) := by rfl
theorem s6_s219 : Disp.arun 117649 (7^25) 343 75117 3 795957517274428331183 3 370572314180206365385 1174796703152891322491 = (3,478975740640423321010,3,562897892145884141488,1233418394603529942333) := by rfl
theorem s6_s220 : Disp.arun 117649 (7^25) 343 75460 3 478975740640423321010 3 562897892145884141488 1233418394603529942333 = (3,1008281684792812334991,3,1294169886423849696718,1279329612445910159961) := by rfl
theorem s6_s221 : Disp.arun 117649 (7^25) 343 75803 3 1008281684792812334991 3 1294169886423849696718 1279329612445910159961 = (3,722470125228953285510,3,597423538710255856861,223494390856658804114) := by rfl
theorem s6_s222 : Disp.arun 117649 (7^25) 343 76146 3 722470125228953285510 3 597423538710255856861 223494390856658804114 = (3,639133074333616322732,3,242045862518722258933,679546962738089289516) := by rfl
theorem s6_s223 : Disp.arun 117649 (7^25) 343 76489 3 639133074333616322732 3 242045862518722258933 679546962738089289516 = (2,61010106840325759401,2,968046136837546948631,108956256562016258592) := by rfl
theorem s6_s224 : Disp.arun 117649 (7^25) 343 76832 2 61010106840325759401 2 968046136837546948631 108956256562016258592 = (3,456525782103256478691,3,416028793542793168753,1195313877716358852271) := by rfl
theorem s6_s225 : Disp.arun 117649 (7^25) 343 77175 3 456525782103256478691 3 416028793542793168753 1195313877716358852271 = (3,830690236935415719187,3,682902725254814601933,1336113800649338864609) := by rfl
theorem s6_s226 : Disp.arun 117649 (7^25) 343 77518 3 830690236935415719187 3 682902725254814601933 1336113800649338864609 = (3,835503480024385799492,3,537347627185918203814,375828164810420384924) := by rfl
theorem s6_s227 : Disp.arun 117649 (7^25) 343 77861 3 835503480024385799492 3 537347627185918203814 375828164810420384924 = (3,402418951863216300661,3,1224955186033673175804,637697690429296882603) := by rfl
theorem s6_s228 : Disp.arun 117649 (7^25) 343 78204 3 402418951863216300661 3 1224955186033673175804 637697690429296882603 = (3,404332313967770139052,3,631411974486790667649,191540656705000327040) := by rfl
theorem s6_s229 : Disp.arun 117649 (7^25) 343 78547 3 404332313967770139052 3 631411974486790667649 191540656705000327040 = (3,691346053645641580915,3,1109754917406792631491,111213818137182226068) := by rfl
theorem s6_s230 : Disp.arun 117649 (7^25) 343 78890 3 691346053645641580915 3 1109754917406792631491 111213818137182226068 = (2,526912302991069203715,2,121592689491404982217,874787224446336191369) := by rfl
theorem s6_s231 : Disp.arun 117649 (7^25) 343 79233 2 526912302991069203715 2 121592689491404982217 874787224446336191369 = (3,781368433062052196353,3,580957014497193313834,124867860747189098239) := by rfl
theorem s6_s232 : Disp.arun 117649 (7^25) 343 79576 3 781368433062052196353 3 580957014497193313834 124867860747189098239 = (3,1032636902545584937024,3,1323379622461116813639,570860292583010364908) := by rfl
theorem s6_s233 : Disp.arun 117649 (7^25) 343 79919 3 1032636902545584937024 3 1323379622461116813639 570860292583010364908 = (3,611783502939398394635,3,800379703368885795636,1279922432535483892380) := by rfl
theorem s6_s234 : Disp.arun 117649 (7^25) 343 80262 3 611783502939398394635 3 800379703368885795636 1279922432535483892380 = (3,250738224251293672224,3,657389560142555892437,680707223628870582180) := by rfl
theorem s6_s235 : Disp.arun 117649 (7^25) 343 80605 3 250738224251293672224 3 657389560142555892437 680707223628870582180 = (3,130138327259196534163,3,1005022069616116467975,16665391524319380613) := by rfl
theorem s6_s236 : Disp.arun 117649 (7^25) 343 80948 3 130138327259196534163 3 1005022069616116467975 16665391524319380613 = (3,633670419586457260398,3,468940157111124086212,168893469584005249112) := by rfl
theorem s6_s237 : Disp.arun 117649 (7^25) 343 81291 3 633670419586457260398 3 468940157111124086212 168893469584005249112 = (2,99218854847007164914,2,243724285253623868560,1035328515848803686658) := by rfl
theorem s6_s238 : Disp.arun 117649 (7^25) 343 81634 2 99218854847007164914 2 243724285253623868560 1035328515848803686658 = (3,1194865341204752958693,3,238928122956807253852,1004768780365383607995) := by rfl
theorem s6_s239 : Disp.arun 117649 (7^25) 343 81977 3 1194865341204752958693 3 238928122956807253852 1004768780365383607995 = (3,426996658482702599756,3,1019469410049412878420,1256515239266966406239) := by rfl
theorem s6_s240 : Disp.arun 117649 (7^25) 343 82320 3 426996658482702599756 3 1019469410049412878420 1256515239266966406239 = (3,1059976910877101531109,3,660205190596020634493,882083222056693518513) := by rfl
theorem s6_s241 : Disp.arun 117649 (7^25) 343 82663 3 1059976910877101531109 3 660205190596020634493 882083222056693518513 = (3,560677798383114115359,3,1061376353247166066966,964406621056088009416) := by rfl
theorem s6_s242 : Disp.arun 117649 (7^25) 343 83006 3 560677798383114115359 3 1061376353247166066966 964406621056088009416 = (3,523186537209546047176,3,1082969979745464028277,1150848937541781116668) := by rfl
theorem s6_s243 : Disp.arun 117649 (7^25) 343 83349 3 523186537209546047176 3 1082969979745464028277 1150848937541781116668 = (3,1222378749202164814023,3,316398315763545883951,559788537751049167184) := by rfl
theorem s6_s244 : Disp.arun 117649 (7^25) 343 83692 3 1222378749202164814023 3 316398315763545883951 559788537751049167184 = (1,709633021594898681717,1,136731638610593564079,195872711746427951600) := by rfl
theorem s6_s245 : Disp.arun 117649 (7^25) 343 84035 1 709633021594898681717 1 136731638610593564079 195872711746427951600 = (3,1334346679077728906043,3,880359562171254234084,1146351405435603219014) := by rfl
theorem s6_s246 : Disp.arun 117649 (7^25) 343 84378 3 1334346679077728906043 3 880359562171254234084 1146351405435603219014 = (3,198271568428530013274,3,337991197885258429054,1284389820562880362997) := by rfl
theorem s6_s247 : Disp.arun 117649 (7^25) 343 84721 3 198271568428530013274 3 337991197885258429054 1284389820562880362997 = (3,239795594347708824763,3,125233466590212580304,1118814966734854740170) := by rfl
theorem s6_s248 : Disp.arun 117649 (7^25) 343 85064 3 239795594347708824763 3 125233466590212580304 1118814966734854740170 = (3,765279858810005124238,3,1266212778425363035892,777277491128315393448) := by rfl
theorem s6_s249 : Disp.arun 117649 (7^25) 343 85407 3 765279858810005124238 3 1266212778425363035892 777277491128315393448 = (3,959775503805076451231,3,957775027632427223068,961949158235928284304) := by rfl
theorem s6_s250 : Disp.arun 117649 (7^25) 343 85750 3 959775503805076451231 3 957775027632427223068 961949158235928284304 = (3,247715934816110733636,3,1233163318113140503620,918114446757392574110) := by rfl
theorem s6_s251 : Disp.arun 117649 (7^25) 343 86093 3 247715934816110733636 3 1233163318113140503620 918114446757392574110 = (2,1076333504034051436655,2,447368043181492696152,316413626720375602832) := by rfl
theorem s6_s252 : Disp.arun 117649 (7^25) 343 86436 2 1076333504034051436655 2 447368043181492696152 316413626720375602832 = (3,186292149194001486483,3,255843314369789799115,1315372619236060954479) := by rfl
theorem s6_s253 : Disp.arun 117649 (7^25) 343 86779 3 186292149194001486483 3 255843314369789799115 1315372619236060954479 = (3,482543509336840688124,3,1216222961015728217444,801220736519288138789) := by rfl
theorem s6_s254 : Disp.arun 117649 (7^25) 343 87122 3 482543509336840688124 3 1216222961015728217444 801220736519288138789 = (3,650920936721968061644,3,1239722446946058228249,407162166901410589845) := by rfl
theorem s6_s255 : Disp.arun 117649 (7^25) 343 87465 3 650920936721968061644 3 1239722446946058228249 407162166901410589845 = (3,1283448156589248951908,3,1103111903291125825386,648472532133228546003) := by rfl
theorem s6_s256 : Disp.arun 117649 (7^25) 343 87808 3 1283448156589248951908 3 1103111903291125825386 648472532133228546003 = (3,626201552150371863403,3,685305523973161424728,190844134991335921383) := by rfl
theorem s6_s257 : Disp.arun 117649 (7^25) 343 88151 3 626201552150371863403 3 685305523973161424728 190844134991335921383 = (3,859804890804137210059,3,559596324097609640197,998617152003792992777) := by rfl
theorem s6_s258 : Disp.arun 117649 (7^25) 343 88494 3 859804890804137210059 3 559596324097609640197 998617152003792992777 = (2,839487347159287581381,2,302003000365889461468,322979377450224208015) := by rfl
theorem s6_s259 : Disp.arun 117649 (7^25) 343 88837 2 839487347159287581381 2 302003000365889461468 322979377450224208015 = (3,648625448067642446302,3,6207350811490281188,344176942279356711603) := by rfl
theorem s6_s260 : Disp.arun 117649 (7^25) 343 89180 3 648625448067642446302 3 6207350811490281188 344176942279356711603 = (3,1021001427147166857697,3,175684430618991809323,432196946230920155832) := by rfl
theorem s6_s261 : Disp.arun 117649 (7^25) 343 89523 3 1021001427147166857697 3 175684430618991809323 432196946230920155832 = (3,126303903384071558483,3,1189477763450587662098,714832191302270598432) := by rfl
theorem s6_s262 : Disp.arun 117649 (7^25) 343 89866 3 126303903384071558483 3 1189477763450587662098 714832191302270598432 = (3,257632332866704955168,3,202780796861735710039,415500517559988377868) := by rfl
theorem s6_s263 : Disp.arun 117649 (7^25) 343 90209 3 257632332866704955168 3 202780796861735710039 415500517559988377868 = (3,611438204244777217354,3,885017765953196297313,175821142744677793679) := by rfl
theorem s6_s264 : Disp.arun 117649 (7^25) 343 90552 3 611438204244777217354 3 885017765953196297313 175821142744677793679 = (3,655126397143078579816,3,348223410331194877583,939159258202920658177) := by rfl
theorem s6_s265 : Disp.arun 117649 (7^25) 343 90895 3 655126397143078579816 3 348223410331194877583 939159258202920658177 = (2,1185229143978850067463,2,436180181355680203650,219296354069344602044) := by rfl
theorem s6_s266 : Disp.arun 117649 (7^25) 343 91238 2 1185229143978850067463 2 436180181355680203650 219296354069344602044 = (3,789733115710830678570,3,1188012841965241095994,278537586416525935850) := by rfl
theorem s6_s267 : Disp.arun 117649 (7^25) 343 91581 3 789733115710830678570 3 1188012841965241095994 278537586416525935850 = (3,995797094524875363234,3,235481205614382364452,1204088651323249306399) := by rfl
theorem s6_s268 : Disp.arun 117649 (7^25) 343 91924 3 995797094524875363234 3 235481205614382364452 1204088651323249306399 = (3,1156274683175943225606,3,739077176910875805427,888007942385135615975) := by rfl
theorem s6_s269 : Disp.arun 117649 (7^25) 343 92267 3 1156274683175943225606 3 739077176910875805427 888007942385135615975 = (3,94962586788471709368,3,769373799901325919421,1302430164595913623068) := by rfl
theorem s6_s270 : Disp.arun 117649 (7^25) 343 92610 3 94962586788471709368 3 769373799901325919421 1302430164595913623068 = (3,1147883549103635509000,3,1241714789323137930636,1298501443726420147152) := by rfl
theorem s6_s271 : Disp.arun 117649 (7^25) 343 92953 3 1147883549103635509000 3 1241714789323137930636 1298501443726420147152 = (3,405128729024883230067,3,1064910132573166079507,939391446386344354831) := by rfl
theorem s6_s272 : Disp.arun 117649 (7^25) 343 93296 3 405128729024883230067 3 1064910132573166079507 939391446386344354831 = (2,555963522565663419321,2,150095176540187901626,960073672689148884371) := by rfl
theorem s6_s273 : Disp.arun 117649 (7^25) 343 93639 2 555963522565663419321 2 150095176540187901626 960073672689148884371 = (3,579260003286308011114,3,716705090944332848170,686304370592933583058) := by rfl
theorem s6_s274 : Disp.arun 117649 (7^25) 343 93982 3 579260003286308011114 3 716705090944332848170 686304370592933583058 = (3,816323275075703991516,3,997270628373317142849,1196618071732433889680) := by rfl
theorem s6_s275 : Disp.arun 117649 (7^25) 343 94325 3 816323275075703991516 3 997270628373317142849 1196618071732433889680 = (3,71768111654060588839,3,818387658425602905813,1027669830225508425236) := by rfl
theorem s6_s276 : Disp.arun 117649 (7^25) 343 94668 3 71768111654060588839 3 818387658425602905813 1027669830225508425236 = (3,198192622445232525154,3,322794532044034870773,593853018901863439720) := by rfl
theorem s6_s277 : Disp.arun 117649 (7^25) 343 95011 3 198192622445232525154 3 322794532044034870773 593853018901863439720 = (3,753725665173533748427,3,285973604264345945412,1184540756803361907671) := by rfl
theorem s6_s278 : Disp.arun 117649 (7^25) 343 95354 3 753725665173533748427 3 285973604264345945412 1184540756803361907671 = (3,194813878651403946654,3,416787390835225464438,1280542216551672847452) := by rfl
theorem s6_s279 : Disp.arun 117649 (7^25) 343 95697 3 194813878651403946654 3 416787390835225464438 1280542216551672847452 = (2,1325940205989865057883,2,1147933906614412561367,142968198977632409676) := by rfl
theorem s6_s280 : Disp.arun 117649 (7^25) 343 96040 2 1325940205989865057883 2 1147933906614412561367 142968198977632409676 = (3,280279446638240623981,3,308100609694678229255,639397046029918131117) := by rfl
theorem s6_s281 : Disp.arun 117649 (7^25) 343 96383 3 280279446638240623981 3 308100609694678229255 639397046029918131117 = (3,1022693995748578526817,3,710483794494914714684,893993438686329767080) := by rfl
theorem s6_s282 : Disp.arun 117649 (7^25) 343 96726 3 1022693995748578526817 3 710483794494914714684 893993438686329767080 = (3,834867975508530372190,3,890628707178759435437,288552051310531470330) := by rfl
theorem s6_s283 : Disp.arun 117649 (7^25) 343 97069 3 834867975508530372190 3 890628707178759435437 288552051310531470330 = (3,773228459137821733212,3,194894898940777853750,244555017866506932761) := by rfl
theorem s6_s284 : Disp.arun 117649 (7^25) 343 97412 3 773228459137821733212 3 194894898940777853750 244555017866506932761 = (3,1157534283125895391734,3,1016802169512550412113,740900113928880827370) := by rfl
theorem s6_s285 : Disp.arun 117649 (7^25) 343 97755 3 1157534283125895391734 3 1016802169512550412113 740900113928880827370 = (3,1208561507862274829915,3,1234665240229515975257,9387728181614605565) := by rfl
theorem s6_s286 : Disp.arun 117649 (7^25) 343 98098 3 1208561507862274829915 3 1234665240229515975257 9387728181614605565 = (2,652992312247592459981,2,530213704389757656827,897896832297899088362) := by rfl
theorem s6_s287 : Disp.arun 117649 (7^25) 343 98441 2 652992312247592459981 2 530213704389757656827 897896832297899088362 = (3,1169791340116692844340,3,1205832661607615270902,1314525060377154056019) := by rfl
theorem s6_s288 : Disp.arun 117649 (7^25) 343 98784 3 1169791340116692844340 3 1205832661607615270902 1314525060377154056019 = (3,351704394635956446550,3,455541288976086593914,283761971739508390801) := by rfl
theorem s6_s289 : Disp.arun 117649 (7^25) 343 99127 3 351704394635956446550 3 455541288976086593914 283761971739508390801 = (3,939496994992914279420,3,458808453887174553209,72408263080572439658) := by rfl
theorem s6_s290 : Disp.arun 117649 (7^25) 343 99470 3 939496994992914279420 3 458808453887174553209 72408263080572439658 = (3,130936805473861681471,3,953077123585767013388,739455718686583500757) := by rfl
theorem s6_s291 : Disp.arun 117649 (7^25) 343 99813 3 130936805473861681471 3 953077123585767013388 739455718686583500757 = (3,318826659332766945168,3,643239273420570467259,134987722656818118011) := by rfl
theorem s6_s292 : Disp.arun 117649 (7^25) 343 100156 3 318826659332766945168 3 643239273420570467259 134987722656818118011 = (3,1170467558225757008503,3,564760361718190675834,821088589085949378615) := by rfl
theorem s6_s293 : Disp.arun 117649 (7^25) 343 100499 3 1170467558225757008503 3 564760361718190675834 821088589085949378615 = (1,250682943662213745446,1,880131730000175599736,629365902767589354032) := by rfl
theorem s6_s294 : Disp.arun 117649 (7^25) 343 100842 1 250682943662213745446 1 880131730000175599736 629365902767589354032 = (3,624976193127525882826,3,1294092625329759559347,284532566090947115376) := by rfl
theorem s6_s295 : Disp.arun 117649 (7^25) 343 101185 3 624976193127525882826 3 1294092625329759559347 284532566090947115376 = (3,127640055842949049095,3,879613917516794721748,1136858797240037675868) := by rfl
theorem s6_s296 : Disp.arun 117649 (7^25) 343 101528 3 127640055842949049095 3 879613917516794721748 1136858797240037675868 = (3,455947466389503145160,3,835210583241395159454,560693178542771437206) := by rfl
theorem s6_s297 : Disp.arun 117649 (7^25) 343 101871 3 455947466389503145160 3 835210583241395159454 560693178542771437206 = (3,418036360015284155360,3,1083610294122854808256,154230552334721216747) := by rfl
theorem s6_s298 : Disp.arun 117649 (7^25) 343 102214 3 418036360015284155360 3 1083610294122854808256 154230552334721216747 = (3,851430368967532455426,3,552673477340568728826,363838692000302589092) := by rfl
theorem s6_s299 : Disp.arun 117649 (7^25) 343 102557 3 851430368967532455426 3 552673477340568728826 363838692000302589092 = (3,443053607397517948014,3,820679062551863663336,291899000332970041887) := by rfl
theorem s6_s300 : Disp.arun 117649 (7^25) 343 102900 3 443053607397517948014 3 820679062551863663336 291899000332970041887 = (2,1155438908825828169831,2,1279669104920132168145,263891387606354881843) := by rfl
theorem s6_s301 : Disp.arun 117649 (7^25) 343 103243 2 1155438908825828169831 2 1279669104920132168145 263891387606354881843 = (3,624209434588727324273,3,998874748575666088372,106225363781434343279) := by rfl
theorem s6_s302 : Disp.arun 117649 (7^25) 343 103586 3 624209434588727324273 3 998874748575666088372 106225363781434343279 = (3,209935717457740091206,3,677017375178906533083,156851161228772637243) := by rfl
theorem s6_s303 : Disp.arun 117649 (7^25) 343 103929 3 209935717457740091206 3 677017375178906533083 156851161228772637243 = (3,1131982467941576327526,3,958221704379611788905,275813332156609441664) := by rfl
theorem s6_s304 : Disp.arun 117649 (7^25) 343 104272 3 1131982467941576327526 3 958221704379611788905 275813332156609441664 = (3,39392278533245709528,3,196564381413991799833,497411061032856325244) := by rfl
theorem s6_s305 : Disp.arun 117649 (7^25) 343 104615 3 39392278533245709528 3 196564381413991799833 497411061032856325244 = (3,407845693585122485179,3,191619264963384156230,332675405818114765316) := by rfl
theorem s6_s306 : Disp.arun 117649 (7^25) 343 104958 3 407845693585122485179 3 191619264963384156230 332675405818114765316 = (3,876438941251343474521,3,435883544809713264291,1001317424936152956227) := by rfl
theorem s6_s307 : Disp.arun 117649 (7^25) 343 105301 3 876438941251343474521 3 435883544809713264291 1001317424936152956227 = (2,149757218028327919292,2,460465636727177059283,691195091290837809012) := by rfl
theorem s6_s308 : Disp.arun 117649 (7^25) 343 105644 2 149757218028327919292 2 460465636727177059283 691195091290837809012 = (3,1124770197481180240810,3,40019781699382924020,424831639823386496268) := by rfl
theorem s6_s309 : Disp.arun 117649 (7^25) 343 105987 3 1124770197481180240810 3 40019781699382924020 424831639823386496268 = (3,421854992434666939326,3,139041377014227818365,32331460039405177274) := by rfl
theorem s6_s310 : Disp.arun 117649 (7^25) 343 106330 3 421854992434666939326 3 139041377014227818365 32331460039405177274 = (3,1114727749503533584354,3,1195233496354139842654,54963364271684516796) := by rfl
theorem s6_s311 : Disp.arun 117649 (7^25) 343 106673 3 1114727749503533584354 3 1195233496354139842654 54963364271684516796 = (3,1127043048553611256905,3,478359176370817245961,321075964275332264083) := by rfl
theorem s6_s312 : Disp.arun 117649 (7^25) 343 107016 3 1127043048553611256905 3 478359176370817245961 321075964275332264083 = (3,297180757953847922101,3,1317395591022362778958,972176386154365514816) := by rfl
theorem s6_s313 : Disp.arun 117649 (7^25) 343 107359 3 297180757953847922101 3 1317395591022362778958 972176386154365514816 = (3,286743065708758124880,3,1027592201252859471592,1276997047686201204861) := by rfl
theorem s6_s314 : Disp.arun 117649 (7^25) 343 107702 3 286743065708758124880 3 1027592201252859471592 1276997047686201204861 = (2,860052123623736754436,2,1062657771257393316570,147900533572193660098) := by rfl
theorem s6_s315 : Disp.arun 117649 (7^25) 343 108045 2 860052123623736754436 2 1062657771257393316570 147900533572193660098 = (3,270749732791302488884,3,1062510612805312852231,1111952578508005556449) := by rfl
theorem s6_s316 : Disp.arun 117649 (7^25) 343 108388 3 270749732791302488884 3 1062510612805312852231 1111952578508005556449 = (3,656993141551310246057,3,529192584882962050607,194276413660324077454) := by rfl
theorem s6_s317 : Disp.arun 117649 (7^25) 343 108731 3 656993141551310246057 3 529192584882962050607 194276413660324077454 = (3,930517691570142379713,3,1059719254569641284302,182750169552817330598) := by rfl
theorem s6_s318 : Disp.arun 117649 (7^25) 343 109074 3 930517691570142379713 3 1059719254569641284302 182750169552817330598 = (3,896809642618983789425,3,236944173858829974637,495349411494636925332) := by rfl
theorem s6_s319 : Disp.arun 117649 (7^25) 343 109417 3 896809642618983789425 3 236944173858829974637 495349411494636925332 = (3,597057720594278716735,3,1262338073164730313909,613609156640920507565) := by rfl
theorem s6_s320 : Disp.arun 117649 (7^25) 343 109760 3 597057720594278716735 3 1262338073164730313909 613609156640920507565 = (3,670189137411284383528,3,1155519468091601268214,923978539601291036304) := by rfl
theorem s6_s321 : Disp.arun 117649 (7^25) 343 110103 3 670189137411284383528 3 1155519468091601268214 923978539601291036304 = (2,1318141762523998581909,2,1180977147357136835792,556783790765136595963) := by rfl
theorem s6_s322 : Disp.arun 117649 (7^25) 343 110446 2 1318141762523998581909 2 1180977147357136835792 556783790765136595963 = (3,1131186596708439174583,3,190876943945720679725,533130776158698310825) := by rfl
theorem s6_s323 : Disp.arun 117649 (7^25) 343 110789 3 1131186596708439174583 3 190876943945720679725 533130776158698310825 = (3,517598928768395453542,3,593708784964107500349,442397626675548237100) := by rfl
theorem s6_s324 : Disp.arun 117649 (7^25) 343 111132 3 517598928768395453542 3 593708784964107500349 442397626675548237100 = (3,387085178131660867017,3,263855810983215969600,1287806544285585198981) := by rfl
theorem s6_s325 : Disp.arun 117649 (7^25) 343 111475 3 387085178131660867017 3 263855810983215969600 1287806544285585198981 = (3,265231419042721748433,3,420453703513863598007,109884381442555718307) := by rfl
theorem s6_s326 : Disp.arun 117649 (7^25) 343 111818 3 265231419042721748433 3 420453703513863598007 109884381442555718307 = (3,793973234892083640677,3,1162995910968396877319,93752965049785649133) := by rfl
theorem s6_s327 : Disp.arun 117649 (7^25) 343 112161 3 793973234892083640677 3 1162995910968396877319 93752965049785649133 = (3,38603342118300162183,3,113869547925662276418,1188858966224350516376) := by rfl
theorem s6_s328 : Disp.arun 117649 (7^25) 343 112504 3 38603342118300162183 3 113869547925662276418 1188858966224350516376 = (2,527749988428974657293,2,1131990438222581422264,695604309998638450677) := by rfl
theorem s6_s329 : Disp.arun 117649 (7^25) 343 112847 2 527749988428974657293 2 1131990438222581422264 695604309998638450677 = (3,198994904548099032673,3,813338747183063999374,870964602607070261396) := by rfl
theorem s6_s330 : Disp.arun 117649 (7^25) 343 113190 3 198994904548099032673 3 813338747183063999374 870964602607070261396 = (3,880409664531227717492,3,951110382867019954940,826590682816069486687) := by rfl
theorem s6_s331 : Disp.arun 117649 (7^25) 343 113533 3 880409664531227717492 3 951110382867019954940 826590682816069486687 = (3,939522389194202614761,3,399035412372099227184,287852960579060089109) := by rfl
theorem s6_s332 : Disp.arun 117649 (7^25) 343 113876 3 939522389194202614761 3 399035412372099227184 287852960579060089109 = (3,1086049373877897747250,3,910082214606480195835,1192616460897212951678) := by rfl
theorem s6_s333 : Disp.arun 117649 (7^25) 343 114219 3 1086049373877897747250 3 910082214606480195835 1192616460897212951678 = (3,90078468004214639499,3,1030167007161345419229,574337089712344182806) := by rfl
theorem s6_s334 : Disp.arun 117649 (7^25) 343 114562 3 90078468004214639499 3 1030167007161345419229 574337089712344182806 = (3,1245071362813592380695,3,267894300476374396684,1037327497235646435092) := by rfl
theorem s6_s335 : Disp.arun 117649 (7^25) 343 114905 3 1245071362813592380695 3 267894300476374396684 1037327497235646435092 = (2,150941942414299175196,2,1242776448777207885099,542842637659903305334) := by rfl
theorem s6_s336 : Disp.arun 117649 (7^25) 343 115248 2 150941942414299175196 2 1242776448777207885099 542842637659903305334 = (3,51544946519567379446,3,222876284232909526668,1029119213947003546620) := by rfl
theorem s6_s337 : Disp.arun 117649 (7^25) 343 115591 3 51544946519567379446 3 222876284232909526668 1029119213947003546620 = (3,1039626253192599878809,3,354152654228906810344,688238840273426259546) := by rfl
theorem s6_s338 : Disp.arun 117649 (7^25) 343 115934 3 1039626253192599878809 3 354152654228906810344 688238840273426259546 = (3,1219021433766825930603,3,215254208389170556835,1209310202012476557498) := by rfl
theorem s6_s339 : Disp.arun 117649 (7^25) 343 116277 3 1219021433766825930603 3 215254208389170556835 1209310202012476557498 = (3,68793879830137568419,3,731291885325590202077,1045639033025257126562) := by rfl
theorem s6_s340 : Disp.arun 117649 (7^25) 343 116620 3 68793879830137568419 3 731291885325590202077 1045639033025257126562 = (3,1219663972324357079096,3,987943894097897562129,68507982851596800254) := by rfl
theorem s6_s341 : Disp.arun 117649 (7^25) 343 116963 3 1219663972324357079096 3 987943894097897562129 68507982851596800254 = (3,687843876034320749108,3,1031382220773721705069,980738726689953528564) := by rfl
theorem s6_s342 : Disp.arun 117649 (7^25) 343 117306 3 687843876034320749108 3 1031382220773721705069 980738726689953528564 = (0,1,0,1053715666652496881601,821327337676838434975) := by rfl
theorem s6_c0 : Disp.arun 117649 (7^25) 343 0 0 1 0 1 0 = (3,687843876034320749108,3,902522019511674612289,551076796170696751852) := s6_s0
theorem s6_c1 : Disp.arun 117649 (7^25) 686 0 0 1 0 1 0 = (3,1219663972324357079096,3,426507929425418769338,40769893373183237194) := by
  rw [show (686:ℕ) = 343 + 343 from rfl, Disp.arun_add, s6_c0, Nat.zero_add]; exact s6_s1
theorem s6_c2 : Disp.arun 117649 (7^25) 1029 0 0 1 0 1 0 = (3,68793879830137568419,3,565213276705932892056,1013353305520025371497) := by
  rw [show (1029:ℕ) = 686 + 343 from rfl, Disp.arun_add, s6_c1, Nat.zero_add]; exact s6_s2
theorem s6_c3 : Disp.arun 117649 (7^25) 1372 0 0 1 0 1 0 = (3,1219021433766825930603,3,1311661256272797974196,427540824636435020442) := by
  rw [show (1372:ℕ) = 1029 + 343 from rfl, Disp.arun_add, s6_c2, Nat.zero_add]; exact s6_s3
theorem s6_c4 : Disp.arun 117649 (7^25) 1715 0 0 1 0 1 0 = (3,1039626253192599878809,3,1280646931357401056263,1029076554173697220325) := by
  rw [show (1715:ℕ) = 1372 + 343 from rfl, Disp.arun_add, s6_c3, Nat.zero_add]; exact s6_s4
theorem s6_c5 : Disp.arun 117649 (7^25) 2058 0 0 1 0 1 0 = (3,51544946519567379446,3,987443114735406241142,1230712469793538122490) := by
  rw [show (2058:ℕ) = 1715 + 343 from rfl, Disp.arun_add, s6_c4, Nat.zero_add]; exact s6_s5
theorem s6_c6 : Disp.arun 117649 (7^25) 2401 0 0 1 0 1 0 = (2,150941942414299175196,2,57320838784838356862,78196334352884457123) := by
  rw [show (2401:ℕ) = 2058 + 343 from rfl, Disp.arun_add, s6_c5, Nat.zero_add]; exact s6_s6
theorem s6_c7 : Disp.arun 117649 (7^25) 2744 0 0 1 0 1 0 = (3,1245071362813592380695,3,1191051242167027476971,1096265209628194880492) := by
  rw [show (2744:ℕ) = 2401 + 343 from rfl, Disp.arun_add, s6_c6, Nat.zero_add]; exact s6_s7
theorem s6_c8 : Disp.arun 117649 (7^25) 3087 0 0 1 0 1 0 = (3,90078468004214639499,3,1270341202918376488407,1069411118606992289241) := by
  rw [show (3087:ℕ) = 2744 + 343 from rfl, Disp.arun_add, s6_c7, Nat.zero_add]; exact s6_s8
theorem s6_c9 : Disp.arun 117649 (7^25) 3430 0 0 1 0 1 0 = (3,1086049373877897747250,3,979383174582226449677,377633130830572839755) := by
  rw [show (3430:ℕ) = 3087 + 343 from rfl, Disp.arun_add, s6_c8, Nat.zero_add]; exact s6_s9
theorem s6_c10 : Disp.arun 117649 (7^25) 3773 0 0 1 0 1 0 = (3,939522389194202614761,3,416117099917593106069,811553718672183766077) := by
  rw [show (3773:ℕ) = 3430 + 343 from rfl, Disp.arun_add, s6_c9, Nat.zero_add]; exact s6_s10
theorem s6_c11 : Disp.arun 117649 (7^25) 4116 0 0 1 0 1 0 = (3,880409664531227717492,3,930428623566339315106,45967446507574591217) := by
  rw [show (4116:ℕ) = 3773 + 343 from rfl, Disp.arun_add, s6_c10, Nat.zero_add]; exact s6_s11
theorem s6_c12 : Disp.arun 117649 (7^25) 4459 0 0 1 0 1 0 = (3,198994904548099032673,3,1177165824075289425845,878784587035238101625) := by
  rw [show (4459:ℕ) = 4116 + 343 from rfl, Disp.arun_add, s6_c11, Nat.zero_add]; exact s6_s12
theorem s6_c13 : Disp.arun 117649 (7^25) 4802 0 0 1 0 1 0 = (2,527749988428974657293,2,653011441757198116758,893358679276337407442) := by
  rw [show (4802:ℕ) = 4459 + 343 from rfl, Disp.arun_add, s6_c12, Nat.zero_add]; exact s6_s13
theorem s6_c14 : Disp.arun 117649 (7^25) 5145 0 0 1 0 1 0 = (3,38603342118300162183,3,1106499439545657640127,846441009176007288688) := by
  rw [show (5145:ℕ) = 4802 + 343 from rfl, Disp.arun_add, s6_c13, Nat.zero_add]; exact s6_s14
theorem s6_c15 : Disp.arun 117649 (7^25) 5488 0 0 1 0 1 0 = (3,793973234892083640677,3,809431443451975572001,962453379122682503421) := by
  rw [show (5488:ℕ) = 5145 + 343 from rfl, Disp.arun_add, s6_c14, Nat.zero_add]; exact s6_s15
theorem s6_c16 : Disp.arun 117649 (7^25) 5831 0 0 1 0 1 0 = (3,265231419042721748433,3,817068750979548731207,995693077445025581175) := by
  rw [show (5831:ℕ) = 5488 + 343 from rfl, Disp.arun_add, s6_c15, Nat.zero_add]; exact s6_s16
theorem s6_c17 : Disp.arun 117649 (7^25) 6174 0 0 1 0 1 0 = (3,387085178131660867017,3,292097598483212147432,836884229962347700575) := by
  rw [show (6174:ℕ) = 5831 + 343 from rfl, Disp.arun_add, s6_c16, Nat.zero_add]; exact s6_s17
theorem s6_c18 : Disp.arun 117649 (7^25) 6517 0 0 1 0 1 0 = (3,517598928768395453542,3,477137282273868155929,583577396939935537021) := by
  rw [show (6517:ℕ) = 6174 + 343 from rfl, Disp.arun_add, s6_c17, Nat.zero_add]; exact s6_s18
theorem s6_c19 : Disp.arun 117649 (7^25) 6860 0 0 1 0 1 0 = (3,1131186596708439174583,3,620183840581702020378,909436749797145935954) := by
  rw [show (6860:ℕ) = 6517 + 343 from rfl, Disp.arun_add, s6_c18, Nat.zero_add]; exact s6_s19
theorem s6_c20 : Disp.arun 117649 (7^25) 7203 0 0 1 0 1 0 = (2,1318141762523998581909,2,77873453347969728937,337975805035398218767) := by
  rw [show (7203:ℕ) = 6860 + 343 from rfl, Disp.arun_add, s6_c19, Nat.zero_add]; exact s6_s20
theorem s6_c21 : Disp.arun 117649 (7^25) 7546 0 0 1 0 1 0 = (3,670189137411284383528,3,706900085621746396108,1309655523474205020569) := by
  rw [show (7546:ℕ) = 7203 + 343 from rfl, Disp.arun_add, s6_c20, Nat.zero_add]; exact s6_s21
theorem s6_c22 : Disp.arun 117649 (7^25) 7889 0 0 1 0 1 0 = (3,597057720594278716735,3,661728804178229548457,49222045603715980507) := by
  rw [show (7889:ℕ) = 7546 + 343 from rfl, Disp.arun_add, s6_c21, Nat.zero_add]; exact s6_s22
theorem s6_c23 : Disp.arun 117649 (7^25) 8232 0 0 1 0 1 0 = (3,896809642618983789425,3,582026545627512215879,1067877272200453693560) := by
  rw [show (8232:ℕ) = 7889 + 343 from rfl, Disp.arun_add, s6_c22, Nat.zero_add]; exact s6_s23
theorem s6_c24 : Disp.arun 117649 (7^25) 8575 0 0 1 0 1 0 = (3,930517691570142379713,3,1220877569132597673418,463274298830733183823) := by
  rw [show (8575:ℕ) = 8232 + 343 from rfl, Disp.arun_add, s6_c23, Nat.zero_add]; exact s6_s24
theorem s6_c25 : Disp.arun 117649 (7^25) 8918 0 0 1 0 1 0 = (3,656993141551310246057,3,498572070891286677925,1081919249262809533724) := by
  rw [show (8918:ℕ) = 8575 + 343 from rfl, Disp.arun_add, s6_c24, Nat.zero_add]; exact s6_s25
theorem s6_c26 : Disp.arun 117649 (7^25) 9261 0 0 1 0 1 0 = (3,270749732791302488884,3,568522086236994619078,1323338026252057737573) := by
  rw [show (9261:ℕ) = 8918 + 343 from rfl, Disp.arun_add, s6_c25, Nat.zero_add]; exact s6_s26
theorem s6_c27 : Disp.arun 117649 (7^25) 9604 0 0 1 0 1 0 = (2,860052123623736754436,2,1025141928328109655345,168808975404140683067) := by
  rw [show (9604:ℕ) = 9261 + 343 from rfl, Disp.arun_add, s6_c26, Nat.zero_add]; exact s6_s27
theorem s6_c28 : Disp.arun 117649 (7^25) 9947 0 0 1 0 1 0 = (3,286743065708758124880,3,114528605409731586165,961806440453043639350) := by
  rw [show (9947:ℕ) = 9604 + 343 from rfl, Disp.arun_add, s6_c27, Nat.zero_add]; exact s6_s28
theorem s6_c29 : Disp.arun 117649 (7^25) 10290 0 0 1 0 1 0 = (3,297180757953847922101,3,869157647923561462141,1323846563066175194236) := by
  rw [show (10290:ℕ) = 9947 + 343 from rfl, Disp.arun_add, s6_c28, Nat.zero_add]; exact s6_s29
theorem s6_c30 : Disp.arun 117649 (7^25) 10633 0 0 1 0 1 0 = (3,1127043048553611256905,3,936103112244767043281,438028832455059773558) := by
  rw [show (10633:ℕ) = 10290 + 343 from rfl, Disp.arun_add, s6_c29, Nat.zero_add]; exact s6_s30
theorem s6_c31 : Disp.arun 117649 (7^25) 10976 0 0 1 0 1 0 = (3,1114727749503533584354,3,696565683488488350133,1164358886137697325027) := by
  rw [show (10976:ℕ) = 10633 + 343 from rfl, Disp.arun_add, s6_c30, Nat.zero_add]; exact s6_s31
theorem s6_c32 : Disp.arun 117649 (7^25) 11319 0 0 1 0 1 0 = (3,421854992434666939326,3,2293022504199788672,917253041535226016902) := by
  rw [show (11319:ℕ) = 10976 + 343 from rfl, Disp.arun_add, s6_c31, Nat.zero_add]; exact s6_s32
theorem s6_c33 : Disp.arun 117649 (7^25) 11662 0 0 1 0 1 0 = (3,1124770197481180240810,3,1041929654337942203238,375709537187207178656) := by
  rw [show (11662:ℕ) = 11319 + 343 from rfl, Disp.arun_add, s6_c32, Nat.zero_add]; exact s6_s33
theorem s6_c34 : Disp.arun 117649 (7^25) 12005 0 0 1 0 1 0 = (2,149757218028327919292,2,878536251335294870664,855496157477003031669) := by
  rw [show (12005:ℕ) = 11662 + 343 from rfl, Disp.arun_add, s6_c33, Nat.zero_add]; exact s6_s34
theorem s6_c35 : Disp.arun 117649 (7^25) 12348 0 0 1 0 1 0 = (3,876438941251343474521,3,800689307087766842831,140110180107258932033) := by
  rw [show (12348:ℕ) = 12005 + 343 from rfl, Disp.arun_add, s6_c34, Nat.zero_add]; exact s6_s35
theorem s6_c36 : Disp.arun 117649 (7^25) 12691 0 0 1 0 1 0 = (3,407845693585122485179,3,527838781225434218404,406980878276315902105) := by
  rw [show (12691:ℕ) = 12348 + 343 from rfl, Disp.arun_add, s6_c35, Nat.zero_add]; exact s6_s36
theorem s6_c37 : Disp.arun 117649 (7^25) 13034 0 0 1 0 1 0 = (3,39392278533245709528,3,786284851834909997981,730011989277903424107) := by
  rw [show (13034:ℕ) = 12691 + 343 from rfl, Disp.arun_add, s6_c36, Nat.zero_add]; exact s6_s37
theorem s6_c38 : Disp.arun 117649 (7^25) 13377 0 0 1 0 1 0 = (3,1131982467941576327526,3,515040383355701128277,1099943022457649298468) := by
  rw [show (13377:ℕ) = 13034 + 343 from rfl, Disp.arun_add, s6_c37, Nat.zero_add]; exact s6_s38
theorem s6_c39 : Disp.arun 117649 (7^25) 13720 0 0 1 0 1 0 = (3,209935717457740091206,3,436266036774214487802,1243296802523960381695) := by
  rw [show (13720:ℕ) = 13377 + 343 from rfl, Disp.arun_add, s6_c38, Nat.zero_add]; exact s6_s39
theorem s6_c40 : Disp.arun 117649 (7^25) 14063 0 0 1 0 1 0 = (3,624209434588727324273,3,343892143419006588195,565246907015968773345) := by
  rw [show (14063:ℕ) = 13720 + 343 from rfl, Disp.arun_add, s6_c39, Nat.zero_add]; exact s6_s40
theorem s6_c41 : Disp.arun 117649 (7^25) 14406 0 0 1 0 1 0 = (2,1155438908825828169831,2,486692699433517295746,1167461358978198323705) := by
  rw [show (14406:ℕ) = 14063 + 343 from rfl, Disp.arun_add, s6_c40, Nat.zero_add]; exact s6_s41
theorem s6_c42 : Disp.arun 117649 (7^25) 14749 0 0 1 0 1 0 = (3,443053607397517948014,3,869938254596606661908,1184839154729857552192) := by
  rw [show (14749:ℕ) = 14406 + 343 from rfl, Disp.arun_add, s6_c41, Nat.zero_add]; exact s6_s42
theorem s6_c43 : Disp.arun 117649 (7^25) 15092 0 0 1 0 1 0 = (3,851430368967532455426,3,1207738234124173467888,827055489129964267377) := by
  rw [show (15092:ℕ) = 14749 + 343 from rfl, Disp.arun_add, s6_c42, Nat.zero_add]; exact s6_s43
theorem s6_c44 : Disp.arun 117649 (7^25) 15435 0 0 1 0 1 0 = (3,418036360015284155360,3,1277967187322780955131,1113120770365485253912) := by
  rw [show (15435:ℕ) = 15092 + 343 from rfl, Disp.arun_add, s6_c43, Nat.zero_add]; exact s6_s44
theorem s6_c45 : Disp.arun 117649 (7^25) 15778 0 0 1 0 1 0 = (3,455947466389503145160,3,1053712637109822226441,1330840584131832216171) := by
  rw [show (15778:ℕ) = 15435 + 343 from rfl, Disp.arun_add, s6_c44, Nat.zero_add]; exact s6_s45
theorem s6_c46 : Disp.arun 117649 (7^25) 16121 0 0 1 0 1 0 = (3,127640055842949049095,3,754498206587754276707,1074310246950948434127) := by
  rw [show (16121:ℕ) = 15778 + 343 from rfl, Disp.arun_add, s6_c45, Nat.zero_add]; exact s6_s46
theorem s6_c47 : Disp.arun 117649 (7^25) 16464 0 0 1 0 1 0 = (3,624976193127525882826,3,627422644928273058941,1175734619201115879207) := by
  rw [show (16464:ℕ) = 16121 + 343 from rfl, Disp.arun_add, s6_c46, Nat.zero_add]; exact s6_s47
theorem s6_c48 : Disp.arun 117649 (7^25) 16807 0 0 1 0 1 0 = (1,250682943662213745446,1,89846240798014862155,689710024495785018615) := by
  rw [show (16807:ℕ) = 16464 + 343 from rfl, Disp.arun_add, s6_c47, Nat.zero_add]; exact s6_s48
theorem s6_c49 : Disp.arun 117649 (7^25) 17150 0 0 1 0 1 0 = (3,1170467558225757008503,3,1286819131857509911935,882856758682892012818) := by
  rw [show (17150:ℕ) = 16807 + 343 from rfl, Disp.arun_add, s6_c48, Nat.zero_add]; exact s6_s49
theorem s6_c50 : Disp.arun 117649 (7^25) 17493 0 0 1 0 1 0 = (3,318826659332766945168,3,584653884995716777406,529443946051140874909) := by
  rw [show (17493:ℕ) = 17150 + 343 from rfl, Disp.arun_add, s6_c49, Nat.zero_add]; exact s6_s50
theorem s6_c51 : Disp.arun 117649 (7^25) 17836 0 0 1 0 1 0 = (3,130936805473861681471,3,1011953604894787872651,1227797631207746540453) := by
  rw [show (17836:ℕ) = 17493 + 343 from rfl, Disp.arun_add, s6_c50, Nat.zero_add]; exact s6_s51
theorem s6_c52 : Disp.arun 117649 (7^25) 18179 0 0 1 0 1 0 = (3,939496994992914279420,3,431304349732216830207,903374249431910753407) := by
  rw [show (18179:ℕ) = 17836 + 343 from rfl, Disp.arun_add, s6_c51, Nat.zero_add]; exact s6_s52
theorem s6_c53 : Disp.arun 117649 (7^25) 18522 0 0 1 0 1 0 = (3,351704394635956446550,3,81740941697478918536,309365818254744574884) := by
  rw [show (18522:ℕ) = 18179 + 343 from rfl, Disp.arun_add, s6_c52, Nat.zero_add]; exact s6_s53
theorem s6_c54 : Disp.arun 117649 (7^25) 18865 0 0 1 0 1 0 = (3,1169791340116692844340,3,1057735648713650104491,938665502429661095895) := by
  rw [show (18865:ℕ) = 18522 + 343 from rfl, Disp.arun_add, s6_c53, Nat.zero_add]; exact s6_s54
theorem s6_c55 : Disp.arun 117649 (7^25) 19208 0 0 1 0 1 0 = (2,652992312247592459981,2,1309144239586714338221,570272944696549130317) := by
  rw [show (19208:ℕ) = 18865 + 343 from rfl, Disp.arun_add, s6_c54, Nat.zero_add]; exact s6_s55
theorem s6_c56 : Disp.arun 117649 (7^25) 19551 0 0 1 0 1 0 = (3,1208561507862274829915,3,226024487481782740990,1278814537345957520938) := by
  rw [show (19551:ℕ) = 19208 + 343 from rfl, Disp.arun_add, s6_c55, Nat.zero_add]; exact s6_s56
theorem s6_c57 : Disp.arun 117649 (7^25) 19894 0 0 1 0 1 0 = (3,1157534283125895391734,3,1015632625785454754158,1108776792924387988906) := by
  rw [show (19894:ℕ) = 19551 + 343 from rfl, Disp.arun_add, s6_c56, Nat.zero_add]; exact s6_s57
theorem s6_c58 : Disp.arun 117649 (7^25) 20237 0 0 1 0 1 0 = (3,773228459137821733212,3,569378246103938736141,693824776165078635820) := by
  rw [show (20237:ℕ) = 19894 + 343 from rfl, Disp.arun_add, s6_c57, Nat.zero_add]; exact s6_s58
theorem s6_c59 : Disp.arun 117649 (7^25) 20580 0 0 1 0 1 0 = (3,834867975508530372190,3,625638414149281821318,24976443609107710455) := by
  rw [show (20580:ℕ) = 20237 + 343 from rfl, Disp.arun_add, s6_c58, Nat.zero_add]; exact s6_s59
theorem s6_c60 : Disp.arun 117649 (7^25) 20923 0 0 1 0 1 0 = (3,1022693995748578526817,3,1075976599226230992314,781236624117194951028) := by
  rw [show (20923:ℕ) = 20580 + 343 from rfl, Disp.arun_add, s6_c59, Nat.zero_add]; exact s6_s60
theorem s6_c61 : Disp.arun 117649 (7^25) 21266 0 0 1 0 1 0 = (3,280279446638240623981,3,1083516781252450314566,436032686620753775176) := by
  rw [show (21266:ℕ) = 20923 + 343 from rfl, Disp.arun_add, s6_c60, Nat.zero_add]; exact s6_s61
theorem s6_c62 : Disp.arun 117649 (7^25) 21609 0 0 1 0 1 0 = (2,1325940205989865057883,2,343850291026238153364,1270624637189747548178) := by
  rw [show (21609:ℕ) = 21266 + 343 from rfl, Disp.arun_add, s6_c61, Nat.zero_add]; exact s6_s62
theorem s6_c63 : Disp.arun 117649 (7^25) 21952 0 0 1 0 1 0 = (3,194813878651403946654,3,736758037258869909977,862089982829833510558) := by
  rw [show (21952:ℕ) = 21609 + 343 from rfl, Disp.arun_add, s6_c62, Nat.zero_add]; exact s6_s63
theorem s6_c64 : Disp.arun 117649 (7^25) 22295 0 0 1 0 1 0 = (3,753725665173533748427,3,411335442909636841607,123269222652664514525) := by
  rw [show (22295:ℕ) = 21952 + 343 from rfl, Disp.arun_add, s6_c63, Nat.zero_add]; exact s6_s64
theorem s6_c65 : Disp.arun 117649 (7^25) 22638 0 0 1 0 1 0 = (3,198192622445232525154,3,430737688720415520358,220108791815687096113) := by
  rw [show (22638:ℕ) = 22295 + 343 from rfl, Disp.arun_add, s6_c64, Nat.zero_add]; exact s6_s65
theorem s6_c66 : Disp.arun 117649 (7^25) 22981 0 0 1 0 1 0 = (3,71768111654060588839,3,604390370342037229414,289010544728331609086) := by
  rw [show (22981:ℕ) = 22638 + 343 from rfl, Disp.arun_add, s6_c65, Nat.zero_add]; exact s6_s66
theorem s6_c67 : Disp.arun 117649 (7^25) 23324 0 0 1 0 1 0 = (3,816323275075703991516,3,420959555583694002410,1193085227257236476612) := by
  rw [show (23324:ℕ) = 22981 + 343 from rfl, Disp.arun_add, s6_c66, Nat.zero_add]; exact s6_s67
theorem s6_c68 : Disp.arun 117649 (7^25) 23667 0 0 1 0 1 0 = (3,579260003286308011114,3,502128876904133068386,85658290712939975164) := by
  rw [show (23667:ℕ) = 23324 + 343 from rfl, Disp.arun_add, s6_c67, Nat.zero_add]; exact s6_s68
theorem s6_c69 : Disp.arun 117649 (7^25) 24010 0 0 1 0 1 0 = (2,555963522565663419321,2,798340369734065910841,162411943839145073207) := by
  rw [show (24010:ℕ) = 23667 + 343 from rfl, Disp.arun_add, s6_c68, Nat.zero_add]; exact s6_s69
theorem s6_c70 : Disp.arun 117649 (7^25) 24353 0 0 1 0 1 0 = (3,405128729024883230067,3,1203356912955639298662,357092610948105081001) := by
  rw [show (24353:ℕ) = 24010 + 343 from rfl, Disp.arun_add, s6_c69, Nat.zero_add]; exact s6_s70
theorem s6_c71 : Disp.arun 117649 (7^25) 24696 0 0 1 0 1 0 = (3,1147883549103635509000,3,1095583425907884246869,913507298268310347561) := by
  rw [show (24696:ℕ) = 24353 + 343 from rfl, Disp.arun_add, s6_c70, Nat.zero_add]; exact s6_s71
theorem s6_c72 : Disp.arun 117649 (7^25) 25039 0 0 1 0 1 0 = (3,94962586788471709368,3,510657895891447500040,591690857481335736986) := by
  rw [show (25039:ℕ) = 24696 + 343 from rfl, Disp.arun_add, s6_c71, Nat.zero_add]; exact s6_s72
theorem s6_c73 : Disp.arun 117649 (7^25) 25382 0 0 1 0 1 0 = (3,1156274683175943225606,3,1266201955021084678095,1103690521882544277634) := by
  rw [show (25382:ℕ) = 25039 + 343 from rfl, Disp.arun_add, s6_c72, Nat.zero_add]; exact s6_s73
theorem s6_c74 : Disp.arun 117649 (7^25) 25725 0 0 1 0 1 0 = (3,995797094524875363234,3,881743798774211946002,1184675997783472357983) := by
  rw [show (25725:ℕ) = 25382 + 343 from rfl, Disp.arun_add, s6_c73, Nat.zero_add]; exact s6_s74
theorem s6_c75 : Disp.arun 117649 (7^25) 26068 0 0 1 0 1 0 = (3,789733115710830678570,3,1217920041245024738466,602069183044108187864) := by
  rw [show (26068:ℕ) = 25725 + 343 from rfl, Disp.arun_add, s6_c74, Nat.zero_add]; exact s6_s75
theorem s6_c76 : Disp.arun 117649 (7^25) 26411 0 0 1 0 1 0 = (2,1185229143978850067463,2,543249749342110583453,974502363180203290777) := by
  rw [show (26411:ℕ) = 26068 + 343 from rfl, Disp.arun_add, s6_c75, Nat.zero_add]; exact s6_s76
theorem s6_c77 : Disp.arun 117649 (7^25) 26754 0 0 1 0 1 0 = (3,655126397143078579816,3,704256131902253774663,621750950903577243274) := by
  rw [show (26754:ℕ) = 26411 + 343 from rfl, Disp.arun_add, s6_c76, Nat.zero_add]; exact s6_s77
theorem s6_c78 : Disp.arun 117649 (7^25) 27097 0 0 1 0 1 0 = (3,611438204244777217354,3,112501753244845610447,408206216600023946952) := by
  rw [show (27097:ℕ) = 26754 + 343 from rfl, Disp.arun_add, s6_c77, Nat.zero_add]; exact s6_s78
theorem s6_c79 : Disp.arun 117649 (7^25) 27440 0 0 1 0 1 0 = (3,257632332866704955168,3,1238632718638357412263,518391971103598149811) := by
  rw [show (27440:ℕ) = 27097 + 343 from rfl, Disp.arun_add, s6_c78, Nat.zero_add]; exact s6_s79
theorem s6_c80 : Disp.arun 117649 (7^25) 27783 0 0 1 0 1 0 = (3,126303903384071558483,3,1280289211275816203786,561048801512328528106) := by
  rw [show (27783:ℕ) = 27440 + 343 from rfl, Disp.arun_add, s6_c79, Nat.zero_add]; exact s6_s80
theorem s6_c81 : Disp.arun 117649 (7^25) 28126 0 0 1 0 1 0 = (3,1021001427147166857697,3,714855164387871685125,1188357529274506738463) := by
  rw [show (28126:ℕ) = 27783 + 343 from rfl, Disp.arun_add, s6_c80, Nat.zero_add]; exact s6_s81
theorem s6_c82 : Disp.arun 117649 (7^25) 28469 0 0 1 0 1 0 = (3,648625448067642446302,3,415931142361062555681,599324162394966561274) := by
  rw [show (28469:ℕ) = 28126 + 343 from rfl, Disp.arun_add, s6_c81, Nat.zero_add]; exact s6_s82
theorem s6_c83 : Disp.arun 117649 (7^25) 28812 0 0 1 0 1 0 = (2,839487347159287581381,2,711936197930143615838,192493436316737872877) := by
  rw [show (28812:ℕ) = 28469 + 343 from rfl, Disp.arun_add, s6_c82, Nat.zero_add]; exact s6_s83
theorem s6_c84 : Disp.arun 117649 (7^25) 29155 0 0 1 0 1 0 = (3,859804890804137210059,3,62957690645469284274,289162663561808006601) := by
  rw [show (29155:ℕ) = 28812 + 343 from rfl, Disp.arun_add, s6_c83, Nat.zero_add]; exact s6_s84
theorem s6_c85 : Disp.arun 117649 (7^25) 29498 0 0 1 0 1 0 = (3,626201552150371863403,3,1163310901924274980041,397064332173382117700) := by
  rw [show (29498:ℕ) = 29155 + 343 from rfl, Disp.arun_add, s6_c84, Nat.zero_add]; exact s6_s85
theorem s6_c86 : Disp.arun 117649 (7^25) 29841 0 0 1 0 1 0 = (3,1283448156589248951908,3,896130526714842890693,1153119397220785157570) := by
  rw [show (29841:ℕ) = 29498 + 343 from rfl, Disp.arun_add, s6_c85, Nat.zero_add]; exact s6_s86
theorem s6_c87 : Disp.arun 117649 (7^25) 30184 0 0 1 0 1 0 = (3,650920936721968061644,3,1190823295286166231958,734085090067566043136) := by
  rw [show (30184:ℕ) = 29841 + 343 from rfl, Disp.arun_add, s6_c86, Nat.zero_add]; exact s6_s87
theorem s6_c88 : Disp.arun 117649 (7^25) 30527 0 0 1 0 1 0 = (3,482543509336840688124,3,1007093567632715214116,1107880383885864190715) := by
  rw [show (30527:ℕ) = 30184 + 343 from rfl, Disp.arun_add, s6_c87, Nat.zero_add]; exact s6_s88
theorem s6_c89 : Disp.arun 117649 (7^25) 30870 0 0 1 0 1 0 = (3,186292149194001486483,3,863171737571840548032,292132712837444354380) := by
  rw [show (30870:ℕ) = 30527 + 343 from rfl, Disp.arun_add, s6_c88, Nat.zero_add]; exact s6_s89
theorem s6_c90 : Disp.arun 117649 (7^25) 31213 0 0 1 0 1 0 = (2,1076333504034051436655,2,1248523579403242147613,162427272926837670389) := by
  rw [show (31213:ℕ) = 30870 + 343 from rfl, Disp.arun_add, s6_c89, Nat.zero_add]; exact s6_s90
theorem s6_c91 : Disp.arun 117649 (7^25) 31556 0 0 1 0 1 0 = (3,247715934816110733636,3,1335999597829216541285,227691448257350392344) := by
  rw [show (31556:ℕ) = 31213 + 343 from rfl, Disp.arun_add, s6_c90, Nat.zero_add]; exact s6_s91
theorem s6_c92 : Disp.arun 117649 (7^25) 31899 0 0 1 0 1 0 = (3,959775503805076451231,3,174074000450436491941,340963333569578870396) := by
  rw [show (31899:ℕ) = 31556 + 343 from rfl, Disp.arun_add, s6_c91, Nat.zero_add]; exact s6_s92
theorem s6_c93 : Disp.arun 117649 (7^25) 32242 0 0 1 0 1 0 = (3,765279858810005124238,3,1167331248046752177800,248774559581420751271) := by
  rw [show (32242:ℕ) = 31899 + 343 from rfl, Disp.arun_add, s6_c92, Nat.zero_add]; exact s6_s93
theorem s6_c94 : Disp.arun 117649 (7^25) 32585 0 0 1 0 1 0 = (3,239795594347708824763,3,1016513565324503745074,998136246520979018531) := by
  rw [show (32585:ℕ) = 32242 + 343 from rfl, Disp.arun_add, s6_c93, Nat.zero_add]; exact s6_s94
theorem s6_c95 : Disp.arun 117649 (7^25) 32928 0 0 1 0 1 0 = (3,198271568428530013274,3,1164902220263228939551,235211520122922633207) := by
  rw [show (32928:ℕ) = 32585 + 343 from rfl, Disp.arun_add, s6_c94, Nat.zero_add]; exact s6_s95
theorem s6_c96 : Disp.arun 117649 (7^25) 33271 0 0 1 0 1 0 = (3,1334346679077728906043,3,953212997387624044847,1331269588659569543447) := by
  rw [show (33271:ℕ) = 32928 + 343 from rfl, Disp.arun_add, s6_c95, Nat.zero_add]; exact s6_s96
theorem s6_c97 : Disp.arun 117649 (7^25) 33614 0 0 1 0 1 0 = (1,709633021594898681717,1,642850582735398853414,1300949595003434934594) := by
  rw [show (33614:ℕ) = 33271 + 343 from rfl, Disp.arun_add, s6_c96, Nat.zero_add]; exact s6_s97
theorem s6_c98 : Disp.arun 117649 (7^25) 33957 0 0 1 0 1 0 = (3,1222378749202164814023,3,304177555253421881403,824286970356133505285) := by
  rw [show (33957:ℕ) = 33614 + 343 from rfl, Disp.arun_add, s6_c97, Nat.zero_add]; exact s6_s98
theorem s6_c99 : Disp.arun 117649 (7^25) 34300 0 0 1 0 1 0 = (3,523186537209546047176,3,662121407460399191666,611638695904919362450) := by
  rw [show (34300:ℕ) = 33957 + 343 from rfl, Disp.arun_add, s6_c98, Nat.zero_add]; exact s6_s99
theorem s6_c100 : Disp.arun 117649 (7^25) 34643 0 0 1 0 1 0 = (3,560677798383114115359,3,1096443276797644327263,84797872940990505080) := by
  rw [show (34643:ℕ) = 34300 + 343 from rfl, Disp.arun_add, s6_c99, Nat.zero_add]; exact s6_s100
theorem s6_c101 : Disp.arun 117649 (7^25) 34986 0 0 1 0 1 0 = (3,1059976910877101531109,3,506316293756346605373,1133120983051923371983) := by
  rw [show (34986:ℕ) = 34643 + 343 from rfl, Disp.arun_add, s6_c100, Nat.zero_add]; exact s6_s101
theorem s6_c102 : Disp.arun 117649 (7^25) 35329 0 0 1 0 1 0 = (3,426996658482702599756,3,907967891960095188050,159132747868867714565) := by
  rw [show (35329:ℕ) = 34986 + 343 from rfl, Disp.arun_add, s6_c101, Nat.zero_add]; exact s6_s102
theorem s6_c103 : Disp.arun 117649 (7^25) 35672 0 0 1 0 1 0 = (3,1194865341204752958693,3,1262523163118085826796,858451049452183337746) := by
  rw [show (35672:ℕ) = 35329 + 343 from rfl, Disp.arun_add, s6_c102, Nat.zero_add]; exact s6_s103
theorem s6_c104 : Disp.arun 117649 (7^25) 36015 0 0 1 0 1 0 = (2,99218854847007164914,2,748634788215217853055,1100203902226905286574) := by
  rw [show (36015:ℕ) = 35672 + 343 from rfl, Disp.arun_add, s6_c103, Nat.zero_add]; exact s6_s104
theorem s6_c105 : Disp.arun 117649 (7^25) 36358 0 0 1 0 1 0 = (3,633670419586457260398,3,152739839165607110649,442674676565814433077) := by
  rw [show (36358:ℕ) = 36015 + 343 from rfl, Disp.arun_add, s6_c104, Nat.zero_add]; exact s6_s105
theorem s6_c106 : Disp.arun 117649 (7^25) 36701 0 0 1 0 1 0 = (3,130138327259196534163,3,744438468309020553009,1263483189344521615961) := by
  rw [show (36701:ℕ) = 36358 + 343 from rfl, Disp.arun_add, s6_c105, Nat.zero_add]; exact s6_s106
theorem s6_c107 : Disp.arun 117649 (7^25) 37044 0 0 1 0 1 0 = (3,250738224251293672224,3,1336831227696818841300,172230137805497375143) := by
  rw [show (37044:ℕ) = 36701 + 343 from rfl, Disp.arun_add, s6_c106, Nat.zero_add]; exact s6_s107
theorem s6_c108 : Disp.arun 117649 (7^25) 37387 0 0 1 0 1 0 = (3,611783502939398394635,3,1215984824189144690249,224557834528308615272) := by
  rw [show (37387:ℕ) = 37044 + 343 from rfl, Disp.arun_add, s6_c107, Nat.zero_add]; exact s6_s108
theorem s6_c109 : Disp.arun 117649 (7^25) 37730 0 0 1 0 1 0 = (3,1032636902545584937024,3,738716701862623175863,571967069365234938599) := by
  rw [show (37730:ℕ) = 37387 + 343 from rfl, Disp.arun_add, s6_c108, Nat.zero_add]; exact s6_s109
theorem s6_c110 : Disp.arun 117649 (7^25) 38073 0 0 1 0 1 0 = (3,781368433062052196353,3,1075356163910825754488,134436466935883418930) := by
  rw [show (38073:ℕ) = 37730 + 343 from rfl, Disp.arun_add, s6_c109, Nat.zero_add]; exact s6_s110
theorem s6_c111 : Disp.arun 117649 (7^25) 38416 0 0 1 0 1 0 = (2,526912302991069203715,2,919499886179791209535,768603262378936109126) := by
  rw [show (38416:ℕ) = 38073 + 343 from rfl, Disp.arun_add, s6_c110, Nat.zero_add]; exact s6_s111
theorem s6_c112 : Disp.arun 117649 (7^25) 38759 0 0 1 0 1 0 = (3,691346053645641580915,3,114627580878388742088,789656712918180887564) := by
  rw [show (38759:ℕ) = 38416 + 343 from rfl, Disp.arun_add, s6_c111, Nat.zero_add]; exact s6_s112
theorem s6_c113 : Disp.arun 117649 (7^25) 39102 0 0 1 0 1 0 = (3,404332313967770139052,3,1056006310714565598259,1138811402973080997469) := by
  rw [show (39102:ℕ) = 38759 + 343 from rfl, Disp.arun_add, s6_c112, Nat.zero_add]; exact s6_s113
theorem s6_c114 : Disp.arun 117649 (7^25) 39445 0 0 1 0 1 0 = (3,402418951863216300661,3,1147648609003186038180,752729549784483024069) := by
  rw [show (39445:ℕ) = 39102 + 343 from rfl, Disp.arun_add, s6_c113, Nat.zero_add]; exact s6_s114
theorem s6_c115 : Disp.arun 117649 (7^25) 39788 0 0 1 0 1 0 = (3,835503480024385799492,3,345797009471927355225,985363562073982353613) := by
  rw [show (39788:ℕ) = 39445 + 343 from rfl, Disp.arun_add, s6_c114, Nat.zero_add]; exact s6_s115
theorem s6_c116 : Disp.arun 117649 (7^25) 40131 0 0 1 0 1 0 = (3,830690236935415719187,3,1031615918423687829333,578816746098119178644) := by
  rw [show (40131:ℕ) = 39788 + 343 from rfl, Disp.arun_add, s6_c115, Nat.zero_add]; exact s6_s116
theorem s6_c117 : Disp.arun 117649 (7^25) 40474 0 0 1 0 1 0 = (3,456525782103256478691,3,712488741834277055570,571509389196603698730) := by
  rw [show (40474:ℕ) = 40131 + 343 from rfl, Disp.arun_add, s6_c116, Nat.zero_add]; exact s6_s117
theorem s6_c118 : Disp.arun 117649 (7^25) 40817 0 0 1 0 1 0 = (2,61010106840325759401,2,1063377944192012211621,31512933436256909456) := by
  rw [show (40817:ℕ) = 40474 + 343 from rfl, Disp.arun_add, s6_c117, Nat.zero_add]; exact s6_s118
theorem s6_c119 : Disp.arun 117649 (7^25) 41160 0 0 1 0 1 0 = (3,639133074333616322732,3,808529355213205228590,434706823955251806169) := by
  rw [show (41160:ℕ) = 40817 + 343 from rfl, Disp.arun_add, s6_c118, Nat.zero_add]; exact s6_s119
theorem s6_c120 : Disp.arun 117649 (7^25) 41503 0 0 1 0 1 0 = (3,722470125228953285510,3,669968972174562536655,469128176537656357226) := by
  rw [show (41503:ℕ) = 41160 + 343 from rfl, Disp.arun_add, s6_c119, Nat.zero_add]; exact s6_s120
theorem s6_c121 : Disp.arun 117649 (7^25) 41846 0 0 1 0 1 0 = (3,1008281684792812334991,3,1119602878024698170339,122047727567696151894) := by
  rw [show (41846:ℕ) = 41503 + 343 from rfl, Disp.arun_add, s6_c120, Nat.zero_add]; exact s6_s121
theorem s6_c122 : Disp.arun 117649 (7^25) 42189 0 0 1 0 1 0 = (3,478975740640423321010,3,375262669015116890737,165671921594137567904) := by
  rw [show (42189:ℕ) = 41846 + 343 from rfl, Disp.arun_add, s6_c121, Nat.zero_add]; exact s6_s122
theorem s6_c123 : Disp.arun 117649 (7^25) 42532 0 0 1 0 1 0 = (3,795957517274428331183,3,83649365803057091124,322644101907745300880) := by
  rw [show (42532:ℕ) = 42189 + 343 from rfl, Disp.arun_add, s6_c122, Nat.zero_add]; exact s6_s123
theorem s6_c124 : Disp.arun 117649 (7^25) 42875 0 0 1 0 1 0 = (3,1316836500818879373248,3,241825794366707671196,585675079043884692262) := by
  rw [show (42875:ℕ) = 42532 + 343 from rfl, Disp.arun_add, s6_c123, Nat.zero_add]; exact s6_s124
theorem s6_c125 : Disp.arun 117649 (7^25) 43218 0 0 1 0 1 0 = (2,768107112475173600365,2,204118777161730641324,236718704252949506162) := by
  rw [show (43218:ℕ) = 42875 + 343 from rfl, Disp.arun_add, s6_c124, Nat.zero_add]; exact s6_s125
theorem s6_c126 : Disp.arun 117649 (7^25) 43561 0 0 1 0 1 0 = (3,984677135260595478906,3,333134879098066765105,154604776081354411163) := by
  rw [show (43561:ℕ) = 43218 + 343 from rfl, Disp.arun_add, s6_c125, Nat.zero_add]; exact s6_s126
theorem s6_c127 : Disp.arun 117649 (7^25) 43904 0 0 1 0 1 0 = (3,926073856623157794625,3,236703537357723242846,482834507975746069130) := by
  rw [show (43904:ℕ) = 43561 + 343 from rfl, Disp.arun_add, s6_c126, Nat.zero_add]; exact s6_s127
theorem s6_c128 : Disp.arun 117649 (7^25) 44247 0 0 1 0 1 0 = (3,607130960361601556424,3,1278704842490774147727,132997421229302092891) := by
  rw [show (44247:ℕ) = 43904 + 343 from rfl, Disp.arun_add, s6_c127, Nat.zero_add]; exact s6_s128
theorem s6_c129 : Disp.arun 117649 (7^25) 44590 0 0 1 0 1 0 = (3,1247939011374395378085,3,400404741603102635989,522371028925463275706) := by
  rw [show (44590:ℕ) = 44247 + 343 from rfl, Disp.arun_add, s6_c128, Nat.zero_add]; exact s6_s129
theorem s6_c130 : Disp.arun 117649 (7^25) 44933 0 0 1 0 1 0 = (3,1121656430874392897179,3,9708767576113654366,1214712721019927801085) := by
  rw [show (44933:ℕ) = 44590 + 343 from rfl, Disp.arun_add, s6_c129, Nat.zero_add]; exact s6_s130
theorem s6_c131 : Disp.arun 117649 (7^25) 45276 0 0 1 0 1 0 = (3,936072142495107277766,3,1041185577773157861232,385043586712998843421) := by
  rw [show (45276:ℕ) = 44933 + 343 from rfl, Disp.arun_add, s6_c130, Nat.zero_add]; exact s6_s131
theorem s6_c132 : Disp.arun 117649 (7^25) 45619 0 0 1 0 1 0 = (2,898436631060887402291,2,624803482673763808677,991115676853030338142) := by
  rw [show (45619:ℕ) = 45276 + 343 from rfl, Disp.arun_add, s6_c131, Nat.zero_add]; exact s6_s132
theorem s6_c133 : Disp.arun 117649 (7^25) 45962 0 0 1 0 1 0 = (3,683590921929283580792,3,698247364249650764634,110721972276560410627) := by
  rw [show (45962:ℕ) = 45619 + 343 from rfl, Disp.arun_add, s6_c132, Nat.zero_add]; exact s6_s133
theorem s6_c134 : Disp.arun 117649 (7^25) 46305 0 0 1 0 1 0 = (3,251637051084367900214,3,1317921750025860984666,477672211839956299356) := by
  rw [show (46305:ℕ) = 45962 + 343 from rfl, Disp.arun_add, s6_c133, Nat.zero_add]; exact s6_s134
theorem s6_c135 : Disp.arun 117649 (7^25) 46648 0 0 1 0 1 0 = (3,648474993470234099514,3,377978524965801231484,1100792623328834485848) := by
  rw [show (46648:ℕ) = 46305 + 343 from rfl, Disp.arun_add, s6_c134, Nat.zero_add]; exact s6_s135
theorem s6_c136 : Disp.arun 117649 (7^25) 46991 0 0 1 0 1 0 = (3,979065741551623088407,3,292105284920154119080,849967953336882331855) := by
  rw [show (46991:ℕ) = 46648 + 343 from rfl, Disp.arun_add, s6_c135, Nat.zero_add]; exact s6_s136
theorem s6_c137 : Disp.arun 117649 (7^25) 47334 0 0 1 0 1 0 = (3,1166654970950917467954,3,751274157530719132159,417736110094436244504) := by
  rw [show (47334:ℕ) = 46991 + 343 from rfl, Disp.arun_add, s6_c136, Nat.zero_add]; exact s6_s137
theorem s6_c138 : Disp.arun 117649 (7^25) 47677 0 0 1 0 1 0 = (3,1324094019028561926445,3,286988647373495800375,48284301669892364189) := by
  rw [show (47677:ℕ) = 47334 + 343 from rfl, Disp.arun_add, s6_c137, Nat.zero_add]; exact s6_s138
theorem s6_c139 : Disp.arun 117649 (7^25) 48020 0 0 1 0 1 0 = (2,729602723427281199392,2,432920833090033206092,380004477216662028788) := by
  rw [show (48020:ℕ) = 47677 + 343 from rfl, Disp.arun_add, s6_c138, Nat.zero_add]; exact s6_s139
theorem s6_c140 : Disp.arun 117649 (7^25) 48363 0 0 1 0 1 0 = (3,389438847863976305004,3,315467072646540308782,826719675106332061209) := by
  rw [show (48363:ℕ) = 48020 + 343 from rfl, Disp.arun_add, s6_c139, Nat.zero_add]; exact s6_s140
theorem s6_c141 : Disp.arun 117649 (7^25) 48706 0 0 1 0 1 0 = (3,639507622222514358526,3,1276981741455175622080,998337761380314152372) := by
  rw [show (48706:ℕ) = 48363 + 343 from rfl, Disp.arun_add, s6_c140, Nat.zero_add]; exact s6_s141
theorem s6_c142 : Disp.arun 117649 (7^25) 49049 0 0 1 0 1 0 = (3,333588378337370501693,3,1169927726533721076591,30854918406220408431) := by
  rw [show (49049:ℕ) = 48706 + 343 from rfl, Disp.arun_add, s6_c141, Nat.zero_add]; exact s6_s142
theorem s6_c143 : Disp.arun 117649 (7^25) 49392 0 0 1 0 1 0 = (3,887209012730216222884,3,1264131355177578720751,230147418065490769180) := by
  rw [show (49392:ℕ) = 49049 + 343 from rfl, Disp.arun_add, s6_c142, Nat.zero_add]; exact s6_s143
theorem s6_c144 : Disp.arun 117649 (7^25) 49735 0 0 1 0 1 0 = (3,491743403887554199566,3,161560969357995170960,1311022542449353352704) := by
  rw [show (49735:ℕ) = 49392 + 343 from rfl, Disp.arun_add, s6_c143, Nat.zero_add]; exact s6_s144
theorem s6_c145 : Disp.arun 117649 (7^25) 50078 0 0 1 0 1 0 = (3,824338857707459511075,3,1010232076454538270178,409148875251118695288) := by
  rw [show (50078:ℕ) = 49735 + 343 from rfl, Disp.arun_add, s6_c144, Nat.zero_add]; exact s6_s145
theorem s6_c146 : Disp.arun 117649 (7^25) 50421 0 0 1 0 1 0 = (1,345914931324913199737,1,410489464889564925821,1158312404966529299761) := by
  rw [show (50421:ℕ) = 50078 + 343 from rfl, Disp.arun_add, s6_c145, Nat.zero_add]; exact s6_s146
theorem s6_c147 : Disp.arun 117649 (7^25) 50764 0 0 1 0 1 0 = (3,1339637301740512115305,3,988941188291249840704,120086424151649680747) := by
  rw [show (50764:ℕ) = 50421 + 343 from rfl, Disp.arun_add, s6_c146, Nat.zero_add]; exact s6_s147
theorem s6_c148 : Disp.arun 117649 (7^25) 51107 0 0 1 0 1 0 = (3,800700500507328377044,3,403251556675724213790,1743684405020375952) := by
  rw [show (51107:ℕ) = 50764 + 343 from rfl, Disp.arun_add, s6_c147, Nat.zero_add]; exact s6_s148
theorem s6_c149 : Disp.arun 117649 (7^25) 51450 0 0 1 0 1 0 = (3,1114094416565411013546,3,806623128755462847540,394363950241708754077) := by
  rw [show (51450:ℕ) = 51107 + 343 from rfl, Disp.arun_add, s6_c148, Nat.zero_add]; exact s6_s149
theorem s6_c150 : Disp.arun 117649 (7^25) 51793 0 0 1 0 1 0 = (3,116090331746338854823,3,788394921451545080066,507876351684544731246) := by
  rw [show (51793:ℕ) = 51450 + 343 from rfl, Disp.arun_add, s6_c149, Nat.zero_add]; exact s6_s150
theorem s6_c151 : Disp.arun 117649 (7^25) 52136 0 0 1 0 1 0 = (3,1282565615589254047888,3,896947633567891984046,807141876448116929504) := by
  rw [show (52136:ℕ) = 51793 + 343 from rfl, Disp.arun_add, s6_c150, Nat.zero_add]; exact s6_s151
theorem s6_c152 : Disp.arun 117649 (7^25) 52479 0 0 1 0 1 0 = (3,1115589721290841680442,3,589465955003197073192,552111770476059897188) := by
  rw [show (52479:ℕ) = 52136 + 343 from rfl, Disp.arun_add, s6_c151, Nat.zero_add]; exact s6_s152
theorem s6_c153 : Disp.arun 117649 (7^25) 52822 0 0 1 0 1 0 = (2,79212833160926550455,2,75377369344497154488,1037318767682309904310) := by
  rw [show (52822:ℕ) = 52479 + 343 from rfl, Disp.arun_add, s6_c152, Nat.zero_add]; exact s6_s153
theorem s6_c154 : Disp.arun 117649 (7^25) 53165 0 0 1 0 1 0 = (3,715147471935083603613,3,543410238378495683126,17154187176524665618) := by
  rw [show (53165:ℕ) = 52822 + 343 from rfl, Disp.arun_add, s6_c153, Nat.zero_add]; exact s6_s154
theorem s6_c155 : Disp.arun 117649 (7^25) 53508 0 0 1 0 1 0 = (3,1081575642119154054806,3,1154695730379441489495,565083348335968308344) := by
  rw [show (53508:ℕ) = 53165 + 343 from rfl, Disp.arun_add, s6_c154, Nat.zero_add]; exact s6_s155
theorem s6_c156 : Disp.arun 117649 (7^25) 53851 0 0 1 0 1 0 = (3,41664000991564487023,3,931377932312015147370,980627668557763187543) := by
  rw [show (53851:ℕ) = 53508 + 343 from rfl, Disp.arun_add, s6_c155, Nat.zero_add]; exact s6_s156
theorem s6_c157 : Disp.arun 117649 (7^25) 54194 0 0 1 0 1 0 = (3,293475387745617606037,3,664896907588720541695,798321347103240912071) := by
  rw [show (54194:ℕ) = 53851 + 343 from rfl, Disp.arun_add, s6_c156, Nat.zero_add]; exact s6_s157
theorem s6_c158 : Disp.arun 117649 (7^25) 54537 0 0 1 0 1 0 = (3,422510616900959501064,3,384151139815860407490,1124276994432207879250) := by
  rw [show (54537:ℕ) = 54194 + 343 from rfl, Disp.arun_add, s6_c157, Nat.zero_add]; exact s6_s158
theorem s6_c159 : Disp.arun 117649 (7^25) 54880 0 0 1 0 1 0 = (3,662149268588163069617,3,217924837563915699216,1159804618316509616571) := by
  rw [show (54880:ℕ) = 54537 + 343 from rfl, Disp.arun_add, s6_c158, Nat.zero_add]; exact s6_s159
theorem s6_c160 : Disp.arun 117649 (7^25) 55223 0 0 1 0 1 0 = (2,1160425210072364664698,2,114020494092556142900,348855812533298539610) := by
  rw [show (55223:ℕ) = 54880 + 343 from rfl, Disp.arun_add, s6_c159, Nat.zero_add]; exact s6_s160
theorem s6_c161 : Disp.arun 117649 (7^25) 55566 0 0 1 0 1 0 = (3,46427847536038536651,3,497565197483740568575,477384493904048389072) := by
  rw [show (55566:ℕ) = 55223 + 343 from rfl, Disp.arun_add, s6_c160, Nat.zero_add]; exact s6_s161
theorem s6_c162 : Disp.arun 117649 (7^25) 55909 0 0 1 0 1 0 = (3,372125877597873450629,3,533041405276111030429,254796201668739404451) := by
  rw [show (55909:ℕ) = 55566 + 343 from rfl, Disp.arun_add, s6_c161, Nat.zero_add]; exact s6_s162
theorem s6_c163 : Disp.arun 117649 (7^25) 56252 0 0 1 0 1 0 = (3,693397722790282630836,3,1014609550254871723234,62299175610949195668) := by
  rw [show (56252:ℕ) = 55909 + 343 from rfl, Disp.arun_add, s6_c162, Nat.zero_add]; exact s6_s163
theorem s6_c164 : Disp.arun 117649 (7^25) 56595 0 0 1 0 1 0 = (3,502187668016387113854,3,786466863680358522069,1077450388834162785709) := by
  rw [show (56595:ℕ) = 56252 + 343 from rfl, Disp.arun_add, s6_c163, Nat.zero_add]; exact s6_s164
theorem s6_c165 : Disp.arun 117649 (7^25) 56938 0 0 1 0 1 0 = (3,2491428399987748162,3,1322378029730870632663,117267278108593117219) := by
  rw [show (56938:ℕ) = 56595 + 343 from rfl, Disp.arun_add, s6_c164, Nat.zero_add]; exact s6_s165
theorem s6_c166 : Disp.arun 117649 (7^25) 57281 0 0 1 0 1 0 = (3,41355164925711258348,3,590694428162132430597,143185885069274332377) := by
  rw [show (57281:ℕ) = 56938 + 343 from rfl, Disp.arun_add, s6_c165, Nat.zero_add]; exact s6_s166
theorem s6_c167 : Disp.arun 117649 (7^25) 57624 0 0 1 0 1 0 = (2,807538709769513812820,2,1239997587430630667238,755331015102551531351) := by
  rw [show (57624:ℕ) = 57281 + 343 from rfl, Disp.arun_add, s6_c166, Nat.zero_add]; exact s6_s167
theorem s6_c168 : Disp.arun 117649 (7^25) 57967 0 0 1 0 1 0 = (3,270974223040882111661,3,44812823276674380124,1061724833285165086164) := by
  rw [show (57967:ℕ) = 57624 + 343 from rfl, Disp.arun_add, s6_c167, Nat.zero_add]; exact s6_s168
theorem s6_c169 : Disp.arun 117649 (7^25) 58310 0 0 1 0 1 0 = (3,884075411407395278256,3,1302722808809355502762,763099605692399064650) := by
  rw [show (58310:ℕ) = 57967 + 343 from rfl, Disp.arun_add, s6_c168, Nat.zero_add]; exact s6_s169
theorem s6_c170 : Disp.arun 117649 (7^25) 58653 0 0 1 0 1 0 = (3,719734107958896622247,3,1002303269253429509581,1174389098020459231478) := by
  rw [show (58653:ℕ) = 58310 + 343 from rfl, Disp.arun_add, s6_c169, Nat.zero_add]; exact s6_s170
theorem s6_c171 : Disp.arun 117649 (7^25) 58996 0 0 1 0 1 0 = (3,719734107958896622247,3,193292911637315706687,334366764170207362231) := by
  rw [show (58996:ℕ) = 58653 + 343 from rfl, Disp.arun_add, s6_c170, Nat.zero_add]; exact s6_s171
theorem s6_c172 : Disp.arun 117649 (7^25) 59339 0 0 1 0 1 0 = (3,884075411407395278256,3,500273883816332087304,1236292045002445635009) := by
  rw [show (59339:ℕ) = 58996 + 343 from rfl, Disp.arun_add, s6_c171, Nat.zero_add]; exact s6_s172
theorem s6_c173 : Disp.arun 117649 (7^25) 59682 0 0 1 0 1 0 = (3,270974223040882111661,3,1185239789042623628978,388340772174963612425) := by
  rw [show (59682:ℕ) = 59339 + 343 from rfl, Disp.arun_add, s6_c172, Nat.zero_add]; exact s6_s173
theorem s6_c174 : Disp.arun 117649 (7^25) 60025 0 0 1 0 1 0 = (2,807538709769513812820,2,911638371242174621103,909620746666576474951) := by
  rw [show (60025:ℕ) = 59682 + 343 from rfl, Disp.arun_add, s6_c173, Nat.zero_add]; exact s6_s174
theorem s6_c175 : Disp.arun 117649 (7^25) 60368 0 0 1 0 1 0 = (3,41355164925711258348,3,835000084988093742985,757848478176961361688) := by
  rw [show (60368:ℕ) = 60025 + 343 from rfl, Disp.arun_add, s6_c174, Nat.zero_add]; exact s6_s175
theorem s6_c176 : Disp.arun 117649 (7^25) 60711 0 0 1 0 1 0 = (3,2491428399987748162,3,1240773247773438245759,1101965351565880711750) := by
  rw [show (60711:ℕ) = 60368 + 343 from rfl, Disp.arun_add, s6_c175, Nat.zero_add]; exact s6_s176
theorem s6_c177 : Disp.arun 117649 (7^25) 61054 0 0 1 0 1 0 = (3,502187668016387113854,3,95338653229246561475,356264690087691624051) := by
  rw [show (61054:ℕ) = 60711 + 343 from rfl, Disp.arun_add, s6_c176, Nat.zero_add]; exact s6_s177
theorem s6_c178 : Disp.arun 117649 (7^25) 61397 0 0 1 0 1 0 = (3,693397722790282630836,3,1261263298077695548939,525972382039944561779) := by
  rw [show (61397:ℕ) = 61054 + 343 from rfl, Disp.arun_add, s6_c177, Nat.zero_add]; exact s6_s178
theorem s6_c179 : Disp.arun 117649 (7^25) 61740 0 0 1 0 1 0 = (3,372125877597873450629,3,708925773713626154899,316830067157965300164) := by
  rw [show (61740:ℕ) = 61397 + 343 from rfl, Disp.arun_add, s6_c178, Nat.zero_add]; exact s6_s179
theorem s6_c180 : Disp.arun 117649 (7^25) 62083 0 0 1 0 1 0 = (3,46427847536038536651,3,745631478616908623382,1138025163157270847964) := by
  rw [show (62083:ℕ) = 61740 + 343 from rfl, Disp.arun_add, s6_c179, Nat.zero_add]; exact s6_s180
theorem s6_c181 : Disp.arun 117649 (7^25) 62426 0 0 1 0 1 0 = (2,1160425210072364664698,2,178131950585483473477,368535578837067529707) := by
  rw [show (62426:ℕ) = 62083 + 343 from rfl, Disp.arun_add, s6_c180, Nat.zero_add]; exact s6_s181
theorem s6_c182 : Disp.arun 117649 (7^25) 62769 0 0 1 0 1 0 = (3,662149268588163069617,3,1297765146325720190133,995106516237798577474) := by
  rw [show (62769:ℕ) = 62426 + 343 from rfl, Disp.arun_add, s6_c181, Nat.zero_add]; exact s6_s182
theorem s6_c183 : Disp.arun 117649 (7^25) 63112 0 0 1 0 1 0 = (3,422510616900959501064,3,1278245472043049721334,1103493210654136068131) := by
  rw [show (63112:ℕ) = 62769 + 343 from rfl, Disp.arun_add, s6_c182, Nat.zero_add]; exact s6_s183
theorem s6_c184 : Disp.arun 117649 (7^25) 63455 0 0 1 0 1 0 = (3,293475387745617606037,3,879231182140182682592,733398754960473440483) := by
  rw [show (63455:ℕ) = 63112 + 343 from rfl, Disp.arun_add, s6_c183, Nat.zero_add]; exact s6_s184
theorem s6_c185 : Disp.arun 117649 (7^25) 63798 0 0 1 0 1 0 = (3,41664000991564487023,3,65271284756599147249,768152984575991119512) := by
  rw [show (63798:ℕ) = 63455 + 343 from rfl, Disp.arun_add, s6_c184, Nat.zero_add]; exact s6_s185
theorem s6_c186 : Disp.arun 117649 (7^25) 64141 0 0 1 0 1 0 = (3,1081575642119154054806,3,287049855092484965841,789081344440448525215) := by
  rw [show (64141:ℕ) = 63798 + 343 from rfl, Disp.arun_add, s6_c185, Nat.zero_add]; exact s6_s186
theorem s6_c187 : Disp.arun 117649 (7^25) 64484 0 0 1 0 1 0 = (3,715147471935083603613,3,1186623605964740867601,1296854662081548127986) := by
  rw [show (64484:ℕ) = 64141 + 343 from rfl, Disp.arun_add, s6_c186, Nat.zero_add]; exact s6_s187
theorem s6_c188 : Disp.arun 117649 (7^25) 64827 0 0 1 0 1 0 = (2,79212833160926550455,2,386027143532324518055,359874824062327951028) := by
  rw [show (64827:ℕ) = 64484 + 343 from rfl, Disp.arun_add, s6_c187, Nat.zero_add]; exact s6_s188
theorem s6_c189 : Disp.arun 117649 (7^25) 65170 0 0 1 0 1 0 = (3,1115589721290841680442,3,867128368597170676928,1038349085410301916805) := by
  rw [show (65170:ℕ) = 64827 + 343 from rfl, Disp.arun_add, s6_c188, Nat.zero_add]; exact s6_s189
theorem s6_c190 : Disp.arun 117649 (7^25) 65513 0 0 1 0 1 0 = (3,1282565615589254047888,3,499413173126745910365,706452117482815277778) := by
  rw [show (65513:ℕ) = 65170 + 343 from rfl, Disp.arun_add, s6_c189, Nat.zero_add]; exact s6_s190
theorem s6_c191 : Disp.arun 117649 (7^25) 65856 0 0 1 0 1 0 = (3,116090331746338854823,3,110630045528806497762,84359735710465655182) := by
  rw [show (65856:ℕ) = 65513 + 343 from rfl, Disp.arun_add, s6_c190, Nat.zero_add]; exact s6_s191
theorem s6_c192 : Disp.arun 117649 (7^25) 66199 0 0 1 0 1 0 = (3,1114094416565411013546,3,1027247679959573308161,888088062241059630532) := by
  rw [show (66199:ℕ) = 65856 + 343 from rfl, Disp.arun_add, s6_c191, Nat.zero_add]; exact s6_s192
theorem s6_c193 : Disp.arun 117649 (7^25) 66542 0 0 1 0 1 0 = (3,800700500507328377044,3,21694348623371099469,1029328383042449751766) := by
  rw [show (66542:ℕ) = 66199 + 343 from rfl, Disp.arun_add, s6_c192, Nat.zero_add]; exact s6_s193
theorem s6_c194 : Disp.arun 117649 (7^25) 66885 0 0 1 0 1 0 = (3,1339637301740512115305,3,396766405766406654614,1284100617764481715899) := by
  rw [show (66885:ℕ) = 66542 + 343 from rfl, Disp.arun_add, s6_c193, Nat.zero_add]; exact s6_s194
theorem s6_c195 : Disp.arun 117649 (7^25) 67228 0 0 1 0 1 0 = (1,345914931324913199737,1,1326242041598476389193,1159973539277806548821) := by
  rw [show (67228:ℕ) = 66885 + 343 from rfl, Disp.arun_add, s6_c194, Nat.zero_add]; exact s6_s195
theorem s6_c196 : Disp.arun 117649 (7^25) 67571 0 0 1 0 1 0 = (3,824338857707459511075,3,853397808683171672950,846569266488618101318) := by
  rw [show (67571:ℕ) = 67228 + 343 from rfl, Disp.arun_add, s6_c195, Nat.zero_add]; exact s6_s196
theorem s6_c197 : Disp.arun 117649 (7^25) 67914 0 0 1 0 1 0 = (3,491743403887554199566,3,205891604232339921466,735706164082943330488) := by
  rw [show (67914:ℕ) = 67571 + 343 from rfl, Disp.arun_add, s6_c196, Nat.zero_add]; exact s6_s197
theorem s6_c198 : Disp.arun 117649 (7^25) 68257 0 0 1 0 1 0 = (3,887209012730216222884,3,815282538945560784390,1151457904007550484066) := by
  rw [show (68257:ℕ) = 67914 + 343 from rfl, Disp.arun_add, s6_c197, Nat.zero_add]; exact s6_s198
theorem s6_c199 : Disp.arun 117649 (7^25) 68600 0 0 1 0 1 0 = (3,333588378337370501693,3,1284874730577720004340,503692560044956306361) := by
  rw [show (68600:ℕ) = 68257 + 343 from rfl, Disp.arun_add, s6_c198, Nat.zero_add]; exact s6_s199
theorem s6_c200 : Disp.arun 117649 (7^25) 68943 0 0 1 0 1 0 = (3,639507622222514358526,3,545191098243988889325,1190281939189763909644) := by
  rw [show (68943:ℕ) = 68600 + 343 from rfl, Disp.arun_add, s6_c199, Nat.zero_add]; exact s6_s200
theorem s6_c201 : Disp.arun 117649 (7^25) 69286 0 0 1 0 1 0 = (3,389438847863976305004,3,23705349112079221432,231376177840593905001) := by
  rw [show (69286:ℕ) = 68943 + 343 from rfl, Disp.arun_add, s6_c200, Nat.zero_add]; exact s6_s201
theorem s6_c202 : Disp.arun 117649 (7^25) 69629 0 0 1 0 1 0 = (2,729602723427281199392,2,828567519999631286358,621386099157422242358) := by
  rw [show (69629:ℕ) = 69286 + 343 from rfl, Disp.arun_add, s6_c201, Nat.zero_add]; exact s6_s202
theorem s6_c203 : Disp.arun 117649 (7^25) 69972 0 0 1 0 1 0 = (3,1324094019028561926445,3,913728318599724856572,1080008988712186109732) := by
  rw [show (69972:ℕ) = 69629 + 343 from rfl, Disp.arun_add, s6_c202, Nat.zero_add]; exact s6_s203
theorem s6_c204 : Disp.arun 117649 (7^25) 70315 0 0 1 0 1 0 = (3,1166654970950917467954,3,699183104718286980775,1319641386447879669539) := by
  rw [show (70315:ℕ) = 69972 + 343 from rfl, Disp.arun_add, s6_c203, Nat.zero_add]; exact s6_s204
theorem s6_c205 : Disp.arun 117649 (7^25) 70658 0 0 1 0 1 0 = (3,979065741551623088407,3,461497316284980291587,999147903379713014705) := by
  rw [show (70658:ℕ) = 70315 + 343 from rfl, Disp.arun_add, s6_c204, Nat.zero_add]; exact s6_s205
theorem s6_c206 : Disp.arun 117649 (7^25) 71001 0 0 1 0 1 0 = (3,648474993470234099514,3,65633720138250958444,953258754971488452341) := by
  rw [show (71001:ℕ) = 70658 + 343 from rfl, Disp.arun_add, s6_c205, Nat.zero_add]; exact s6_s206
theorem s6_c207 : Disp.arun 117649 (7^25) 71344 0 0 1 0 1 0 = (3,251637051084367900214,3,483978262995665776096,442829010971526657899) := by
  rw [show (71344:ℕ) = 71001 + 343 from rfl, Disp.arun_add, s6_c206, Nat.zero_add]; exact s6_s207
theorem s6_c208 : Disp.arun 117649 (7^25) 71687 0 0 1 0 1 0 = (3,683590921929283580792,3,397721052541665001932,432745897863326866617) := by
  rw [show (71687:ℕ) = 71344 + 343 from rfl, Disp.arun_add, s6_c207, Nat.zero_add]; exact s6_s208
theorem s6_c209 : Disp.arun 117649 (7^25) 72030 0 0 1 0 1 0 = (2,898436631060887402291,2,1014518090106286090952,880022089999905833107) := by
  rw [show (72030:ℕ) = 71687 + 343 from rfl, Disp.arun_add, s6_c208, Nat.zero_add]; exact s6_s209
theorem s6_c210 : Disp.arun 117649 (7^25) 72373 0 0 1 0 1 0 = (3,936072142495107277766,3,278475646896534455397,485056298150492333350) := by
  rw [show (72373:ℕ) = 72030 + 343 from rfl, Disp.arun_add, s6_c209, Nat.zero_add]; exact s6_s210
theorem s6_c211 : Disp.arun 117649 (7^25) 72716 0 0 1 0 1 0 = (3,1121656430874392897179,3,1040072085813108793344,205731115042047246835) := by
  rw [show (72716:ℕ) = 72373 + 343 from rfl, Disp.arun_add, s6_c210, Nat.zero_add]; exact s6_s211
theorem s6_c212 : Disp.arun 117649 (7^25) 73059 0 0 1 0 1 0 = (3,1247939011374395378085,3,955637158558684944585,121798886703463597048) := by
  rw [show (73059:ℕ) = 72716 + 343 from rfl, Disp.arun_add, s6_c211, Nat.zero_add]; exact s6_s212
theorem s6_c213 : Disp.arun 117649 (7^25) 73402 0 0 1 0 1 0 = (3,607130960361601556424,3,124493735074632959576,527000801689695998127) := by
  rw [show (73402:ℕ) = 73059 + 343 from rfl, Disp.arun_add, s6_c212, Nat.zero_add]; exact s6_s213
theorem s6_c214 : Disp.arun 117649 (7^25) 73745 0 0 1 0 1 0 = (3,926073856623157794625,3,1057863277012999790637,1196636118097844231599) := by
  rw [show (73745:ℕ) = 73402 + 343 from rfl, Disp.arun_add, s6_c213, Nat.zero_add]; exact s6_s214
theorem s6_c215 : Disp.arun 117649 (7^25) 74088 0 0 1 0 1 0 = (3,984677135260595478906,3,784832403921413684815,306219895338859584027) := by
  rw [show (74088:ℕ) = 73745 + 343 from rfl, Disp.arun_add, s6_c214, Nat.zero_add]; exact s6_s215
theorem s6_c216 : Disp.arun 117649 (7^25) 74431 0 0 1 0 1 0 = (2,768107112475173600365,2,784023851859391127052,183727368853349201434) := by
  rw [show (74431:ℕ) = 74088 + 343 from rfl, Disp.arun_add, s6_c215, Nat.zero_add]; exact s6_s216
theorem s6_c217 : Disp.arun 117649 (7^25) 74774 0 0 1 0 1 0 = (3,1316836500818879373248,3,102062698436329931140,950716010084798661068) := by
  rw [show (74774:ℕ) = 74431 + 343 from rfl, Disp.arun_add, s6_c216, Nat.zero_add]; exact s6_s217
theorem s6_c218 : Disp.arun 117649 (7^25) 75117 0 0 1 0 1 0 = (3,795957517274428331183,3,370572314180206365385,1174796703152891322491) := by
  rw [show (75117:ℕ) = 74774 + 343 from rfl, Disp.arun_add, s6_c217, Nat.zero_add]; exact s6_s218
theorem s6_c219 : Disp.arun 117649 (7^25) 75460 0 0 1 0 1 0 = (3,478975740640423321010,3,562897892145884141488,1233418394603529942333) := by
  rw [show (75460:ℕ) = 75117 + 343 from rfl, Disp.arun_add, s6_c218, Nat.zero_add]; exact s6_s219
theorem s6_c220 : Disp.arun 117649 (7^25) 75803 0 0 1 0 1 0 = (3,1008281684792812334991,3,1294169886423849696718,1279329612445910159961) := by
  rw [show (75803:ℕ) = 75460 + 343 from rfl, Disp.arun_add, s6_c219, Nat.zero_add]; exact s6_s220
theorem s6_c221 : Disp.arun 117649 (7^25) 76146 0 0 1 0 1 0 = (3,722470125228953285510,3,597423538710255856861,223494390856658804114) := by
  rw [show (76146:ℕ) = 75803 + 343 from rfl, Disp.arun_add, s6_c220, Nat.zero_add]; exact s6_s221
theorem s6_c222 : Disp.arun 117649 (7^25) 76489 0 0 1 0 1 0 = (3,639133074333616322732,3,242045862518722258933,679546962738089289516) := by
  rw [show (76489:ℕ) = 76146 + 343 from rfl, Disp.arun_add, s6_c221, Nat.zero_add]; exact s6_s222
theorem s6_c223 : Disp.arun 117649 (7^25) 76832 0 0 1 0 1 0 = (2,61010106840325759401,2,968046136837546948631,108956256562016258592) := by
  rw [show (76832:ℕ) = 76489 + 343 from rfl, Disp.arun_add, s6_c222, Nat.zero_add]; exact s6_s223
theorem s6_c224 : Disp.arun 117649 (7^25) 77175 0 0 1 0 1 0 = (3,456525782103256478691,3,416028793542793168753,1195313877716358852271) := by
  rw [show (77175:ℕ) = 76832 + 343 from rfl, Disp.arun_add, s6_c223, Nat.zero_add]; exact s6_s224
theorem s6_c225 : Disp.arun 117649 (7^25) 77518 0 0 1 0 1 0 = (3,830690236935415719187,3,682902725254814601933,1336113800649338864609) := by
  rw [show (77518:ℕ) = 77175 + 343 from rfl, Disp.arun_add, s6_c224, Nat.zero_add]; exact s6_s225
theorem s6_c226 : Disp.arun 117649 (7^25) 77861 0 0 1 0 1 0 = (3,835503480024385799492,3,537347627185918203814,375828164810420384924) := by
  rw [show (77861:ℕ) = 77518 + 343 from rfl, Disp.arun_add, s6_c225, Nat.zero_add]; exact s6_s226
theorem s6_c227 : Disp.arun 117649 (7^25) 78204 0 0 1 0 1 0 = (3,402418951863216300661,3,1224955186033673175804,637697690429296882603) := by
  rw [show (78204:ℕ) = 77861 + 343 from rfl, Disp.arun_add, s6_c226, Nat.zero_add]; exact s6_s227
theorem s6_c228 : Disp.arun 117649 (7^25) 78547 0 0 1 0 1 0 = (3,404332313967770139052,3,631411974486790667649,191540656705000327040) := by
  rw [show (78547:ℕ) = 78204 + 343 from rfl, Disp.arun_add, s6_c227, Nat.zero_add]; exact s6_s228
theorem s6_c229 : Disp.arun 117649 (7^25) 78890 0 0 1 0 1 0 = (3,691346053645641580915,3,1109754917406792631491,111213818137182226068) := by
  rw [show (78890:ℕ) = 78547 + 343 from rfl, Disp.arun_add, s6_c228, Nat.zero_add]; exact s6_s229
theorem s6_c230 : Disp.arun 117649 (7^25) 79233 0 0 1 0 1 0 = (2,526912302991069203715,2,121592689491404982217,874787224446336191369) := by
  rw [show (79233:ℕ) = 78890 + 343 from rfl, Disp.arun_add, s6_c229, Nat.zero_add]; exact s6_s230
theorem s6_c231 : Disp.arun 117649 (7^25) 79576 0 0 1 0 1 0 = (3,781368433062052196353,3,580957014497193313834,124867860747189098239) := by
  rw [show (79576:ℕ) = 79233 + 343 from rfl, Disp.arun_add, s6_c230, Nat.zero_add]; exact s6_s231
theorem s6_c232 : Disp.arun 117649 (7^25) 79919 0 0 1 0 1 0 = (3,1032636902545584937024,3,1323379622461116813639,570860292583010364908) := by
  rw [show (79919:ℕ) = 79576 + 343 from rfl, Disp.arun_add, s6_c231, Nat.zero_add]; exact s6_s232
theorem s6_c233 : Disp.arun 117649 (7^25) 80262 0 0 1 0 1 0 = (3,611783502939398394635,3,800379703368885795636,1279922432535483892380) := by
  rw [show (80262:ℕ) = 79919 + 343 from rfl, Disp.arun_add, s6_c232, Nat.zero_add]; exact s6_s233
theorem s6_c234 : Disp.arun 117649 (7^25) 80605 0 0 1 0 1 0 = (3,250738224251293672224,3,657389560142555892437,680707223628870582180) := by
  rw [show (80605:ℕ) = 80262 + 343 from rfl, Disp.arun_add, s6_c233, Nat.zero_add]; exact s6_s234
theorem s6_c235 : Disp.arun 117649 (7^25) 80948 0 0 1 0 1 0 = (3,130138327259196534163,3,1005022069616116467975,16665391524319380613) := by
  rw [show (80948:ℕ) = 80605 + 343 from rfl, Disp.arun_add, s6_c234, Nat.zero_add]; exact s6_s235
theorem s6_c236 : Disp.arun 117649 (7^25) 81291 0 0 1 0 1 0 = (3,633670419586457260398,3,468940157111124086212,168893469584005249112) := by
  rw [show (81291:ℕ) = 80948 + 343 from rfl, Disp.arun_add, s6_c235, Nat.zero_add]; exact s6_s236
theorem s6_c237 : Disp.arun 117649 (7^25) 81634 0 0 1 0 1 0 = (2,99218854847007164914,2,243724285253623868560,1035328515848803686658) := by
  rw [show (81634:ℕ) = 81291 + 343 from rfl, Disp.arun_add, s6_c236, Nat.zero_add]; exact s6_s237
theorem s6_c238 : Disp.arun 117649 (7^25) 81977 0 0 1 0 1 0 = (3,1194865341204752958693,3,238928122956807253852,1004768780365383607995) := by
  rw [show (81977:ℕ) = 81634 + 343 from rfl, Disp.arun_add, s6_c237, Nat.zero_add]; exact s6_s238
theorem s6_c239 : Disp.arun 117649 (7^25) 82320 0 0 1 0 1 0 = (3,426996658482702599756,3,1019469410049412878420,1256515239266966406239) := by
  rw [show (82320:ℕ) = 81977 + 343 from rfl, Disp.arun_add, s6_c238, Nat.zero_add]; exact s6_s239
theorem s6_c240 : Disp.arun 117649 (7^25) 82663 0 0 1 0 1 0 = (3,1059976910877101531109,3,660205190596020634493,882083222056693518513) := by
  rw [show (82663:ℕ) = 82320 + 343 from rfl, Disp.arun_add, s6_c239, Nat.zero_add]; exact s6_s240
theorem s6_c241 : Disp.arun 117649 (7^25) 83006 0 0 1 0 1 0 = (3,560677798383114115359,3,1061376353247166066966,964406621056088009416) := by
  rw [show (83006:ℕ) = 82663 + 343 from rfl, Disp.arun_add, s6_c240, Nat.zero_add]; exact s6_s241
theorem s6_c242 : Disp.arun 117649 (7^25) 83349 0 0 1 0 1 0 = (3,523186537209546047176,3,1082969979745464028277,1150848937541781116668) := by
  rw [show (83349:ℕ) = 83006 + 343 from rfl, Disp.arun_add, s6_c241, Nat.zero_add]; exact s6_s242
theorem s6_c243 : Disp.arun 117649 (7^25) 83692 0 0 1 0 1 0 = (3,1222378749202164814023,3,316398315763545883951,559788537751049167184) := by
  rw [show (83692:ℕ) = 83349 + 343 from rfl, Disp.arun_add, s6_c242, Nat.zero_add]; exact s6_s243
theorem s6_c244 : Disp.arun 117649 (7^25) 84035 0 0 1 0 1 0 = (1,709633021594898681717,1,136731638610593564079,195872711746427951600) := by
  rw [show (84035:ℕ) = 83692 + 343 from rfl, Disp.arun_add, s6_c243, Nat.zero_add]; exact s6_s244
theorem s6_c245 : Disp.arun 117649 (7^25) 84378 0 0 1 0 1 0 = (3,1334346679077728906043,3,880359562171254234084,1146351405435603219014) := by
  rw [show (84378:ℕ) = 84035 + 343 from rfl, Disp.arun_add, s6_c244, Nat.zero_add]; exact s6_s245
theorem s6_c246 : Disp.arun 117649 (7^25) 84721 0 0 1 0 1 0 = (3,198271568428530013274,3,337991197885258429054,1284389820562880362997) := by
  rw [show (84721:ℕ) = 84378 + 343 from rfl, Disp.arun_add, s6_c245, Nat.zero_add]; exact s6_s246
theorem s6_c247 : Disp.arun 117649 (7^25) 85064 0 0 1 0 1 0 = (3,239795594347708824763,3,125233466590212580304,1118814966734854740170) := by
  rw [show (85064:ℕ) = 84721 + 343 from rfl, Disp.arun_add, s6_c246, Nat.zero_add]; exact s6_s247
theorem s6_c248 : Disp.arun 117649 (7^25) 85407 0 0 1 0 1 0 = (3,765279858810005124238,3,1266212778425363035892,777277491128315393448) := by
  rw [show (85407:ℕ) = 85064 + 343 from rfl, Disp.arun_add, s6_c247, Nat.zero_add]; exact s6_s248
theorem s6_c249 : Disp.arun 117649 (7^25) 85750 0 0 1 0 1 0 = (3,959775503805076451231,3,957775027632427223068,961949158235928284304) := by
  rw [show (85750:ℕ) = 85407 + 343 from rfl, Disp.arun_add, s6_c248, Nat.zero_add]; exact s6_s249
theorem s6_c250 : Disp.arun 117649 (7^25) 86093 0 0 1 0 1 0 = (3,247715934816110733636,3,1233163318113140503620,918114446757392574110) := by
  rw [show (86093:ℕ) = 85750 + 343 from rfl, Disp.arun_add, s6_c249, Nat.zero_add]; exact s6_s250
theorem s6_c251 : Disp.arun 117649 (7^25) 86436 0 0 1 0 1 0 = (2,1076333504034051436655,2,447368043181492696152,316413626720375602832) := by
  rw [show (86436:ℕ) = 86093 + 343 from rfl, Disp.arun_add, s6_c250, Nat.zero_add]; exact s6_s251
theorem s6_c252 : Disp.arun 117649 (7^25) 86779 0 0 1 0 1 0 = (3,186292149194001486483,3,255843314369789799115,1315372619236060954479) := by
  rw [show (86779:ℕ) = 86436 + 343 from rfl, Disp.arun_add, s6_c251, Nat.zero_add]; exact s6_s252
theorem s6_c253 : Disp.arun 117649 (7^25) 87122 0 0 1 0 1 0 = (3,482543509336840688124,3,1216222961015728217444,801220736519288138789) := by
  rw [show (87122:ℕ) = 86779 + 343 from rfl, Disp.arun_add, s6_c252, Nat.zero_add]; exact s6_s253
theorem s6_c254 : Disp.arun 117649 (7^25) 87465 0 0 1 0 1 0 = (3,650920936721968061644,3,1239722446946058228249,407162166901410589845) := by
  rw [show (87465:ℕ) = 87122 + 343 from rfl, Disp.arun_add, s6_c253, Nat.zero_add]; exact s6_s254
theorem s6_c255 : Disp.arun 117649 (7^25) 87808 0 0 1 0 1 0 = (3,1283448156589248951908,3,1103111903291125825386,648472532133228546003) := by
  rw [show (87808:ℕ) = 87465 + 343 from rfl, Disp.arun_add, s6_c254, Nat.zero_add]; exact s6_s255
theorem s6_c256 : Disp.arun 117649 (7^25) 88151 0 0 1 0 1 0 = (3,626201552150371863403,3,685305523973161424728,190844134991335921383) := by
  rw [show (88151:ℕ) = 87808 + 343 from rfl, Disp.arun_add, s6_c255, Nat.zero_add]; exact s6_s256
theorem s6_c257 : Disp.arun 117649 (7^25) 88494 0 0 1 0 1 0 = (3,859804890804137210059,3,559596324097609640197,998617152003792992777) := by
  rw [show (88494:ℕ) = 88151 + 343 from rfl, Disp.arun_add, s6_c256, Nat.zero_add]; exact s6_s257
theorem s6_c258 : Disp.arun 117649 (7^25) 88837 0 0 1 0 1 0 = (2,839487347159287581381,2,302003000365889461468,322979377450224208015) := by
  rw [show (88837:ℕ) = 88494 + 343 from rfl, Disp.arun_add, s6_c257, Nat.zero_add]; exact s6_s258
theorem s6_c259 : Disp.arun 117649 (7^25) 89180 0 0 1 0 1 0 = (3,648625448067642446302,3,6207350811490281188,344176942279356711603) := by
  rw [show (89180:ℕ) = 88837 + 343 from rfl, Disp.arun_add, s6_c258, Nat.zero_add]; exact s6_s259
theorem s6_c260 : Disp.arun 117649 (7^25) 89523 0 0 1 0 1 0 = (3,1021001427147166857697,3,175684430618991809323,432196946230920155832) := by
  rw [show (89523:ℕ) = 89180 + 343 from rfl, Disp.arun_add, s6_c259, Nat.zero_add]; exact s6_s260
theorem s6_c261 : Disp.arun 117649 (7^25) 89866 0 0 1 0 1 0 = (3,126303903384071558483,3,1189477763450587662098,714832191302270598432) := by
  rw [show (89866:ℕ) = 89523 + 343 from rfl, Disp.arun_add, s6_c260, Nat.zero_add]; exact s6_s261
theorem s6_c262 : Disp.arun 117649 (7^25) 90209 0 0 1 0 1 0 = (3,257632332866704955168,3,202780796861735710039,415500517559988377868) := by
  rw [show (90209:ℕ) = 89866 + 343 from rfl, Disp.arun_add, s6_c261, Nat.zero_add]; exact s6_s262
theorem s6_c263 : Disp.arun 117649 (7^25) 90552 0 0 1 0 1 0 = (3,611438204244777217354,3,885017765953196297313,175821142744677793679) := by
  rw [show (90552:ℕ) = 90209 + 343 from rfl, Disp.arun_add, s6_c262, Nat.zero_add]; exact s6_s263
theorem s6_c264 : Disp.arun 117649 (7^25) 90895 0 0 1 0 1 0 = (3,655126397143078579816,3,348223410331194877583,939159258202920658177) := by
  rw [show (90895:ℕ) = 90552 + 343 from rfl, Disp.arun_add, s6_c263, Nat.zero_add]; exact s6_s264
theorem s6_c265 : Disp.arun 117649 (7^25) 91238 0 0 1 0 1 0 = (2,1185229143978850067463,2,436180181355680203650,219296354069344602044) := by
  rw [show (91238:ℕ) = 90895 + 343 from rfl, Disp.arun_add, s6_c264, Nat.zero_add]; exact s6_s265
theorem s6_c266 : Disp.arun 117649 (7^25) 91581 0 0 1 0 1 0 = (3,789733115710830678570,3,1188012841965241095994,278537586416525935850) := by
  rw [show (91581:ℕ) = 91238 + 343 from rfl, Disp.arun_add, s6_c265, Nat.zero_add]; exact s6_s266
theorem s6_c267 : Disp.arun 117649 (7^25) 91924 0 0 1 0 1 0 = (3,995797094524875363234,3,235481205614382364452,1204088651323249306399) := by
  rw [show (91924:ℕ) = 91581 + 343 from rfl, Disp.arun_add, s6_c266, Nat.zero_add]; exact s6_s267
theorem s6_c268 : Disp.arun 117649 (7^25) 92267 0 0 1 0 1 0 = (3,1156274683175943225606,3,739077176910875805427,888007942385135615975) := by
  rw [show (92267:ℕ) = 91924 + 343 from rfl, Disp.arun_add, s6_c267, Nat.zero_add]; exact s6_s268
theorem s6_c269 : Disp.arun 117649 (7^25) 92610 0 0 1 0 1 0 = (3,94962586788471709368,3,769373799901325919421,1302430164595913623068) := by
  rw [show (92610:ℕ) = 92267 + 343 from rfl, Disp.arun_add, s6_c268, Nat.zero_add]; exact s6_s269
theorem s6_c270 : Disp.arun 117649 (7^25) 92953 0 0 1 0 1 0 = (3,1147883549103635509000,3,1241714789323137930636,1298501443726420147152) := by
  rw [show (92953:ℕ) = 92610 + 343 from rfl, Disp.arun_add, s6_c269, Nat.zero_add]; exact s6_s270
theorem s6_c271 : Disp.arun 117649 (7^25) 93296 0 0 1 0 1 0 = (3,405128729024883230067,3,1064910132573166079507,939391446386344354831) := by
  rw [show (93296:ℕ) = 92953 + 343 from rfl, Disp.arun_add, s6_c270, Nat.zero_add]; exact s6_s271
theorem s6_c272 : Disp.arun 117649 (7^25) 93639 0 0 1 0 1 0 = (2,555963522565663419321,2,150095176540187901626,960073672689148884371) := by
  rw [show (93639:ℕ) = 93296 + 343 from rfl, Disp.arun_add, s6_c271, Nat.zero_add]; exact s6_s272
theorem s6_c273 : Disp.arun 117649 (7^25) 93982 0 0 1 0 1 0 = (3,579260003286308011114,3,716705090944332848170,686304370592933583058) := by
  rw [show (93982:ℕ) = 93639 + 343 from rfl, Disp.arun_add, s6_c272, Nat.zero_add]; exact s6_s273
theorem s6_c274 : Disp.arun 117649 (7^25) 94325 0 0 1 0 1 0 = (3,816323275075703991516,3,997270628373317142849,1196618071732433889680) := by
  rw [show (94325:ℕ) = 93982 + 343 from rfl, Disp.arun_add, s6_c273, Nat.zero_add]; exact s6_s274
theorem s6_c275 : Disp.arun 117649 (7^25) 94668 0 0 1 0 1 0 = (3,71768111654060588839,3,818387658425602905813,1027669830225508425236) := by
  rw [show (94668:ℕ) = 94325 + 343 from rfl, Disp.arun_add, s6_c274, Nat.zero_add]; exact s6_s275
theorem s6_c276 : Disp.arun 117649 (7^25) 95011 0 0 1 0 1 0 = (3,198192622445232525154,3,322794532044034870773,593853018901863439720) := by
  rw [show (95011:ℕ) = 94668 + 343 from rfl, Disp.arun_add, s6_c275, Nat.zero_add]; exact s6_s276
theorem s6_c277 : Disp.arun 117649 (7^25) 95354 0 0 1 0 1 0 = (3,753725665173533748427,3,285973604264345945412,1184540756803361907671) := by
  rw [show (95354:ℕ) = 95011 + 343 from rfl, Disp.arun_add, s6_c276, Nat.zero_add]; exact s6_s277
theorem s6_c278 : Disp.arun 117649 (7^25) 95697 0 0 1 0 1 0 = (3,194813878651403946654,3,416787390835225464438,1280542216551672847452) := by
  rw [show (95697:ℕ) = 95354 + 343 from rfl, Disp.arun_add, s6_c277, Nat.zero_add]; exact s6_s278
theorem s6_c279 : Disp.arun 117649 (7^25) 96040 0 0 1 0 1 0 = (2,1325940205989865057883,2,1147933906614412561367,142968198977632409676) := by
  rw [show (96040:ℕ) = 95697 + 343 from rfl, Disp.arun_add, s6_c278, Nat.zero_add]; exact s6_s279
theorem s6_c280 : Disp.arun 117649 (7^25) 96383 0 0 1 0 1 0 = (3,280279446638240623981,3,308100609694678229255,639397046029918131117) := by
  rw [show (96383:ℕ) = 96040 + 343 from rfl, Disp.arun_add, s6_c279, Nat.zero_add]; exact s6_s280
theorem s6_c281 : Disp.arun 117649 (7^25) 96726 0 0 1 0 1 0 = (3,1022693995748578526817,3,710483794494914714684,893993438686329767080) := by
  rw [show (96726:ℕ) = 96383 + 343 from rfl, Disp.arun_add, s6_c280, Nat.zero_add]; exact s6_s281
theorem s6_c282 : Disp.arun 117649 (7^25) 97069 0 0 1 0 1 0 = (3,834867975508530372190,3,890628707178759435437,288552051310531470330) := by
  rw [show (97069:ℕ) = 96726 + 343 from rfl, Disp.arun_add, s6_c281, Nat.zero_add]; exact s6_s282
theorem s6_c283 : Disp.arun 117649 (7^25) 97412 0 0 1 0 1 0 = (3,773228459137821733212,3,194894898940777853750,244555017866506932761) := by
  rw [show (97412:ℕ) = 97069 + 343 from rfl, Disp.arun_add, s6_c282, Nat.zero_add]; exact s6_s283
theorem s6_c284 : Disp.arun 117649 (7^25) 97755 0 0 1 0 1 0 = (3,1157534283125895391734,3,1016802169512550412113,740900113928880827370) := by
  rw [show (97755:ℕ) = 97412 + 343 from rfl, Disp.arun_add, s6_c283, Nat.zero_add]; exact s6_s284
theorem s6_c285 : Disp.arun 117649 (7^25) 98098 0 0 1 0 1 0 = (3,1208561507862274829915,3,1234665240229515975257,9387728181614605565) := by
  rw [show (98098:ℕ) = 97755 + 343 from rfl, Disp.arun_add, s6_c284, Nat.zero_add]; exact s6_s285
theorem s6_c286 : Disp.arun 117649 (7^25) 98441 0 0 1 0 1 0 = (2,652992312247592459981,2,530213704389757656827,897896832297899088362) := by
  rw [show (98441:ℕ) = 98098 + 343 from rfl, Disp.arun_add, s6_c285, Nat.zero_add]; exact s6_s286
theorem s6_c287 : Disp.arun 117649 (7^25) 98784 0 0 1 0 1 0 = (3,1169791340116692844340,3,1205832661607615270902,1314525060377154056019) := by
  rw [show (98784:ℕ) = 98441 + 343 from rfl, Disp.arun_add, s6_c286, Nat.zero_add]; exact s6_s287
theorem s6_c288 : Disp.arun 117649 (7^25) 99127 0 0 1 0 1 0 = (3,351704394635956446550,3,455541288976086593914,283761971739508390801) := by
  rw [show (99127:ℕ) = 98784 + 343 from rfl, Disp.arun_add, s6_c287, Nat.zero_add]; exact s6_s288
theorem s6_c289 : Disp.arun 117649 (7^25) 99470 0 0 1 0 1 0 = (3,939496994992914279420,3,458808453887174553209,72408263080572439658) := by
  rw [show (99470:ℕ) = 99127 + 343 from rfl, Disp.arun_add, s6_c288, Nat.zero_add]; exact s6_s289
theorem s6_c290 : Disp.arun 117649 (7^25) 99813 0 0 1 0 1 0 = (3,130936805473861681471,3,953077123585767013388,739455718686583500757) := by
  rw [show (99813:ℕ) = 99470 + 343 from rfl, Disp.arun_add, s6_c289, Nat.zero_add]; exact s6_s290
theorem s6_c291 : Disp.arun 117649 (7^25) 100156 0 0 1 0 1 0 = (3,318826659332766945168,3,643239273420570467259,134987722656818118011) := by
  rw [show (100156:ℕ) = 99813 + 343 from rfl, Disp.arun_add, s6_c290, Nat.zero_add]; exact s6_s291
theorem s6_c292 : Disp.arun 117649 (7^25) 100499 0 0 1 0 1 0 = (3,1170467558225757008503,3,564760361718190675834,821088589085949378615) := by
  rw [show (100499:ℕ) = 100156 + 343 from rfl, Disp.arun_add, s6_c291, Nat.zero_add]; exact s6_s292
theorem s6_c293 : Disp.arun 117649 (7^25) 100842 0 0 1 0 1 0 = (1,250682943662213745446,1,880131730000175599736,629365902767589354032) := by
  rw [show (100842:ℕ) = 100499 + 343 from rfl, Disp.arun_add, s6_c292, Nat.zero_add]; exact s6_s293
theorem s6_c294 : Disp.arun 117649 (7^25) 101185 0 0 1 0 1 0 = (3,624976193127525882826,3,1294092625329759559347,284532566090947115376) := by
  rw [show (101185:ℕ) = 100842 + 343 from rfl, Disp.arun_add, s6_c293, Nat.zero_add]; exact s6_s294
theorem s6_c295 : Disp.arun 117649 (7^25) 101528 0 0 1 0 1 0 = (3,127640055842949049095,3,879613917516794721748,1136858797240037675868) := by
  rw [show (101528:ℕ) = 101185 + 343 from rfl, Disp.arun_add, s6_c294, Nat.zero_add]; exact s6_s295
theorem s6_c296 : Disp.arun 117649 (7^25) 101871 0 0 1 0 1 0 = (3,455947466389503145160,3,835210583241395159454,560693178542771437206) := by
  rw [show (101871:ℕ) = 101528 + 343 from rfl, Disp.arun_add, s6_c295, Nat.zero_add]; exact s6_s296
theorem s6_c297 : Disp.arun 117649 (7^25) 102214 0 0 1 0 1 0 = (3,418036360015284155360,3,1083610294122854808256,154230552334721216747) := by
  rw [show (102214:ℕ) = 101871 + 343 from rfl, Disp.arun_add, s6_c296, Nat.zero_add]; exact s6_s297
theorem s6_c298 : Disp.arun 117649 (7^25) 102557 0 0 1 0 1 0 = (3,851430368967532455426,3,552673477340568728826,363838692000302589092) := by
  rw [show (102557:ℕ) = 102214 + 343 from rfl, Disp.arun_add, s6_c297, Nat.zero_add]; exact s6_s298
theorem s6_c299 : Disp.arun 117649 (7^25) 102900 0 0 1 0 1 0 = (3,443053607397517948014,3,820679062551863663336,291899000332970041887) := by
  rw [show (102900:ℕ) = 102557 + 343 from rfl, Disp.arun_add, s6_c298, Nat.zero_add]; exact s6_s299
theorem s6_c300 : Disp.arun 117649 (7^25) 103243 0 0 1 0 1 0 = (2,1155438908825828169831,2,1279669104920132168145,263891387606354881843) := by
  rw [show (103243:ℕ) = 102900 + 343 from rfl, Disp.arun_add, s6_c299, Nat.zero_add]; exact s6_s300
theorem s6_c301 : Disp.arun 117649 (7^25) 103586 0 0 1 0 1 0 = (3,624209434588727324273,3,998874748575666088372,106225363781434343279) := by
  rw [show (103586:ℕ) = 103243 + 343 from rfl, Disp.arun_add, s6_c300, Nat.zero_add]; exact s6_s301
theorem s6_c302 : Disp.arun 117649 (7^25) 103929 0 0 1 0 1 0 = (3,209935717457740091206,3,677017375178906533083,156851161228772637243) := by
  rw [show (103929:ℕ) = 103586 + 343 from rfl, Disp.arun_add, s6_c301, Nat.zero_add]; exact s6_s302
theorem s6_c303 : Disp.arun 117649 (7^25) 104272 0 0 1 0 1 0 = (3,1131982467941576327526,3,958221704379611788905,275813332156609441664) := by
  rw [show (104272:ℕ) = 103929 + 343 from rfl, Disp.arun_add, s6_c302, Nat.zero_add]; exact s6_s303
theorem s6_c304 : Disp.arun 117649 (7^25) 104615 0 0 1 0 1 0 = (3,39392278533245709528,3,196564381413991799833,497411061032856325244) := by
  rw [show (104615:ℕ) = 104272 + 343 from rfl, Disp.arun_add, s6_c303, Nat.zero_add]; exact s6_s304
theorem s6_c305 : Disp.arun 117649 (7^25) 104958 0 0 1 0 1 0 = (3,407845693585122485179,3,191619264963384156230,332675405818114765316) := by
  rw [show (104958:ℕ) = 104615 + 343 from rfl, Disp.arun_add, s6_c304, Nat.zero_add]; exact s6_s305
theorem s6_c306 : Disp.arun 117649 (7^25) 105301 0 0 1 0 1 0 = (3,876438941251343474521,3,435883544809713264291,1001317424936152956227) := by
  rw [show (105301:ℕ) = 104958 + 343 from rfl, Disp.arun_add, s6_c305, Nat.zero_add]; exact s6_s306
theorem s6_c307 : Disp.arun 117649 (7^25) 105644 0 0 1 0 1 0 = (2,149757218028327919292,2,460465636727177059283,691195091290837809012) := by
  rw [show (105644:ℕ) = 105301 + 343 from rfl, Disp.arun_add, s6_c306, Nat.zero_add]; exact s6_s307
theorem s6_c308 : Disp.arun 117649 (7^25) 105987 0 0 1 0 1 0 = (3,1124770197481180240810,3,40019781699382924020,424831639823386496268) := by
  rw [show (105987:ℕ) = 105644 + 343 from rfl, Disp.arun_add, s6_c307, Nat.zero_add]; exact s6_s308
theorem s6_c309 : Disp.arun 117649 (7^25) 106330 0 0 1 0 1 0 = (3,421854992434666939326,3,139041377014227818365,32331460039405177274) := by
  rw [show (106330:ℕ) = 105987 + 343 from rfl, Disp.arun_add, s6_c308, Nat.zero_add]; exact s6_s309
theorem s6_c310 : Disp.arun 117649 (7^25) 106673 0 0 1 0 1 0 = (3,1114727749503533584354,3,1195233496354139842654,54963364271684516796) := by
  rw [show (106673:ℕ) = 106330 + 343 from rfl, Disp.arun_add, s6_c309, Nat.zero_add]; exact s6_s310
theorem s6_c311 : Disp.arun 117649 (7^25) 107016 0 0 1 0 1 0 = (3,1127043048553611256905,3,478359176370817245961,321075964275332264083) := by
  rw [show (107016:ℕ) = 106673 + 343 from rfl, Disp.arun_add, s6_c310, Nat.zero_add]; exact s6_s311
theorem s6_c312 : Disp.arun 117649 (7^25) 107359 0 0 1 0 1 0 = (3,297180757953847922101,3,1317395591022362778958,972176386154365514816) := by
  rw [show (107359:ℕ) = 107016 + 343 from rfl, Disp.arun_add, s6_c311, Nat.zero_add]; exact s6_s312
theorem s6_c313 : Disp.arun 117649 (7^25) 107702 0 0 1 0 1 0 = (3,286743065708758124880,3,1027592201252859471592,1276997047686201204861) := by
  rw [show (107702:ℕ) = 107359 + 343 from rfl, Disp.arun_add, s6_c312, Nat.zero_add]; exact s6_s313
theorem s6_c314 : Disp.arun 117649 (7^25) 108045 0 0 1 0 1 0 = (2,860052123623736754436,2,1062657771257393316570,147900533572193660098) := by
  rw [show (108045:ℕ) = 107702 + 343 from rfl, Disp.arun_add, s6_c313, Nat.zero_add]; exact s6_s314
theorem s6_c315 : Disp.arun 117649 (7^25) 108388 0 0 1 0 1 0 = (3,270749732791302488884,3,1062510612805312852231,1111952578508005556449) := by
  rw [show (108388:ℕ) = 108045 + 343 from rfl, Disp.arun_add, s6_c314, Nat.zero_add]; exact s6_s315
theorem s6_c316 : Disp.arun 117649 (7^25) 108731 0 0 1 0 1 0 = (3,656993141551310246057,3,529192584882962050607,194276413660324077454) := by
  rw [show (108731:ℕ) = 108388 + 343 from rfl, Disp.arun_add, s6_c315, Nat.zero_add]; exact s6_s316
theorem s6_c317 : Disp.arun 117649 (7^25) 109074 0 0 1 0 1 0 = (3,930517691570142379713,3,1059719254569641284302,182750169552817330598) := by
  rw [show (109074:ℕ) = 108731 + 343 from rfl, Disp.arun_add, s6_c316, Nat.zero_add]; exact s6_s317
theorem s6_c318 : Disp.arun 117649 (7^25) 109417 0 0 1 0 1 0 = (3,896809642618983789425,3,236944173858829974637,495349411494636925332) := by
  rw [show (109417:ℕ) = 109074 + 343 from rfl, Disp.arun_add, s6_c317, Nat.zero_add]; exact s6_s318
theorem s6_c319 : Disp.arun 117649 (7^25) 109760 0 0 1 0 1 0 = (3,597057720594278716735,3,1262338073164730313909,613609156640920507565) := by
  rw [show (109760:ℕ) = 109417 + 343 from rfl, Disp.arun_add, s6_c318, Nat.zero_add]; exact s6_s319
theorem s6_c320 : Disp.arun 117649 (7^25) 110103 0 0 1 0 1 0 = (3,670189137411284383528,3,1155519468091601268214,923978539601291036304) := by
  rw [show (110103:ℕ) = 109760 + 343 from rfl, Disp.arun_add, s6_c319, Nat.zero_add]; exact s6_s320
theorem s6_c321 : Disp.arun 117649 (7^25) 110446 0 0 1 0 1 0 = (2,1318141762523998581909,2,1180977147357136835792,556783790765136595963) := by
  rw [show (110446:ℕ) = 110103 + 343 from rfl, Disp.arun_add, s6_c320, Nat.zero_add]; exact s6_s321
theorem s6_c322 : Disp.arun 117649 (7^25) 110789 0 0 1 0 1 0 = (3,1131186596708439174583,3,190876943945720679725,533130776158698310825) := by
  rw [show (110789:ℕ) = 110446 + 343 from rfl, Disp.arun_add, s6_c321, Nat.zero_add]; exact s6_s322
theorem s6_c323 : Disp.arun 117649 (7^25) 111132 0 0 1 0 1 0 = (3,517598928768395453542,3,593708784964107500349,442397626675548237100) := by
  rw [show (111132:ℕ) = 110789 + 343 from rfl, Disp.arun_add, s6_c322, Nat.zero_add]; exact s6_s323
theorem s6_c324 : Disp.arun 117649 (7^25) 111475 0 0 1 0 1 0 = (3,387085178131660867017,3,263855810983215969600,1287806544285585198981) := by
  rw [show (111475:ℕ) = 111132 + 343 from rfl, Disp.arun_add, s6_c323, Nat.zero_add]; exact s6_s324
theorem s6_c325 : Disp.arun 117649 (7^25) 111818 0 0 1 0 1 0 = (3,265231419042721748433,3,420453703513863598007,109884381442555718307) := by
  rw [show (111818:ℕ) = 111475 + 343 from rfl, Disp.arun_add, s6_c324, Nat.zero_add]; exact s6_s325
theorem s6_c326 : Disp.arun 117649 (7^25) 112161 0 0 1 0 1 0 = (3,793973234892083640677,3,1162995910968396877319,93752965049785649133) := by
  rw [show (112161:ℕ) = 111818 + 343 from rfl, Disp.arun_add, s6_c325, Nat.zero_add]; exact s6_s326
theorem s6_c327 : Disp.arun 117649 (7^25) 112504 0 0 1 0 1 0 = (3,38603342118300162183,3,113869547925662276418,1188858966224350516376) := by
  rw [show (112504:ℕ) = 112161 + 343 from rfl, Disp.arun_add, s6_c326, Nat.zero_add]; exact s6_s327
theorem s6_c328 : Disp.arun 117649 (7^25) 112847 0 0 1 0 1 0 = (2,527749988428974657293,2,1131990438222581422264,695604309998638450677) := by
  rw [show (112847:ℕ) = 112504 + 343 from rfl, Disp.arun_add, s6_c327, Nat.zero_add]; exact s6_s328
theorem s6_c329 : Disp.arun 117649 (7^25) 113190 0 0 1 0 1 0 = (3,198994904548099032673,3,813338747183063999374,870964602607070261396) := by
  rw [show (113190:ℕ) = 112847 + 343 from rfl, Disp.arun_add, s6_c328, Nat.zero_add]; exact s6_s329
theorem s6_c330 : Disp.arun 117649 (7^25) 113533 0 0 1 0 1 0 = (3,880409664531227717492,3,951110382867019954940,826590682816069486687) := by
  rw [show (113533:ℕ) = 113190 + 343 from rfl, Disp.arun_add, s6_c329, Nat.zero_add]; exact s6_s330
theorem s6_c331 : Disp.arun 117649 (7^25) 113876 0 0 1 0 1 0 = (3,939522389194202614761,3,399035412372099227184,287852960579060089109) := by
  rw [show (113876:ℕ) = 113533 + 343 from rfl, Disp.arun_add, s6_c330, Nat.zero_add]; exact s6_s331
theorem s6_c332 : Disp.arun 117649 (7^25) 114219 0 0 1 0 1 0 = (3,1086049373877897747250,3,910082214606480195835,1192616460897212951678) := by
  rw [show (114219:ℕ) = 113876 + 343 from rfl, Disp.arun_add, s6_c331, Nat.zero_add]; exact s6_s332
theorem s6_c333 : Disp.arun 117649 (7^25) 114562 0 0 1 0 1 0 = (3,90078468004214639499,3,1030167007161345419229,574337089712344182806) := by
  rw [show (114562:ℕ) = 114219 + 343 from rfl, Disp.arun_add, s6_c332, Nat.zero_add]; exact s6_s333
theorem s6_c334 : Disp.arun 117649 (7^25) 114905 0 0 1 0 1 0 = (3,1245071362813592380695,3,267894300476374396684,1037327497235646435092) := by
  rw [show (114905:ℕ) = 114562 + 343 from rfl, Disp.arun_add, s6_c333, Nat.zero_add]; exact s6_s334
theorem s6_c335 : Disp.arun 117649 (7^25) 115248 0 0 1 0 1 0 = (2,150941942414299175196,2,1242776448777207885099,542842637659903305334) := by
  rw [show (115248:ℕ) = 114905 + 343 from rfl, Disp.arun_add, s6_c334, Nat.zero_add]; exact s6_s335
theorem s6_c336 : Disp.arun 117649 (7^25) 115591 0 0 1 0 1 0 = (3,51544946519567379446,3,222876284232909526668,1029119213947003546620) := by
  rw [show (115591:ℕ) = 115248 + 343 from rfl, Disp.arun_add, s6_c335, Nat.zero_add]; exact s6_s336
theorem s6_c337 : Disp.arun 117649 (7^25) 115934 0 0 1 0 1 0 = (3,1039626253192599878809,3,354152654228906810344,688238840273426259546) := by
  rw [show (115934:ℕ) = 115591 + 343 from rfl, Disp.arun_add, s6_c336, Nat.zero_add]; exact s6_s337
theorem s6_c338 : Disp.arun 117649 (7^25) 116277 0 0 1 0 1 0 = (3,1219021433766825930603,3,215254208389170556835,1209310202012476557498) := by
  rw [show (116277:ℕ) = 115934 + 343 from rfl, Disp.arun_add, s6_c337, Nat.zero_add]; exact s6_s338
theorem s6_c339 : Disp.arun 117649 (7^25) 116620 0 0 1 0 1 0 = (3,68793879830137568419,3,731291885325590202077,1045639033025257126562) := by
  rw [show (116620:ℕ) = 116277 + 343 from rfl, Disp.arun_add, s6_c338, Nat.zero_add]; exact s6_s339
theorem s6_c340 : Disp.arun 117649 (7^25) 116963 0 0 1 0 1 0 = (3,1219663972324357079096,3,987943894097897562129,68507982851596800254) := by
  rw [show (116963:ℕ) = 116620 + 343 from rfl, Disp.arun_add, s6_c339, Nat.zero_add]; exact s6_s340
theorem s6_c341 : Disp.arun 117649 (7^25) 117306 0 0 1 0 1 0 = (3,687843876034320749108,3,1031382220773721705069,980738726689953528564) := by
  rw [show (117306:ℕ) = 116963 + 343 from rfl, Disp.arun_add, s6_c340, Nat.zero_add]; exact s6_s341
theorem s6_c342 : Disp.arun 117649 (7^25) 117649 0 0 1 0 1 0 = (0,1,0,1053715666652496881601,821327337676838434975) := by
  rw [show (117649:ℕ) = 117306 + 343 from rfl, Disp.arun_add, s6_c341, Nat.zero_add]; exact s6_s342
theorem final_sum_6 : (∑ k ∈ Finset.range (7^6), Disp.tt (7^6) k) % (7^25) = 821327337676838434975 := by
  rw [Disp.aMod (7^6) (by norm_num) (by norm_num), show (((7^6)):ℕ) = 117649 from rfl, s6_c342]

theorem s5_s0 : Disp.arun 16807 (7^25) 343 0 0 1 0 1 0 = (2,263808536815926437546,2,531891256355969439665,78196334352884457123) := by rfl
theorem s5_s1 : Disp.arun 16807 (7^25) 343 343 2 263808536815926437546 2 531891256355969439665 78196334352884457123 = (2,79605710885040566502,2,682648100587024949899,318614985134638164239) := by rfl
theorem s5_s2 : Disp.arun 16807 (7^25) 343 686 2 79605710885040566502 2 682648100587024949899 318614985134638164239 = (2,206072748255136115813,2,207683285658457649430,529557036415964633168) := by rfl
theorem s5_s3 : Disp.arun 16807 (7^25) 343 1029 2 206072748255136115813 2 207683285658457649430 529557036415964633168 = (2,138667053107664143011,2,439198231308265602637,935133900926406340671) := by rfl
theorem s5_s4 : Disp.arun 16807 (7^25) 343 1372 2 138667053107664143011 2 439198231308265602637 935133900926406340671 = (2,468438648289851293631,2,560336698567030710825,1047077388857569446070) := by rfl
theorem s5_s5 : Disp.arun 16807 (7^25) 343 1715 2 468438648289851293631 2 560336698567030710825 1047077388857569446070 = (2,602196943822245250494,2,283080904382895239403,592717664836499080502) := by rfl
theorem s5_s6 : Disp.arun 16807 (7^25) 343 2058 2 602196943822245250494 2 283080904382895239403 592717664836499080502 = (1,960761965018693950575,1,856606916505909128071,689710024495785018615) := by rfl
theorem s5_s7 : Disp.arun 16807 (7^25) 343 2401 1 960761965018693950575 1 856606916505909128071 689710024495785018615 = (2,495428522916560649464,2,711756282396600418601,208893770634664377788) := by rfl
theorem s5_s8 : Disp.arun 16807 (7^25) 343 2744 2 495428522916560649464 2 711756282396600418601 208893770634664377788 = (2,800968383414225309735,2,1207195744001341262361,334501768986163552446) := by rfl
theorem s5_s9 : Disp.arun 16807 (7^25) 343 3087 2 800968383414225309735 2 1207195744001341262361 334501768986163552446 = (2,775695839739518945753,2,532504771660182945083,1333682620821791635886) := by rfl
theorem s5_s10 : Disp.arun 16807 (7^25) 343 3430 2 775695839739518945753 2 532504771660182945083 1333682620821791635886 = (2,1234050666315649066852,2,620682062496760329865,38379494976619295045) := by rfl
theorem s5_s11 : Disp.arun 16807 (7^25) 343 3773 2 1234050666315649066852 2 620682062496760329865 38379494976619295045 = (2,524753670962811639661,2,1053136173776629157407,22695493635419534749) := by rfl
theorem s5_s12 : Disp.arun 16807 (7^25) 343 4116 2 524753670962811639661 2 1053136173776629157407 22695493635419534749 = (2,126672404650829875998,2,456899610050493661610,567373024387218575464) := by rfl
theorem s5_s13 : Disp.arun 16807 (7^25) 343 4459 2 126672404650829875998 2 456899610050493661610 567373024387218575464 = (1,1041048521399036363020,1,1147867766755059694502,939570420941550182065) := by rfl
theorem s5_s14 : Disp.arun 16807 (7^25) 343 4802 1 1041048521399036363020 1 1147867766755059694502 939570420941550182065 = (2,628629374788768332764,2,1122316276367987384846,1264974932131474068639) := by rfl
theorem s5_s15 : Disp.arun 16807 (7^25) 343 5145 2 628629374788768332764 2 1122316276367987384846 1264974932131474068639 = (2,587358874675105918003,2,1036734918106531172281,358630598141805647988) := by rfl
theorem s5_s16 : Disp.arun 16807 (7^25) 343 5488 2 587358874675105918003 2 1036734918106531172281 358630598141805647988 = (2,75448968072199405500,2,483070817381993972472,387865194721392105922) := by rfl
theorem s5_s17 : Disp.arun 16807 (7^25) 343 5831 2 75448968072199405500 2 483070817381993972472 387865194721392105922 = (2,1281113301066636905586,2,658678865923925039979,1167814659679783945831) := by rfl
theorem s5_s18 : Disp.arun 16807 (7^25) 343 6174 2 1281113301066636905586 2 658678865923925039979 1167814659679783945831 = (2,404870253420595566663,2,801712976791716998641,6399318474200633801) := by rfl
theorem s5_s19 : Disp.arun 16807 (7^25) 343 6517 2 404870253420595566663 2 801712976791716998641 6399318474200633801 = (2,406920827603488568154,2,922427652269941524300,1311100432643496468457) := by rfl
theorem s5_s20 : Disp.arun 16807 (7^25) 343 6860 2 406920827603488568154 2 922427652269941524300 1311100432643496468457 = (1,456264279088523067419,1,726446700272183271575,1323083434871098081826) := by rfl
theorem s5_s21 : Disp.arun 16807 (7^25) 343 7203 1 456264279088523067419 1 726446700272183271575 1323083434871098081826 = (2,1104715450421846051158,2,247759647811976037515,816693151369412721545) := by rfl
theorem s5_s22 : Disp.arun 16807 (7^25) 343 7546 2 1104715450421846051158 2 247759647811976037515 816693151369412721545 = (2,965576800455439530859,2,556661201649473181881,894555121742667014449) := by rfl
theorem s5_s23 : Disp.arun 16807 (7^25) 343 7889 2 965576800455439530859 2 556661201649473181881 894555121742667014449 = (2,1135383048364926488640,2,634474585250883854013,726286630170220762987) := by rfl
theorem s5_s24 : Disp.arun 16807 (7^25) 343 8232 2 1135383048364926488640 2 634474585250883854013 726286630170220762987 = (2,1135383048364926488640,2,1123097911241209224708,114251436211980048983) := by rfl
theorem s5_s25 : Disp.arun 16807 (7^25) 343 8575 2 1135383048364926488640 2 1123097911241209224708 114251436211980048983 = (2,965576800455439530859,2,1338147824265699027451,339491193904736761343) := by rfl
theorem s5_s26 : Disp.arun 16807 (7^25) 343 8918 2 965576800455439530859 2 1338147824265699027451 339491193904736761343 = (2,1104715450421846051158,2,1162384283029872954400,905574133271696425867) := by rfl
theorem s5_s27 : Disp.arun 16807 (7^25) 343 9261 2 1104715450421846051158 2 1162384283029872954400 905574133271696425867 = (1,456264279088523067419,1,576200687095495538372,939347922964909366056) := by rfl
theorem s5_s28 : Disp.arun 16807 (7^25) 343 9604 1 456264279088523067419 1 576200687095495538372 939347922964909366056 = (2,406920827603488568154,2,1033998333747664983265,1212327623357536721764) := by rfl
theorem s5_s29 : Disp.arun 16807 (7^25) 343 9947 2 406920827603488568154 2 1033998333747664983265 1212327623357536721764 = (2,404870253420595566663,2,1126860679188484123167,896219920058321069310) := by rfl
theorem s5_s30 : Disp.arun 16807 (7^25) 343 10290 2 404870253420595566663 2 1126860679188484123167 896219920058321069310 = (2,1281113301066636905586,2,1158544225992290712755,966250124434030095241) := by rfl
theorem s5_s31 : Disp.arun 16807 (7^25) 343 10633 2 1281113301066636905586 2 1158544225992290712755 966250124434030095241 = (2,75448968072199405500,2,471414193620869924399,125154086620431494795) := by rfl
theorem s5_s32 : Disp.arun 16807 (7^25) 343 10976 2 75448968072199405500 2 471414193620869924399 125154086620431494795 = (2,587358874675105918003,2,556453740948862003593,316241360363052184369) := by rfl
theorem s5_s33 : Disp.arun 16807 (7^25) 343 11319 2 587358874675105918003 2 556453740948862003593 316241360363052184369 = (2,628629374788768332764,2,487735766955719393943,1051526345907218922861) := by rfl
theorem s5_s34 : Disp.arun 16807 (7^25) 343 11662 2 628629374788768332764 2 487735766955719393943 1051526345907218922861 = (1,1041048521399036363020,1,664016780388929542424,786814235946542431006) := by rfl
theorem s5_s35 : Disp.arun 16807 (7^25) 343 12005 1 1041048521399036363020 1 664016780388929542424 786814235946542431006 = (2,126672404650829875998,2,1246847147401255492121,1288283430225289775012) := by rfl
theorem s5_s36 : Disp.arun 16807 (7^25) 343 12348 2 126672404650829875998 2 1246847147401255492121 1288283430225289775012 = (2,524753670962811639661,2,824404459907115499815,720105486813439136992) := by rfl
theorem s5_s37 : Disp.arun 16807 (7^25) 343 12691 2 524753670962811639661 2 824404459907115499815 720105486813439136992 = (2,1234050666315649066852,2,1193342671265538335526,41678769290860287818) := by rfl
theorem s5_s38 : Disp.arun 16807 (7^25) 343 13034 2 1234050666315649066852 2 1193342671265538335526 41678769290860287818 = (2,775695839739518945753,2,46934446700980717650,16131162388398912541) := by rfl
theorem s5_s39 : Disp.arun 16807 (7^25) 343 13377 2 775695839739518945753 2 46934446700980717650 16131162388398912541 = (2,800968383414225309735,2,1138682479317947299802,1306419233863112996257) := by rfl
theorem s5_s40 : Disp.arun 16807 (7^25) 343 13720 2 800968383414225309735 2 1138682479317947299802 1306419233863112996257 = (2,495428522916560649464,2,466934258683399517345,1295022941661114017339) := by rfl
theorem s5_s41 : Disp.arun 16807 (7^25) 343 14063 2 495428522916560649464 2 466934258683399517345 1295022941661114017339 = (1,960761965018693950575,1,300950110310211838993,260167086608538625405) := by rfl
theorem s5_s42 : Disp.arun 16807 (7^25) 343 14406 1 960761965018693950575 1 300950110310211838993 260167086608538625405 = (2,602196943822245250494,2,1053680335212328299134,455472618986921296244) := by rfl
theorem s5_s43 : Disp.arun 16807 (7^25) 343 14749 2 602196943822245250494 2 1053680335212328299134 455472618986921296244 = (2,468438648289851293631,2,944109285942836130240,308032628529704980210) := by rfl
theorem s5_s44 : Disp.arun 16807 (7^25) 343 15092 2 468438648289851293631 2 944109285942836130240 308032628529704980210 = (2,138667053107664143011,2,42376700517777286554,531062996333326488900) := by rfl
theorem s5_s45 : Disp.arun 16807 (7^25) 343 15435 2 138667053107664143011 2 42376700517777286554 531062996333326488900 = (2,206072748255136115813,2,300295635773386583493,173621328004003767161) := by rfl
theorem s5_s46 : Disp.arun 16807 (7^25) 343 15778 2 206072748255136115813 2 300295635773386583493 173621328004003767161 = (2,79605710885040566502,2,131359198347321428879,1078766772759771279479) := by rfl
theorem s5_s47 : Disp.arun 16807 (7^25) 343 16121 2 79605710885040566502 2 131359198347321428879 1078766772759771279479 = (2,263808536815926437546,2,1032732348801416906061,159680174898770476532) := by rfl
theorem s5_s48 : Disp.arun 16807 (7^25) 343 16464 2 263808536815926437546 2 1032732348801416906061 159680174898770476532 = (0,1,0,833959623200883878602,1012908569057404849376) := by rfl
theorem s5_c0 : Disp.arun 16807 (7^25) 343 0 0 1 0 1 0 = (2,263808536815926437546,2,531891256355969439665,78196334352884457123) := s5_s0
theorem s5_c1 : Disp.arun 16807 (7^25) 686 0 0 1 0 1 0 = (2,79605710885040566502,2,682648100587024949899,318614985134638164239) := by
  rw [show (686:ℕ) = 343 + 343 from rfl, Disp.arun_add, s5_c0, Nat.zero_add]; exact s5_s1
theorem s5_c2 : Disp.arun 16807 (7^25) 1029 0 0 1 0 1 0 = (2,206072748255136115813,2,207683285658457649430,529557036415964633168) := by
  rw [show (1029:ℕ) = 686 + 343 from rfl, Disp.arun_add, s5_c1, Nat.zero_add]; exact s5_s2
theorem s5_c3 : Disp.arun 16807 (7^25) 1372 0 0 1 0 1 0 = (2,138667053107664143011,2,439198231308265602637,935133900926406340671) := by
  rw [show (1372:ℕ) = 1029 + 343 from rfl, Disp.arun_add, s5_c2, Nat.zero_add]; exact s5_s3
theorem s5_c4 : Disp.arun 16807 (7^25) 1715 0 0 1 0 1 0 = (2,468438648289851293631,2,560336698567030710825,1047077388857569446070) := by
  rw [show (1715:ℕ) = 1372 + 343 from rfl, Disp.arun_add, s5_c3, Nat.zero_add]; exact s5_s4
theorem s5_c5 : Disp.arun 16807 (7^25) 2058 0 0 1 0 1 0 = (2,602196943822245250494,2,283080904382895239403,592717664836499080502) := by
  rw [show (2058:ℕ) = 1715 + 343 from rfl, Disp.arun_add, s5_c4, Nat.zero_add]; exact s5_s5
theorem s5_c6 : Disp.arun 16807 (7^25) 2401 0 0 1 0 1 0 = (1,960761965018693950575,1,856606916505909128071,689710024495785018615) := by
  rw [show (2401:ℕ) = 2058 + 343 from rfl, Disp.arun_add, s5_c5, Nat.zero_add]; exact s5_s6
theorem s5_c7 : Disp.arun 16807 (7^25) 2744 0 0 1 0 1 0 = (2,495428522916560649464,2,711756282396600418601,208893770634664377788) := by
  rw [show (2744:ℕ) = 2401 + 343 from rfl, Disp.arun_add, s5_c6, Nat.zero_add]; exact s5_s7
theorem s5_c8 : Disp.arun 16807 (7^25) 3087 0 0 1 0 1 0 = (2,800968383414225309735,2,1207195744001341262361,334501768986163552446) := by
  rw [show (3087:ℕ) = 2744 + 343 from rfl, Disp.arun_add, s5_c7, Nat.zero_add]; exact s5_s8
theorem s5_c9 : Disp.arun 16807 (7^25) 3430 0 0 1 0 1 0 = (2,775695839739518945753,2,532504771660182945083,1333682620821791635886) := by
  rw [show (3430:ℕ) = 3087 + 343 from rfl, Disp.arun_add, s5_c8, Nat.zero_add]; exact s5_s9
theorem s5_c10 : Disp.arun 16807 (7^25) 3773 0 0 1 0 1 0 = (2,1234050666315649066852,2,620682062496760329865,38379494976619295045) := by
  rw [show (3773:ℕ) = 3430 + 343 from rfl, Disp.arun_add, s5_c9, Nat.zero_add]; exact s5_s10
theorem s5_c11 : Disp.arun 16807 (7^25) 4116 0 0 1 0 1 0 = (2,524753670962811639661,2,1053136173776629157407,22695493635419534749) := by
  rw [show (4116:ℕ) = 3773 + 343 from rfl, Disp.arun_add, s5_c10, Nat.zero_add]; exact s5_s11
theorem s5_c12 : Disp.arun 16807 (7^25) 4459 0 0 1 0 1 0 = (2,126672404650829875998,2,456899610050493661610,567373024387218575464) := by
  rw [show (4459:ℕ) = 4116 + 343 from rfl, Disp.arun_add, s5_c11, Nat.zero_add]; exact s5_s12
theorem s5_c13 : Disp.arun 16807 (7^25) 4802 0 0 1 0 1 0 = (1,1041048521399036363020,1,1147867766755059694502,939570420941550182065) := by
  rw [show (4802:ℕ) = 4459 + 343 from rfl, Disp.arun_add, s5_c12, Nat.zero_add]; exact s5_s13
theorem s5_c14 : Disp.arun 16807 (7^25) 5145 0 0 1 0 1 0 = (2,628629374788768332764,2,1122316276367987384846,1264974932131474068639) := by
  rw [show (5145:ℕ) = 4802 + 343 from rfl, Disp.arun_add, s5_c13, Nat.zero_add]; exact s5_s14
theorem s5_c15 : Disp.arun 16807 (7^25) 5488 0 0 1 0 1 0 = (2,587358874675105918003,2,1036734918106531172281,358630598141805647988) := by
  rw [show (5488:ℕ) = 5145 + 343 from rfl, Disp.arun_add, s5_c14, Nat.zero_add]; exact s5_s15
theorem s5_c16 : Disp.arun 16807 (7^25) 5831 0 0 1 0 1 0 = (2,75448968072199405500,2,483070817381993972472,387865194721392105922) := by
  rw [show (5831:ℕ) = 5488 + 343 from rfl, Disp.arun_add, s5_c15, Nat.zero_add]; exact s5_s16
theorem s5_c17 : Disp.arun 16807 (7^25) 6174 0 0 1 0 1 0 = (2,1281113301066636905586,2,658678865923925039979,1167814659679783945831) := by
  rw [show (6174:ℕ) = 5831 + 343 from rfl, Disp.arun_add, s5_c16, Nat.zero_add]; exact s5_s17
theorem s5_c18 : Disp.arun 16807 (7^25) 6517 0 0 1 0 1 0 = (2,404870253420595566663,2,801712976791716998641,6399318474200633801) := by
  rw [show (6517:ℕ) = 6174 + 343 from rfl, Disp.arun_add, s5_c17, Nat.zero_add]; exact s5_s18
theorem s5_c19 : Disp.arun 16807 (7^25) 6860 0 0 1 0 1 0 = (2,406920827603488568154,2,922427652269941524300,1311100432643496468457) := by
  rw [show (6860:ℕ) = 6517 + 343 from rfl, Disp.arun_add, s5_c18, Nat.zero_add]; exact s5_s19
theorem s5_c20 : Disp.arun 16807 (7^25) 7203 0 0 1 0 1 0 = (1,456264279088523067419,1,726446700272183271575,1323083434871098081826) := by
  rw [show (7203:ℕ) = 6860 + 343 from rfl, Disp.arun_add, s5_c19, Nat.zero_add]; exact s5_s20
theorem s5_c21 : Disp.arun 16807 (7^25) 7546 0 0 1 0 1 0 = (2,1104715450421846051158,2,247759647811976037515,816693151369412721545) := by
  rw [show (7546:ℕ) = 7203 + 343 from rfl, Disp.arun_add, s5_c20, Nat.zero_add]; exact s5_s21
theorem s5_c22 : Disp.arun 16807 (7^25) 7889 0 0 1 0 1 0 = (2,965576800455439530859,2,556661201649473181881,894555121742667014449) := by
  rw [show (7889:ℕ) = 7546 + 343 from rfl, Disp.arun_add, s5_c21, Nat.zero_add]; exact s5_s22
theorem s5_c23 : Disp.arun 16807 (7^25) 8232 0 0 1 0 1 0 = (2,1135383048364926488640,2,634474585250883854013,726286630170220762987) := by
  rw [show (8232:ℕ) = 7889 + 343 from rfl, Disp.arun_add, s5_c22, Nat.zero_add]; exact s5_s23
theorem s5_c24 : Disp.arun 16807 (7^25) 8575 0 0 1 0 1 0 = (2,1135383048364926488640,2,1123097911241209224708,114251436211980048983) := by
  rw [show (8575:ℕ) = 8232 + 343 from rfl, Disp.arun_add, s5_c23, Nat.zero_add]; exact s5_s24
theorem s5_c25 : Disp.arun 16807 (7^25) 8918 0 0 1 0 1 0 = (2,965576800455439530859,2,1338147824265699027451,339491193904736761343) := by
  rw [show (8918:ℕ) = 8575 + 343 from rfl, Disp.arun_add, s5_c24, Nat.zero_add]; exact s5_s25
theorem s5_c26 : Disp.arun 16807 (7^25) 9261 0 0 1 0 1 0 = (2,1104715450421846051158,2,1162384283029872954400,905574133271696425867) := by
  rw [show (9261:ℕ) = 8918 + 343 from rfl, Disp.arun_add, s5_c25, Nat.zero_add]; exact s5_s26
theorem s5_c27 : Disp.arun 16807 (7^25) 9604 0 0 1 0 1 0 = (1,456264279088523067419,1,576200687095495538372,939347922964909366056) := by
  rw [show (9604:ℕ) = 9261 + 343 from rfl, Disp.arun_add, s5_c26, Nat.zero_add]; exact s5_s27
theorem s5_c28 : Disp.arun 16807 (7^25) 9947 0 0 1 0 1 0 = (2,406920827603488568154,2,1033998333747664983265,1212327623357536721764) := by
  rw [show (9947:ℕ) = 9604 + 343 from rfl, Disp.arun_add, s5_c27, Nat.zero_add]; exact s5_s28
theorem s5_c29 : Disp.arun 16807 (7^25) 10290 0 0 1 0 1 0 = (2,404870253420595566663,2,1126860679188484123167,896219920058321069310) := by
  rw [show (10290:ℕ) = 9947 + 343 from rfl, Disp.arun_add, s5_c28, Nat.zero_add]; exact s5_s29
theorem s5_c30 : Disp.arun 16807 (7^25) 10633 0 0 1 0 1 0 = (2,1281113301066636905586,2,1158544225992290712755,966250124434030095241) := by
  rw [show (10633:ℕ) = 10290 + 343 from rfl, Disp.arun_add, s5_c29, Nat.zero_add]; exact s5_s30
theorem s5_c31 : Disp.arun 16807 (7^25) 10976 0 0 1 0 1 0 = (2,75448968072199405500,2,471414193620869924399,125154086620431494795) := by
  rw [show (10976:ℕ) = 10633 + 343 from rfl, Disp.arun_add, s5_c30, Nat.zero_add]; exact s5_s31
theorem s5_c32 : Disp.arun 16807 (7^25) 11319 0 0 1 0 1 0 = (2,587358874675105918003,2,556453740948862003593,316241360363052184369) := by
  rw [show (11319:ℕ) = 10976 + 343 from rfl, Disp.arun_add, s5_c31, Nat.zero_add]; exact s5_s32
theorem s5_c33 : Disp.arun 16807 (7^25) 11662 0 0 1 0 1 0 = (2,628629374788768332764,2,487735766955719393943,1051526345907218922861) := by
  rw [show (11662:ℕ) = 11319 + 343 from rfl, Disp.arun_add, s5_c32, Nat.zero_add]; exact s5_s33
theorem s5_c34 : Disp.arun 16807 (7^25) 12005 0 0 1 0 1 0 = (1,1041048521399036363020,1,664016780388929542424,786814235946542431006) := by
  rw [show (12005:ℕ) = 11662 + 343 from rfl, Disp.arun_add, s5_c33, Nat.zero_add]; exact s5_s34
theorem s5_c35 : Disp.arun 16807 (7^25) 12348 0 0 1 0 1 0 = (2,126672404650829875998,2,1246847147401255492121,1288283430225289775012) := by
  rw [show (12348:ℕ) = 12005 + 343 from rfl, Disp.arun_add, s5_c34, Nat.zero_add]; exact s5_s35
theorem s5_c36 : Disp.arun 16807 (7^25) 12691 0 0 1 0 1 0 = (2,524753670962811639661,2,824404459907115499815,720105486813439136992) := by
  rw [show (12691:ℕ) = 12348 + 343 from rfl, Disp.arun_add, s5_c35, Nat.zero_add]; exact s5_s36
theorem s5_c37 : Disp.arun 16807 (7^25) 13034 0 0 1 0 1 0 = (2,1234050666315649066852,2,1193342671265538335526,41678769290860287818) := by
  rw [show (13034:ℕ) = 12691 + 343 from rfl, Disp.arun_add, s5_c36, Nat.zero_add]; exact s5_s37
theorem s5_c38 : Disp.arun 16807 (7^25) 13377 0 0 1 0 1 0 = (2,775695839739518945753,2,46934446700980717650,16131162388398912541) := by
  rw [show (13377:ℕ) = 13034 + 343 from rfl, Disp.arun_add, s5_c37, Nat.zero_add]; exact s5_s38
theorem s5_c39 : Disp.arun 16807 (7^25) 13720 0 0 1 0 1 0 = (2,800968383414225309735,2,1138682479317947299802,1306419233863112996257) := by
  rw [show (13720:ℕ) = 13377 + 343 from rfl, Disp.arun_add, s5_c38, Nat.zero_add]; exact s5_s39
theorem s5_c40 : Disp.arun 16807 (7^25) 14063 0 0 1 0 1 0 = (2,495428522916560649464,2,466934258683399517345,1295022941661114017339) := by
  rw [show (14063:ℕ) = 13720 + 343 from rfl, Disp.arun_add, s5_c39, Nat.zero_add]; exact s5_s40
theorem s5_c41 : Disp.arun 16807 (7^25) 14406 0 0 1 0 1 0 = (1,960761965018693950575,1,300950110310211838993,260167086608538625405) := by
  rw [show (14406:ℕ) = 14063 + 343 from rfl, Disp.arun_add, s5_c40, Nat.zero_add]; exact s5_s41
theorem s5_c42 : Disp.arun 16807 (7^25) 14749 0 0 1 0 1 0 = (2,602196943822245250494,2,1053680335212328299134,455472618986921296244) := by
  rw [show (14749:ℕ) = 14406 + 343 from rfl, Disp.arun_add, s5_c41, Nat.zero_add]; exact s5_s42
theorem s5_c43 : Disp.arun 16807 (7^25) 15092 0 0 1 0 1 0 = (2,468438648289851293631,2,944109285942836130240,308032628529704980210) := by
  rw [show (15092:ℕ) = 14749 + 343 from rfl, Disp.arun_add, s5_c42, Nat.zero_add]; exact s5_s43
theorem s5_c44 : Disp.arun 16807 (7^25) 15435 0 0 1 0 1 0 = (2,138667053107664143011,2,42376700517777286554,531062996333326488900) := by
  rw [show (15435:ℕ) = 15092 + 343 from rfl, Disp.arun_add, s5_c43, Nat.zero_add]; exact s5_s44
theorem s5_c45 : Disp.arun 16807 (7^25) 15778 0 0 1 0 1 0 = (2,206072748255136115813,2,300295635773386583493,173621328004003767161) := by
  rw [show (15778:ℕ) = 15435 + 343 from rfl, Disp.arun_add, s5_c44, Nat.zero_add]; exact s5_s45
theorem s5_c46 : Disp.arun 16807 (7^25) 16121 0 0 1 0 1 0 = (2,79605710885040566502,2,131359198347321428879,1078766772759771279479) := by
  rw [show (16121:ℕ) = 15778 + 343 from rfl, Disp.arun_add, s5_c45, Nat.zero_add]; exact s5_s46
theorem s5_c47 : Disp.arun 16807 (7^25) 16464 0 0 1 0 1 0 = (2,263808536815926437546,2,1032732348801416906061,159680174898770476532) := by
  rw [show (16464:ℕ) = 16121 + 343 from rfl, Disp.arun_add, s5_c46, Nat.zero_add]; exact s5_s47
theorem s5_c48 : Disp.arun 16807 (7^25) 16807 0 0 1 0 1 0 = (0,1,0,833959623200883878602,1012908569057404849376) := by
  rw [show (16807:ℕ) = 16464 + 343 from rfl, Disp.arun_add, s5_c47, Nat.zero_add]; exact s5_s48
theorem final_sum_5 : (∑ k ∈ Finset.range (7^5), Disp.tt (7^5) k) % (7^25) = 1012908569057404849376 := by
  rw [Disp.aMod (7^5) (by norm_num) (by norm_num), show (((7^5)):ℕ) = 16807 from rfl, s5_c48]

/--
Conjecture 2 is FALSE: at p = 7, r = 6 the supercongruence fails
(v_7(a(7^6) - a(7^5)) = 24 < 25 = 4*6+1), so the universally quantified statement
does not hold.
-/
theorem oeis_361713_conjecture_2.disproof :
    ¬ (∀ (p r : ℕ), Nat.Prime p → p ≥ 7 → r ≥ 2 →
        a (p ^ r) ≡ a (p ^ (r - 1)) [MOD (p ^ (4 * r + 1))]) := by
  intro h
  have H := h 7 6 (by norm_num) (by norm_num) (by norm_num)
  rw [show (6 - 1 : ℕ) = 5 from rfl, show (4 * 6 + 1 : ℕ) = 25 from rfl] at H
  have H2 : a (7 ^ 6) % (7 ^ 25) = a (7 ^ 5) % (7 ^ 25) := H
  have e6 : a (7 ^ 6) = ∑ k ∈ Finset.range (7 ^ 6), Disp.tt (7 ^ 6) k := rfl
  have e5 : a (7 ^ 5) = ∑ k ∈ Finset.range (7 ^ 5), Disp.tt (7 ^ 5) k := rfl
  rw [e6, e5, final_sum_6, final_sum_5] at H2
  exact absurd H2 (by norm_num)
