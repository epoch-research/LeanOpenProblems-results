import FormalConjectures.Util.ProblemImports

open Finset Nat

namespace AGL

def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => 5 * a (n + 1) - 8 * a n

structure M3 (R : Type) : Type where
  a11 : R
  a12 : R
  a13 : R
  a21 : R
  a22 : R
  a23 : R
  a31 : R
  a32 : R
  a33 : R
deriving DecidableEq

namespace M3
variable {R : Type} [CommRing R]

def mul (P Q : M3 R) : M3 R where
  a11 := P.a11*Q.a11 + P.a12*Q.a21 + P.a13*Q.a31
  a12 := P.a11*Q.a12 + P.a12*Q.a22 + P.a13*Q.a32
  a13 := P.a11*Q.a13 + P.a12*Q.a23 + P.a13*Q.a33
  a21 := P.a21*Q.a11 + P.a22*Q.a21 + P.a23*Q.a31
  a22 := P.a21*Q.a12 + P.a22*Q.a22 + P.a23*Q.a32
  a23 := P.a21*Q.a13 + P.a22*Q.a23 + P.a23*Q.a33
  a31 := P.a31*Q.a11 + P.a32*Q.a21 + P.a33*Q.a31
  a32 := P.a31*Q.a12 + P.a32*Q.a22 + P.a33*Q.a32
  a33 := P.a31*Q.a13 + P.a32*Q.a23 + P.a33*Q.a33

def one : M3 R := ⟨1,0,0,0,1,0,0,0,1⟩

theorem mul_assoc' (P Q S : M3 R) : mul (mul P Q) S = mul P (mul Q S) := by
  cases P; cases Q; cases S
  simp only [mul, mk.injEq]
  and_intros <;> ring

theorem one_mul' (P : M3 R) : mul one P = P := by
  cases P
  simp only [mul, one, mk.injEq]
  and_intros <;> ring

theorem mul_one' (P : M3 R) : mul P one = P := by
  cases P
  simp only [mul, one, mk.injEq]
  and_intros <;> ring

end M3

section Generic
variable {R : Type} [CommRing R] (W : R) (L : ℕ)

def Cm (k : ℕ) : M3 R :=
  ⟨(-136) * (8*((2*k+1:ℕ):R)^3 * W), 45 * (8*((2*k+1:ℕ):R)^3 * W), 0,
   (-360) * (8*((2*k+1:ℕ):R)^3 * W), 89 * (8*((2*k+1:ℕ):R)^3 * W), 0,
   ((k:R)+1)^3, 0, ((k:R)+1)^3⟩

def Cp (k : ℕ) : M3 R := if k < L then Cm W k else M3.one

def Qs (lo : ℕ) : ℕ → M3 R
  | 0 => M3.one
  | len+1 => M3.mul (Cp W L (lo+len)) (Qs lo len)

def PP : ℕ → ℕ → M3 R
  | 0, lo => Cp W L lo
  | d+1, lo => M3.mul (PP d (lo + 2^d)) (PP d lo)

theorem Qs_add (m : ℕ) : ∀ (len lo : ℕ),
    Qs W L lo (m+len) = M3.mul (Qs W L (lo+m) len) (Qs W L lo m)
  | 0, lo => by
      simp [Qs, M3.one_mul']
  | len+1, lo => by
      show Qs W L lo ((m+len)+1) = _
      rw [Qs, Qs_add m len lo, Qs, ← M3.mul_assoc']
      have h : lo + (m + len) = lo + m + len := by omega
      rw [h]

theorem PP_eq : ∀ (d lo : ℕ), PP W L d lo = Qs W L lo (2^d)
  | 0, lo => by
      show Cp W L lo = _
      rw [pow_zero]
      show _ = M3.mul (Cp W L (lo+0)) (Qs W L lo 0)
      rw [Nat.add_zero]
      exact (M3.mul_one' _).symm
  | d+1, lo => by
      rw [PP, PP_eq d, PP_eq d,
        show (2:ℕ)^(d+1) = 2^d + 2^d by rw [pow_succ]; omega, Qs_add]

theorem Qs_pad : ∀ (len lo : ℕ), L ≤ lo → Qs W L lo len = M3.one
  | 0, _, _ => rfl
  | len+1, lo, h => by
      rw [Qs, Qs_pad len lo h, Cp, if_neg (by omega), M3.mul_one']

def f (k : ℕ) : R := ((a (4*k) : ℤ) : R) * ((Nat.choose (2*k) k : ℕ) : R)^3 * W^k

theorem a_step (m : ℕ) : a (m+4) = -136 * a m + 45 * a (m+1) := by
  show a (m+2+2) = _
  rw [a]
  show (5:ℤ) * a (m+1+2) - 8 * a (m+2) = _
  rw [a, a]
  ring

theorem a_step' (m : ℕ) : a (m+5) = -360 * a m + 89 * a (m+1) := by
  have h1 : a (m+1+4) = -136 * a (m+1) + 45 * a (m+1+1) := a_step (m+1)
  have h2 : a (m+2) = 5 * a (m+1) - 8 * a m := by rw [a]
  have h3 : m+1+4 = m+5 := by omega
  have h4 : m+1+1 = m+2 := by omega
  rw [h3, h4] at h1
  rw [h1, h2]
  ring

theorem cb_step (N : ℕ) :
    (N+1)^3 * (Nat.choose (2*(N+1)) (N+1))^3
      = 8*(2*N+1)^3 * (Nat.choose (2*N) N)^3 := by
  have h := Nat.succ_mul_centralBinom_succ N
  rw [Nat.centralBinom, Nat.centralBinom] at h
  calc (N+1)^3 * (Nat.choose (2*(N+1)) (N+1))^3
      = ((N+1) * Nat.choose (2*(N+1)) (N+1))^3 := by ring
    _ = (2*(2*N+1) * Nat.choose (2*N) N)^3 := by rw [h]
    _ = 8*(2*N+1)^3 * (Nat.choose (2*N) N)^3 := by ring

theorem main_ind : ∀ N : ℕ, N ≤ L →
    ((Qs W L 0 N).a12
        = ((N.factorial : ℕ) : R)^3 * ((a (4*N) : ℤ) : R)
            * ((Nat.choose (2*N) N : ℕ) : R)^3 * W^N)
    ∧ ((Qs W L 0 N).a22
        = ((N.factorial : ℕ) : R)^3 * ((a (4*N+1) : ℤ) : R)
            * ((Nat.choose (2*N) N : ℕ) : R)^3 * W^N)
    ∧ ((Qs W L 0 N).a32
        = ((N.factorial : ℕ) : R)^3 * (∑ k ∈ Finset.range N, f W k))
  | 0, _ => by
      refine ⟨?_, ?_, ?_⟩ <;> simp [Qs, M3.one, a, f]
  | N+1, hN => by
      obtain ⟨ih1, ih2, ih3⟩ := main_ind N (by omega)
      have hCp : Cp W L (0+N) = Cm W N := by
        rw [Cp, if_pos (by omega), Nat.zero_add]
      have hK1 : ((N:R)+1)^3 * ((Nat.choose (2*(N+1)) (N+1) : ℕ) : R)^3
          = 8*(2*(N:R)+1)^3 * ((Nat.choose (2*N) N : ℕ) : R)^3 := by
        have h := congrArg (Nat.cast : ℕ → R) (cb_step N)
        push_cast at h
        linear_combination h
      have hK2 : ((a (4*(N+1)) : ℤ) : R)
          = -136 * ((a (4*N):ℤ):R) + 45 * ((a (4*N+1):ℤ):R) := by
        have h : a (4*N+4) = -136 * a (4*N) + 45 * a (4*N+1) := a_step (4*N)
        have h4 : 4*(N+1) = 4*N+4 := by ring
        rw [h4]
        exact_mod_cast congrArg (Int.cast : ℤ → R) h
      have hK3 : ((a (4*(N+1)+1) : ℤ) : R)
          = -360 * ((a (4*N):ℤ):R) + 89 * ((a (4*N+1):ℤ):R) := by
        have h : a (4*N+5) = -360 * a (4*N) + 89 * a (4*N+1) := a_step' (4*N)
        have h4 : 4*(N+1)+1 = 4*N+5 := by ring
        rw [h4]
        exact_mod_cast congrArg (Int.cast : ℤ → R) h
      have hQ : Qs W L 0 (N+1) = M3.mul (Cm W N) (Qs W L 0 N) := by
        rw [Qs, hCp]
      have hFa : (((N+1).factorial : ℕ) : R) = ((N:R)+1) * ((N.factorial : ℕ) : R) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      refine ⟨?_, ?_, ?_⟩
      · rw [hQ]
        show (Cm W N).a11 * (Qs W L 0 N).a12 + (Cm W N).a12 * (Qs W L 0 N).a22
            + (Cm W N).a13 * (Qs W L 0 N).a32 = _
        rw [ih1, ih2, ih3, hK2, hFa]
        simp only [Cm]
        push_cast
        linear_combination (-(((N.factorial:ℕ):R)^3 * W^(N+1)
          * (-136*((a (4*N):ℤ):R)+45*((a (4*N+1):ℤ):R)))) * hK1
      · rw [hQ]
        show (Cm W N).a21 * (Qs W L 0 N).a12 + (Cm W N).a22 * (Qs W L 0 N).a22
            + (Cm W N).a23 * (Qs W L 0 N).a32 = _
        rw [ih1, ih2, ih3, hK3, hFa]
        simp only [Cm]
        push_cast
        linear_combination (-(((N.factorial:ℕ):R)^3 * W^(N+1)
          * (-360*((a (4*N):ℤ):R)+89*((a (4*N+1):ℤ):R)))) * hK1
      · rw [hQ]
        show (Cm W N).a31 * (Qs W L 0 N).a12 + (Cm W N).a32 * (Qs W L 0 N).a22
            + (Cm W N).a33 * (Qs W L 0 N).a32 = _
        rw [ih1, ih2, ih3, Finset.sum_range_succ, hFa]
        simp only [Cm, f]
        push_cast
        ring

theorem key (p n D : ℕ) (W : ZMod n)
    (hp1 : 1 ≤ p)
    (hpn : ((p : ℕ) : ZMod n)^3 = 0)
    (hpd : p ∣ Nat.choose (2*(p-1)) (p-1))
    (hD : p - 1 ≤ 2^D)
    (hW : ((-4096:ℤ) : ZMod n) * W = 1)
    (hne : (PP W (p-1) D 0).a32 ≠ 0) :
    (∑ k ∈ Finset.range p, ((a (4*k) : ℤ) : ZMod n) * ((Nat.choose (2*k) k : ℕ) : ZMod n)^3
        * ((((-4096:ℤ)) : ZMod n)^k)⁻¹) ≠ 0 := by
  intro h0
  apply hne
  have hWk : ∀ k : ℕ, ((((-4096:ℤ)) : ZMod n)^k)⁻¹ = W^k := by
    intro k
    have h1 : ((-4096:ℤ) : ZMod n)^k * W^k = 1 := by
      rw [← mul_pow, hW, one_pow]
    have hu : IsUnit (((-4096:ℤ) : ZMod n)^k) := ⟨Units.mkOfMulEqOne _ _ h1, rfl⟩
    calc (((-4096:ℤ) : ZMod n)^k)⁻¹
        = (((-4096:ℤ) : ZMod n)^k)⁻¹ * (((-4096:ℤ) : ZMod n)^k * W^k) := by
          rw [h1, mul_one]
      _ = ((((-4096:ℤ)) : ZMod n)^k)⁻¹ * ((((-4096:ℤ)) : ZMod n)^k) * W^k := by
          ring
      _ = W^k := by rw [ZMod.inv_mul_of_unit _ hu, one_mul]
  have hsum : (∑ k ∈ Finset.range p, ((a (4*k) : ℤ) : ZMod n)
      * ((Nat.choose (2*k) k : ℕ) : ZMod n)^3 * ((((-4096:ℤ)) : ZMod n)^k)⁻¹)
      = ∑ k ∈ Finset.range p, f W k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hWk k, f]
  obtain ⟨q, hq⟩ := hpd
  have hlast : f W (p-1) = 0 := by
    rw [f, hq]
    push_cast
    linear_combination (((a (4*(p-1)) : ℤ) : ZMod n) * ((q:ZMod n))^3 * W^(p-1)) * hpn
  have hs := Finset.sum_range_succ (f W) (p-1)
  rw [Nat.sub_add_cancel hp1, hlast, add_zero] at hs
  have hm := (main_ind W (p-1) (p-1) le_rfl).2.2
  have hPP : PP W (p-1) D 0 = Qs W (p-1) 0 (p-1) := by
    rw [PP_eq]
    rw [show 2^D = (p-1) + (2^D - (p-1)) by omega]
    rw [Qs_add]
    rw [Qs_pad W (p-1) (2^D-(p-1)) (0+(p-1)) (by omega), M3.one_mul']
  rw [hPP, hm]
  rw [hsum] at h0
  rw [hs] at h0
  rw [h0, mul_zero]

end Generic

section NatSide

def oneN : M3 ℕ := ⟨1,0,0,0,1,0,0,0,1⟩

def mulN (Mo : ℕ) (P Q : M3 ℕ) : M3 ℕ where
  a11 := (P.a11*Q.a11 + P.a12*Q.a21 + P.a13*Q.a31) % Mo
  a12 := (P.a11*Q.a12 + P.a12*Q.a22 + P.a13*Q.a32) % Mo
  a13 := (P.a11*Q.a13 + P.a12*Q.a23 + P.a13*Q.a33) % Mo
  a21 := (P.a21*Q.a11 + P.a22*Q.a21 + P.a23*Q.a31) % Mo
  a22 := (P.a21*Q.a12 + P.a22*Q.a22 + P.a23*Q.a32) % Mo
  a23 := (P.a21*Q.a13 + P.a22*Q.a23 + P.a23*Q.a33) % Mo
  a31 := (P.a31*Q.a11 + P.a32*Q.a21 + P.a33*Q.a31) % Mo
  a32 := (P.a31*Q.a12 + P.a32*Q.a22 + P.a33*Q.a32) % Mo
  a33 := (P.a31*Q.a13 + P.a32*Q.a23 + P.a33*Q.a33) % Mo

def CmN (Mo W k : ℕ) : M3 ℕ :=
  ⟨(Mo-136) * (8*(2*k+1)^3 % Mo * W % Mo) % Mo, 45 * (8*(2*k+1)^3 % Mo * W % Mo) % Mo, 0,
   (Mo-360) * (8*(2*k+1)^3 % Mo * W % Mo) % Mo, 89 * (8*(2*k+1)^3 % Mo * W % Mo) % Mo, 0,
   (k+1)^3 % Mo, 0, (k+1)^3 % Mo⟩

def CpN (Mo W L k : ℕ) : M3 ℕ := if k < L then CmN Mo W k else oneN

def PPN (Mo W L : ℕ) : ℕ → ℕ → M3 ℕ
  | 0, lo => CpN Mo W L lo
  | d+1, lo => mulN Mo (PPN Mo W L d (lo + 2^d)) (PPN Mo W L d lo)

def castM3 (n : ℕ) (P : M3 ℕ) : M3 (ZMod n) :=
  ⟨P.a11, P.a12, P.a13, P.a21, P.a22, P.a23, P.a31, P.a32, P.a33⟩

theorem castM3_mulN (n : ℕ) (P Q : M3 ℕ) :
    castM3 n (mulN n P Q) = M3.mul (castM3 n P) (castM3 n Q) := by
  cases P; cases Q
  simp only [mulN, M3.mul, castM3, M3.mk.injEq]
  and_intros <;> · push_cast [ZMod.natCast_mod]; ring

theorem castM3_oneN (n : ℕ) : castM3 n oneN = M3.one := by
  simp only [oneN, M3.one, castM3]
  norm_num

theorem castM3_CmN (n W k : ℕ) (hn : 360 ≤ n) :
    castM3 n (CmN n W k) = Cm ((W : ZMod n)) k := by
  have h136 : ((n - 136 : ℕ) : ZMod n) = -136 := by
    have : ((n - 136 : ℕ) : ZMod n) = ((n : ℕ) : ZMod n) - ((136:ℕ) : ZMod n) :=
      Nat.cast_sub (by omega)
    rw [this, ZMod.natCast_self]
    push_cast
    ring
  have h360 : ((n - 360 : ℕ) : ZMod n) = -360 := by
    have : ((n - 360 : ℕ) : ZMod n) = ((n : ℕ) : ZMod n) - ((360:ℕ) : ZMod n) :=
      Nat.cast_sub (by omega)
    rw [this, ZMod.natCast_self]
    push_cast
    ring
  simp only [CmN, Cm, castM3, M3.mk.injEq]
  and_intros <;> · push_cast [ZMod.natCast_mod, h136, h360]; ring

theorem castM3_CpN (n W L k : ℕ) (hn : 360 ≤ n) :
    castM3 n (CpN n W L k) = Cp ((W : ZMod n)) L k := by
  rw [CpN, Cp]
  by_cases h : k < L
  · rw [if_pos h, if_pos h, castM3_CmN n W k hn]
  · rw [if_neg h, if_neg h, castM3_oneN]

theorem castM3_PPN (n W L : ℕ) (hn : 360 ≤ n) :
    ∀ (d lo : ℕ), castM3 n (PPN n W L d lo) = PP ((W : ZMod n)) L d lo
  | 0, lo => by
      rw [PPN, PP]
      exact castM3_CpN n W L lo hn
  | d+1, lo => by
      rw [PPN, PP, castM3_mulN, castM3_PPN n W L hn d, castM3_PPN n W L hn d]

end NatSide


theorem test13a : (PP (376 : ZMod 2197) 12 4 0).a32 = 169 := by decide

theorem test13 :
    (∑ k ∈ Finset.range 13, ((a (4*k) : ℤ) : ZMod 2197)
        * ((Nat.choose (2*k) k : ℕ) : ZMod 2197)^3
        * ((((-4096:ℤ)) : ZMod 2197)^k)⁻¹) ≠ 0 := by
  have hpd : (13:ℕ) ∣ Nat.choose (2*(13-1)) (13-1) := by
    have h := Nat.Prime.dvd_choose_add (p:=13) (a:=12) (b:=12)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  exact key 13 2197 4 (376 : ZMod 2197) (by norm_num) (by decide) hpd
    (by norm_num) (by decide) (by decide)

end AGL


namespace AGL

set_option maxRecDepth 8192 in
theorem cc0 : PPN 27000459002601004913 2643355483408936272 3000016 12 0 = (⟨21009730171552250749,22489929932456631997,0,9083773558553978415,25457543823431391082,0,8316872478289469520,26309072986037441318,17593732464400516330⟩ : M3 ℕ) := by decide +kernel

set_option maxRecDepth 8192 in
theorem cc1 : PPN 27000459002601004913 2643355483408936272 3000016 12 4096 = (⟨25740929427402534983,14688174090076393918,0,17496902292393873221,18180422869981489834,0,5650786547524115101,25836772322292467790,24432812578900434036⟩ : M3 ℕ) := by decide +kernel

set_option maxRecDepth 8192 in
theorem cc2 : PPN 27000459002601004913 2643355483408936272 3000016 12 8192 = (⟨8292698906672394739,3889642461170786305,0,22883778315835719386,740452209925321351,0,10745946863883985659,3807911255455052568,24083745302998585605⟩ : M3 ℕ) := by decide +kernel

set_option maxRecDepth 8192 in
theorem cc3 : PPN 27000459002601004913 2643355483408936272 3000016 12 12288 = (⟨8204927588501489554,20360866789995698203,0,26116278698241448767,2007425528075960917,0,26763401332859081913,16288119986290991607,502869639650782869⟩ : M3 ℕ) := by decide +kernel

set_option maxRecDepth 8192 in
theorem cc4 : PPN 27000459002601004913 2643355483408936272 3000016 12 16384 = (⟨11554153308333994278,1620209582466112942,0,14038782342872101377,19655201220664558988,0,2493521180525328107,6701426927350414310,13317283750681513550⟩ : M3 ℕ) := by decide +kernel

set_option maxRecDepth 8192 in
theorem cc5 : PPN 27000459002601004913 2643355483408936272 3000016 12 20480 = (⟨18848630519791217162,2188401784261904069,0,9493244728505772361,2790180438499732594,0,25106737644467793897,17499370758490443889,11639164902863541392⟩ : M3 ℕ) := by decide +kernel

set_option maxRecDepth 8192 in
theorem cc6 : PPN 27000459002601004913 2643355483408936272 3000016 12 24576 = (⟨10194812038333046740,16385245487528324029,0,3920331112778432333,11119662468171652146,0,9468835670304690036,5074643848680582934,16283458107789274896⟩ : M3 ℕ) := by decide +kernel

set_option maxRecDepth 8192 in
theorem cc7 : PPN 27000459002601004913 2643355483408936272 3000016 12 28672 = (⟨1426460595460185705,720700362073814259,0,21234856106010490841,5029962405829257000,0,7477584205569037821,13139812090265789323,3505619088428213728⟩ : M3 ℕ) := by decide +kernel

set_option maxRecDepth 8192 in
theorem cc8 : PPN 27000459002601004913 2643355483408936272 3000016 12 32768 = (⟨25037575346806157638,19966427947739961719,0,2271330433686335726,16867879075101946581,0,19549541499896743924,2412466170685528879,12436434316729114679⟩ : M3 ℕ) := by decide +kernel

set_option maxRecDepth 8192 in
theorem cc9 : PPN 27000459002601004913 2643355483408936272 3000016 12 36864 = (⟨6506674109727062684,11716199999898449382,0,14272236011216424596,11086756104017299768,0,18119875753821411811,4407958017389027822,15018372403474863224⟩ : M3 ℕ) := by decide +kernel

set_option maxRecDepth 8192 in
theorem cc10 : PPN 27000459002601004913 2643355483408936272 3000016 12 40960 = (⟨16269939227262209899,14495240577738992921,0,19040370391093081197,7744765108154159765,0,21115372719491312239,13970647241874191205,6606203001852591321⟩ : M3 ℕ) := by decide +kernel

set_option maxRecDepth 8192 in
theorem cc11 : PPN 27000459002601004913 2643355483408936272 3000016 12 45056 = (⟨24659320715403239863,23849199131308850006,0,25210078970337239256,8903021358942465328,0,5936887969987563672,21068414018395538720,21959859231854569546⟩ : M3 ℕ) := by decide +kernel

set_option maxRecDepth 8192 in
theorem cc12 : PPN 27000459002601004913 2643355483408936272 3000016 12 49152 = (⟨11408827502469903531,22734506686267357038,0,7127159528068178087,17079524923402669069,0,3218378078392837151,13893390529545740580,3349524729263645344⟩ : M3 ℕ) := by decide +kernel

set_option maxRecDepth 8192 in
theorem cc13 : PPN 27000459002601004913 2643355483408936272 3000016 12 53248 = (⟨1762371426241045747,6722022186172288127,0,224740515823704810,8372023354501481469,0,5145468480385093863,21920803390595470443,11241279954104721165⟩ : M3 ℕ) := by decide +kernel

set_option maxRecDepth 8192 in
theorem cc14 : PPN 27000459002601004913 2643355483408936272 3000016 12 57344 = (⟨2005570936626942721,7897295864771150243,0,17823010089633812795,14491591257881689023,0,12573059656372370878,15719981251972177209,26853479971708803465⟩ : M3 ℕ) := by decide +kernel

set_option maxRecDepth 8192 in
theorem cc15 : PPN 27000459002601004913 2643355483408936272 3000016 12 61440 = (⟨23345127875279481748,10878922744130465527,0,20970454057360295436,23738823590729799557,0,16612140823275050376,23372806768738596331,5842393360178024624⟩ : M3 ℕ) := by decide +kernel

end AGL
