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
set_option maxRecDepth 100000 in
theorem bigtest :
    (PP ((2643355483408936272 : ZMod 27000459002601004913)) 3000016 22 0).a32
      = 8138756238453341544 := by
  decide +kernel
end AGL
