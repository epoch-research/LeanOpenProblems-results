import Submission.Positive
import Submission.PairShift
open Nat Finset BigOperators Int Polynomial
open Core

noncomputable def linear : Polynomial ℤ := 1+Polynomial.X

lemma frobError_dvd_linear {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    linear ∣ Core.frobError p := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have he := congr_arg (fun f : Polynomial ℤ => f.eval (-1))
    (Core.frob_decomposition hp)
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C] at he
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hev : (Core.frobError p).eval (-1)=0 := by
    have hpow : (-1 : ℤ)^p = -1 := by
      obtain ⟨t,rfl⟩ := hodd
      simp [pow_succ,pow_mul]
    rw [hpow] at he
    norm_num [hp.ne_zero] at he
    exact he
  rw [show linear = Polynomial.X - Polynomial.C (-1) by
    ext n
    simp [linear,Polynomial.coeff_X]
    ring]
  exact (Polynomial.dvd_iff_isRoot).mpr hev

noncomputable def rQuot (p : ℕ) : Polynomial ℤ :=
  Core.frobError p /ₘ linear

lemma frobError_eq_linear_mul {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Core.frobError p = linear * rQuot p := by
  have hm : linear.Monic := by dsimp [linear]; monicity <;> norm_num
  calc
    Core.frobError p = Core.frobError p %ₘ linear +
        linear * (Core.frobError p /ₘ linear) :=
      (Polynomial.modByMonic_add_div (Core.frobError p) hm).symm
    _ = linear*rQuot p := by
      rw [(Polynomial.modByMonic_eq_zero_iff_dvd hm).mpr
        (frobError_dvd_linear hp hp5), zero_add]
      rfl

lemma natDegree_linear : linear.natDegree=1 := by
  dsimp [linear]
  compute_degree <;> norm_num

lemma natDegree_rQuot_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (rQuot p).natDegree ≤ p-2 := by
  have heq := frobError_eq_linear_mul hp hp5
  have hq0 : rQuot p ≠ 0 := by
    intro h
    rw [h,mul_zero] at heq
    have hc := congr_arg (fun f : Polynomial ℤ => f.coeff 1) heq
    change (Core.frobError p).coeff 1 = (0 : Polynomial ℤ).coeff 1 at hc
    rw [Core.coeff_frobError] at hc
    norm_num [hp.one_lt,hp.ne_zero] at hc
  have hl0 : linear ≠ 0 := by
    have hm : linear.Monic := by dsimp [linear]; monicity <;> norm_num
    exact hm.ne_zero
  have hd := Polynomial.natDegree_mul hl0 hq0
  rw [_root_.natDegree_linear] at hd
  have hle := Core.natDegree_frobError_le p
  rw [heq,hd] at hle
  omega

lemma reflect_linear : Polynomial.reflect 1 linear = linear := by
  ext n
  rw [Polynomial.coeff_reflect]
  by_cases hn : n≤1
  · rw [Polynomial.revAt_le hn]
    interval_cases n <;> norm_num [linear,Polynomial.coeff_X,Polynomial.coeff_one]
  · rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hn)]

lemma reflect_rQuot {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Polynomial.reflect (p-1) (rQuot p) = rQuot p := by
  have heq := frobError_eq_linear_mul hp hp5
  have hdL : linear.natDegree≤1 := natDegree_linear.le
  have hdQ : (rQuot p).natDegree≤p-1 := (natDegree_rQuot_le hp hp5).trans (by omega)
  have hm := Polynomial.reflect_mul linear (rQuot p) hdL hdQ
  have hi : 1+(p-1)=p := by omega
  rw [hi,←heq,Core.reflect_frobError,reflect_linear] at hm
  apply mul_left_cancel₀ (show linear≠0 by
    have hmon : linear.Monic := by dsimp [linear]; monicity <;> norm_num
    exact hmon.ne_zero)
  calc
    linear*Polynomial.reflect (p-1) (rQuot p) = Core.frobError p := hm.symm
    _ = linear*rQuot p := heq

noncomputable def rCoeff (n : ℕ) : ℤ :=
  if n=0 then 1 else 2*((-1 : ℤ)^n)

noncomputable def Rseries : PowerSeries ℤ := PowerSeries.mk rCoeff

lemma rCoeff_mul_prime {p n : ℕ} (hp : p.Prime) (hp5 : 5≤p) :
    rCoeff (p*n)=rCoeff n := by
  by_cases hn : n=0
  · subst n; simp [rCoeff]
  have hp0 := hp.ne_zero
  simp only [rCoeff,mul_eq_zero,hp0,hn,or_self,if_false]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  rw [pow_mul]
  have hpneg : (-1 : ℤ)^p=-1 := by
    obtain ⟨t,rfl⟩ := hodd
    simp [pow_succ,pow_mul]
  rw [hpneg]

lemma linear_mul_Rseries :
    (linear : PowerSeries ℤ)*Rseries = 1-PowerSeries.X := by
  ext n
  rw [show (linear : PowerSeries ℤ)=1+PowerSeries.X by simp [linear]]
  rw [add_mul,map_add]
  simp only [one_mul,Rseries,PowerSeries.coeff_mk]
  rw [show PowerSeries.X*PowerSeries.mk rCoeff =
      PowerSeries.X^1*PowerSeries.mk rCoeff by simp,
    PowerSeries.coeff_X_pow_mul']
  by_cases hn0 : n=0
  · subst n; simp [rCoeff]
  have hn1 : 1≤n := by omega
  rw [if_pos hn1]
  simp only [map_sub,map_one,PowerSeries.coeff_X]
  by_cases hn1eq : n=1
  · subst n; norm_num [rCoeff]
  have hpred : n=(n-1)+1 := by omega
  rw [PowerSeries.coeff_mk]

  rw [show rCoeff n + rCoeff (n-1)=0 by
    simp only [rCoeff,hn0,if_false]
    have hp0 : n-1≠0 := by omega
    rw [if_neg hp0]
    have hs : (-1 : ℤ)^n = -((-1 : ℤ)^(n-1)) := by
      conv_lhs => rw [hpred,pow_succ]
      ring
    rw [hs]
    ring]
  simp [hn0,hn1eq]

noncomputable def rErrorPoly (p j : ℕ) : Polynomial ℤ :=
  if j=0 then 0 else
    (1-Polynomial.X)*linear^(j-1)*rQuot p^j

lemma Rseries_mul_frobError_pow {p j : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    (hj : 0<j) :
    Rseries*(Core.frobError p : PowerSeries ℤ)^j =
      (rErrorPoly p j : PowerSeries ℤ) := by
  rw [frobError_eq_linear_mul hp hp5,Polynomial.coe_mul]
  rw [rErrorPoly,if_neg (Nat.ne_of_gt hj),Polynomial.coe_mul,Polynomial.coe_mul]
  simp only [Polynomial.coe_pow,Polynomial.coe_sub,Polynomial.coe_one,Polynomial.coe_X]
  have hj_eq : j=(j-1)+1 := by omega
  conv_lhs => enter [2]; rw [hj_eq,pow_succ]
  have h := linear_mul_Rseries
  change (linear : PowerSeries ℤ)*Rseries=1-PowerSeries.X at h
  rw [←h]
  have hq : (rQuot p : PowerSeries ℤ)^j =
      (rQuot p : PowerSeries ℤ)^(j-1)*(rQuot p : PowerSeries ℤ) := by
    conv_lhs => rw [hj_eq,pow_succ]
  rw [hq]
  ring


lemma reflect_pow_local {f : Polynomial ℤ} {D : ℕ} (hdeg : f.natDegree≤D)
    (href : Polynomial.reflect D f=f) (j : ℕ) :
    Polynomial.reflect (D*j) (f^j)=f^j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ,Nat.mul_succ,Polynomial.reflect_mul (f^j) f]
      · rw [ih,href]
      · simpa [Nat.mul_comm] using
          Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left j hdeg)
      · exact hdeg

lemma reflect_one_sub_X :
    Polynomial.reflect 1 (1-Polynomial.X : Polynomial ℤ) = -(1-Polynomial.X) := by
  ext n
  rw [Polynomial.coeff_reflect]
  by_cases hn : n≤1
  · rw [Polynomial.revAt_le hn]
    interval_cases n <;> norm_num [Polynomial.coeff_X,Polynomial.coeff_one]
  · rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hn)]
    simp only [Polynomial.coeff_neg, Polynomial.coeff_sub,
      Polynomial.coeff_X, Polynomial.coeff_one]
    simp [show 1 ≠ n by omega, show n ≠ 0 by omega]

lemma reflect_rErrorPoly {p j : ℕ} (hp : p.Prime) (hp5 : 5≤p) (hj : 0<j) :
    Polynomial.reflect (p*j) (rErrorPoly p j) = -rErrorPoly p j := by
  rw [rErrorPoly,if_neg (Nat.ne_of_gt hj)]
  have hdL : linear.natDegree≤1 := natDegree_linear.le
  have hdQ : (rQuot p).natDegree≤p-1 := (natDegree_rQuot_le hp hp5).trans (by omega)
  have hLp := reflect_pow_local hdL reflect_linear (j-1)
  have hQp := reflect_pow_local hdQ (reflect_rQuot hp hp5) j
  have hdA : (1-Polynomial.X : Polynomial ℤ).natDegree≤1 := by compute_degree <;> norm_num
  have hdB : (linear^(j-1)).natDegree≤1*(j-1) := by
    simpa [Nat.mul_comm] using
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left (j-1) hdL)
  have hdC : (rQuot p^j).natDegree≤(p-1)*j := by
    simpa [Nat.mul_comm] using
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left j hdQ)
  have hm1 := Polynomial.reflect_mul (1-Polynomial.X : Polynomial ℤ)
    (linear^(j-1)) hdA hdB
  have hm2 := Polynomial.reflect_mul
    ((1-Polynomial.X : Polynomial ℤ)*linear^(j-1)) (rQuot p^j)
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hdA hdB)) hdC
  have hi : 1+1*(j-1)+(p-1)*j=p*j := by
    simp only [one_mul]
    calc
      1 + (j-1) + (p-1)*j = j + (p-1)*j := by
        rw [show 1 + (j-1) = j by omega]
      _ = (1+(p-1))*j := by rw [Nat.add_mul, one_mul]
      _ = p*j := by rw [show 1+(p-1)=p by omega]
  rw [hi] at hm2
  rw [hm1,reflect_one_sub_X,hLp,hQp] at hm2
  convert hm2 using 1 <;> ring

lemma rError_coeff_antisymm {p j d : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    (hj : 0<j) (hd : d≤j) :
    (rErrorPoly p j).coeff (p*(j-d)) = -(rErrorPoly p j).coeff (p*d) := by
  have h := congr_arg (fun f : Polynomial ℤ => f.coeff (p*d))
    (reflect_rErrorPoly hp hp5 hj)
  change (Polynomial.reflect (p*j) (rErrorPoly p j)).coeff (p*d) =
    (-rErrorPoly p j).coeff (p*d) at h
  rw [Polynomial.coeff_reflect,Polynomial.revAt_le (Nat.mul_le_mul_left p hd),
    Polynomial.coeff_neg] at h
  rw [Nat.mul_sub_left_distrib]
  exact h

lemma rError_coeff_zero {p j : ℕ} (hp : p.Prime) (hp5 : 5≤p) (hj : 0<j) :
    (rErrorPoly p j).coeff 0=0 := by
  have h := congr_arg (PowerSeries.coeff 0) (Rseries_mul_frobError_pow hp hp5 hj)
  simp only [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_one,Rseries,PowerSeries.coeff_mk,Polynomial.coeff_coe] at h
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,map_pow,
    ←PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  simp [rCoeff,Polynomial.coeff_coe,Core.coeff_frobError,hj.ne'] at h
  exact h.symm

lemma rError_coeff_above {p j d : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    (hj : 0<j) (hd : j<d) : (rErrorPoly p j).coeff (p*d)=0 := by
  have h := congr_arg (fun f : Polynomial ℤ => f.coeff (p*d))
    (reflect_rErrorPoly hp hp5 hj)
  change (Polynomial.reflect (p*j) (rErrorPoly p j)).coeff (p*d) =
    (-rErrorPoly p j).coeff (p*d) at h
  rw [Polynomial.coeff_reflect,Polynomial.revAt_eq_self_of_lt
      (Nat.mul_lt_mul_of_pos_left hd hp.pos),Polynomial.coeff_neg] at h
  omega

lemma contracted_rError_coeff_sum {p j A B : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    (hj : 0<j) :
    (rErrorPoly p j*(1+Polynomial.X^p)^(A-j)).coeff (p*B) =
      ∑ d ∈ Finset.range (j+1), (rErrorPoly p j).coeff (p*d)*
        (chooseSub (A-j) B d : ℤ) := by
  rw [base_eq_expand]
  have hc := Polynomial.contract_mul_expand hp.ne_zero (rErrorPoly p j)
    ((1+Polynomial.X : Polynomial ℤ)^(A-j))
  have heq := congr_arg (fun f : Polynomial ℤ => f.coeff B) hc
  change (Polynomial.contract p
      (rErrorPoly p j*Polynomial.expand ℤ p ((1+Polynomial.X)^(A-j)))).coeff B =
    (Polynomial.contract p (rErrorPoly p j)*(1+Polynomial.X)^(A-j)).coeff B at heq
  rw [Polynomial.coeff_contract hp.ne_zero,coeff_mul_one_add_pow] at heq
  rw [Nat.mul_comm] at heq
  rw [heq]
  have hs := sum_chooseSub_eq (N:=A-j) (B:=B) (j:=j)
    (f:=fun d => (Polynomial.contract p (rErrorPoly p j)).coeff d) (by
      intro d hd
      change (Polynomial.contract p (rErrorPoly p j)).coeff d=0
      rw [Polynomial.coeff_contract hp.ne_zero]
      simpa [Nat.mul_comm] using rError_coeff_above hp hp5 hj hd)
  simpa only [Polynomial.coeff_contract hp.ne_zero,Nat.mul_comm] using hs

noncomputable def RNat (A B : ℕ) : ℤ :=
  PowerSeries.coeff B
    (Rseries*(((1+Polynomial.X : Polynomial ℤ)^A : Polynomial ℤ) : PowerSeries ℤ))

lemma RNat_base_scale {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) (A B : ℕ) :
    PowerSeries.coeff (p*B)
      (Rseries*(((1+Polynomial.X^p : Polynomial ℤ)^A : Polynomial ℤ) : PowerSeries ℤ)) =
      RNat A B := by
  rw [base_eq_expand,Nat.mul_comm p B]
  change PowerSeries.coeff (B*p)
    (PowerSeries.mk rCoeff*(Polynomial.expand ℤ p
      ((1+Polynomial.X : Polynomial ℤ)^A) : PowerSeries ℤ))=_
  rw [coeff_series_mul_expand rCoeff hp.pos]
  · rfl
  · intro t
    simpa [Nat.mul_comm] using rCoeff_mul_prime (hp:=hp) (hp5:=hp5) (n:=t)

lemma rCorrection_coeff_eq {p A B j : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    (hj : 0<j) :
    PowerSeries.coeff (p*B)
      (Rseries*((Polynomial.C ((p:ℤ)^j*(A.choose j:ℤ))*Core.frobError p^j*
        (1+Polynomial.X^p : Polynomial ℤ)^(A-j) : Polynomial ℤ) : PowerSeries ℤ)) =
      ∑ d ∈ Finset.range (j+1), (p:ℤ)^j*(rErrorPoly p j).coeff (p*d)*
        (A.choose j:ℤ)*(chooseSub (A-j) B d:ℤ) := by
  have herr := Rseries_mul_frobError_pow hp hp5 hj
  have hs : Rseries*((Polynomial.C ((p:ℤ)^j*(A.choose j:ℤ))*Core.frobError p^j*
        (1+Polynomial.X^p : Polynomial ℤ)^(A-j) : Polynomial ℤ) : PowerSeries ℤ) =
      PowerSeries.C ((p:ℤ)^j*(A.choose j:ℤ))*
        ((rErrorPoly p j*(1+Polynomial.X^p)^(A-j) : Polynomial ℤ) : PowerSeries ℤ) := by
    simp only [Polynomial.coe_mul,Polynomial.coe_pow,Polynomial.coe_C]
    calc
      Rseries*(PowerSeries.C ((p:ℤ)^j*(A.choose j:ℤ))*
          (Core.frobError p : PowerSeries ℤ)^j*
          ((1+Polynomial.X^p : Polynomial ℤ) : PowerSeries ℤ)^(A-j)) =
        PowerSeries.C ((p:ℤ)^j*(A.choose j:ℤ))*
          (Rseries*(Core.frobError p : PowerSeries ℤ)^j)*
          ((1+Polynomial.X^p : Polynomial ℤ) : PowerSeries ℤ)^(A-j) := by ring
      _ = PowerSeries.C ((p:ℤ)^j*(A.choose j:ℤ))*(rErrorPoly p j : PowerSeries ℤ)*
          ((1+Polynomial.X^p : Polynomial ℤ) : PowerSeries ℤ)^(A-j) := by rw [herr]
      _ = _ := by ring
  rw [hs,PowerSeries.coeff_C_mul,Polynomial.coeff_coe,
    contracted_rError_coeff_sum hp hp5 hj,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

lemma rCorrection_coeff_dvd_total {p L B Y j : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    (hprod : ((p:ℤ)^L) ∣ (B:ℤ)*Y*((Y:ℤ)-B)) (hj : 0<j) (hjA : j≤B+Y) :
    ((p:ℤ)^(L+3)) ∣ PowerSeries.coeff (p*B)
      (Rseries*((Polynomial.C ((p:ℤ)^j*((B+Y).choose j:ℤ))*Core.frobError p^j*
        (1+Polynomial.X^p : Polynomial ℤ)^((B+Y)-j) : Polynomial ℤ) : PowerSeries ℤ)) := by
  rw [rCorrection_coeff_eq hp hp5 hj]
  apply shifted_paired_sum_dvd_total hp hp5 hprod hjA
  · exact rError_coeff_zero hp hp5 hj
  · intro d hd
    exact rError_coeff_antisymm hp hp5 hj hd

lemma RNat_scale_expansion {p : ℕ} (hp : p.Prime) (hp5 : 5≤p) (A B : ℕ) :
    RNat (p*A) (p*B) = RNat A B +
      ∑ i ∈ Finset.range A,
        PowerSeries.coeff (p*B)
          (Rseries *
            ((Polynomial.C ((p:ℤ)^(i+1) * (A.choose (i+1):ℤ)) *
              Core.frobError p^(i+1) *
              (1+Polynomial.X^p : Polynomial ℤ)^(A-(i+1)) : Polynomial ℤ) :
                PowerSeries ℤ)) := by
  unfold RNat
  rw [frobenius_expansion hp]
  rw [coe_finset_sum_poly]
  rw [Finset.mul_sum, map_sum]
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, pow_zero, Int.natCast_one,
    mul_one, Polynomial.C_1, one_mul, Nat.sub_zero]
  rw [RNat_base_scale hp hp5]
  abel

lemma RNat_scale_supercongruence_total {p L B Y : ℕ}
    (hp : p.Prime) (hp5 : 5≤p)
    (hprod : ((p:ℤ)^L) ∣ (B:ℤ)*Y*((Y:ℤ)-B)) :
    RNat (p*(B+Y)) (p*B) ≡ RNat (B+Y) B [ZMOD ((p:ℤ)^(L+3))] := by
  rw [Int.modEq_iff_dvd]
  rw [RNat_scale_expansion hp hp5]
  rw [show RNat (B+Y) B -
      (RNat (B+Y) B + ∑ i ∈ Finset.range (B+Y),
        PowerSeries.coeff (p*B)
          (Rseries *
            ((Polynomial.C ((p:ℤ)^(i+1) * ((B+Y).choose (i+1):ℤ)) *
              Core.frobError p^(i+1) *
              (1+Polynomial.X^p : Polynomial ℤ)^((B+Y)-(i+1)) : Polynomial ℤ) :
                PowerSeries ℤ))) =
      -(∑ i ∈ Finset.range (B+Y),
        PowerSeries.coeff (p*B)
          (Rseries *
            ((Polynomial.C ((p:ℤ)^(i+1) * ((B+Y).choose (i+1):ℤ)) *
              Core.frobError p^(i+1) *
              (1+Polynomial.X^p : Polynomial ℤ)^((B+Y)-(i+1)) : Polynomial ℤ) :
                PowerSeries ℤ))) by ring]
  apply dvd_neg.mpr
  apply Finset.dvd_sum
  intro i hi
  have hiA : i+1≤B+Y := by
    simp only [Finset.mem_range] at hi
    omega
  exact rCorrection_coeff_dvd_total hp hp5 hprod (by omega) hiA


lemma RNat_eq_choose_sub {A B : ℕ} (hA : 0<A) (hB : 0<B) :
    RNat A B = (A-1).choose B - (A-1).choose (B-1) := by
  have hAs : A=(A-1)+1 := by omega
  have hBs : B=(B-1)+1 := by omega
  have hseries : Rseries *
      (((1+Polynomial.X : Polynomial ℤ)^A : Polynomial ℤ) : PowerSeries ℤ) =
      (((1-Polynomial.X)*linear^(A-1) : Polynomial ℤ) : PowerSeries ℤ) := by
    rw [show (1+Polynomial.X : Polynomial ℤ)=linear by rfl]
    simp only [Polynomial.coe_pow, Polynomial.coe_mul, Polynomial.coe_sub,
      Polynomial.coe_one, Polynomial.coe_X]
    change Rseries * (linear : PowerSeries ℤ)^A =
      (1-PowerSeries.X) * (linear : PowerSeries ℤ)^(A-1)
    rw [show (linear : PowerSeries ℤ)^A =
        (linear : PowerSeries ℤ)^(A-1)*linear by
      calc
        (linear : PowerSeries ℤ)^A = linear^((A-1)+1) := congrArg _ hAs
        _ = linear^(A-1)*linear := pow_succ _ _]
    have h := linear_mul_Rseries
    change (linear : PowerSeries ℤ)*Rseries=1-PowerSeries.X at h
    rw [←h]
    ring
  unfold RNat
  rw [hseries, Polynomial.coeff_coe]
  rw [show (1-Polynomial.X)*linear^(A-1) =
      linear^(A-1)-Polynomial.X*linear^(A-1) by ring,
    Polynomial.coeff_sub]
  rw [hBs, Polynomial.coeff_X_mul]
  simp only [linear, Polynomial.coeff_one_add_X_pow]
  rw [show B-1+1-1=B-1 by omega]

lemma RNat_eq_boundary_mul (S N : ℕ) (hS : 2≤S) (hN : 0<N) :
    RNat (S*N) N = ((S:ℤ)-2) * (((S*N-1).choose (N-1) : ℕ) : ℤ) := by
  have hA : 0<S*N := mul_pos (by omega) hN
  rw [RNat_eq_choose_sub hA hN]
  have hNS : N≤S*N := by
    simpa only [one_mul] using Nat.mul_le_mul_right N (show 1≤S by omega)
  have hc := Nat.choose_succ_right_eq (S*N-1) (N-1)
  have hmul : (S-1)*N=S*N-N := by
    rw [Nat.sub_mul, one_mul]
  have hsub : (S*N-1)-(N-1)=(S-1)*N := by
    rw [hmul]
    omega
  rw [show (N-1)+1=N by omega, hsub] at hc
  apply mul_left_cancel₀ (show (N:ℤ)≠0 by exact_mod_cast hN.ne')
  have hcz : (((S*N-1).choose N : ℕ):ℤ) * N =
      (((S*N-1).choose (N-1):ℕ):ℤ) * (((S:ℤ)-1)*N) := by
    have hz := congrArg (fun x : ℕ => (x:ℤ)) hc
    push_cast at hz
    rw [Nat.cast_sub (show 1≤S by omega)] at hz
    exact hz
  calc
    (N:ℤ) * (((S*N-1).choose N:ℕ) - (S*N-1).choose (N-1)) =
        (((S*N-1).choose N:ℕ):ℤ)*N -
          (((S*N-1).choose (N-1):ℕ):ℤ)*N := by push_cast; ring
    _ = (((S*N-1).choose (N-1):ℕ):ℤ) * (((S:ℤ)-1)*N) -
          (((S*N-1).choose (N-1):ℕ):ℤ)*N := by rw [hcz]
    _ = (N:ℤ) * (((S:ℤ)-2) * (((S*N-1).choose (N-1):ℕ):ℤ)) := by ring

