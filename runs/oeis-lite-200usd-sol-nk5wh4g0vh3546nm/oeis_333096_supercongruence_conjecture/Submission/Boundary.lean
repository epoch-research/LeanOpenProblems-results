import Submission.RationalR
open Nat Finset BigOperators Int Polynomial

lemma boundary_scale_gt_two {S p N lev : ℕ} (hS : 2<S)
    (hp : p.Prime) (hp5 : 5≤p) (hN : 0<N) (hdiv : p^lev ∣ N) :
    (((S*(p*N)-1).choose (p*N-1) : ℕ) : ℤ) ≡
      (((S*N-1).choose (N-1) : ℕ) : ℤ)
      [ZMOD ((p:ℤ)^(3*(lev+1)))] := by
  let q := padicValNat p (S-2)
  let c : ℤ := (S:ℤ)-2
  let BH : ℤ := ((S*(p*N)-1).choose (p*N-1) : ℕ)
  let BL : ℤ := ((S*N-1).choose (N-1) : ℕ)
  letI : Fact p.Prime := ⟨hp⟩
  have hc0 : c≠0 := by dsimp [c]; omega
  have hqnat : p^q ∣ S-2 := by
    dsimp [q]
    exact pow_padicValNat_dvd
  have hprod : ((p:ℤ)^(3*lev+q)) ∣
      (N:ℤ)*(((S-1)*N:ℕ):ℤ)*((((S-1)*N:ℕ):ℤ)-N) := by
    obtain ⟨u,hu⟩ := hdiv
    obtain ⟨v,hv⟩ := hqnat
    use (u:ℤ)^3 * (S-1) * v
    have hpcast : ((p^lev:ℕ):ℤ)=(p:ℤ)^lev := by push_cast; rfl
    have hpcq : ((p^q:ℕ):ℤ)=(p:ℤ)^q := by push_cast; rfl
    have hNcast : (N:ℤ)=(p:ℤ)^lev*(u:ℤ) := by
      exact_mod_cast hu
    have hScast : ((S-2:ℕ):ℤ)=(p:ℤ)^q*(v:ℤ) := by
      exact_mod_cast hv
    have hdiff : ((((S-1)*N:ℕ):ℤ)-(N:ℤ)) = ((S-2:ℕ):ℤ)*(N:ℤ) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1≤S), Nat.cast_sub (by omega : 2≤S)]
      push_cast
      ring
    rw [hdiff]
    push_cast
    rw [hNcast, hScast]
    rw [pow_add, pow_mul]
    push_cast
    rw [Nat.cast_sub (show 1≤S by omega)]
    ring
  have hr := RNat_scale_supercongruence_total
    (p:=p) (L:=3*lev+q) (B:=N) (Y:=(S-1)*N) hp hp5 hprod
  have hsum : N+(S-1)*N=S*N := by
    calc
      N+(S-1)*N = 1*N+(S-1)*N := by rw [one_mul]
      _ = (1+(S-1))*N := (Nat.add_mul _ _ _).symm
      _ = S*N := by rw [show 1+(S-1)=S by omega]
  rw [hsum] at hr
  have hpN : 0<p*N := mul_pos hp.pos hN
  have hlow := RNat_eq_boundary_mul S N (by omega) hN
  have hhigh := RNat_eq_boundary_mul S (p*N) (by omega) hpN
  have harg : S*(p*N)=p*(S*N) := by ring
  rw [harg] at hhigh
  change RNat (p*(S*N)) (p*N) ≡ RNat (S*N) N
      [ZMOD ((p:ℤ)^((3*lev+q)+3))] at hr
  rw [hhigh, hlow] at hr
  change c * (((p*(S*N)-1).choose (p*N-1):ℕ):ℤ) ≡ c*BL
      [ZMOD ((p:ℤ)^((3*lev+q)+3))] at hr
  rw [show p*(S*N)=S*(p*N) by ring] at hr
  change c*BH ≡ c*BL [ZMOD ((p:ℤ)^((3*lev+q)+3))] at hr
  rw [Int.modEq_iff_dvd] at hr ⊢
  have hexp : (3*lev+q)+3=3*(lev+1)+q := by omega
  rw [hexp] at hr
  let D : ℤ := BL-BH
  change ((p:ℤ)^(3*(lev+1))) ∣ D
  have hrD : ((p:ℤ)^(3*(lev+1)+q)) ∣ c*D := by
    dsimp [D]
    convert hr using 1 <;> ring
  by_cases hD : D=0
  · simp [hD]
  have hval := (padicValInt_dvd_iff (3*(lev+1)+q) (c*D)).mp hrD
  have hval' : 3*(lev+1)+q ≤ padicValInt p (c*D) :=
    hval.resolve_left (mul_ne_zero hc0 hD)
  rw [padicValInt.mul hc0 hD] at hval'
  have hvc : padicValInt p c=q := by
    dsimp [c,q]
    rw [← padicValInt.of_nat]
    congr 2
    omega
  rw [hvc] at hval'
  apply (padicValInt_dvd_iff (3*(lev+1)) D).mpr
  exact Or.inr (by omega)
