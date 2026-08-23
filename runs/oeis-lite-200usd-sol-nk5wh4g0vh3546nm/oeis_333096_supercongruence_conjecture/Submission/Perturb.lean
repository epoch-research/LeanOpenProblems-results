import Submission.Boundary
open Nat Finset BigOperators Int Polynomial

private def fallTop (X k : ℕ) : ℤ :=
  ∏ i ∈ Finset.range k, ((X:ℤ)-i)

private lemma fallTop_eq (X k : ℕ) :
    fallTop X k = (k.factorial:ℤ) * (X.choose k:ℤ) := by
  rw [fallTop, ← Ring.choose_natCast (R:=ℤ), ← nsmul_eq_mul,
    ← Ring.descPochhammer_eq_factorial_smul_choose, ← Polynomial.eval_eq_smeval]
  exact (descPochhammer_eval_eq_prod_range k (X:ℤ)).symm

lemma choose_modEq_of_top_modEq {p E X Y k : ℕ} (hp : p.Prime)
    (hXY : (X:ℤ) ≡ (Y:ℤ)
      [ZMOD ((p:ℤ)^(E+padicValNat p k.factorial))]) :
    (X.choose k:ℤ) ≡ (Y.choose k:ℤ) [ZMOD ((p:ℤ)^E)] := by
  let v := padicValNat p k.factorial
  let D : ℤ := (Y.choose k:ℤ)-(X.choose k:ℤ)
  letI : Fact p.Prime := ⟨hp⟩
  have hfall : fallTop X k ≡ fallTop Y k [ZMOD ((p:ℤ)^(E+v))] := by
    apply Int.ModEq.prod
    intro i hi
    exact hXY.sub rfl
  rw [fallTop_eq, fallTop_eq, Int.modEq_iff_dvd] at hfall
  have hfac : (k.factorial:ℤ)≠0 := by positivity
  have hwhole : ((p:ℤ)^(E+v)) ∣ (k.factorial:ℤ)*D := by
    dsimp [D]
    convert hfall using 1 <;> ring
  rw [Int.modEq_iff_dvd]
  change ((p:ℤ)^E) ∣ D
  by_cases hD : D=0
  · simp [hD]
  have hvall := (padicValInt_dvd_iff (E+v) ((k.factorial:ℤ)*D)).mp hwhole
  have hvall' : E+v≤padicValInt p ((k.factorial:ℤ)*D) :=
    hvall.resolve_left (mul_ne_zero hfac hD)
  rw [padicValInt.mul hfac hD, padicValInt.of_nat] at hvall'
  apply (padicValInt_dvd_iff E D).mpr
  exact Or.inr (by dsimp [v] at hvall' ⊢; omega)

lemma boundary_scale_two {p N lev : ℕ}
    (hp : p.Prime) (hp5 : 5≤p) (hN : 0<N) (hdiv : p^lev∣N) :
    (((2*(p*N)-1).choose (p*N-1):ℕ):ℤ) ≡
      (((2*N-1).choose (N-1):ℕ):ℤ)
      [ZMOD ((p:ℤ)^(3*(lev+1)))] := by
  let E := 3*(lev+1)
  let vL := padicValNat p (N-1).factorial
  let vH := padicValNat p (p*N-1).factorial
  let T := E+vL+vH
  let Sp := 2+p^T
  have hSp : 2<Sp := by
    have hpow : 0<p^T := pow_pos hp.pos T
    dsimp [Sp]
    omega
  have hmain := boundary_scale_gt_two hSp hp hp5 hN hdiv
  have hEL : E+vL≤T := by dsimp [T]; omega
  have hEH : E+vH≤T := by dsimp [T]; omega
  have htopL : ((Sp*N-1:ℕ):ℤ) ≡ ((2*N-1:ℕ):ℤ)
      [ZMOD ((p:ℤ)^(E+vL))] := by
    rw [Int.modEq_iff_dvd]
    have hpdiv : ((p:ℤ)^(E+vL)) ∣ (p:ℤ)^T :=
      pow_dvd_pow (p:ℤ) hEL
    have hd : ((p:ℤ)^(E+vL)) ∣ (p:ℤ)^T*(N:ℤ) :=
      dvd_mul_of_dvd_left hpdiv N
    have heq : ((2*N-1:ℕ):ℤ)-((Sp*N-1:ℕ):ℤ) =
        -((p:ℤ)^T*(N:ℤ)) := by
      dsimp [Sp]
      push_cast
      have h2N : 0<2*N := mul_pos (by omega) hN
      have hSpN : 0<(2+p^T)*N := mul_pos (by positivity) hN
      rw [Nat.cast_sub (by omega : 1≤2*N),
        Nat.cast_sub (by omega : 1≤(2+p^T)*N)]
      push_cast
      ring
    rw [heq]
    exact dvd_neg.mpr hd
  have htopH : ((Sp*(p*N)-1:ℕ):ℤ) ≡ ((2*(p*N)-1:ℕ):ℤ)
      [ZMOD ((p:ℤ)^(E+vH))] := by
    rw [Int.modEq_iff_dvd]
    have hpdiv : ((p:ℤ)^(E+vH)) ∣ (p:ℤ)^T :=
      pow_dvd_pow (p:ℤ) hEH
    have hd : ((p:ℤ)^(E+vH)) ∣ (p:ℤ)^T*(p*N:ℤ) :=
      dvd_mul_of_dvd_left hpdiv (p*N)
    have heq : ((2*(p*N)-1:ℕ):ℤ)-((Sp*(p*N)-1:ℕ):ℤ) =
        -((p:ℤ)^T*(p*N:ℤ)) := by
      dsimp [Sp]
      have hpN : 0<p*N := mul_pos hp.pos hN
      have htwo : 0<2*(p*N) := mul_pos (by omega) hpN
      have hbig : 0<(2+p^T)*(p*N) := mul_pos (by positivity) hpN
      rw [Nat.cast_sub (by omega : 1≤2*(p*N)),
        Nat.cast_sub (by omega : 1≤(2+p^T)*(p*N))]
      push_cast
      ring
    rw [heq]
    exact dvd_neg.mpr hd
  have hlow := choose_modEq_of_top_modEq (p:=p) (E:=E)
    (X:=Sp*N-1) (Y:=2*N-1) (k:=N-1) hp (by simpa [vL] using htopL)
  have hhigh := choose_modEq_of_top_modEq (p:=p) (E:=E)
    (X:=Sp*(p*N)-1) (Y:=2*(p*N)-1) (k:=p*N-1) hp
      (by simpa [vH] using htopH)
  change (((Sp*(p*N)-1).choose (p*N-1):ℕ):ℤ) ≡
      (((Sp*N-1).choose (N-1):ℕ):ℤ) [ZMOD ((p:ℤ)^E)] at hmain
  change (((2*(p*N)-1).choose (p*N-1):ℕ):ℤ) ≡
      (((2*N-1).choose (N-1):ℕ):ℤ) [ZMOD ((p:ℤ)^E)]
  exact hhigh.symm.trans (hmain.trans hlow)

lemma boundary_scale {S p N lev : ℕ} (hS : 2≤S)
    (hp : p.Prime) (hp5 : 5≤p) (hN : 0<N) (hdiv : p^lev∣N) :
    (((S*(p*N)-1).choose (p*N-1):ℕ):ℤ) ≡
      (((S*N-1).choose (N-1):ℕ):ℤ)
      [ZMOD ((p:ℤ)^(3*(lev+1)))] := by
  rcases hS.eq_or_lt with rfl | hgt
  · exact boundary_scale_two hp hp5 hN hdiv
  · exact boundary_scale_gt_two hgt hp hp5 hN hdiv

