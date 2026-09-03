import FormalConjecturesUtil

/-! Arithmetic for a restricted paired-linear quintic moment construction.
No assertion about unrestricted representation counts is made. -/
namespace Erdos322Research.QuinticPairedMomentArithmetic
noncomputable section
open Finset
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private def fifth {R : Type*} [CommRing R] (v : Fin 4 → R) : R :=
  2*(v 0^5+v 1^5)-v 2^5
private def square {R : Type*} [CommRing R] (v : Fin 4 → R) : R :=
  v 3^2-3*v 0*v 1

private lemma fifth_scale {R : Type*} [CommRing R] (r : R) (v : Fin 4 → R) :
    fifth (fun i ↦ r*v i) = r^5*fifth v := by unfold fifth; ring
private lemma square_scale {R : Type*} [CommRing R] (r : R) (v : Fin 4 → R) :
    square (fun i ↦ r*v i) = r^2*square v := by unfold square; ring

private theorem mod_eleven : ∀ a c A z : ZMod 11,
    2*(a^5+c^5)=A^5 → z^2=3*a*c → a=0 ∧ c=0 ∧ A=0 ∧ z=0 := by
  decide +kernel

private theorem integer_zero (v : Fin 4 → ℤ)
    (hf : fifth v = 0) (hs : square v = 0) : ∀ i, v i = 0 := by
  suffices h : ∀ N : ℕ, ∀ v : Fin 4 → ℤ, (∑ i, (v i).natAbs) = N →
      fifth v = 0 → square v = 0 → ∀ i, v i = 0 by
    exact h _ v rfl hf hs
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro v hN hf hs
    by_cases hn : N = 0
    · intro i
      have hh := single_le_sum (f := fun j ↦ (v j).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (mem_univ i)
      rw [hN,hn] at hh
      exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hh)
    · have hf' : 2*((v 0 : ZMod 11)^5+(v 1 : ZMod 11)^5)=(v 2 : ZMod 11)^5 := by
        have hh := congrArg (Int.castRingHom (ZMod 11)) hf
        simpa [fifth,sub_eq_zero] using hh
      have hs' : (v 3 : ZMod 11)^2=3*(v 0 : ZMod 11)*(v 1 : ZMod 11) := by
        have hh := congrArg (Int.castRingHom (ZMod 11)) hs
        simpa [square,sub_eq_zero] using hh
      obtain ⟨h0,h1,h2,h3⟩ := mod_eleven _ _ _ _ hf' hs'
      have hz (i : Fin 4) : (v i : ZMod 11) = 0 := by fin_cases i <;> assumption
      have hd : ∀ i, ∃ w : ℤ, v i = 11*w := fun i ↦
        (ZMod.intCast_zmod_eq_zero_iff_dvd (v i) 11).mp (hz i)
      choose w hw using hd
      have hv : v = fun i ↦ 11*w i := funext hw
      have hwf : fifth w = 0 := by
        have hh : (11 : ℤ)^5*fifth w = 0 := by simpa only [hv,fifth_scale] using hf
        exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
      have hws : square w = 0 := by
        have hh : (11 : ℤ)^2*square w = 0 := by simpa only [hv,square_scale] using hs
        exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
      have hsize : 11*(∑ i, (w i).natAbs) = N := by
        rw [←hN,mul_sum]
        apply sum_congr rfl
        intro i _
        rw [hw i,Int.natAbs_mul]
        rfl
      have hh := ih _ (by omega : (∑ i, (w i).natAbs) < N) w rfl hwf hws
      intro i
      rw [hw i,hh i,mul_zero]

private theorem rational_zero (v : Fin 4 → ℚ)
    (hf : fifth v = 0) (hs : square v = 0) : ∀ i, v i = 0 := by
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) v
  choose w hw using hd
  have hd0 : algebraMap ℤ ℚ d ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective ℤ ℚ).ne
      (nonZeroDivisors.ne_zero d.prop)
  have hw' (i : Fin 4) : (w i : ℚ) = algebraMap ℤ ℚ d*v i := by
    simpa only [Algebra.smul_def] using hw i
  have hwf : fifth w = 0 := by
    have hh : fifth (fun i ↦ (w i : ℚ)) = 0 := by
      simp only [hw',fifth_scale,hf,mul_zero]
    unfold fifth at hh ⊢
    dsimp only at hh
    exact_mod_cast hh
  have hws : square w = 0 := by
    have hh : square (fun i ↦ (w i : ℚ)) = 0 := by
      simp only [hw',square_scale,hs,mul_zero]
    unfold square at hh ⊢
    dsimp only at hh
    exact_mod_cast hh
  have hz := integer_zero w hwf hws
  intro i
  have hh := hw' i
  rw [hz i,Int.cast_zero] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_left hd0

/-- A homogeneous modulo-11 descent: these two rational equations have only
 the zero solution. All denominators are covered. -/
theorem no_fifth_and_square (a c A z : ℚ)
    (hf : 2*(a^5+c^5)=A^5) (hs : z^2=3*a*c) :
    a=0 ∧ c=0 ∧ A=0 ∧ z=0 := by
  have hh := rational_zero (![a,c,A,z] : Fin 4 → ℚ)
    (by simpa [fifth] using sub_eq_zero.mpr hf)
    (by simpa [square,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.head_cons,Matrix.tail_cons] using sub_eq_zero.mpr hs)
  exact ⟨hh 0,hh 1,hh 2,hh 3⟩

/-- The paired-centre even-moment equation is incompatible with a nonzero
slope and a fifth-power leading norm. -/
theorem paired_centres_impossible {a c A u v : ℚ} (ha : 0 < a) (hc : 0 < c)
    (hu : u ≠ 0) (hf : 2*(a^5+c^5)=A^5)
    (hH : (a^5+c^5)*(a*u^4+c*v^4)-4*(a^3*u^2+c^3*v^2)^2=0) : False := by
  have hS : a^5+c^5 ≠ 0 := ne_of_gt (by positivity)
  let z := (c*(a^5-3*c^5)*v^2-4*a^3*c^3*u^2)/((a^5+c^5)*u^2)
  have hz : z^2=3*a*c := by
    dsimp [z]
    field_simp
    linear_combination (a^5-3*c^5)*hH
  have hh := no_fifth_and_square a c A z hf hz
  exact ha.ne' hh.1

/-- Both slopes must vanish in the paired-centre branch. -/
theorem paired_centres_slopes_zero {a c A u v : ℚ} (ha : 0 < a) (hc : 0 < c)
    (hf : 2*(a^5+c^5)=A^5)
    (hH : (a^5+c^5)*(a*u^4+c*v^4)-4*(a^3*u^2+c^3*v^2)^2=0) :
    u=0 ∧ v=0 := by
  have hu : u=0 := by by_contra h; exact paired_centres_impossible ha hc h hf hH
  have hv : v=0 := by
    by_contra h
    apply paired_centres_impossible (v := u) hc ha h (by simpa [add_comm] using hf)
    simpa [add_comm] using hH
  exact ⟨hu,hv⟩

/-- The degenerate-slope branch would require a rational fifth root of eight. -/
theorem no_eight_fifth {A c : ℚ} (hc : c ≠ 0) (h : A^5=8*c^5) : False := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hA : A ≠ 0 := by intro hz; simp [hz,hc] at h
  have hp : padicValRat 2 (2 : ℚ) = 1 := by
    simpa using padicValRat.self (by decide : 1 < 2)
  have h8 : padicValRat 2 (8 : ℚ) = 3 := by
    rw [show (8 : ℚ) = 2^3 by norm_num, padicValRat.pow (by norm_num : (2 : ℚ) ≠ 0), hp]
    norm_num
  have hv := congrArg (padicValRat 2) h
  rw [padicValRat.pow hA,
    padicValRat.mul (by norm_num : (8 : ℚ) ≠ 0) (pow_ne_zero 5 hc),
    h8,padicValRat.pow hc] at hv
  omega

end
end Erdos322Research.QuinticPairedMomentArithmetic
