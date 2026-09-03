import Submission.QuadraticQuarticFive

/-! Among three positive coefficients one can select a binary quadratic
subform whose quadratic extension is not inert at five. -/
namespace Erdos322Research.QuadraticQuarticFive
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private lemma finite_pair :
    ∀ (v : Fin 3 → Fin 2) (u : Fin 3 → ZMod 5), (∀ i, u i ≠ 0) →
      ∃ i j, i ≠ j ∧ (v i ≠ v j ∨ ∃ r : ZMod 5, r ≠ 0 ∧ r^2 = -(u i*u j)) := by
  decide

/-- A square factor can be removed from a suitable product of coefficients. -/
theorem exists_good_natural_pair (A : Fin 3 → ℕ) (hA : ∀ i, 0<A i) :
    ∃ i j : Fin 3, i ≠ j ∧ ∃ d s : ℕ,
      0<d ∧ 0<s ∧ GoodFive (d : ℤ) ∧ A i*A j=d*s^2 := by
  have hh (i : Fin 3) := Nat.exists_eq_pow_mul_and_not_dvd
    (ne_of_gt (hA i)) 5 (by decide)
  choose e u hu hE using hh
  have hu0 (i : Fin 3) : (u i : ZMod 5) ≠ 0 := by
    intro h
    exact hu i ((ZMod.natCast_eq_zero_iff (u i) 5).mp h)
  have hup (i : Fin 3) : 0<u i := by
    have hh := hA i
    rw [hE i] at hh
    exact pos_of_mul_pos_right hh (by positivity)
  let v (i : Fin 3) : Fin 2 := ⟨e i%2,Nat.mod_lt _ (by decide)⟩
  obtain ⟨i,j,hij,hij'⟩ := finite_pair v (fun i ↦ (u i : ZMod 5)) hu0
  let E := e i+e j
  let d := 5^(E%2)*(u i*u j)
  let s := 5^(E/2)
  have hd : 0<d := by
    exact mul_pos (pow_pos (by decide) _) (mul_pos (hup i) (hup j))
  have hs : 0<s := by dsimp [s]; positivity
  have hgood : GoodFive (d : ℤ) := by
    by_cases ho : E%2=1
    · apply Or.inr
      refine ⟨(u i*u j : ℕ),?_,?_⟩
      · dsimp [d]
        rw [ho]
        push_cast
        ring
      · have hn : ¬5 ∣ u i*u j := (Nat.Prime.not_dvd_mul (by decide : Nat.Prime 5)) (hu i) (hu j)
        exact_mod_cast hn
    · have hz : E%2=0 := by omega
      have hv : v i=v j := by
        apply Fin.ext
        dsimp [v,E] at *
        omega
      obtain ⟨r,hr,hrr⟩ := hij'.resolve_left (not_not.mpr hv)
      apply Or.inl
      refine ⟨r,hr,?_⟩
      dsimp [d]
      rw [hz]
      simpa using hrr
  refine ⟨i,j,hij,d,s,hd,hs,hgood,?_⟩
  rw [hE i,hE j]
  have hp : e i+e j=E%2+2*(E/2) := by
    have hh := Nat.mod_add_div E 2
    dsimp [E] at *
    omega
  calc
    5^e i*u i*(5^e j*u j) = 5^(e i+e j)*(u i*u j) := by rw [pow_add]; ring
    _ = d*s^2 := by
      rw [hp,pow_add,pow_mul]
      dsimp [d,s]
      rw [show 25^(E/2)=(5^(E/2))^2 by
        change (5^2)^(E/2)=(5^(E/2))^2
        rw [←pow_mul,←pow_mul]; congr 1; omega]
      ring

private lemma positive_integer_scale (a : Fin 3 → ℚ) (ha : ∀ i, 0<a i) :
    ∃ D : ℕ, 0<D ∧ ∃ A : Fin 3 → ℕ, (∀ i, 0<A i) ∧
      ∀ i, (A i : ℚ)=(D : ℚ)*a i := by
  obtain ⟨D,hD⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) a
  choose b hb using hD
  have hDn : (D : ℤ) ≠ 0 := nonZeroDivisors.ne_zero D.prop
  have hDr : ((D : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hDn
  have hb' (i : Fin 3) : (b i : ℚ)=(D : ℤ)*a i := by
    simpa [Algebra.smul_def] using hb i
  have hn (i : Fin 3) : b i ≠ 0 := by
    intro h
    have hh := hb' i
    rw [h,Int.cast_zero] at hh
    exact (mul_ne_zero hDr (ne_of_gt (ha i))) hh.symm
  refine ⟨(D : ℤ).natAbs,Int.natAbs_pos.mpr hDn,fun i ↦ (b i).natAbs,
    fun i ↦ Int.natAbs_pos.mpr (hn i),fun i ↦ ?_⟩
  have hh := congrArg abs (hb' i)
  simpa [abs_mul,abs_of_pos (ha i)] using hh

/-- Rational version, in the form useful for a rational coordinate rescaling. -/
theorem exists_good_rational_pair (a : Fin 3 → ℚ) (ha : ∀ i, 0<a i) :
    ∃ i j : Fin 3, i ≠ j ∧ ∃ d : ℕ, 0<d ∧ GoodFive (d : ℤ) ∧
      ∃ t : ℚ, 0<t ∧ a j=a i*(d : ℚ)*t^2 := by
  obtain ⟨D,hD,A,hA,hDA⟩ := positive_integer_scale a ha
  obtain ⟨i,j,hij,d,s,hd,hs,hgood,hprod⟩ := exists_good_natural_pair A hA
  let t : ℚ := (s : ℚ)/((D : ℚ)*a i)
  have hDr : (0 : ℚ)<D := by exact_mod_cast hD
  have hsr : (0 : ℚ)<s := by exact_mod_cast hs
  have he : (D : ℚ)^2*a i*a j=(d : ℚ)*(s : ℚ)^2 := by
    have hh : (A i : ℚ)*(A j : ℚ)=(d : ℚ)*(s : ℚ)^2 := by exact_mod_cast hprod
    rw [hDA i,hDA j] at hh
    nlinarith [hh]
  refine ⟨i,j,hij,d,hd,hgood,t,div_pos hsr (mul_pos hDr (ha i)),?_⟩
  dsimp [t]
  field_simp [ne_of_gt hDr,ne_of_gt (ha i)]
  linear_combination he

end
end Erdos322Research.QuadraticQuarticFive
