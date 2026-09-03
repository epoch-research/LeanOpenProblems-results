import Submission.BinaryHeightSummability
import Submission.BinaryHomogeneousHeight

/-!
A fixed basepoint-free homogeneous binary family of degree at least three,
with a certified bound on common-factor cancellation, has a reciprocal-
summable cover by its largest normalized coordinates. This familywise result
does not give a bound uniform over all rational curves or all odd cycles.
-/
namespace Erdos1206.NormalizedBinaryFamilySieve
open BinaryHeightSummability BinaryHomogeneousHeight
open scoped Classical

noncomputable def rootHeight {m : ℕ} (N : Fin m → ℤ) : ℕ :=
  Finset.univ.sup (fun i => (N i).natAbs)

lemma rootHeight_attained {m : ℕ} (hm : 0 < m) (N : Fin m → ℤ) :
    ∃ i, rootHeight N=(N i).natAbs := by
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0,hm⟩,by simp⟩
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup Finset.univ hne (fun i => (N i).natAbs)
  exact ⟨i,hi⟩

private lemma natAbs_cast (z : ℤ) : (z.natAbs:ℝ)=|(z:ℝ)| := by
  rw [Nat.cast_natAbs,Int.cast_abs]

private lemma parameter_norm (p : ℤ × ℤ) : ‖((p.1:ℝ),(p.2:ℝ))‖=(height p:ℝ) := by
  simp only [Prod.norm_def,Real.norm_eq_abs,height,Nat.cast_max,natAbs_cast]

private lemma primitive_height_pos {p : ℤ × ℤ} (hp : IsCoprime p.1 p.2) : 1 ≤ height p := by
  rcases hp.ne_zero_or_ne_zero with h | h
  · have hh := Int.natAbs_pos.mpr h
    dsimp [height]
    omega
  · have hh := Int.natAbs_pos.mpr h
    dsimp [height]
    omega

/-- All height estimates are made AFTER the common integer multiplier g
has been divided out. Divisibility by the fixed nonzero certificate R bounds
that multiplier. -/
theorem normalized_cubic_height_bound {m d : ℕ} (hd : 3 ≤ d)
    (F : (ℝ × ℝ) → (Fin m → ℝ)) (hcont : Continuous F)
    (hhom : ∀ (s : ℝ) x, F (s • x)=s^d • F x) (hzero : ∀ x, F x=0 → x=0)
    {T : Set (ℤ × ℤ)} (hprim : ∀ p : T, IsCoprime p.val.1 p.val.2)
    (N : T → Fin m → ℤ) (g : T → ℤ) {R : ℤ} (hR : R ≠ 0)
    (hg : ∀ p, g p ∣ R)
    (hN : ∀ p i, F ((p.val.1:ℝ),(p.val.2:ℝ)) i=((g p*N p i:ℤ):ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : T, ((height p:ℝ)+1)^3 ≤ C*(rootHeight (N p):ℝ) := by
  obtain ⟨c,hc,hcF⟩ := homogeneous_lower_bound (by omega : 0 < d) F hcont hhom hzero
  have hRp : (0:ℝ) < R.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hR
  refine ⟨8*(R.natAbs:ℝ)/c,by positivity,fun p => ?_⟩
  have hH : (1:ℝ) ≤ (height p:ℝ) := by exact_mod_cast primitive_height_pos (hprim p)
  have hF : ‖F ((p.val.1:ℝ),(p.val.2:ℝ))‖ ≤
      (R.natAbs:ℝ)*(rootHeight (N p):ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have hgi : |(g p:ℝ)| ≤ (R.natAbs:ℝ) := by
      rw [← natAbs_cast]
      exact_mod_cast Int.natAbs_le_of_dvd_ne_zero (hg p) hR
    have hni : |(N p i:ℝ)| ≤ (rootHeight (N p):ℝ) := by
      rw [← natAbs_cast]
      exact_mod_cast (Finset.le_sup (f := fun i => (N p i).natAbs) (Finset.mem_univ i))
    rw [hN,Real.norm_eq_abs,Int.cast_mul,abs_mul]
    exact mul_le_mul hgi hni (abs_nonneg _) (by positivity)
  have hlow := hcF ((p.val.1:ℝ),(p.val.2:ℝ))
  rw [parameter_norm] at hlow
  have hp : ((height p:ℝ)+1)^3 ≤ 8*(height p:ℝ)^3 := by
    calc
      _ ≤ (2*(height p:ℝ))^3 := by gcongr; linarith
      _ = _ := by ring
  have hpow : (height p:ℝ)^3 ≤ (height p:ℝ)^d := pow_le_pow_right₀ hH hd
  have hfinal : ((height p:ℝ)+1)^3*c ≤ 8*(R.natAbs:ℝ)*(rootHeight (N p):ℝ) := by
    calc
      _ ≤ (8*(height p:ℝ)^3)*c := mul_le_mul_of_nonneg_right hp hc.le
      _ ≤ (8*(height p:ℝ)^d)*c := by gcongr
      _ ≤ _ := by nlinarith [hlow.trans hF]
  calc
    _ ≤ (8*(R.natAbs:ℝ)*(rootHeight (N p):ℝ))/c := (le_div_iff₀ hc).mpr hfinal
    _ = _ := by ring

/-- A reciprocal-summable cover for all normalized parameter values in a
fixed homogeneous binary family. -/
theorem normalized_maxima_summable {m d : ℕ} (hd : 3 ≤ d)
    (F : (ℝ × ℝ) → (Fin m → ℝ)) (hcont : Continuous F)
    (hhom : ∀ (s : ℝ) x, F (s • x)=s^d • F x) (hzero : ∀ x, F x=0 → x=0)
    {T : Set (ℤ × ℤ)} (hprim : ∀ p : T, IsCoprime p.val.1 p.val.2)
    (N : T → Fin m → ℤ) (g : T → ℤ) {R : ℤ} (hR : R ≠ 0)
    (hg : ∀ p, g p ∣ R)
    (hN : ∀ p i, F ((p.val.1:ℝ),(p.val.2:ℝ)) i=((g p*N p i:ℤ):ℝ)) :
    Summable (fun n : ℕ => if n ∈ Set.range (fun p => rootHeight (N p)) then (1:ℝ)/n else 0) := by
  obtain ⟨C,hC,hbound⟩ := normalized_cubic_height_bound hd F hcont hhom hzero hprim N g hR hg hN
  exact range_reciprocals_summable hC hbound

/-- A positive-density set avoids every entire normalized coordinate tuple
and every integer dilation of it. No individual tuple with maximum one is
allowed, since deleting divisor one would delete the whole source. -/
theorem positive_density_avoids_normalized_family {m d : ℕ} (hm : 0 < m) (hd : 3 ≤ d)
    (F : (ℝ × ℝ) → (Fin m → ℝ)) (hcont : Continuous F)
    (hhom : ∀ (s : ℝ) x, F (s • x)=s^d • F x) (hzero : ∀ x, F x=0 → x=0)
    {T : Set (ℤ × ℤ)} (hprim : ∀ p : T, IsCoprime p.val.1 p.val.2)
    (N : T → Fin m → ℤ) (g : T → ℤ) {R : ℤ} (hR : R ≠ 0)
    (hg : ∀ p, g p ∣ R)
    (hN : ∀ p i, F ((p.val.1:ℝ),(p.val.2:ℝ)) i=((g p*N p i:ℤ):ℝ))
    (hmax : ∀ p, 1 < rootHeight (N p)) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      ∀ (p : T) (t : ℕ), ∃ i : Fin m, t*(N p i).natAbs ∉ A := by
  obtain ⟨C,hC,hbound⟩ := normalized_cubic_height_bound hd F hcont hhom hzero hprim N g hR hg hN
  obtain ⟨A,hA,hden,havoid⟩ := positive_density_avoids_family hC hbound hmax
  refine ⟨A,hA,hden,fun p t => ?_⟩
  obtain ⟨i,hi⟩ := rootHeight_attained hm (N p)
  exact ⟨i,by rw [← hi]; exact havoid p t⟩

#print axioms normalized_cubic_height_bound
#print axioms normalized_maxima_summable
#print axioms positive_density_avoids_normalized_family
end Erdos1206.NormalizedBinaryFamilySieve
