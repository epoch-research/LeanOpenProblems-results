import FormalConjecturesUtil

/-! Rational linear subspaces on which the four-coordinate fourth-power norm
is always a square have dimension at most one. This is a restriction on a
proposed parametrization, not an upper bound for integer representations. -/

namespace Erdos322Research.QuarticSquareLinearRigidity
noncomputable section
open Finset
set_option Elab.async false
set_option maxHeartbeats 0

private abbrev K := ZMod 5
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def norm {R : Type*} [CommSemiring R] (a : Fin 4 → R) : R := ∑ i, a i^4

private lemma square_support : ∀ v : Fin 4 → K, IsSquare (norm v) →
    (∃ i, v i=0) → (univ.filter (fun i ↦ v i ≠ 0)).card ≤ 1 := by
  decide +kernel

private lemma square_zero_support (v : Fin 4 → K) (hs : IsSquare (norm v))
    (hz : ∃ i, v i=0) {j l : Fin 4} (hj : v j ≠ 0) (hl : l ≠ j) : v l=0 := by
  by_contra h
  have he := (card_le_one.mp (square_support v hs hz)) j (by simp [hj]) l (by simp [h])
  exact hl he.symm

/-- The finite-field obstruction applies even to a merely pointwise square
condition; no specified quadratic square root is needed. -/
theorem field_minors_zero (a b : Fin 4 → K)
    (h : ∀ x y : K, IsSquare (norm (fun l ↦ x*a l+y*b l))) (i j : Fin 4) :
    a i*b j-a j*b i=0 := by
  by_contra hd
  let D := a i*b j-a j*b i
  have hD : D ≠ 0 := hd
  have hij : i ≠ j := by intro he; subst j; simp [D] at hD
  let v : Fin 4 → K := fun l ↦ b j*a l-a j*b l
  let w : Fin 4 → K := fun l ↦ -b i*a l+a i*b l
  have hv : IsSquare (norm v) := by simpa [v,sub_eq_add_neg] using h (b j) (-a j)
  have hw : IsSquare (norm w) := h (-b i) (a i)
  have hvi : v i=D := by dsimp [v,D]; ring
  have hvj : v j=0 := by dsimp [v]; ring
  have hwi : w i=0 := by dsimp [w]; ring
  have hwj : w j=D := by dsimp [w,D]; ring
  have hvrest (l : Fin 4) (hl : l ≠ i) : v l=0 :=
    square_zero_support v hv ⟨j,hvj⟩ (by rwa [hvi]) hl
  have hwrest (l : Fin 4) (hl : l ≠ j) : w l=0 :=
    square_zero_support w hw ⟨i,hwi⟩ (by rwa [hwj]) hl
  obtain ⟨l,hli,hlj⟩ : ∃ l : Fin 4, l ≠ i ∧ l ≠ j := by
    fin_cases i <;> fin_cases j <;> decide
  have hs : IsSquare (norm (fun l ↦ v l+w l)) := by
    convert h (b j-b i) (a i-a j) using 1
    congr 1
    funext l
    dsimp [v,w]
    ring
  have hi : v i+w i ≠ 0 := by simpa [hvi,hwi] using hD
  have hj : v j+w j ≠ 0 := by simpa [hvj,hwj] using hD
  exact hj (square_zero_support _ hs ⟨l,by rw [hvrest l hli,hwrest l hlj]; simp⟩ hi hij.symm)

private def SquarePlane (a b : Fin 4 → ℤ) : Prop :=
  ∀ x y : ℚ, IsSquare (norm (fun i ↦ x*(a i : ℚ)+y*(b i : ℚ)))

private lemma integer_field_plane {a b : Fin 4 → ℤ} (h : SquarePlane a b) :
    ∀ x y : K, IsSquare (norm (fun i ↦ x*(a i : K)+y*(b i : K))) := by
  intro x y
  have hq := h (x.val : ℚ) (y.val : ℚ)
  have hz : IsSquare (norm (fun i ↦ (x.val : ℤ)*a i+(y.val : ℤ)*b i)) := by
    apply Rat.isSquare_intCast_iff.mp
    simpa only [norm,Int.cast_sum,Int.cast_pow,Int.cast_add,Int.cast_mul,Int.cast_natCast] using hq
  have hm := IsSquare.map (Int.castRingHom K) hz
  simpa [norm] using hm

private lemma exists_smaller_plane (a b : Fin 4 → ℤ) (h : SquarePlane a b)
    (i j : Fin 4) : ∃ c d : Fin 4 → ℤ, SquarePlane c d ∧
      a i*b j-a j*b i=5*(c i*d j-c j*d i) := by
  by_cases ha : ∀ l, (5 : ℤ) ∣ a l
  · let c : Fin 4 → ℤ := fun l ↦ a l/5
    have hc (l) : 5*c l=a l := Int.mul_ediv_cancel' (ha l)
    refine ⟨c,b,?_,?_⟩
    · intro x y
      convert h (x/5) y using 1
      congr 1
      funext l
      have hcq : (5 : ℚ)*(c l : ℚ)=a l := by exact_mod_cast hc l
      linear_combination (x/5)*hcq
    · linear_combination -(b j)*hc i+(b i)*hc j
  · push_neg at ha
    obtain ⟨l,hl⟩ := ha
    have hal : (a l : K) ≠ 0 := by
      intro hz
      exact hl ((ZMod.intCast_zmod_eq_zero_iff_dvd (a l) 5).mp hz)
    let t : ℤ := (((b l : K)/(a l : K)).val : ℤ)
    have ht : (t : K)=(b l : K)/(a l : K) := by simp [t]
    have hd (q : Fin 4) : (5 : ℤ) ∣ b q-t*a q := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      rw [ht]
      have hh := field_minors_zero (fun q ↦ (a q : K)) (fun q ↦ (b q : K))
        (integer_field_plane h) l q
      apply sub_eq_zero.mpr
      field_simp
      linear_combination hh
    let c : Fin 4 → ℤ := fun q ↦ (b q-t*a q)/5
    have hc (q) : 5*c q=b q-t*a q := Int.mul_ediv_cancel' (hd q)
    refine ⟨a,c,?_,?_⟩
    · intro x y
      convert h (x-y*(t : ℚ)/5) (y/5) using 1
      congr 1
      funext q
      have hcq : (5 : ℚ)*(c q : ℚ)=(b q : ℚ)-(t : ℚ)*(a q : ℚ) := by
        exact_mod_cast hc q
      linear_combination (y/5)*hcq
    · linear_combination -(a i)*hc j+(a j)*hc i

private theorem integer_minors_zero (a b : Fin 4 → ℤ) (h : SquarePlane a b)
    (i j : Fin 4) : a i*b j-a j*b i=0 := by
  suffices ∀ N : ℕ, ∀ a b : Fin 4 → ℤ,
      (a i*b j-a j*b i).natAbs=N → SquarePlane a b → a i*b j-a j*b i=0 by
    exact this _ a b rfl h
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro a b hab hp
    by_cases hz : a i*b j-a j*b i=0
    · exact hz
    have hN : 0<N := hab ▸ Int.natAbs_pos.mpr hz
    obtain ⟨c,d,hcd,he⟩ := exists_smaller_plane a b hp i j
    have heabs : N=5*(c i*d j-c j*d i).natAbs := by
      rw [← hab,he,Int.natAbs_mul]
      rfl
    have hlt : (c i*d j-c j*d i).natAbs<N := by omega
    have hh := ih _ hlt c d rfl hcd
    rw [he,hh]
    ring


/-- If every rational linear combination of two vectors has square fourth-power
norm, then the two vectors are proportional (expressed by vanishing minors). -/
theorem pointwise_square_minors_zero (a b : Fin 4 → ℚ)
    (h : ∀ x y : ℚ, IsSquare (∑ l, (x*a l+y*b l)^4)) (i j : Fin 4) :
    a i*b j=a j*b i := by
  obtain ⟨da,hda⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) a
  obtain ⟨db,hdb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) b
  choose A hA using hda
  choose B hB using hdb
  have hA' (l) : (A l : ℚ)=(da : ℤ)*a l := by
    simpa [Algebra.smul_def] using hA l
  have hB' (l) : (B l : ℚ)=(db : ℤ)*b l := by
    simpa [Algebra.smul_def] using hB l
  have hp : SquarePlane A B := by
    intro x y
    convert h (x*(da : ℤ)) (y*(db : ℤ)) using 1
    congr 1
    funext l
    rw [hA',hB']
    ring
  have hm := integer_minors_zero A B hp i j
  have hmq : (A i : ℚ)*(B j : ℚ)-(A j : ℚ)*(B i : ℚ)=0 := by exact_mod_cast hm
  have he : ((da : ℤ) : ℚ)*(db : ℤ)*(a i*b j-a j*b i)=0 := by
    rw [hA',hA',hB',hB'] at hmq
    linear_combination hmq
  have hda0 : ((da : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero da
  have hdb0 : ((db : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero db
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (mul_ne_zero hda0 hdb0))

/-- In particular, a polynomial square identity on a rational two-dimensional
linear family is impossible. The square root here is allowed to be any function. -/
theorem square_identity_minors_zero (a b : Fin 4 → ℚ) (G : ℚ → ℚ → ℚ)
    (h : ∀ x y : ℚ, (∑ l, (x*a l+y*b l)^4)=G x y^2) (i j : Fin 4) :
    a i*b j=a j*b i := by
  apply pointwise_square_minors_zero a b (fun x y ↦ ?_) i j
  exact (isSquare_iff_exists_sq _).mpr ⟨G x y,h x y⟩

/-- A version for a linear map from an arbitrary rational vector space. -/
theorem linear_image_minors_zero {V : Type*} [AddCommGroup V] [Module ℚ V]
    (L : V →ₗ[ℚ] (Fin 4 → ℚ))
    (h : ∀ x : V, IsSquare (∑ i, (L x i)^4))
    (x y : V) (i j : Fin 4) : L x i*L y j=L x j*L y i := by
  apply pointwise_square_minors_zero (L x) (L y) ?_ i j
  intro s t
  simpa only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using h (s • x+t • y)

/-- Every such linear image is contained in the span of any of its nonzero
vectors. This conclusion requires the square condition on the whole image. -/
theorem linear_image_proportional {V : Type*} [AddCommGroup V] [Module ℚ V]
    (L : V →ₗ[ℚ] (Fin 4 → ℚ))
    (h : ∀ x : V, IsSquare (∑ i, (L x i)^4))
    (x : V) (j : Fin 4) (hj : L x j ≠ 0) (y : V) :
    L y=(L y j/L x j) • L x := by
  funext i
  change L y i=(L y j/L x j)*L x i
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hj).mpr
  linear_combination linear_image_minors_zero L h x y j i

end
end Erdos322Research.QuarticSquareLinearRigidity
