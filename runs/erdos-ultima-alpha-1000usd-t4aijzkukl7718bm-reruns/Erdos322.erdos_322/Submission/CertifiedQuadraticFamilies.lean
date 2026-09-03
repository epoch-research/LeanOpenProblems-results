import Submission.UniformPositiveQuadratic

/-! Uniform parameter counts for varying quadratic denominators with an
explicit two-chart arithmetic certificate. The scale in the certificate is
part of the bound; it is not silently treated as a fixed constant. -/
namespace Erdos322Research.CertifiedQuadraticFamilies

open Finset UniformPositiveQuadratic
set_option Elab.async false

abbrev Pair := ℤ × ℤ

/-- A projective reducedness certificate. Polynomial Bezout identities in the
two homogeneous coordinates supply certificates of this form by evaluation. -/
def Certified {ι : Type*} [Fintype ι] (f : Pair → ℤ) (g : ι → Pair → ℤ)
    (C : ℤ) (D : ℕ) : Prop :=
  ∀ p, (∃ a : ι → ℤ, ∃ b : ℤ, (∑ i, a i*g i p)+b*f p=C*p.1^D) ∧
       (∃ a : ι → ℤ, ∃ b : ℤ, (∑ i, a i*g i p)+b*f p=C*p.2^D)

/-- Two chart certificates cancel the parameter denominator without an
extra factor involving the leading coefficient of the form. -/
theorem denominator_dvd_scale {ι : Type*} [Fintype ι]
    (f : Pair → ℤ) (g : ι → Pair → ℤ) (C L D : ℕ)
    (hcert : Certified f g (C : ℤ) D) (p : Pair)
    (hp : p.1.gcd p.2=1) (hf : f p ≠ 0)
    (hint : ∀ i, ∃ z : ℤ, (L : ℚ)*(g i p : ℚ)/(f p : ℚ)=z) :
    (f p).natAbs ∣ C*L := by
  have hfq : (f p : ℚ) ≠ 0 := by exact_mod_cast hf
  have hi (i : ι) : f p ∣ (L : ℤ)*g i p := by
    obtain ⟨z,hz⟩ := hint i
    have he := (div_eq_iff hfq).mp hz
    have hzI : (L : ℤ)*g i p=z*f p := by exact_mod_cast he
    rw [hzI]
    exact dvd_mul_left _ _
  have hchart (a : ι → ℤ) (b t : ℤ)
      (h : (∑ i, a i*g i p)+b*f p=(C : ℤ)*t^D) :
      f p ∣ ((C*L : ℕ) : ℤ)*t^D := by
    have hs : f p ∣ ∑ i, a i*((L : ℤ)*g i p) :=
      Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (hi i) (a i))
    have hb : f p ∣ ((L : ℤ)*b)*f p := dvd_mul_left _ _
    have he : (∑ i, a i*((L : ℤ)*g i p))+((L : ℤ)*b)*f p=
        ((C*L : ℕ) : ℤ)*t^D := by
      push_cast
      rw [show (∑ i, a i*((L : ℤ)*g i p))=(L : ℤ)*(∑ i, a i*g i p) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring]
      calc
        _ = (L : ℤ)*((∑ i, a i*g i p)+b*f p) := by ring
        _ = _ := by rw [h]; ring
    exact he ▸ dvd_add hs hb
  obtain ⟨⟨a,b,h0⟩,⟨c,d,h1⟩⟩ := hcert p
  have hd0 := hchart a b p.1 h0
  have hd1 := hchart c d p.2 h1
  have hcop : IsCoprime (p.1^D) (p.2^D) :=
    (Int.isCoprime_iff_gcd_eq_one.mpr hp).pow
  obtain ⟨r,s,hrs⟩ := hcop
  have hc : f p ∣ ((C*L : ℕ) : ℤ) := by
    have hh := dvd_add (dvd_mul_of_dvd_right hd0 r) (dvd_mul_of_dvd_right hd1 s)
    have he : r*(((C*L : ℕ) : ℤ)*p.1^D)+s*(((C*L : ℕ) : ℤ)*p.2^D)=
        ((C*L : ℕ) : ℤ) := by
      calc
        _ = ((C*L : ℕ) : ℤ)*(r*p.1^D+s*p.2^D) := by ring
        _ = _ := by rw [hrs,mul_one]
    exact he ▸ hh
  simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hc

/-- Canonical primitive homogeneous coordinates, including infinity. -/
def parameterPair : Option ℚ → Pair
  | none => (1,0)
  | some t => (t.num,(t.den : ℤ))

lemma parameterPair_primitive (t : Option ℚ) :
    (parameterPair t).1.gcd (parameterPair t).2=1 := by
  cases t with
  | none => simp [parameterPair]
  | some t => simpa only [parameterPair,Int.gcd,Int.natAbs_natCast] using t.reduced

lemma parameterPair_injective : Function.Injective parameterPair := by
  intro t u he
  cases t with
  | none =>
    cases u with
    | none => rfl
    | some u =>
      have h := congrArg Prod.snd he
      change (0 : ℤ)=(u.den : ℤ) at h
      have := u.den_pos
      omega
  | some t =>
    cases u with
    | none =>
      have h := congrArg Prod.snd he
      change (t.den : ℤ)=0 at h
      have := t.den_pos
      omega
    | some u =>
      apply congrArg Option.some
      have h := congrArg (fun p : Pair => (p.1 : ℚ)/(p.2 : ℚ)) he
      simpa only [parameterPair,Int.cast_natCast,Rat.num_div_den] using h

lemma quadratic_value_positive (A B C : ℤ) (hA : 0 < A) (hD : 0 < 4*A*C-B^2)
    (p : Pair) (hp : p.1.gcd p.2=1) : 0 < value A B C p := by
  have hid : 4*A*value A B C p=(2*A*p.1+B*p.2)^2+(4*A*C-B^2)*p.2^2 := by
    dsimp [value]
    ring
  by_cases hy : p.2=0
  · have hx : p.1 ≠ 0 := by intro hx; simp [hx,hy] at hp
    dsimp [value]
    rw [hy]
    simpa using mul_pos hA (sq_pos_of_ne_zero hx)
  · have hh : 0 < (4*A*C-B^2)*p.2^2 := mul_pos hD (sq_pos_of_ne_zero hy)
    have hz := sq_nonneg (2*A*p.1+B*p.2)
    have hpv : 0 < 4*A*value A B C p := by omega
    exact (mul_pos_iff_of_pos_left (by omega : 0 < 4*A)).mp hpv

/-- Uniform bound for all projective parameters at scale `L`. All coefficients
and the certificate may vary; their arithmetic cost is explicitly `C₀*L`. -/
theorem projective_parameter_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ {ι : Type} [Fintype ι],
      ∀ A B C : ℤ, 0 < A → 0 < 4*A*C-B^2 →
      ∀ g : ι → Pair → ℤ, ∀ C₀ L D : ℕ, 0 < C₀ → 0 < L →
      Certified (value A B C) g (C₀ : ℤ) D →
      ∀ S : Finset (Option ℚ),
      (∀ t ∈ S, ∀ i, ∃ z : ℤ,
        (L : ℚ)*(g i (parameterPair t) : ℚ)/(value A B C (parameterPair t) : ℚ)=z) →
      (S.card : ℝ) ≤ K*((C₀*L : ℕ) : ℝ)^ε := by
  obtain ⟨K,hK,hbound⟩ := quadratic_divisor_fibers_subpolynomial ε hε
  refine ⟨K,hK,?_⟩
  intro ι inst A B C hA hD g C₀ L D hC₀ hL hcert S hint
  classical
  have hb := hbound A B C hD (C₀*L) (Nat.mul_pos hC₀ hL) (S.image parameterPair)
    (by
      intro p hp
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hp
      exact quadratic_value_positive A B C hA hD _ (parameterPair_primitive t))
    (by
      intro p hp
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hp
      have hpos := quadratic_value_positive A B C hA hD _ (parameterPair_primitive t)
      have hdvd := denominator_dvd_scale (value A B C) g C₀ L D hcert _
        (parameterPair_primitive t) hpos.ne' (hint t ht)
      have he : (value A B C (parameterPair t)).toNat=
          (value A B C (parameterPair t)).natAbs := by
        apply Int.natCast_inj.mp
        exact (Int.toNat_of_nonneg hpos.le).trans (Int.natAbs_of_nonneg hpos.le).symm
      rw [he]
      exact hdvd)
  rwa [Finset.card_image_of_injective _ parameterPair_injective] at hb

/-- A polynomial bound on the certificate times the scale is sufficient,
even for a family selected separately at each target. -/
theorem varying_projective_parameter_bound (R H : ℕ) (hH : 0 < H)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ {ι : Type} [Fintype ι], ∀ n : ℕ, 0 < n →
      ∀ A B C : ℤ, 0 < A → 0 < 4*A*C-B^2 →
      ∀ g : ι → Pair → ℤ, ∀ C₀ L D : ℕ, 0 < C₀ → 0 < L →
      C₀*L ≤ H*n^R → Certified (value A B C) g (C₀ : ℤ) D →
      ∀ S : Finset (Option ℚ),
      (∀ t ∈ S, ∀ i, ∃ z : ℤ,
        (L : ℚ)*(g i (parameterPair t) : ℚ)/(value A B C (parameterPair t) : ℚ)=z) →
      (S.card : ℝ) ≤ K*(n : ℝ)^ε := by
  let δ : ℝ := ε/((R : ℝ)+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K,hK,hbound⟩ := projective_parameter_bound δ hδ
  refine ⟨K*(H : ℝ)^δ,by positivity,?_⟩
  intro ι inst n hn A B C hA hD g C₀ L D hC₀ hL hsize hcert S hint
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he : (R : ℝ)*δ ≤ ε := by
    have hcancel : δ*((R : ℝ)+1)=ε := div_mul_cancel₀ _ (by positivity)
    nlinarith [hδ]
  calc
    (S.card : ℝ) ≤ K*((C₀*L : ℕ) : ℝ)^δ :=
      hbound A B C hA hD g C₀ L D hC₀ hL hcert S hint
    _ ≤ K*((H : ℝ)*(n : ℝ)^R)^δ := by
      apply mul_le_mul_of_nonneg_left _ hK.le
      apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hδ.le
      exact_mod_cast hsize
    _ = (K*(H : ℝ)^δ)*(n : ℝ)^((R : ℝ)*δ) := by
      rw [Real.mul_rpow (Nat.cast_nonneg H) (by positivity),
        ← Real.rpow_natCast_mul (Nat.cast_nonneg n)]
      ring
    _ ≤ (K*(H : ℝ)^δ)*(n : ℝ)^ε :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 he) (by positivity)

/-- Transfer the parameter bound to distinct nonnegative tuples. The family,
its coefficients, and its projective certificate may all vary with the target;
only the displayed arithmetic scale bound is required. -/
theorem varying_family_tuple_bound (R H : ℕ) (hH : 0 < H)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ {ι α : Type} [Fintype ι], ∀ n : ℕ, 0 < n →
      ∀ A B C : ℤ, 0 < A → 0 < 4*A*C-B^2 →
      ∀ g : ι → Pair → ℤ, ∀ C₀ L D e : ℕ, 0 < C₀ → 0 < L → 0 < e →
      C₀*L ≤ H*n^R → Certified (value A B C) g (C₀ : ℤ) D →
      ∀ (S : Finset α) (v : α → ι → ℕ), Function.Injective v →
      (∀ a ∈ S, ∃ t : Option ℚ, ∀ i,
        (v a i : ℚ)^e=(L : ℚ)*(g i (parameterPair t) : ℚ)/
          (value A B C (parameterPair t) : ℚ)) →
      (S.card : ℝ) ≤ K*(n : ℝ)^ε := by
  obtain ⟨K,hK,hbound⟩ := varying_projective_parameter_bound R H hH ε hε
  refine ⟨K,hK,?_⟩
  intro ι α inst n hn A B C hA hD g C₀ L D e hC₀ hL he hsize hcert S v hv hS
  classical
  have hx (a : S) := hS a.val a.property
  let t : S → Option ℚ := fun a => Classical.choose (hx a)
  have ht (a : S) (i : ι) :
      (v a.val i : ℚ)^e=(L : ℚ)*(g i (parameterPair (t a)) : ℚ)/
        (value A B C (parameterPair (t a)) : ℚ) := Classical.choose_spec (hx a) i
  have hi : Function.Injective t := by
    intro a b hab
    apply Subtype.ext
    apply hv
    funext i
    have hp : (v a.val i : ℚ)^e=(v b.val i : ℚ)^e := by rw [ht a i,ht b i,hab]
    exact Nat.pow_left_injective he.ne' (by exact_mod_cast hp)
  let T := Finset.univ.image t
  have hT : T.card=S.card := by
    rw [Finset.card_image_of_injective _ hi]
    simp
  have hb := hbound n hn A B C hA hD g C₀ L D hC₀ hL hsize hcert T (by
    intro s hs i
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hs
    refine ⟨(v a.val i : ℤ)^e,?_⟩
    rw [← ht a i]
    push_cast
    rfl)
  rwa [hT] at hb

end Erdos322Research.CertifiedQuadraticFamilies
