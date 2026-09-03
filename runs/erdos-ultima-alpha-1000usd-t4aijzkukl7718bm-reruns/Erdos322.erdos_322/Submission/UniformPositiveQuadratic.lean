import Submission.UniformBinaryNorm

/-! Coefficient-uniform bounds for arbitrary positive definite binary quadratic
forms. The mixed coefficient and both diagonal coefficients may vary. These
are bounds for one form at a time, not a union over varying forms. -/
namespace Erdos322Research.UniformPositiveQuadratic

open Finset UniformBinaryNorm
set_option Elab.async false

/-- An integral binary quadratic form, on signed integral coordinates. -/
def value (A B C : ℤ) (p : ℤ × ℤ) : ℤ := A*p.1^2+B*p.1*p.2+C*p.2^2

private lemma signed_abs_injective :
    Function.Injective (fun x : ℤ => (x.natAbs,decide (0 ≤ x))) := by
  intro x y h
  have ha := congrArg Prod.fst h
  have hs : 0 ≤ x ↔ 0 ≤ y := decide_eq_decide.mp (congrArg Prod.snd h)
  have he := congrArg (fun a : ℕ => (a : ℤ)) ha
  simp only [Int.natCast_natAbs] at he
  by_cases hx : 0 ≤ x
  · simpa only [abs_of_nonneg hx,abs_of_nonneg (hs.mp hx)] using he
  · rw [abs_of_nonpos (le_of_not_ge hx),
      abs_of_nonpos (le_of_not_ge (fun hy => hx (hs.mpr hy)))] at he
    omega

lemma signed_norm_fiber_bound (d n : ℕ) (hd : 0 < d) (hn : 0 < n)
    (S : Finset (ℤ × ℤ))
    (hS : ∀ p ∈ S, p.1^2+(d : ℤ)*p.2^2=(n : ℤ)) :
    S.card ≤ 16*n.divisors.card^2 := by
  classical
  let tag : ℤ × ℤ → (ℕ × ℕ) × (Bool × Bool) := fun p =>
    ((p.1.natAbs,p.2.natAbs),(decide (0 ≤ p.1),decide (0 ≤ p.2)))
  have hi : Function.Injective tag := by
    intro p q he
    have h0 := congrArg (fun v : (ℕ × ℕ) × (Bool × Bool) => (v.1.1,v.2.1)) he
    have h1 := congrArg (fun v : (ℕ × ℕ) × (Bool × Bool) => (v.1.2,v.2.2)) he
    exact Prod.ext (signed_abs_injective h0) (signed_abs_injective h1)
  have hc : S.card ≤ (binaryNormSolutions d n ×ˢ (Finset.univ : Finset (Bool × Bool))).card := by
    apply Finset.card_le_card_of_injOn tag
    · intro p hp
      refine Finset.mem_product.mpr ⟨?_,Finset.mem_univ _⟩
      apply (mem_binaryNormSolutions hd _).mpr
      have he : (p.1.natAbs : ℤ)^2+(d : ℤ)*(p.2.natAbs : ℤ)^2=(n : ℤ) := by
        simpa only [Int.natCast_natAbs,sq_abs] using hS p hp
      exact_mod_cast he
    · exact hi.injOn
  simp only [Finset.card_product,Finset.card_univ,Fintype.card_prod,Fintype.card_bool] at hc
  have hb := binary_norm_count_uniform hd hn
  nlinarith

/-- Completing the square before a change of basis. -/
lemma fiber_bound_with_leading (A B C : ℤ) (hA : 0 < A) (hD : 0 < 4*A*C-B^2)
    (n : ℕ) (hn : 0 < n) (S : Finset (ℤ × ℤ))
    (hS : ∀ p ∈ S, value A B C p=(n : ℤ)) :
    S.card ≤ 16*(4*A.toNat*n).divisors.card^2 := by
  classical
  let d := (4*A*C-B^2).toNat
  have hd : 0 < d := by dsimp [d]; omega
  have hdc : (d : ℤ)=4*A*C-B^2 := Int.toNat_of_nonneg hD.le
  have hAc : (A.toNat : ℤ)=A := Int.toNat_of_nonneg hA.le
  let f : ℤ × ℤ → ℤ × ℤ := fun p => (2*A*p.1+B*p.2,p.2)
  have hi : Function.Injective f := by
    intro p q he
    have h0 := congrArg Prod.fst he
    have h1 := congrArg Prod.snd he
    change p.2=q.2 at h1
    dsimp [f] at h0
    rw [h1] at h0
    apply Prod.ext _ h1
    have heq : (2*A)*p.1=(2*A)*q.1 := by omega
    exact mul_left_cancel₀ (by omega : 2*A ≠ 0) heq
  have hnorm (p : ℤ × ℤ) (hp : p ∈ S.image f) :
      p.1^2+(d : ℤ)*p.2^2=((4*A.toNat*n : ℕ) : ℤ) := by
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    push_cast
    rw [hAc,hdc]
    change (2*A*q.1+B*q.2)^2+(4*A*C-B^2)*q.2^2=4*A*(n : ℤ)
    calc
      _ = 4*A*value A B C q := by dsimp [value]; ring
      _ = _ := by rw [hS q hq]
  have htarget : 0 < 4*A.toNat*n := by
    have hat : 0 < A.toNat := by omega
    positivity
  have hb := signed_norm_fiber_bound d (4*A.toNat*n) hd htarget (S.image f) hnorm
  rwa [Finset.card_image_of_injective _ hi] at hb

lemma value_scale (A B C g x y : ℤ) :
    value A B C (g*x,g*y)=g^2*value A B C (x,y) := by
  dsimp [value]
  ring

private def basisValue (A B C : ℤ) (u v : ℤ × ℤ) : ℤ :=
  2*A*u.1*v.1+B*(u.1*v.2+u.2*v.1)+2*C*u.2*v.2

lemma value_basis (A B C : ℤ) (u v : ℤ × ℤ) (r s : ℤ) :
    value A B C (u.1*r+v.1*s,u.2*r+v.2*s)=
      value (value A B C u) (basisValue A B C u v) (value A B C v) (r,s) := by
  dsimp [value,basisValue]
  ring

lemma discriminant_basis (A B C : ℤ) (u v : ℤ × ℤ) :
    4*value A B C u*value A B C v-(basisValue A B C u v)^2=
      (4*A*C-B^2)*(u.1*v.2-u.2*v.1)^2 := by
  dsimp [value,basisValue]
  ring

/-- Uniformity is obtained by using the primitive part of one represented
vector as the first basis vector. Its new leading coefficient divides `n`. -/
theorem quadratic_fiber_divisor_bound (A B C : ℤ)
    (hD : 0 < 4*A*C-B^2) (n : ℕ) (hn : 0 < n) (S : Finset (ℤ × ℤ))
    (hS : ∀ p ∈ S, value A B C p=(n : ℤ)) :
    S.card ≤ 16*(4*n^2).divisors.card^2 := by
  classical
  by_cases he : S.Nonempty
  swap
  · simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.zero_le]
  obtain ⟨p,hp⟩ := he
  have hpN := hS p hp
  have hp0 : p.1 ≠ 0 ∨ p.2 ≠ 0 := by
    by_contra h
    push_neg at h
    simp [value,h.1,h.2] at hpN
    omega
  have hg : 0 < p.1.gcd p.2 := hp0.elim
    (Int.gcd_pos_of_ne_zero_left p.2) (Int.gcd_pos_of_ne_zero_right p.1)
  obtain ⟨x,y,hprim,hx,hy⟩ := Int.exists_gcd_one hg
  let u : ℤ × ℤ := (x,y)
  let v : ℤ × ℤ := (-x.gcdB y,x.gcdA y)
  have hdet : u.1*v.2-u.2*v.1=1 := by
    have h := Int.gcd_eq_gcd_ab x y
    rw [hprim,Nat.cast_one] at h
    dsimp [u,v]
    nlinarith
  let a := value A B C u
  let b := basisValue A B C u v
  let c := value A B C v
  have han : ((p.1.gcd p.2 : ℕ) : ℤ)^2*a=(n : ℤ) := by
    let g : ℤ := (p.1.gcd p.2 : ℕ)
    have hcoords : p=(g*x,g*y) := Prod.ext (by simpa only [mul_comm] using hx)
      (by simpa only [mul_comm] using hy)
    rw [hcoords,value_scale] at hpN
    exact hpN
  have hgp : (0 : ℤ) < ((p.1.gcd p.2 : ℕ) : ℤ)^2 := by positivity
  have ha : 0 < a := by
    have hnz : (0 : ℤ) < n := by exact_mod_cast hn
    exact (mul_pos_iff_of_pos_left hgp).mp (han ▸ hnz)
  have hac : (a.toNat : ℤ)=a := Int.toNat_of_nonneg ha.le
  have hadvd : a.toNat ∣ n := by
    apply Int.natCast_dvd_natCast.mp
    rw [hac,← han]
    exact dvd_mul_left _ _
  have hdisc : 0 < 4*a*c-b^2 := by
    dsimp [a,b,c]
    rw [discriminant_basis,hdet]
    simpa using hD
  let f : ℤ × ℤ → ℤ × ℤ := fun q =>
    (v.2*q.1-v.1*q.2,-u.2*q.1+u.1*q.2)
  have hback (q : ℤ × ℤ) :
      (u.1*(f q).1+v.1*(f q).2,u.2*(f q).1+v.2*(f q).2)=q := by
    apply Prod.ext <;> dsimp [f]
    · linear_combination q.1*hdet
    · linear_combination q.2*hdet
  have hi : Function.Injective f := by
    intro q r he
    have hh := congrArg (fun w : ℤ × ℤ =>
      (u.1*w.1+v.1*w.2,u.2*w.1+v.2*w.2)) he
    simpa only [hback] using hh
  have hf (q : ℤ × ℤ) (hq : q ∈ S.image f) : value a b c q=(n : ℤ) := by
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
    rw [← value_basis,hback]
    exact hS r hr
  have hb := fiber_bound_with_leading a b c ha hdisc n hn (S.image f) hf
  rw [Finset.card_image_of_injective _ hi] at hb
  have hdiv : 4*a.toNat*n ∣ 4*n^2 := by
    convert Nat.mul_dvd_mul_left (4*n) hadvd using 1 <;> ring
  have hc : (4*a.toNat*n).divisors.card ≤ (4*n^2).divisors.card :=
    Finset.card_le_card (Nat.divisors_subset_of_dvd (by positivity) hdiv)
  exact hb.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hc 2))

/-- A single subpolynomial constant works for all three coefficients, including
arbitrarily large mixed coefficients and arbitrary integral coordinates. -/
theorem quadratic_fibers_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ A B C : ℤ, 0 < 4*A*C-B^2 →
      ∀ n : ℕ, 0 < n → ∀ S : Finset (ℤ × ℤ),
      (∀ p ∈ S, value A B C p=(n : ℤ)) →
      (S.card : ℝ) ≤ K*(n : ℝ)^ε := by
  obtain ⟨K,hK,hdiv⟩ := divisor_count_subpolynomial (ε/4) (by linarith)
  refine ⟨16*K^2*(4 : ℝ)^(ε/2),by positivity,?_⟩
  intro A B C hD n hn S hS
  have hn4 : 0 < 4*n^2 := by positivity
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (((4*n^2 : ℕ) : ℝ)^(ε/4))^2=(4 : ℝ)^(ε/2)*(n : ℝ)^ε := by
    rw [pow_two,← Real.rpow_add (by exact_mod_cast hn4)]
    rw [show ε/4+ε/4=ε/2 by ring]
    push_cast
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity),
      ← Real.rpow_natCast_mul hnr.le]
    congr 1
    congr 1
    push_cast
    ring
  calc
    (S.card : ℝ) ≤ 16*((4*n^2).divisors.card : ℝ)^2 := by
      exact_mod_cast quadratic_fiber_divisor_bound A B C hD n hn S hS
    _ ≤ 16*(K*(((4*n^2 : ℕ) : ℝ)^(ε/4)))^2 := by
      gcongr
      exact hdiv (4*n^2) hn4
    _ = (16*K^2*(4 : ℝ)^(ε/2))*(n : ℝ)^ε := by rw [mul_pow,hp]; ring

/-- The union of all positive fibers dividing a common scale is also uniform
in every coefficient. -/
theorem quadratic_divisor_fibers_bound (A B C : ℤ)
    (hD : 0 < 4*A*C-B^2) (L : ℕ) (hL : 0 < L) (S : Finset (ℤ × ℤ))
    (hpos : ∀ p ∈ S, 0 < value A B C p)
    (hdvd : ∀ p ∈ S, (value A B C p).toNat ∣ L) :
    S.card ≤ L.divisors.card*(16*(4*L^2).divisors.card^2) := by
  classical
  let v : ℤ × ℤ → ℕ := fun p => (value A B C p).toNat
  let I := S.image v
  have hsub : I ⊆ L.divisors := by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    exact Nat.mem_divisors.mpr ⟨hdvd p hp,hL.ne'⟩
  have hfib (n : ℕ) (hn : n ∈ I) :
      (S.filter (fun p => v p=n)).card ≤ 16*(4*L^2).divisors.card^2 := by
    have hnL := Nat.mem_divisors.mp (hsub hn)
    have hnpos : 0 < n := Nat.pos_of_mem_divisors (hsub hn)
    have hb := quadratic_fiber_divisor_bound A B C hD n hnpos
      (S.filter (fun p => v p=n)) (by
        intro p hp
        obtain ⟨hpS,hpv⟩ := Finset.mem_filter.mp hp
        have hc := Int.toNat_of_nonneg (hpos p hpS).le
        change ((v p : ℕ) : ℤ)=value A B C p at hc
        rw [hpv] at hc
        exact hc.symm)
    have hi : (4*n^2).divisors.card ≤ (4*L^2).divisors.card :=
      Finset.card_le_card (Nat.divisors_subset_of_dvd (by positivity)
        (Nat.mul_dvd_mul_left 4 (pow_dvd_pow_of_dvd hnL.1 2)))
    exact hb.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hi 2))
  calc
    S.card = ∑ n ∈ I, (S.filter (fun p => v p=n)).card :=
      Finset.card_eq_sum_card_image v S
    _ ≤ ∑ _n ∈ I, 16*(4*L^2).divisors.card^2 := Finset.sum_le_sum hfib
    _ = I.card*(16*(4*L^2).divisors.card^2) := by simp
    _ ≤ L.divisors.card*(16*(4*L^2).divisors.card^2) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
  exact le_rfl

/-- Uniform subpolynomiality, even when the entire quadratic form is chosen
as a function of the represented scale. -/
theorem quadratic_divisor_fibers_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ A B C : ℤ, 0 < 4*A*C-B^2 →
      ∀ L : ℕ, 0 < L → ∀ S : Finset (ℤ × ℤ),
      (∀ p ∈ S, 0 < value A B C p) →
      (∀ p ∈ S, (value A B C p).toNat ∣ L) →
      (S.card : ℝ) ≤ K*(L : ℝ)^ε := by
  obtain ⟨K,hK,hdiv⟩ := divisor_count_subpolynomial (ε/5) (by linarith)
  refine ⟨16*K^3*((4 : ℝ)^(ε/5))^2,by positivity,?_⟩
  intro A B C hD L hL S hpos hdvd
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hbL := hdiv L hL
  have hb4 := hdiv (4*L^2) (by positivity)
  have he : (((4*L^2 : ℕ) : ℝ)^(ε/5))=(4 : ℝ)^(ε/5)*(L : ℝ)^(2*ε/5) := by
    push_cast
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity),
      ← Real.rpow_natCast_mul hLr.le]
    congr 1
    congr 1
    push_cast
    ring
  rw [he] at hb4
  have hp : (L : ℝ)^(ε/5)*((L : ℝ)^(2*ε/5))^2=(L : ℝ)^ε := by
    rw [pow_two,← Real.rpow_add hLr,← Real.rpow_add hLr]
    congr 1
    ring
  calc
    (S.card : ℝ) ≤ (L.divisors.card : ℝ)*(16*((4*L^2).divisors.card : ℝ)^2) := by
      exact_mod_cast quadratic_divisor_fibers_bound A B C hD L hL S hpos hdvd
    _ ≤ (K*(L : ℝ)^(ε/5))*(16*(K*((4 : ℝ)^(ε/5)*(L : ℝ)^(2*ε/5)))^2) := by
      gcongr
    _ = (16*K^3*((4 : ℝ)^(ε/5))^2)*(L : ℝ)^ε := by
      calc
        _ = (16*K^3*((4 : ℝ)^(ε/5))^2)*
            ((L : ℝ)^(ε/5)*((L : ℝ)^(2*ε/5))^2) := by ring
        _ = _ := by rw [hp]

/-- Allow both the form and its common divisor scale to vary with `n`.
No restriction at all is imposed on the coefficient heights. -/
theorem varying_quadratic_scale_bound (D H : ℕ) (hH : 0 < H) (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ n L : ℕ, 0 < n → 0 < L → L ≤ H*n^D →
      ∀ A B C : ℤ, 0 < 4*A*C-B^2 → ∀ S : Finset (ℤ × ℤ),
      (∀ p ∈ S, 0 < value A B C p) →
      (∀ p ∈ S, (value A B C p).toNat ∣ L) →
      (S.card : ℝ) ≤ K*(n : ℝ)^ε := by
  let δ : ℝ := ε/((D : ℝ)+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K,hK,hbound⟩ := quadratic_divisor_fibers_subpolynomial δ hδ
  refine ⟨K*(H : ℝ)^δ,by positivity,?_⟩
  intro n L hn hL hLH A B C hD S hpos hdvd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he : (D : ℝ)*δ ≤ ε := by
    have hcancel : δ*((D : ℝ)+1)=ε := div_mul_cancel₀ _ (by positivity)
    nlinarith [hδ]
  calc
    (S.card : ℝ) ≤ K*(L : ℝ)^δ := hbound A B C hD L hL S hpos hdvd
    _ ≤ K*((H : ℝ)*(n : ℝ)^D)^δ := by
      apply mul_le_mul_of_nonneg_left _ hK.le
      apply Real.rpow_le_rpow (Nat.cast_nonneg L) _ hδ.le
      exact_mod_cast hLH
    _ = (K*(H : ℝ)^δ)*(n : ℝ)^((D : ℝ)*δ) := by
      rw [Real.mul_rpow (Nat.cast_nonneg H) (by positivity),
        ← Real.rpow_natCast_mul (Nat.cast_nonneg n)]
      ring
    _ ≤ (K*(H : ℝ)^δ)*(n : ℝ)^ε :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 he) (by positivity)

end Erdos322Research.UniformPositiveQuadratic
