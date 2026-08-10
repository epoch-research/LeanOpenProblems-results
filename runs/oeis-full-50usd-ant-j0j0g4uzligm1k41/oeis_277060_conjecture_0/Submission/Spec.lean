import FormalConjectures.Util.ProblemImports
open Finset
def A277060 (n : ℕ) : ℕ :=
  (Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k * Nat.choose (n + k) (k + 1)) ^ 2) / 2
noncomputable def bb (p k : ℕ) : ℕ := (p-1).choose k * (p-1+k).choose (k+1)

theorem prod_form {R : Type*} [CommRing R] (p : R) {ι : Type*} (s : Finset ι) (a : ι → R) :
    ∃ G : R, ∏ i ∈ s, (1 + p * a i) = 1 + p * (∑ i ∈ s, a i) + p^2 * G := by
  classical
  refine Finset.induction_on s ⟨0, by simp⟩ ?_
  rintro j t hj ⟨G, hG⟩
  refine ⟨G + a j * (∑ i ∈ t, a i) + p * a j * G, ?_⟩
  rw [Finset.prod_insert hj, Finset.sum_insert hj, hG]; ring

theorem prod_form_ps {R : Type*} [CommRing R] (e : R) {ι : Type*} (s : Finset ι) (a : ι → R) :
    ∃ G : R, (6:R) * ∏ i ∈ s, (1 + e * a i)
      = 6 + 6*e*(∑ i ∈ s, a i)
        + 3*e^2*((∑ i ∈ s, a i)^2 - (∑ i ∈ s, (a i)^2))
        + e^3*((∑ i ∈ s, a i)^3 - 3*(∑ i ∈ s, a i)*(∑ i ∈ s, (a i)^2) + 2*(∑ i ∈ s, (a i)^3))
        + e^4 * G := by
  classical
  refine Finset.induction_on s ⟨0, by norm_num⟩ ?_
  rintro j t hj ⟨G, hG⟩
  refine ⟨a j*((∑ i ∈ t, a i)^3 - 3*(∑ i ∈ t, a i)*(∑ i ∈ t, (a i)^2) + 2*(∑ i ∈ t, (a i)^3))
    + (1+e*a j)*G, ?_⟩
  rw [Finset.prod_insert hj]
  rw [show (6:R)*((1+e*a j)*∏ i ∈ t, (1+e*a i)) = (1+e*a j)*(6*∏ i ∈ t, (1+e*a i)) by ring, hG]
  rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj]
  ring

def gg {R : Type*} [CommRing R] (e x y z : R) : R :=
  6 + 6*e*x + 3*e^2*(x^2-y) + e^3*(x^3-3*x*y+2*z)

theorem prod_form_gg {R : Type*} [CommRing R] (e : R) {ι : Type*} (s : Finset ι) (a : ι → R) :
    ∃ G : R, (6:R) * ∏ i ∈ s, (1 + e * a i)
      = gg e (∑ i ∈ s, a i) (∑ i ∈ s, (a i)^2) (∑ i ∈ s, (a i)^3) + e^4 * G := by
  obtain ⟨G, hG⟩ := prod_form_ps e s a
  exact ⟨G, by rw [hG]; unfold gg; ring⟩


section
variable {p : ℕ} [Fact p.Prime]
instance neze : NeZero (p^4) := ⟨by have := (Fact.out : p.Prime).pos; positivity⟩
theorem isUnit_cast_ndvd {m : ℕ} (h : ¬ p ∣ m) : IsUnit ((m:ℕ) : ZMod (p^4)) := by
  apply (ZMod.isUnit_iff_coprime m (p^4)).mpr
  exact (Nat.Coprime.pow_right 4 (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr h).symm))
theorem sum_zmod_eq_sum_range {M : Type*} [AddCommMonoid M]
    (f : ZMod p → M) : ∑ x : ZMod p, f x = ∑ i ∈ range p, f (i : ZMod p) := by
  rw [Finset.sum_range fun i => f (i : ZMod p)]
  have he : Function.Bijective (fun i : Fin p => ((i : ℕ) : ZMod p)) := by
    refine ⟨fun a b hab => ?_, fun x => ⟨⟨x.val, ZMod.val_lt x⟩, by simp [ZMod.natCast_val, ZMod.cast_id]⟩⟩
    have := congrArg ZMod.val hab
    rwa [ZMod.val_cast_of_lt a.2, ZMod.val_cast_of_lt b.2, Fin.val_inj] at this
  exact (Fintype.sum_bijective _ he (fun i => f (i : ZMod p)) f (fun x => rfl)).symm

theorem sum_inv_pow_zero {k : ℕ} (hk : k < p - 1) :
    ∑ i ∈ range p, ((i : ZMod p)⁻¹) ^ k = 0 := by
  rw [← sum_zmod_eq_sum_range (fun x => x⁻¹ ^ k)]
  have hbij : Function.Bijective (fun x : ZMod p => x⁻¹) :=
    Function.Involutive.bijective inv_inv
  rw [Fintype.sum_bijective _ hbij (fun x => x⁻¹ ^ k) (fun x => x ^ k) (fun x => rfl)]
  have h := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) k
  rw [ZMod.card] at h
  exact h hk

noncomputable def redp : ZMod (p^4) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (show (4:ℕ) ≠ 0 by norm_num)) (ZMod p)

theorem redp_sum_inv_pow (k : ℕ) :
    redp (p:=p) (∑ i ∈ range p, ((i:ZMod (p^4))⁻¹)^k) = ∑ i ∈ range p, ((i:ZMod p)⁻¹)^k := by
  rw [map_sum]; refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [map_pow]; congr 1
  rw [mem_range] at hi
  rcases Nat.eq_zero_or_pos i with h|h
  · subst h; rw [Nat.cast_zero, ZMod.inv_zero, map_zero, Nat.cast_zero, ZMod.inv_zero]
  · have hu : IsUnit ((i:ZMod (p^4))) := by
      have : ((i:ZMod (p^4))) = ((i:ℕ):ZMod (p^4)) := by norm_cast
      rw [this]; exact isUnit_cast_ndvd (fun hd => absurd (Nat.le_of_dvd h hd) (by omega))
    have haa : (i:ZMod (p^4)) * (i:ZMod (p^4))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
    have hc := congrArg (redp (p:=p)) haa
    rw [map_mul, map_one, map_natCast] at hc
    exact (inv_eq_of_mul_eq_one_right hc).symm

theorem e3_kill (x : ZMod (p^4)) (hx : (x.val : ZMod p) = 0) :
    (p:ZMod (p^4))^3 * x = 0 := by
  obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff x.val p).mp hx
  have hx2 : x = (p:ZMod (p^4)) * (t:ZMod (p^4)) := by
    have hid : ((x.val:ℕ):ZMod (p^4)) = x := by rw [ZMod.natCast_val, ZMod.cast_id]
    rw [← hid, ht]; push_cast; ring
  have hp4 : (p:ZMod (p^4))^4 = 0 := by
    rw [show (p:ZMod (p^4))^4 = ((p^4:ℕ):ZMod (p^4)) by push_cast; ring, ZMod.natCast_self]
  rw [hx2]; linear_combination (t:ZMod (p^4)) * hp4

theorem e3_kill_sum {k : ℕ} (hk : k < p - 1) :
    (p:ZMod (p^4))^3 * (∑ i ∈ range p, ((i:ZMod (p^4))⁻¹)^k) = 0 := by
  apply e3_kill
  have h0 : redp (p:=p) (∑ i ∈ range p, ((i:ZMod (p^4))⁻¹)^k) = 0 := by
    rw [redp_sum_inv_pow]; exact sum_inv_pow_zero hk
  rw [redp, ZMod.castHom_apply, ZMod.cast_eq_val] at h0
  exact h0

theorem fact_prod (k : ℕ) : (Nat.factorial k : ZMod (p^4)) = ∏ i ∈ range k, ((i:ZMod (p^4)) + 1) := by
  induction k with
  | zero => simp
  | succ n ih => rw [Finset.prod_range_succ, ← ih, Nat.factorial_succ]; push_cast; ring
theorem cast_choose_prod (N k : ℕ) :
    (N.choose k : ZMod (p^4)) * (Nat.factorial k : ZMod (p^4)) = ∏ i ∈ range k, ((N - i : ℕ) : ZMod (p^4)) := by
  have h : ((N.descFactorial k : ℕ) : ZMod (p^4)) = (Nat.factorial k : ZMod (p^4)) * (N.choose k : ZMod (p^4)) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod (p^4)) (Nat.descFactorial_eq_factorial_mul_choose N k)
  have h2 : ((N.descFactorial k : ℕ) : ZMod (p^4)) = ∏ i ∈ range k, ((N - i : ℕ) : ZMod (p^4)) := by
    rw [Nat.descFactorial_eq_prod_range]; push_cast [Nat.cast_prod]; rfl
  rw [← h2, h]; ring
theorem choose_pm1_prod (k : ℕ) (hk : k ≤ p - 1) :
    ((p-1).choose k : ZMod (p^4)) = (-1)^k * ∏ i ∈ range k, (1 - (p:ZMod (p^4)) * ((i:ZMod (p^4))+1)⁻¹) := by
  have hpp : 1 ≤ p := (Fact.out (p := p.Prime)).one_lt.le
  set R := ZMod (p^4)
  have hunit : IsUnit ((Nat.factorial k : ℕ) : R) := by
    apply isUnit_cast_ndvd; intro hd
    have : p ≤ k := (Nat.Prime.dvd_factorial (Fact.out : p.Prime)).mp hd; omega
  have perfac : ∀ i ∈ range k, (((p-1-i : ℕ)) : R) = (-1) * ((i:R)+1) * (1 - (p:R) * ((i:R)+1)⁻¹) := by
    intro i hi; rw [mem_range] at hi
    have hu : IsUnit ((i:R)+1) := by
      have he : ((i:R)+1) = ((i+1:ℕ):R) := by push_cast; ring
      rw [he]; exact isUnit_cast_ndvd (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega))
    have hmul : ((i:R)+1) * ((i:R)+1)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
    have hcast : (((p-1-i : ℕ)) : R) = (p:R)-1-(i:R) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub hpp]; push_cast; ring
    rw [hcast]; linear_combination (-(p:R)) * hmul
  have hprod : ∏ i ∈ range k, (((p-1-i : ℕ)) : R) =
      (-1)^k * (∏ i ∈ range k, ((i:R)+1)) * ∏ i ∈ range k, (1 - (p:R) * ((i:R)+1)⁻¹) := by
    rw [Finset.prod_congr rfl perfac]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have key := cast_choose_prod (p := p) (p-1) k
  rw [hprod, ← fact_prod k] at key
  have key2 : (Nat.factorial k : R) * ((p-1).choose k : R)
      = (Nat.factorial k : R) * ((-1)^k * ∏ i ∈ range k, (1 - (p:R) * ((i:R)+1)⁻¹)) := by
    linear_combination key
  exact (hunit.mul_right_inj).mp key2
theorem choose_pm1k_prod (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ p - 2) :
    ((p-1+k).choose (k+1) : ZMod (p^4)) = (p:ZMod (p^4)) * ((p:ZMod (p^4))-1) *
      ((k:ZMod (p^4))*((k:ZMod (p^4))+1))⁻¹ * ∏ i ∈ range (k-1), (1 + (p:ZMod (p^4))*((i:ZMod (p^4))+1)⁻¹) := by
  set R := ZMod (p^4)
  have hpp : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hasc : ((p-1+k).choose (k+1) : R) * (Nat.factorial (k+1) : R) = ∏ i ∈ range (k+1), (((p-1+i:ℕ)) : R) := by
    have h1 : (p-1).ascFactorial (k+1) = Nat.factorial (k+1) * (p-1+k).choose (k+1) := by
      have := Nat.ascFactorial_eq_factorial_mul_choose' (p-1) (k+1)
      rwa [show p-1+(k+1)-1 = p-1+k by omega] at this
    have h2 : ((p-1).ascFactorial (k+1) : R) = ∏ i ∈ range (k+1), (((p-1+i:ℕ)) : R) := by
      rw [Nat.ascFactorial_eq_prod_range]; push_cast [Nat.cast_prod]; rfl
    rw [← h2]; rw [show ((p-1).ascFactorial (k+1):R) = ((Nat.factorial (k+1) * (p-1+k).choose (k+1) : ℕ):R) from by rw[h1]]; push_cast; ring
  have split : ∏ i ∈ range (k+1), (((p-1+i:ℕ)) : R)
      = ((p-1:ℕ):R) * ((p:ℕ):R) * ∏ i ∈ range (k-1), (((p+1+i:ℕ)) : R) := by
    rw [Finset.prod_range_succ' (fun i => (((p-1+i:ℕ)) : R)) k]
    have hk' : k = (k-1)+1 := by omega
    rw [hk', Finset.prod_range_succ' (fun i => (((p-1+(i+1):ℕ)) : R)) (k-1)]
    have e1 : ∀ i, (((p-1+((i+1)+1):ℕ)) : R) = (((p+1+i:ℕ)) : R) := by
      intro i; have : p-1+((i+1)+1) = p+1+i := by omega
      rw [this]
    rw [Finset.prod_congr rfl (fun i _ => e1 i)]
    have e2 : (((p-1+0:ℕ)) : R) = ((p-1:ℕ):R) := by norm_num
    have e3 : (((p-1+(0+1):ℕ)) : R) = ((p:ℕ):R) := by
      have : p-1+(0+1) = p := by omega
      rw [this]
    have er : k-1+1-1 = k-1 := by omega
    rw [er, e2, e3]; ring
  have factor : ∏ i ∈ range (k-1), (((p+1+i:ℕ)) : R)
      = ((Nat.factorial (k-1) : ℕ):R) * ∏ i ∈ range (k-1), (1 + (p:R)*((i:R)+1)⁻¹) := by
    rw [fact_prod (k-1), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [mem_range] at hi
    have hu : IsUnit ((i:R)+1) := by
      have he : ((i:R)+1) = ((i+1:ℕ):R) := by push_cast; ring
      rw [he]; exact isUnit_cast_ndvd (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega))
    have hmul : ((i:R)+1) * ((i:R)+1)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
    have hcast : (((p+1+i:ℕ)) : R) = (p:R)+1+(i:R) := by push_cast; ring
    rw [hcast]; linear_combination (-(p:R)) * hmul
  have hfac : IsUnit ((Nat.factorial (k+1):ℕ):R) :=
    isUnit_cast_ndvd (fun hd => by
      have := (Nat.Prime.dvd_factorial (Fact.out : p.Prime)).mp hd; omega)
  have hf2 : Nat.factorial k = k * Nat.factorial (k-1) := by
    conv_lhs => rw [show k = (k-1)+1 by omega]
    rw [Nat.factorial_succ]; congr 1; omega
  have hfact_rel : ((Nat.factorial (k+1):ℕ):R)
      = ((k:R)+1)*(k:R)*((Nat.factorial (k-1):ℕ):R) := by
    rw [Nat.factorial_succ k, hf2]; push_cast; ring
  have hkk_unit : IsUnit ((k:R)*((k:R)+1)) := by
    have hka : ((k:R)*((k:R)+1)) = ((k*(k+1):ℕ):R) := by push_cast; ring
    rw [hka]; exact isUnit_cast_ndvd (fun hd => by
      rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp hd with h | h
      · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
      · exact absurd (Nat.le_of_dvd (by omega) h) (by omega))
  have hkk : ((k:R)*((k:R)+1)) * ((k:R)*((k:R)+1))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hkk_unit
  have hpm1 : ((p-1:ℕ):R) = (p:R)-1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hcancel := hasc
  rw [split, factor] at hcancel
  refine (hfac.mul_left_inj).mp ?_
  rw [hcancel, hfact_rel, hpm1]
  linear_combination (-(∏ i ∈ range (k-1), (1 + (p:R)*((i:R)+1)⁻¹)) *
    ((Nat.factorial (k-1):ℕ):R) * (p:R) * ((p:R)-1)) * hkk
theorem phi_form (k : ℕ) (hk1 : 1 ≤ k) :
    ∃ G : ZMod (p^4), (∏ i ∈ range k, (1 - (p:ZMod (p^4))*((i:ZMod (p^4))+1)⁻¹)) *
      (∏ i ∈ range (k-1), (1 + (p:ZMod (p^4))*((i:ZMod (p^4))+1)⁻¹))
      = 1 - (p:ZMod (p^4))*(k:ZMod (p^4))⁻¹ + (p:ZMod (p^4))^2 * G := by
  set R := ZMod (p^4)
  set e := (p:R)
  obtain ⟨G1, h1⟩ := prod_form e (range k) (fun i => -((i:R)+1)⁻¹)
  obtain ⟨G2, h2⟩ := prod_form e (range (k-1)) (fun i => ((i:R)+1)⁻¹)
  have e1 : (∏ i ∈ range k, (1 - e*((i:R)+1)⁻¹)) = ∏ i ∈ range k, (1 + e*(-((i:R)+1)⁻¹)) :=
    Finset.prod_congr rfl (fun i _ => by ring)
  have hc : (((k-1:ℕ)):R)+1 = (k:R) := by rw [Nat.cast_sub hk1, Nat.cast_one]; ring
  have hsplit : (∑ i ∈ range k, ((i:R)+1)⁻¹)
      = (∑ i ∈ range (k-1), ((i:R)+1)⁻¹) + (k:R)⁻¹ := by
    conv_lhs => rw [show k = (k-1)+1 by omega]
    rw [Finset.sum_range_succ, hc]
  have hS : (∑ i ∈ range k, -((i:R)+1)⁻¹) + (∑ i ∈ range (k-1), ((i:R)+1)⁻¹) = -(k:R)⁻¹ := by
    rw [Finset.sum_neg_distrib, hsplit]; ring
  refine ⟨G1+G2+(∑ i ∈ range k, -((i:R)+1)⁻¹)*(∑ i ∈ range (k-1), ((i:R)+1)⁻¹)
    + e*((∑ i ∈ range k, -((i:R)+1)⁻¹)*G2+(∑ i ∈ range (k-1), ((i:R)+1)⁻¹)*G1)
    + e^2*G1*G2, ?_⟩
  rw [e1, h1, h2]; linear_combination e * hS

theorem term_mid (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ p - 2) :
    ((bb p k : ℕ) : ZMod (p^4))^2 =
      (p:ZMod (p^4))^2*(((k:ZMod (p^4))*((k:ZMod (p^4))+1))⁻¹)^2
      - 2*(p:ZMod (p^4))^3*(((k:ZMod (p^4))*((k:ZMod (p^4))+1))⁻¹)^2
      - 2*(p:ZMod (p^4))^3*(((k:ZMod (p^4))*((k:ZMod (p^4))+1))⁻¹)^2*(k:ZMod (p^4))⁻¹ := by
  set R := ZMod (p^4)
  obtain ⟨G, hG⟩ := phi_form (p:=p) k hk1
  set e := (p:R) with he
  set c := ((k:R)*((k:R)+1))⁻¹ with hcdef
  set ki := (k:R)⁻¹ with hkidef
  have hp4 : e^4 = 0 := by
    rw [show e^4 = ((p^4:ℕ):R) by push_cast; ring, ZMod.natCast_self]
  have hbb : (bb p k : R) = (-1)^k * e * (e-1) * c *
      ((∏ i ∈ range k, (1-e*((i:R)+1)⁻¹)) * ∏ i ∈ range (k-1), (1+e*((i:R)+1)⁻¹)) := by
    show ((((p-1).choose k * (p-1+k).choose (k+1) : ℕ)) : R) = _
    push_cast
    rw [choose_pm1_prod (p:=p) k (by omega), choose_pm1k_prod (p:=p) k hk1 hk]
    ring
  set s := (-1:R)^k with hs
  have hsgn : s^2 = 1 := by rw [hs, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hid : e^2*(e-1)^2*(1-e*ki+e^2*G)^2 = e^2 - 2*e^3 - 2*e^3*ki := by
    linear_combination (G^2*e^4 - 2*G^2*e^3 + G^2*e^2 - 2*G*e^3*ki + 4*G*e^2*ki + 2*G*e^2
      - 2*G*e*ki - 4*G*e + 2*G + e^2*ki^2 - 2*e*ki^2 - 2*e*ki + ki^2 + 4*ki + 1) * hp4
  have hsq : (bb p k : R)^2 = c^2 * (e^2*(e-1)^2*
      ((∏ i ∈ range k, (1-e*((i:R)+1)⁻¹)) * ∏ i ∈ range (k-1), (1+e*((i:R)+1)⁻¹))^2) := by
    rw [hbb]
    have hexp : (s*e*(e-1)*c*((∏ i ∈ range k, (1-e*((i:R)+1)⁻¹)) * ∏ i ∈ range (k-1), (1+e*((i:R)+1)⁻¹)))^2
        = s^2*(c^2*(e^2*(e-1)^2*((∏ i ∈ range k, (1-e*((i:R)+1)⁻¹)) * ∏ i ∈ range (k-1), (1+e*((i:R)+1)⁻¹))^2)) := by ring
    rw [hexp, hsgn, one_mul]
  rw [hsq, hG, hid]; ring

theorem last_prod (hp5 : 5 ≤ p) :
    ((bb p (p-1)):ZMod (p^4)) = ∏ i ∈ range (p-2), (1+(p:ZMod (p^4))*((i:ZMod (p^4))+1)⁻¹) := by
  set R := ZMod (p^4)
  set e := (p:R) with he
  have hbbnat : bb p (p-1) = (2*p-2).choose p := by
    unfold bb; rw [Nat.choose_self, one_mul]; congr 1 <;> omega
  have hNat : (2*p-2).choose p * (p-2).factorial = (p+1).ascFactorial (p-2) := by
    rw [Nat.ascFactorial_eq_factorial_mul_choose', show (p+1)+(p-2)-1 = 2*p-2 by omega,
        ← Nat.choose_symm (show p ≤ 2*p-2 by omega), show 2*p-2-p = p-2 by omega]
    ring
  have hcast : ((2*p-2).choose p : R) * ((p-2).factorial : R) = ∏ i ∈ range (p-2), (((p+1+i:ℕ)):R) := by
    have hh := congrArg (Nat.cast : ℕ → R) hNat
    rw [Nat.cast_mul] at hh
    rw [hh, Nat.ascFactorial_eq_prod_range]; push_cast [Nat.cast_prod]; rfl
  have factor : ∏ i ∈ range (p-2), (((p+1+i:ℕ)):R)
      = ((p-2).factorial:R)*∏ i ∈ range (p-2), (1+e*((i:R)+1)⁻¹) := by
    rw [fact_prod (p-2), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [mem_range] at hi
    have hu : IsUnit ((i:R)+1) := by
      have hee : ((i:R)+1) = ((i+1:ℕ):R) := by push_cast; ring
      rw [hee]; exact isUnit_cast_ndvd (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega))
    have hmul : ((i:R)+1)*((i:R)+1)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
    have hcc : (((p+1+i:ℕ)):R) = e+1+(i:R) := by rw [he]; push_cast; ring
    rw [hcc]; linear_combination (-e) * hmul
  have hfu : IsUnit (((p-2).factorial:ℕ):R) := isUnit_cast_ndvd (fun hd => by
     have := (Nat.Prime.dvd_factorial (Fact.out:p.Prime)).mp hd; omega)
  rw [factor] at hcast
  rw [hbbnat]
  refine (hfu.mul_left_inj).mp ?_
  rw [hcast]; ring

theorem reH {k : ℕ} (hk : 1 ≤ k) :
    (∑ i ∈ range p, ((i:ZMod (p^4))⁻¹)^k) = ∑ i ∈ range (p-1), (((i:ZMod (p^4))+1)⁻¹)^k := by
  have hpp : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  rw [show (range p:Finset ℕ) = range ((p-1)+1) by congr 1; omega, Finset.sum_range_succ']
  have h0 : (((0:ℕ):ZMod (p^4))⁻¹)^k = 0 := by rw [Nat.cast_zero, ZMod.inv_zero, zero_pow (by omega)]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show ((i+1:ℕ):ZMod (p^4)) = (i:ZMod (p^4))+1 by push_cast; ring]

theorem reHm (k : ℕ) :
    (∑ i ∈ range (p-1), (((i:ZMod (p^4))+1)⁻¹)^k)
      = (∑ i ∈ range (p-2), (((i:ZMod (p^4))+1)⁻¹)^k) + (((p-1:ℕ):ZMod (p^4))⁻¹)^k := by
  have hpp : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  rw [show (range (p-1):Finset ℕ) = range ((p-2)+1) by congr 1; omega, Finset.sum_range_succ]
  rw [show ((p-2:ℕ):ZMod (p^4))+1 = ((p-1:ℕ):ZMod (p^4)) by
    rw [show (p-1:ℕ) = (p-2)+1 by omega]; push_cast; ring]

theorem term_last (hp5 : 5 ≤ p) :
    ((bb p (p-1)):ZMod (p^4))^2
      = 1 - 2*(p:ZMod (p^4))*((p-1:ℕ):ZMod (p^4))⁻¹
        + (p:ZMod (p^4))^2*(3*(((p-1:ℕ):ZMod (p^4))⁻¹)^2 - 2*(∑ i ∈ range p,((i:ZMod (p^4))⁻¹)^2))
        + (p:ZMod (p^4))^3*(-4*(((p-1:ℕ):ZMod (p^4))⁻¹)^3
            + 4*((p-1:ℕ):ZMod (p^4))⁻¹*(∑ i ∈ range p,((i:ZMod (p^4))⁻¹)^2)) := by
  set R := ZMod (p^4)
  set e := (p:R) with he
  set v := ((p-1:ℕ):R)⁻¹ with hvdef
  set H2 := ∑ i ∈ range p,((i:R)⁻¹)^2 with hH2
  have hp4 : e^4 = 0 := by rw [show e^4=((p^4:ℕ):R) by push_cast;ring, ZMod.natCast_self]
  have hodd : Odd p := (Fact.out (p := p.Prime)).odd_of_ne_two (by omega)
  have hone : ∏ i ∈ range (p-1),(1-e*((i:R)+1)⁻¹) = 1 := by
    have hc := choose_pm1_prod (p:=p) (p-1) (le_refl _)
    rw [← he] at hc
    rw [Nat.choose_self, Nat.cast_one] at hc
    have hs : ((-1:R))^(p-1) = 1 := by
      apply Even.neg_one_pow; rcases hodd with ⟨m,hm⟩; exact ⟨m, by omega⟩
    rw [hs, one_mul] at hc; exact hc.symm
  obtain ⟨G1, hg1⟩ := prod_form_gg e (range (p-1)) (fun i => -((i:R)+1)⁻¹)
  obtain ⟨G2, hg2⟩ := prod_form_gg e (range (p-2)) (fun i => ((i:R)+1)⁻¹)
  have hp1 : (∏ i ∈ range (p-1), (1 + e * (-((i:R)+1)⁻¹))) = 1 := by
    rw [show (∏ i ∈ range (p-1), (1 + e * (-((i:R)+1)⁻¹))) = ∏ i ∈ range (p-1), (1 - e*((i:R)+1)⁻¹) from Finset.prod_congr rfl (fun i _ => by ring)]
    exact hone
  have hp2 : (∏ i ∈ range (p-2), (1 + e * ((i:R)+1)⁻¹)) = (bb p (p-1):R) := by
    have := last_prod (p:=p) hp5; rw [← he] at this; exact this.symm
  rw [hp1, mul_one] at hg1
  rw [hp2] at hg2
  set A1 := ∑ i ∈ range (p-1), -((i:R)+1)⁻¹ with hA1
  set A2 := ∑ i ∈ range (p-1), (-((i:R)+1)⁻¹)^2 with hA2
  set A3 := ∑ i ∈ range (p-1), (-((i:R)+1)⁻¹)^3 with hA3
  set B1 := ∑ i ∈ range (p-2), ((i:R)+1)⁻¹ with hB1
  set B2 := ∑ i ∈ range (p-2), (((i:R)+1)⁻¹)^2 with hB2
  set B3 := ∑ i ∈ range (p-2), (((i:R)+1)⁻¹)^3 with hB3
  have hgA : gg e A1 A2 A3 = 6 := by linear_combination -hg1 - G1*hp4
  have hgB : (6:R)*(bb p (p-1)) = gg e B1 B2 B3 := by linear_combination hg2 + G2*hp4
  -- value lemmas
  have hAsq : (∑ i ∈ range (p-1), (((i:R)+1)⁻¹)^2) = H2 := by rw [hH2]; exact (reH (p:=p) (by norm_num)).symm
  have hBsq : (∑ i ∈ range (p-2), (((i:R)+1)⁻¹)^2) = H2 - v^2 := by
    have hh := reHm (p:=p) 2; rw [hAsq] at hh; rw [hvdef]; linear_combination -hh
  have hv1 : A1 + B1 = -v := by
    rw [hA1, hB1, Finset.sum_neg_distrib]
    have hsp : (∑ i ∈ range (p-1), ((i:R)+1)⁻¹) = (∑ i ∈ range (p-2), ((i:R)+1)⁻¹) + v := by
      have hh := reHm (p:=p) 1
      simp only [pow_one] at hh; rw [hvdef]; linear_combination hh
    rw [hsp]; ring
  have hv2 : A2 + B2 = 2*H2 - v^2 := by
    rw [hA2, hB2]
    have hA2' : (∑ i ∈ range (p-1), (-((i:R)+1)⁻¹)^2) = ∑ i ∈ range (p-1), (((i:R)+1)⁻¹)^2 :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [hA2', hAsq, hBsq]; ring
  have hv3 : A3 + B3 = -v^3 := by
    rw [hA3, hB3]
    have hA3' : (∑ i ∈ range (p-1), (-((i:R)+1)⁻¹)^3) = -(∑ i ∈ range (p-1), (((i:R)+1)⁻¹)^3) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hA3']
    have hAcb : (∑ i ∈ range (p-1), (((i:R)+1)⁻¹)^3) = (∑ i ∈ range (p-2), (((i:R)+1)⁻¹)^3) + v^3 := by
      have hh := reHm (p:=p) 3; rw [hvdef]; linear_combination hh
    rw [hAcb]; ring
  have hprodid : gg e A1 A2 A3 * gg e B1 B2 B3
      = 6 * gg e (A1+B1) (A2+B2) (A3+B3) + e^4 * (A1^3*B1^3*e^2 + 3*A1^3*B1^2*e - 3*A1^3*B1*B2*e^2 + 6*A1^3*B1 - 3*A1^3*B2*e + 2*A1^3*B3*e^2 + 3*A1^2*B1^3*e + 9*A1^2*B1^2 - 9*A1^2*B1*B2*e - 9*A1^2*B2 + 6*A1^2*B3*e - 3*A1*A2*B1^3*e^2 - 9*A1*A2*B1^2*e + 9*A1*A2*B1*B2*e^2 - 18*A1*A2*B1 + 9*A1*A2*B2*e - 6*A1*A2*B3*e^2 + 6*A1*B1^3 - 18*A1*B1*B2 + 12*A1*B3 - 3*A2*B1^3*e - 9*A2*B1^2 + 9*A2*B1*B2*e + 9*A2*B2 - 6*A2*B3*e + 2*A3*B1^3*e^2 + 6*A3*B1^2*e - 6*A3*B1*B2*e^2 + 12*A3*B1 - 6*A3*B2*e + 4*A3*B3*e^2) := by unfold gg; ring
  have hu36 : IsUnit (36:R) := by
    have hc : Nat.Coprime 36 (p^4) := by
      have : Nat.Coprime 36 p := by
        have h6 : (36:ℕ) = 2^2*3^2 := by norm_num
        rw [h6]; refine Nat.Coprime.mul ?_ ?_ <;> refine Nat.Coprime.pow_left _ ?_
        · exact (Nat.coprime_primes (by norm_num) (Fact.out)).mpr (by omega)
        · exact (Nat.coprime_primes (by norm_num) (Fact.out)).mpr (by omega)
      simpa using this.pow_right 4
    have := (ZMod.isUnit_iff_coprime 36 (p^4)).mpr hc
    simpa using this
  have hbb1 : (bb p (p-1):R) = 1 - e*v + e^2*(v^2-H2) + e^3*(v*H2-v^3) := by
    refine (hu36.mul_right_inj).mp ?_
    have key : (36:R)*(bb p (p-1)) = 6 * gg e (A1+B1) (A2+B2) (A3+B3) := by
      linear_combination 6*hgB - (gg e B1 B2 B3)*hgA + hprodid + (A1^3*B1^3*e^2 + 3*A1^3*B1^2*e - 3*A1^3*B1*B2*e^2 + 6*A1^3*B1 - 3*A1^3*B2*e + 2*A1^3*B3*e^2 + 3*A1^2*B1^3*e + 9*A1^2*B1^2 - 9*A1^2*B1*B2*e - 9*A1^2*B2 + 6*A1^2*B3*e - 3*A1*A2*B1^3*e^2 - 9*A1*A2*B1^2*e + 9*A1*A2*B1*B2*e^2 - 18*A1*A2*B1 + 9*A1*A2*B2*e - 6*A1*A2*B3*e^2 + 6*A1*B1^3 - 18*A1*B1*B2 + 12*A1*B3 - 3*A2*B1^3*e - 9*A2*B1^2 + 9*A2*B1*B2*e + 9*A2*B2 - 6*A2*B3*e + 2*A3*B1^3*e^2 + 6*A3*B1^2*e - 6*A3*B1*B2*e^2 + 12*A3*B1 - 6*A3*B2*e + 4*A3*B3*e^2)*hp4
    rw [key, hv1, hv2, hv3]; unfold gg; ring
  rw [hbb1]
  linear_combination (H2^2*e^2*v^2 - 2*H2^2*e*v + H2^2 - 2*H2*e^2*v^4 + 4*H2*e*v^3 - 4*H2*v^2 + e^2*v^6 - 2*e*v^5 + 3*v^4) * hp4

theorem shift2 {k : ℕ} (hk : 1 ≤ k) :
    (∑ i ∈ range p, ((i:ZMod (p^4))⁻¹)^k)
      = (∑ i ∈ range (p-2), (((i:ZMod (p^4))+2)⁻¹)^k) + 1 := by
  have hpp : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  rw [reH hk, show (range (p-1):Finset ℕ) = range ((p-2)+1) by congr 1; omega, Finset.sum_range_succ']
  rw [show ((0:ℕ):ZMod (p^4))+1 = 1 by push_cast; ring, ZMod.inv_one, one_pow]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show ((i+1:ℕ):ZMod (p^4))+1 = (i:ZMod (p^4))+2 by push_cast; ring]

theorem cpf_lemma (i : ℕ) (hi : i < p - 2) :
    (((i:ZMod (p^4))+1)*((i:ZMod (p^4))+2))⁻¹ = ((i:ZMod (p^4))+1)⁻¹ - ((i:ZMod (p^4))+2)⁻¹ := by
  set R := ZMod (p^4)
  have ha : IsUnit ((i:R)+1) := by
    have : ((i:R)+1) = ((i+1:ℕ):R) := by push_cast; ring
    rw [this]; exact isUnit_cast_ndvd (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega))
  have hb : IsUnit ((i:R)+2) := by
    have : ((i:R)+2) = ((i+2:ℕ):R) := by push_cast; ring
    rw [this]; exact isUnit_cast_ndvd (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega))
  have hab : IsUnit (((i:R)+1)*((i:R)+2)) := ha.mul hb
  have hma : ((i:R)+1)*((i:R)+1)⁻¹ = 1 := ZMod.mul_inv_of_unit _ ha
  have hmb : ((i:R)+2)*((i:R)+2)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hb
  have hmab : (((i:R)+1)*((i:R)+2))*(((i:R)+1)*((i:R)+2))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hab
  refine (hab.mul_left_inj).mp ?_
  linear_combination hmab - ((i:R)+2)*hma + ((i:R)+1)*hmb

theorem cpf2_lemma (i : ℕ) (hi : i < p - 2) :
    ((i:ZMod (p^4))+1)⁻¹*((i:ZMod (p^4))+2)⁻¹ = ((i:ZMod (p^4))+1)⁻¹ - ((i:ZMod (p^4))+2)⁻¹ := by
  set R := ZMod (p^4)
  have ha : IsUnit ((i:R)+1) := by
    have : ((i:R)+1) = ((i+1:ℕ):R) := by push_cast; ring
    rw [this]; exact isUnit_cast_ndvd (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega))
  have hb : IsUnit ((i:R)+2) := by
    have : ((i:R)+2) = ((i+2:ℕ):R) := by push_cast; ring
    rw [this]; exact isUnit_cast_ndvd (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega))
  have hab : IsUnit (((i:R)+1)*((i:R)+2)) := ha.mul hb
  have hma : ((i:R)+1)*((i:R)+1)⁻¹ = 1 := ZMod.mul_inv_of_unit _ ha
  have hmb : ((i:R)+2)*((i:R)+2)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hb
  refine (hab.mul_left_inj).mp ?_
  linear_combination (((i:R)+2)*((i:R)+2)⁻¹ - ((i:R)+2))*hma + (1+((i:R)+1))*hmb

theorem core_sum (hp5 : 5 ≤ p) :
    ((∑ k ∈ range p, (bb p k)^2 : ℕ) : ZMod (p^4)) = 2 := by
  set R := ZMod (p^4)
  set e := (p:R) with he
  set v := ((p-1:ℕ):R)⁻¹ with hvdef
  set H1 := ∑ i ∈ range p,((i:R)⁻¹)^1 with hH1
  set H2 := ∑ i ∈ range p,((i:R)⁻¹)^2 with hH2
  set H3 := ∑ i ∈ range p,((i:R)⁻¹)^3 with hH3
  set S2 := ∑ i ∈ range (p-2), (((i:R)+1)*((i:R)+2))⁻¹^2 with hS2def
  set W := ∑ i ∈ range (p-2), ((((i:R)+1)*((i:R)+2))⁻¹^2 * ((i:R)+1)⁻¹) with hWdef
  have hp4 : e^4 = 0 := by rw [show e^4=((p^4:ℕ):R) by push_cast;ring, ZMod.natCast_self]
  have hue : IsUnit (((p-1:ℕ):R)) := isUnit_cast_ndvd (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega))
  have hev : (e-1)*v = 1 := by
    rw [hvdef, show e-1 = ((p-1:ℕ):R) by rw [he, Nat.cast_sub (show 1≤p by omega)]; push_cast; ring]
    exact ZMod.mul_inv_of_unit _ hue
  have hue1 : IsUnit (e-1) := by
    rw [show e-1 = ((p-1:ℕ):R) by rw [he, Nat.cast_sub (show 1≤p by omega)]; push_cast; ring]; exact hue
  have hvpoly : v = -(1+e+e^2+e^3) := by
    refine (hue1.mul_right_inj).mp ?_
    rw [hev]; linear_combination hp4
  have hk2 : e^3 * H2 = 0 := by
    have hz := e3_kill_sum (p:=p) (k:=2) (by omega); rw [← he, ← hH2] at hz; exact hz
  have hk3 : e^3 * H3 = 0 := by
    have hz := e3_kill_sum (p:=p) (k:=3) (by omega); rw [← he, ← hH3] at hz; exact hz
  have sumU : ∀ m, 1 ≤ m → (∑ i ∈ range (p-2), (((i:R)+1)⁻¹)^m) = (∑ i ∈ range p,((i:R)⁻¹)^m) - (((p-1:ℕ):R)⁻¹)^m := by
    intro m hm
    have h1 := reH (p:=p) (k:=m) hm
    have h2 := reHm (p:=p) m
    linear_combination -h1 - h2
  have sumWi : ∀ m, 1 ≤ m → (∑ i ∈ range (p-2), (((i:R)+2)⁻¹)^m) = (∑ i ∈ range p,((i:R)⁻¹)^m) - 1 := by
    intro m hm; have hz := shift2 (p:=p) hm; linear_combination -hz
  have hc : ((∑ k∈range p,(bb p k)^2 :ℕ):R) = ∑ k∈range p,((bb p k:R))^2 := by
    rw [Nat.cast_sum]; simp only [Nat.cast_pow]
  rw [hc]
  have hsplit : ∑ k∈range p,((bb p k:R))^2
     = (bb p 0:R)^2 + (∑ i ∈ range (p-2), (bb p (i+1):R)^2) + (bb p (p-1):R)^2 := by
    rw [show (range p:Finset ℕ)=range ((p-1)+1) by congr 1; omega, Finset.sum_range_succ']
    rw [show (range (p-1):Finset ℕ)=range ((p-2)+1) by congr 1; omega, Finset.sum_range_succ]
    rw [show (p-2)+1 = p-1 by omega]; ring
  rw [hsplit]
  have hb0 : (bb p 0:R) = e - 1 := by
    show ((((p-1).choose 0 * (p-1+0).choose 1 :ℕ)):R) = e-1
    rw [Nat.choose_zero_right, one_mul, Nat.add_zero, Nat.choose_one_right, he,
      Nat.cast_sub (show 1≤p by omega)]; push_cast; ring
  have hmid : (∑ i∈range (p-2),(bb p (i+1):R)^2) = e^2*S2 - 2*e^3*S2 - 2*e^3*W := by
    have step : (∑ i∈range (p-2),(bb p (i+1):R)^2)
        = ∑ i∈range (p-2), (e^2*(((i:R)+1)*((i:R)+2))⁻¹^2 - 2*e^3*(((i:R)+1)*((i:R)+2))⁻¹^2 - 2*e^3*(((i:R)+1)*((i:R)+2))⁻¹^2*((i:R)+1)⁻¹) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [mem_range] at hi
      have ht := term_mid (p:=p) (i+1) (by omega) (by omega)
      rw [← he] at ht
      rw [ht, show ((i+1:ℕ):R) = (i:R)+1 by push_cast; ring, show (i:R)+1+1 = (i:R)+2 by ring]
    rw [step, hS2def, hWdef, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun x _ => by ring)
  rw [hb0, hmid]
  have hlast := term_last (p:=p) hp5
  rw [← he, ← hvdef, ← hH2] at hlast
  rw [hlast]
  have hP1 : S2 = 2*H2 - v^2 + 2*v - 3 := by
    rw [hS2def]
    have hexp : (∑ i ∈ range (p-2), (((i:R)+1)*((i:R)+2))⁻¹^2)
        = ∑ i ∈ range (p-2), ((((i:R)+1)⁻¹)^2 + (((i:R)+2)⁻¹)^2 - 2*((i:R)+1)⁻¹^1 + 2*((i:R)+2)⁻¹^1) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [mem_range] at hi
      rw [cpf_lemma (p:=p) i hi]
      linear_combination (-2)*(cpf2_lemma (p:=p) i hi)
    rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    rw [sumU 2 (by norm_num), sumU 1 (by norm_num), sumWi 2 (by norm_num), sumWi 1 (by norm_num)]
    rw [← hvdef, ← hH1, ← hH2]
    ring
  have hP2 : W = -3*H2 + H3 + 4 - 3*v + 2*v^2 - v^3 := by
    rw [hWdef]
    have hexp : (∑ i ∈ range (p-2), ((((i:R)+1)*((i:R)+2))⁻¹^2 * ((i:R)+1)⁻¹))
        = ∑ i ∈ range (p-2), ((((i:R)+1)⁻¹)^3 - 2*(((i:R)+1)⁻¹)^2 + 3*((i:R)+1)⁻¹^1 - 3*((i:R)+2)⁻¹^1 - (((i:R)+2)⁻¹)^2) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [mem_range] at hi
      rw [cpf_lemma (p:=p) i hi]
      linear_combination ((-2)*((i:R)+1)⁻¹ + ((i:R)+2)⁻¹ + 3)*(cpf2_lemma (p:=p) i hi)
    rw [hexp]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sumU 3 (by norm_num), sumU 2 (by norm_num), sumU 1 (by norm_num), sumWi 1 (by norm_num), sumWi 2 (by norm_num)]
    rw [← hvdef, ← hH1, ← hH2, ← hH3]
    ring
  rw [hP1, hP2, hvpoly]
  linear_combination (-2*(2*e^3+2*e^2+2*e+1))*hk2 + (-2)*hk3 + (2*(e^8+3*e^7+6*e^6+9*e^5+11*e^4+11*e^3+8*e^2+5*e+3))*hp4
end

theorem term_id (n k : ℕ) :
    (n+1) * (n.choose k * (n+k).choose (k+1)) = n * ((n+1).choose (k+1) * (n+k).choose k) := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos k)
  have hA : (n+k).choose (k+1) * (k+1) = (n+k).choose k * n := by
    rw [Nat.choose_succ_right_eq]; congr 1; omega
  have hB : (n+1) * n.choose k = (n+1).choose (k+1) * (k+1) := Nat.succ_mul_choose_eq n k
  calc (n+1) * (n.choose k * (n+k).choose (k+1)) * (k+1)
      = ((n+1) * n.choose k) * ((n+k).choose (k+1) * (k+1)) := by ring
    _ = ((n+1).choose (k+1) * (k+1)) * ((n+k).choose k * n) := by rw [hA, hB]
    _ = n * ((n+1).choose (k+1) * (n+k).choose k) * (k+1) := by ring

noncomputable def cc (p k : ℕ) : ℕ := p.choose (k+1) * (p-1+k).choose k

theorem pb_eq {p : ℕ} (hp : 1 ≤ p) (k : ℕ) : p * bb p k = (p-1) * cc p k := by
  have h := term_id (p-1) k
  rw [Nat.sub_add_cancel hp] at h
  simpa [bb, cc] using h

theorem sq_identity {p : ℕ} (hp : 1 ≤ p) :
    p^2 * (∑ k ∈ range p, (bb p k)^2) = (p-1)^2 * (∑ k ∈ range p, (cc p k)^2) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h := pb_eq hp k
  calc p^2 * (bb p k)^2 = (p * bb p k)^2 := by ring
    _ = ((p-1) * cc p k)^2 := by rw [h]
    _ = (p-1)^2 * (cc p k)^2 := by ring

theorem two_dvd_S {p : ℕ} (hp : Odd p) (hp1 : 1 ≤ p) :
    2 ∣ ∑ k ∈ range p, (bb p k)^2 := by
  have h4 : (4:ℕ) ∣ (p-1)^2 := by
    obtain ⟨m, hm⟩ := hp; have : p - 1 = 2 * m := by omega
    rw [this]; exact ⟨m^2, by ring⟩
  have hdvd : (4:ℕ) ∣ p^2 * (∑ k ∈ range p, (bb p k)^2) := by
    rw [sq_identity hp1]; exact Dvd.dvd.mul_right h4 _
  have h2 : Nat.Coprime 2 p := (Nat.coprime_two_left).mpr hp
  have hcop : Nat.Coprime 4 (p^2) := by
    have hh : Nat.Coprime (2^2) (p^2) := h2.pow 2 2
    rwa [show (2:ℕ)^2 = 4 from rfl] at hh
  exact dvd_trans (by norm_num) (Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd)

theorem A_eq {p : ℕ} (hp1 : 1 ≤ p) (hodd : Odd p) :
    2 * A277060 (p-1) = ∑ k ∈ range p, (bb p k)^2 := by
  have hSeq : A277060 (p-1) = (∑ k ∈ range p, (bb p k)^2) / 2 := by
    unfold A277060 bb
    rw [Nat.sub_add_cancel hp1]
  rw [hSeq, Nat.mul_div_cancel' (two_dvd_S hodd hp1)]

theorem c1 {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    A277060 (p-1) ≡ 1 [MOD p^4] := by
  have hp1 : 1 ≤ p := by omega
  have hodd : Odd p := (Fact.out (p := p.Prime)).odd_of_ne_two (by omega)
  rw [← ZMod.natCast_eq_natCast_iff]
  have hSc : ((∑ k ∈ range p, (bb p k)^2 : ℕ) : ZMod (p^4)) = 2 := core_sum hp5
  have h2A := A_eq hp1 hodd
  have key : (2 : ZMod (p^4)) * ((A277060 (p-1) : ℕ) : ZMod (p^4)) = 2 := by
    have h : (((2 * A277060 (p-1) : ℕ)) : ZMod (p^4)) = 2 := by rw [h2A]; exact hSc
    push_cast at h; exact h
  have hne : NeZero (p^4) := ⟨by positivity⟩
  have hu : IsUnit (2 : ZMod (p^4)) := by
    have hc : Nat.Coprime 2 (p^4) := by
      have h2 : Nat.Coprime 2 p := (Nat.coprime_two_left).mpr hodd
      simpa using h2.pow_right 4
    have := (ZMod.isUnit_iff_coprime 2 (p^4)).mpr hc
    simpa using this
  rw [Nat.cast_one]
  refine (hu.mul_right_inj).mp ?_
  rw [mul_one]; exact key


theorem core_sum2 {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) :
    ((∑ k ∈ range (p^2), (bb (p^2) k)^2 : ℕ) : ZMod (p^5)) = 2 := sorry

theorem c2 {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) :
    A277060 (p^2-1) ≡ 1 [MOD p^5] := by
  have hp1 : 1 ≤ p^2 := by nlinarith [Nat.Prime.two_le (Fact.out : p.Prime)]
  have hodd : Odd (p^2) := by
    have : Odd p := (Fact.out (p := p.Prime)).odd_of_ne_two (by omega)
    exact this.pow
  rw [← ZMod.natCast_eq_natCast_iff]
  have hSc : ((∑ k ∈ range (p^2), (bb (p^2) k)^2 : ℕ) : ZMod (p^5)) = 2 := core_sum2 hp3
  have h2A := A_eq hp1 hodd
  have key : (2 : ZMod (p^5)) * ((A277060 (p^2-1) : ℕ) : ZMod (p^5)) = 2 := by
    have h : (((2 * A277060 (p^2-1) : ℕ)) : ZMod (p^5)) = 2 := by rw [h2A]; exact hSc
    push_cast at h; exact h
  have hne : NeZero (p^5) := ⟨by positivity⟩
  have hu : IsUnit (2 : ZMod (p^5)) := by
    have hc : Nat.Coprime 2 (p^5) := by
      have h2 : Nat.Coprime 2 p := (Nat.coprime_two_left).mpr ((Fact.out (p := p.Prime)).odd_of_ne_two (by omega))
      simpa using h2.pow_right 5
    have := (ZMod.isUnit_iff_coprime 2 (p^5)).mpr hc
    simpa using this
  rw [Nat.cast_one]
  refine (hu.mul_right_inj).mp ?_
  rw [mul_one]; exact key

theorem oeis_277060_conjecture_0 :
  (∀ p : ℕ, Nat.Prime p → 5 ≤ p → A277060 (p - 1) ≡ 1 [MOD p ^ 4]) ∧
  (∀ p : ℕ, Nat.Prime p → 3 ≤ p → A277060 (p ^ 2 - 1) ≡ 1 [MOD p ^ 5]) := by
  refine ⟨fun p hp hp5 => ?_, fun p hp hp3 => ?_⟩
  · haveI : Fact p.Prime := ⟨hp⟩; exact c1 hp5
  · haveI : Fact p.Prime := ⟨hp⟩; exact c2 hp3
