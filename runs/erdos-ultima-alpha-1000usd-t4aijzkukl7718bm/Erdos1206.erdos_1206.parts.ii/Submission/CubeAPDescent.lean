import FormalConjecturesUtil

/-!
Infinite descent excluding a repeated middle root in cubic Sidon collisions.
The integer theorem treats a nonzero middle term; the natural-number theorem
also handles zero. This does not settle the density conjecture.
-/

namespace Erdos1206.CubeAPDescent
open NumberField

abbrev K := CyclotomicField 3 ℚ
noncomputable instance : NumberField K := IsCyclotomicExtension.numberField {3} ℚ K
abbrev O := 𝓞 K
noncomputable instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

noncomputable def zeta : K := IsCyclotomicExtension.zeta 3 ℚ K
lemma hzeta : IsPrimitiveRoot zeta 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K
noncomputable def eta : O := hzeta.toInteger

lemma eta_sq : eta ^ 2 = -eta - 1 := by
  exact IsCyclotomicExtension.Rat.Three.eta_sq hzeta

lemma eta_cube : eta ^ 3 = 1 := hzeta.toInteger_cube_eq_one

noncomputable def pb : PowerBasis ℤ O := hzeta.integralPowerBasis
lemma pb_dim : pb.dim = 2 := by
  simp [pb, Nat.totient_prime Nat.prime_three]
noncomputable def basis : Module.Basis (Fin 2) ℤ O := pb.basis.reindex (finCongr pb_dim)

lemma basis_zero : basis 0 = 1 := by
  simp [basis, Module.Basis.reindex_apply, PowerBasis.coe_basis]

lemma basis_one : basis 1 = eta := by
  simp [basis, Module.Basis.reindex_apply, PowerBasis.coe_basis, pb, eta]

noncomputable def enc (a b : ℤ) : O := (a : O) + (b : O) * eta

lemma enc_smul (a b : ℤ) : enc a b = a • basis 0 + b • basis 1 := by
  simp [enc, basis_zero, basis_one, zsmul_eq_mul]

lemma enc_injective {a b c d : ℤ} (h : enc a b = enc c d) : a = c ∧ b = d := by
  have h0 := congrArg (fun z : O => basis.repr z 0) h
  have h1 := congrArg (fun z : O => basis.repr z 1) h
  simp only [enc_smul, map_add, map_smul] at h0 h1
  simpa using And.intro h0 h1

lemma exists_enc (z : O) : ∃ a b : ℤ, z = enc a b := by
  refine ⟨basis.repr z 0, basis.repr z 1, ?_⟩
  have h := basis.sum_repr z
  simpa [Fin.sum_univ_two, enc_smul] using h.symm

lemma enc_mul (a b c d : ℤ) : enc a b * enc c d = enc (a*c-b*d) (a*d+b*c-b*d) := by
  dsimp [enc]
  push_cast
  linear_combination b*d*eta_sq

lemma enc_add (a b c d : ℤ) : enc a b + enc c d = enc (a+c) (b+d) := by
  simp only [enc, Int.cast_add]
  ring

lemma enc_neg (a b : ℤ) : -enc a b = enc (-a) (-b) := by
  simp only [enc, Int.cast_neg]
  ring

lemma enc_cube (a b : ℤ) :
    enc a b ^ 3 = enc (a^3 - 3*a*b^2 + b^3) (3*a*b*(a-b)) := by
  rw [pow_succ, pow_two, enc_mul, enc_mul]
  congr 1 <;> ring

noncomputable def delta : O := 1 + 2*eta
lemma delta_sq : delta^2 = -3 := by
  dsimp [delta]
  linear_combination 4*eta_sq

noncomputable def pair (x y : ℤ) : O := (x : O) + (y : O)*delta
lemma pair_enc (x y : ℤ) : pair x y = enc (x+y) (2*y) := by
  simp only [pair, delta, enc, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  ring

lemma pair_injective {x y u v : ℤ} (h : pair x y = pair u v) : x = u ∧ y = v := by
  rw [pair_enc, pair_enc] at h
  obtain ⟨h1,h2⟩ := enc_injective h
  omega

lemma pair_cube (x y : ℤ) :
    pair x y ^ 3 = pair (x*(x^2-9*y^2)) (3*y*(x^2-y^2)) := by
  rw [pair_enc, enc_cube, pair_enc]
  congr 1 <;> ring

lemma pair_norm (x y : ℤ) : pair x y * pair x (-y) = ((x^2+3*y^2 : ℤ) : O) := by
  dsimp [pair]
  push_cast
  linear_combination -y^2*delta_sq


lemma eta_enc : eta = enc 0 1 := by simp [enc]
lemma eta_sq_enc : eta^2 = enc (-1) (-1) := by
  rw [eta_sq]
  simp only [enc, Int.cast_neg, Int.cast_one]
  ring

lemma cube_pair_representative (z : O) : ∃ e f : ℤ, pair e f ^ 3 = z ^ 3 := by
  obtain ⟨a,b,rfl⟩ := exists_enc z
  have represent (c d : ℤ) (hd : Even d) : ∃ e f : ℤ, pair e f = enc c d := by
    obtain ⟨f,hf⟩ := hd
    refine ⟨c-f,f,?_⟩
    rw [pair_enc]
    congr 1 <;> omega
  by_cases hb : Even b
  · obtain ⟨e,f,hef⟩ := represent a b hb
    exact ⟨e,f,congrArg (fun w : O => w^3) hef⟩
  · by_cases ha : Even a
    · obtain ⟨e,f,hef⟩ := represent (b-a) (-a) ha.neg
      refine ⟨e,f,?_⟩
      have he : enc (b-a) (-a) = eta^2 * enc a b := by
        rw [eta_sq_enc, enc_mul]
        congr 1 <;> ring
      rw [hef, he, mul_pow]
      have ht : (eta^2)^3 = 1 := by rw [← pow_mul, mul_comm 2 3, pow_mul, eta_cube]; simp
      rw [ht,one_mul]
    · have hab : Even (a-b) := by
        rw [Int.even_iff] at ha hb ⊢
        omega
      obtain ⟨e,f,hef⟩ := represent (-b) (a-b) hab
      refine ⟨e,f,?_⟩
      have he : enc (-b) (a-b) = eta * enc a b := by
        rw [eta_enc, enc_mul]
        congr 1 <;> ring
      rw [hef, he, mul_pow, eta_cube, one_mul]

lemma pair_unit_eq_one_or_neg_one {x y X Y : ℤ} (hodd : Odd (x+y))
    (u : Oˣ) (h : pair X Y * u = pair x y) : u = 1 ∨ u = -1 := by
  have hexcl (a b : ℤ)
      (hab : (a=0 ∧ b=1) ∨ (a=0 ∧ b = -1) ∨ (a = -1 ∧ b = -1) ∨ (a=1 ∧ b=1)) :
      pair X Y * enc a b ≠ pair x y := by
    intro hh
    rw [pair_enc, pair_enc, enc_mul] at hh
    obtain ⟨h1,h2⟩ := enc_injective hh
    obtain ⟨k,hk⟩ := hodd
    rcases hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      norm_num at h1 h2 <;> omega
  have hu := IsCyclotomicExtension.Rat.Three.Units.mem hzeta u
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exfalso
    apply hexcl 0 1 (by simp)
    simpa only [← eta_enc] using h
  · exfalso
    apply hexcl 0 (-1) (by simp)
    have he : enc 0 (-1) = -eta := by simp [enc]
    simpa only [he,Units.val_neg] using h
  · exfalso
    apply hexcl (-1) (-1) (by simp)
    simpa only [← eta_sq_enc,Units.val_pow_eq_pow_val] using h
  · exfalso
    apply hexcl 1 1 (by simp)
    have he : enc 1 1 = -(eta^2) := by rw [eta_sq]; simp [enc]
    simpa only [he,Units.val_neg,Units.val_pow_eq_pow_val] using h

lemma pair_coprime {x y : ℤ} (hxy : IsCoprime x y)
    (hn : IsCoprime (x^2+3*y^2) 6) : IsCoprime (pair x y) (pair x (-y)) := by
  obtain ⟨a,b,hab⟩ := hxy
  obtain ⟨r,s,hrs⟩ := hn
  have habO : (a : O)*x + b*y = 1 := by exact_mod_cast hab
  have hrsO : (r : O)*((x : O)^2+3*y^2)+s*6=1 := by exact_mod_cast hrs
  have h6 : (3*(a : O)-b*delta)*pair x y + (3*(a : O)+b*delta)*pair x (-y) = 6 := by
    dsimp [pair]
    push_cast
    linear_combination 6*habO - 2*b*y*delta_sq
  refine ⟨(r : O)*pair x (-y) + s*(3*a-b*delta), (s : O)*(3*a+b*delta), ?_⟩
  have hnorm := pair_norm x y
  push_cast at hnorm
  linear_combination r*hnorm + s*h6 + hrsO

/-- The classical cube parametrization of a primitive norm `x^2+3*y^2`,
under the conditions excluding the ramified prime and the prime `2`. -/
lemma primitive_norm_cube {x y z : ℤ} (hxy : IsCoprime x y)
    (hn : IsCoprime (x^2+3*y^2) 6) (hodd : Odd (x+y))
    (he : x^2+3*y^2=z^3) :
    ∃ e f : ℤ, x=e*(e^2-9*f^2) ∧ y=3*f*(e^2-f^2) := by
  have hc := pair_coprime hxy hn
  have hm : pair x y * pair x (-y) = (z : O)^3 := by
    rw [pair_norm, he, Int.cast_pow]
  obtain ⟨w,u,hu⟩ := exists_associated_pow_of_mul_eq_pow' hc hm
  obtain ⟨e,f,hef⟩ := cube_pair_representative w
  rw [← hef, pair_cube] at hu
  rcases pair_unit_eq_one_or_neg_one hodd u hu with hu1 | hu1
  · subst u
    simp only [Units.val_one,mul_one] at hu
    exact ⟨e,f,(pair_injective hu).1.symm,(pair_injective hu).2.symm⟩
  · subst u
    simp only [Units.val_neg,Units.val_one,mul_neg,mul_one] at hu
    have hneg : -pair (e*(e^2-9*f^2)) (3*f*(e^2-f^2)) =
        pair ((-e)*((-e)^2-9*(-f)^2)) (3*(-f)*((-e)^2-(-f)^2)) := by
      simp only [pair,Int.cast_mul,Int.cast_sub,Int.cast_neg,Int.cast_pow,Int.cast_ofNat]
      ring
    rw [hneg] at hu
    exact ⟨-e,-f,(pair_injective hu).1.symm,(pair_injective hu).2.symm⟩


lemma norm_mod_two (x y : ℤ) : (x^2+3*y^2)%2=(x+y)%2 := by
  have hx0 := Int.emod_nonneg x (by decide : (2 : ℤ) ≠ 0)
  have hy0 := Int.emod_nonneg y (by decide : (2 : ℤ) ≠ 0)
  have hx1 := Int.emod_lt_of_pos x (by decide : (0 : ℤ) < 2)
  have hy1 := Int.emod_lt_of_pos y (by decide : (0 : ℤ) < 2)
  have hx : x%2=0 ∨ x%2=1 := by omega
  have hy : y%2=0 ∨ y%2=1 := by omega
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    norm_num [Int.add_emod,Int.mul_emod,pow_two,hx,hy]

lemma cube_pair_mod_two (e f : ℤ) :
    (e*(e^2-9*f^2)+3*f*(e^2-f^2))%2=(e+f)%2 := by
  have he0 := Int.emod_nonneg e (by decide : (2 : ℤ) ≠ 0)
  have hf0 := Int.emod_nonneg f (by decide : (2 : ℤ) ≠ 0)
  have he1 := Int.emod_lt_of_pos e (by decide : (0 : ℤ) < 2)
  have hf1 := Int.emod_lt_of_pos f (by decide : (0 : ℤ) < 2)
  have he : e%2=0 ∨ e%2=1 := by omega
  have hf : f%2=0 ∨ f%2=1 := by omega
  rcases he with he | he <;> rcases hf with hf | hf <;>
    norm_num [Int.add_emod,Int.sub_emod,Int.mul_emod,pow_two,he,hf]

lemma primitive_norm_cube_strong {x y z : ℤ} (hxy : IsCoprime x y)
    (hn : IsCoprime (x^2+3*y^2) 6) (hodd : Odd (x+y))
    (he : x^2+3*y^2=z^3) :
    ∃ e f : ℤ, x=e*(e^2-9*f^2) ∧ y=3*f*(e^2-f^2) ∧
      z=e^2+3*f^2 ∧ IsCoprime e f ∧ Odd (e+f) := by
  obtain ⟨e,f,hx,hy⟩ := primitive_norm_cube hxy hn hodd he
  have hnorm : x^2+3*y^2=(e^2+3*f^2)^3 := by rw [hx,hy]; ring
  have hz : z=e^2+3*f^2 := (Odd.pow_inj (by decide : Odd 3)).mp (he.symm.trans hnorm)
  have hcop : IsCoprime e f := by
    rw [hx,hy] at hxy
    have hh : IsCoprime (e*(e^2-9*f^2)) (f*(3*(e^2-f^2))) := by
      convert hxy using 1 <;> ring
    exact hh.of_mul_left_left.of_mul_right_left
  have ho : Odd (e+f) := by
    rw [Int.odd_iff] at hodd ⊢
    rw [hx,hy,cube_pair_mod_two] at hodd
    exact hodd
  exact ⟨e,f,hx,hy,hz,hcop,ho⟩

lemma norm_coprime_six {s t : ℤ} (hs : ¬ (3 : ℤ) ∣ s) (ho : Odd (s+t)) :
    IsCoprime (s^2+3*t^2) 6 := by
  have h2 : ¬ (2 : ℤ) ∣ s^2+3*t^2 := by
    rw [Int.dvd_iff_emod_eq_zero,norm_mod_two]
    rw [Int.odd_iff] at ho
    omega
  have h3 : ¬ (3 : ℤ) ∣ s^2+3*t^2 := by
    intro hh
    have hd : (3 : ℤ) ∣ s^2 := by
      convert dvd_sub hh (dvd_mul_right (3 : ℤ) (t^2)) using 1 <;> ring
    exact hs (Int.prime_three.dvd_of_dvd_pow hd)
  have hcp2 := (Int.prime_two.coprime_iff_not_dvd.mpr h2).symm
  have hcp3 := (Int.prime_three.coprime_iff_not_dvd.mpr h3).symm
  exact hcp2.mul_right hcp3

lemma int_cube_of_coprime_mul {a b c : ℤ} (hab : IsCoprime a b) (h : a*b=c^3) :
    ∃ d : ℤ, a=d^3 := by
  obtain ⟨d,u,hu⟩ := exists_associated_pow_of_mul_eq_pow' hab h
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨d,by simpa using hu.symm⟩
  · refine ⟨-d,?_⟩
    simp only [Units.val_neg,Units.val_one,mul_neg,mul_one] at hu
    rw [← hu]
    ring

lemma coprime_of_no_common_prime {a b : ℤ}
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → (p : ℤ) ∣ b → False) : IsCoprime a b := by
  apply Int.isCoprime_iff_nat_coprime.mpr
  apply Nat.coprime_of_dvd'
  intro p hp ha hb
  exact False.elim (h p hp (Int.natCast_dvd.mpr ha) (Int.natCast_dvd.mpr hb))

lemma no_common_prime {a b : ℤ} (h : IsCoprime a b) {p : ℕ} (hp : p.Prime)
    (ha : (p : ℤ) ∣ a) (hb : (p : ℤ) ∣ b) : False := by
  have hu := Int.isUnit_iff_natAbs_eq.mp (h.isUnit_of_dvd' ha hb)
  exact hp.ne_one (by simpa using hu)

lemma norm_coprime_left {s t : ℤ} (hst : IsCoprime s t) (hs : ¬ (3 : ℤ) ∣ s) :
    IsCoprime s (s^2+3*t^2) := by
  apply coprime_of_no_common_prime
  intro p hp hps hpn
  have hp' := Nat.prime_iff_prime_int.mp hp
  have hd : (p : ℤ) ∣ 3*t^2 := by
    convert dvd_sub hpn (hps.trans (dvd_pow_self s (by decide : 2 ≠ 0))) using 1 <;> ring
  rcases hp'.dvd_mul.mp hd with hp3 | hpt
  · have hp3n : p ∣ 3 := Int.natCast_dvd_natCast.mp hp3
    have heq : p=3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3n
    exact hs (by simpa [heq] using hps)
  · exact no_common_prime hst hp hps (hp'.dvd_of_dvd_pow hpt)


lemma three_coprime_cubes {a b c z : ℤ} (hab : IsCoprime a b) (hac : IsCoprime a c)
    (hbc : IsCoprime b c) (h : a*b*c=z^3) :
    ∃ r s t : ℤ, a=r^3 ∧ b=s^3 ∧ c=t^3 := by
  obtain ⟨r,hr⟩ := int_cube_of_coprime_mul (hab.mul_right hac)
    (show a*(b*c)=z^3 by nlinarith only [h])
  obtain ⟨s,hs⟩ := int_cube_of_coprime_mul (hab.symm.mul_right hbc)
    (show b*(a*c)=z^3 by nlinarith only [h])
  obtain ⟨t,ht⟩ := int_cube_of_coprime_mul (hac.symm.mul_right hbc.symm)
    (show c*(a*b)=z^3 by nlinarith only [h])
  exact ⟨r,s,t,hr,hs,ht⟩

lemma coprime_linear_three {e f : ℤ} (hef : IsCoprime e f) (h3 : ¬ (3 : ℤ) ∣ e)
    (ho : Odd (e+f)) :
    IsCoprime e (e-3*f) ∧ IsCoprime e (e+3*f) ∧ IsCoprime (e-3*f) (e+3*f) := by
  have he3 : IsCoprime e 3 := (Int.prime_three.coprime_iff_not_dvd.mpr h3).symm
  have he3f : IsCoprime e (3*f) := he3.mul_right hef
  refine ⟨?_,?_,?_⟩
  · convert he3f.neg_right.add_mul_right_right 1 using 1 <;> ring
  · convert he3f.add_mul_right_right 1 using 1 <;> ring
  · apply coprime_of_no_common_prime
    intro p hp hl hr
    have hp' := Nat.prime_iff_prime_int.mp hp
    have hd : (p : ℤ) ∣ 6*f := by convert dvd_sub hr hl using 1 <;> ring
    rcases hp'.dvd_mul.mp hd with h6 | hpf
    · have hp6 : p ∣ 2*3 := Int.natCast_dvd_natCast.mp h6
      rcases hp.dvd_mul.mp hp6 with hp2 | hp3
      · have heq : p=2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
        rw [heq] at hl
        obtain ⟨q,hq⟩ := hl
        obtain ⟨k,hk⟩ := ho
        omega
      · have heq : p=3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3
        rw [heq] at hl
        apply h3
        convert dvd_add hl (dvd_mul_right (3 : ℤ) f) using 1 <;> ring
    · have hpe : (p : ℤ) ∣ e := by
        convert dvd_add hl (dvd_mul_of_dvd_right hpf 3) using 1 <;> ring
      exact no_common_prime hef hp hpe hpf

lemma coprime_linear_one {e f : ℤ} (hef : IsCoprime e f) (ho : Odd (e+f)) :
    IsCoprime f (e-f) ∧ IsCoprime f (e+f) ∧ IsCoprime (e-f) (e+f) := by
  refine ⟨?_,?_,?_⟩
  · convert hef.symm.add_mul_right_right (-1) using 1 <;> ring
  · convert hef.symm.add_mul_right_right 1 using 1 <;> ring
  · apply coprime_of_no_common_prime
    intro p hp hl hr
    have hp' := Nat.prime_iff_prime_int.mp hp
    have hd : (p : ℤ) ∣ 2*f := by convert dvd_sub hr hl using 1 <;> ring
    rcases hp'.dvd_mul.mp hd with hp2 | hpf
    · have heq : p=2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (Int.natCast_dvd_natCast.mp hp2)
      rw [heq] at hr
      obtain ⟨q,hq⟩ := hr
      obtain ⟨k,hk⟩ := ho
      omega
    · have hpe : (p : ℤ) ∣ e := by convert dvd_add hl hpf using 1 <;> ring
      exact no_common_prime hef hp hpe hpf

lemma norm_natAbs (e f : ℤ) :
    (e^2+3*f^2).natAbs=e.natAbs^2+3*f.natAbs^2 := by
  apply Int.natCast_inj.mp
  rw [Int.natCast_natAbs,abs_of_nonneg (by positivity : (0 : ℤ) ≤ e^2+3*f^2)]
  push_cast
  rw [sq_abs,sq_abs]

lemma cube_center_norm_bound {r e f a z : ℤ} (hr : e=r^3 ∨ f=r^3)
    (hf : f ≠ 0) (ha : a ≠ 0) (hz : z=a*(e^2+3*f^2)) : r.natAbs < z.natAbs := by
  have hfpos := Int.natAbs_pos.mpr hf
  have hapos := Int.natAbs_pos.mpr ha
  have he2 := Nat.le_self_pow (by decide : 2 ≠ 0) e.natAbs
  have hf2 := Nat.le_self_pow (by decide : 2 ≠ 0) f.natAbs
  have hr3 := Nat.le_self_pow (by decide : 3 ≠ 0) r.natAbs
  have hm : max e.natAbs f.natAbs < (e^2+3*f^2).natAbs := by
    rw [norm_natAbs,max_lt_iff]
    constructor <;> nlinarith
  have hrm : r.natAbs ≤ max e.natAbs f.natAbs := by
    rcases hr with hr | hr
    · have he : e.natAbs=r.natAbs^3 := by rw [hr,Int.natAbs_pow]
      exact (hr3.trans_eq he.symm).trans (le_max_left _ _)
    · have he : f.natAbs=r.natAbs^3 := by rw [hr,Int.natAbs_pow]
      exact (hr3.trans_eq he.symm).trans (le_max_right _ _)
  rw [hz,Int.natAbs_mul]
  exact (hrm.trans_lt hm).trans_le (Nat.le_mul_of_pos_left _ hapos)

lemma centered_descent_case_one {s t z : ℤ} (hst : IsCoprime s t) (ho : Odd (s+t))
    (hs : s ≠ 0) (ht : t ≠ 0) (h3 : ¬ (3 : ℤ) ∣ s)
    (he : s*(s^2+3*t^2)=z^3) :
    ∃ x y w : ℤ, w ≠ 0 ∧ x ≠ y ∧ x^3+y^3=2*w^3 ∧ w.natAbs < z.natAbs := by
  have hcop := norm_coprime_left hst h3
  obtain ⟨a,ha⟩ := int_cube_of_coprime_mul hcop he
  obtain ⟨b,hb⟩ := int_cube_of_coprime_mul hcop.symm
    (show (s^2+3*t^2)*s=z^3 by nlinarith only [he])
  obtain ⟨e,f,hes,htf,hbN,hef,hof⟩ :=
    primitive_norm_cube_strong hst (norm_coprime_six h3 ho) ho hb
  have he3 : ¬ (3 : ℤ) ∣ e := by
    intro hh
    apply h3
    rw [hes]
    exact dvd_mul_of_dvd_left hh _
  obtain ⟨hc1,hc2,hc3⟩ := coprime_linear_three hef he3 hof
  have hprod : e*(e-3*f)*(e+3*f)=a^3 := by nlinarith only [hes,ha]
  obtain ⟨r,u,v,hr,hu,hv⟩ := three_coprime_cubes hc1 hc2 hc3 hprod
  have hr0 : r ≠ 0 := by
    intro h
    have he0 : e=0 := by simpa [h] using hr
    exact hs (by simp [hes,he0])
  have hf0 : f ≠ 0 := by
    intro h
    exact ht (by simp [htf,h])
  have huv : u ≠ v := by
    intro h
    rw [h] at hu
    have : f=0 := by nlinarith only [hu,hv]
    exact hf0 this
  have ha0 : a ≠ 0 := by intro h; exact hs (by simp [ha,h])
  have hz : z=a*(e^2+3*f^2) := by
    apply (Odd.pow_inj (by decide : Odd 3)).mp
    calc z^3 = s*(s^2+3*t^2) := he.symm
      _ = (a*b)^3 := by rw [hb,ha]; ring
      _ = (a*(e^2+3*f^2))^3 := by rw [hbN]
  exact ⟨u,v,r,hr0,huv,by nlinarith only [hr,hu,hv],
    cube_center_norm_bound (Or.inl hr) hf0 ha0 hz⟩


lemma centered_descent_case_three {s t z : ℤ} (hst : IsCoprime s t) (ho : Odd (s+t))
    (hs : s ≠ 0) (ht : t ≠ 0) (h3 : (3 : ℤ) ∣ s)
    (he : s*(s^2+3*t^2)=z^3) :
    ∃ x y w : ℤ, w ≠ 0 ∧ x ≠ y ∧ x^3+y^3=2*w^3 ∧ w.natAbs < z.natAbs := by
  obtain ⟨k,hsk⟩ := h3
  have ht3 : ¬ (3 : ℤ) ∣ t := by
    intro h
    exact no_common_prime hst Nat.prime_three (by rw [hsk]; exact dvd_mul_right 3 k) h
  let B : ℤ := 3*k^2+t^2
  have hB3 : ¬ (3 : ℤ) ∣ B := by
    intro h
    have hdiv : (3 : ℤ) ∣ t^2 := by
      convert dvd_sub h (dvd_mul_right (3 : ℤ) (k^2)) using 1 <;> dsimp [B] <;> ring
    exact ht3 (Int.prime_three.dvd_of_dvd_pow hdiv)
  have hBs : IsCoprime B s := by
    apply coprime_of_no_common_prime
    intro p hp hpB hps
    have hp' := Nat.prime_iff_prime_int.mp hp
    have hpk : (p : ℤ) ∣ k := by
      rw [hsk] at hps
      rcases hp'.dvd_mul.mp hps with hp3 | hpk
      · have heq : p=3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
          (Int.natCast_dvd_natCast.mp hp3)
        exact False.elim (hB3 (by simpa [heq] using hpB))
      · exact hpk
    have hpt2 : (p : ℤ) ∣ t^2 := by
      convert dvd_sub hpB (dvd_mul_of_dvd_right
        (hpk.trans (dvd_pow_self k (by decide : 2 ≠ 0))) 3) using 1 <;> dsimp [B] <;> ring
    exact no_common_prime hst hp hps (hp'.dvd_of_dvd_pow hpt2)
  have hBcop : IsCoprime B (3*s) :=
    (Int.prime_three.coprime_iff_not_dvd.mpr hB3).symm.mul_right hBs
  have hprod : B*(3*s)=z^3 := by dsimp [B]; rw [hsk] at he ⊢; nlinarith only [he]
  obtain ⟨b,hb⟩ := int_cube_of_coprime_mul hBcop hprod
  have htpos : 0 < t^2 := sq_pos_of_ne_zero ht
  have hBpos : 0 < B := by dsimp [B]; nlinarith [sq_nonneg k]
  have hb0 : b ≠ 0 := by intro h; rw [h] at hb; norm_num at hb; omega
  have hZ : 3*s*b^3=z^3 := by rw [hb] at hprod; nlinarith only [hprod]
  have hbd : b ∣ z := by
    apply (Int.pow_dvd_pow_iff (by decide : 3 ≠ 0)).mp
    rw [← hZ]
    exact dvd_mul_left (b^3) (3*s)
  obtain ⟨u,hzu⟩ := hbd
  have hu3 : u^3=3*s := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hb0)
    rw [hzu] at hZ
    nlinarith only [hZ]
  have h3u : (3 : ℤ) ∣ u := Int.prime_three.dvd_of_dvd_pow
    (show (3 : ℤ) ∣ u^3 by rw [hu3]; exact dvd_mul_right 3 s)
  obtain ⟨a,hua⟩ := h3u
  have hs9 : s=9*a^3 := by rw [hua] at hu3; nlinarith only [hu3]
  have hka : k=3*a^3 := by nlinarith only [hsk,hs9]
  have ha0 : a ≠ 0 := by intro h; exact hs (by simp [hs9,h])
  have htk : IsCoprime t k := by rw [hsk] at hst; exact hst.of_mul_left_right.symm
  have htkodd : Odd (t+k) := by
    rw [Int.odd_iff] at ho ⊢
    rw [hsk] at ho
    omega
  have hnorm : t^2+3*k^2=b^3 := by dsimp [B] at hb; nlinarith only [hb]
  obtain ⟨e,f,htf,hkf,hbN,hef,hof⟩ :=
    primitive_norm_cube_strong htk (norm_coprime_six ht3 htkodd) htkodd hnorm
  obtain ⟨hc1,hc2,hc3⟩ := coprime_linear_one hef hof
  have hprod' : f*(e-f)*(e+f)=a^3 := by nlinarith only [hkf,hka]
  obtain ⟨r,v,w,hr,hv,hw⟩ := three_coprime_cubes hc1 hc2 hc3 hprod'
  have hf0 : f ≠ 0 := by
    intro h
    have hk0 : k=0 := by simp [hkf,h]
    exact hs (by simp [hsk,hk0])
  have he0 : e ≠ 0 := by intro h; exact ht (by simp [htf,h])
  have hr0 : r ≠ 0 := by intro h; exact hf0 (by simp [hr,h])
  have hwv : w ≠ -v := by
    intro h
    rw [h] at hw
    have : e=0 := by nlinarith only [hv,hw]
    exact he0 this
  have hz : z=(3*a)*(e^2+3*f^2) := by rw [hzu,hua,hbN]; ring
  refine ⟨w,-v,r,hr0,hwv,?_,cube_center_norm_bound (Or.inr hr) hf0
    (mul_ne_zero (by norm_num) ha0) hz⟩
  nlinarith only [hr,hv,hw]


lemma common_prime_dvd_center {x y z : ℤ} (he : x^3+y^3=2*z^3)
    {p : ℕ} (hp : p.Prime) (hpx : (p : ℤ) ∣ x) (hpy : (p : ℤ) ∣ y) :
    (p : ℤ) ∣ z := by
  have hp' := Nat.prime_iff_prime_int.mp hp
  by_cases hp2 : p=2
  · rw [hp2] at hpx hpy ⊢
    obtain ⟨a,ha⟩ := hpx
    obtain ⟨b,hb⟩ := hpy
    rw [ha,hb] at he
    norm_num only [Nat.cast_ofNat] at he
    apply Int.prime_two.dvd_of_dvd_pow (n := 3)
    exact ⟨2*(a^3+b^3),by nlinarith only [he]⟩
  · have hdiv : (p : ℤ) ∣ 2*z^3 := by
      rw [← he]
      exact dvd_add (hpx.trans (dvd_pow_self x (by decide : 3 ≠ 0)))
        (hpy.trans (dvd_pow_self y (by decide : 3 ≠ 0)))
    rcases hp'.dvd_mul.mp hdiv with hp2' | hpz
    · exact False.elim (hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (Int.natCast_dvd_natCast.mp hp2')))
    · exact hp'.dvd_of_dvd_pow hpz

lemma cube_mod_two (x : ℤ) : x^3%2=x%2 := by
  have hx : x%2=0 ∨ x%2=1 := by omega
  rcases hx with hx | hx <;> norm_num [pow_succ,Int.mul_emod,hx]

lemma sum_even_of_cube_AP {x y z : ℤ} (he : x^3+y^3=2*z^3) : Even (x+y) := by
  rw [Int.even_iff,Int.add_emod]
  have hm := congrArg (fun n : ℤ => n%2) he
  simpa [Int.add_emod,cube_mod_two,Int.mul_emod] using hm

/-- The classical descent excluding three nonconstant integer cubes in an
arithmetic progression whose middle cube is nonzero. -/
theorem int_cube_AP_trivial (x y z : ℤ) (hz : z ≠ 0) (he : x^3+y^3=2*z^3) : x=y := by
  suffices hmain : ∀ n : ℕ, ∀ x y z : ℤ, z.natAbs=n → z ≠ 0 →
      x^3+y^3=2*z^3 → x=y from hmain z.natAbs x y z rfl hz he
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y z hn hz he
    by_contra hne
    have hcop : IsCoprime x y := by
      apply coprime_of_no_common_prime
      intro p hp hpx hpy
      have hpz := common_prime_dvd_center he hp hpx hpy
      obtain ⟨a,ha⟩ := hpx
      obtain ⟨b,hb⟩ := hpy
      obtain ⟨c,hc⟩ := hpz
      have hc0 : c ≠ 0 := by intro h; exact hz (by simp [hc,h])
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have he' : a^3+b^3=2*c^3 := by
        apply mul_left_cancel₀ (pow_ne_zero 3 hp0)
        rw [ha,hb,hc] at he
        nlinarith only [he]
      have hcn : c.natAbs < n := by
        rw [← hn,hc,Int.natAbs_mul,Int.natAbs_natCast]
        have hp1 := hp.one_lt
        have hc1 := Int.natAbs_pos.mpr hc0
        nlinarith
      have hab := ih c.natAbs hcn a b c rfl hc0 he'
      exact hne (by rw [ha,hb,hab])
    have hsum : Even (x+y) := sum_even_of_cube_AP he
    have hxo : Odd x := by
      rw [Int.odd_iff]
      by_contra h
      have hx0 : x%2=0 := by omega
      have hy0 : y%2=0 := by rw [Int.even_iff] at hsum; omega
      exact no_common_prime hcop Nat.prime_two
        (Int.dvd_iff_emod_eq_zero.mpr hx0) (Int.dvd_iff_emod_eq_zero.mpr hy0)
    let s := (x+y)/2
    let t := (x-y)/2
    have hx : x=s+t := by dsimp [s,t]; rw [Int.even_iff] at hsum; omega
    have hy : y=s-t := by dsimp [s,t]; rw [Int.even_iff] at hsum; omega
    have hcenter : s*(s^2+3*t^2)=z^3 := by
      rw [hx,hy] at he
      nlinarith only [he]
    have ht : t ≠ 0 := by intro h; exact hne (by rw [hx,hy,h]; ring)
    have hs : s ≠ 0 := by
      intro h
      rw [h,zero_mul] at hcenter
      exact hz (eq_zero_of_pow_eq_zero hcenter.symm)
    have hst : IsCoprime s t := by
      apply coprime_of_no_common_prime
      intro p hp hps hpt
      exact no_common_prime hcop hp (hx ▸ dvd_add hps hpt) (hy ▸ dvd_sub hps hpt)
    have ho : Odd (s+t) := hx ▸ hxo
    have hd : ∃ u v w : ℤ, w ≠ 0 ∧ u ≠ v ∧ u^3+v^3=2*w^3 ∧ w.natAbs < z.natAbs := by
      by_cases h3 : (3 : ℤ) ∣ s
      · exact centered_descent_case_three hst ho hs ht h3 hcenter
      · exact centered_descent_case_one hst ho hs ht h3 hcenter
    obtain ⟨u,v,w,hw,huv,heq,hlt⟩ := hd
    exact huv (ih w.natAbs (hlt.trans_le hn.le) u v w rfl hw heq)

/-- Over the naturals the zero-middle case is trivial too. -/
theorem nat_cube_AP_trivial (a b c : ℕ) (h : a^3+c^3=2*b^3) : a=b ∧ c=b := by
  by_cases hb : b=0
  · subst b
    norm_num at h
    obtain ⟨ha,hc⟩ := h
    exact ⟨ha,hc⟩
  · have he : (a : ℤ)^3+(c : ℤ)^3=2*(b : ℤ)^3 := by exact_mod_cast h
    have hac : a=c := by
      exact_mod_cast int_cube_AP_trivial a c b (by exact_mod_cast hb) he
    have hpow : a^3=b^3 := by rw [← hac] at h; omega
    have hab : a=b := Nat.pow_left_injective (by decide : 3 ≠ 0) hpow
    exact ⟨hab,hac ▸ hab⟩

#print axioms int_cube_AP_trivial
#print axioms nat_cube_AP_trivial






end Erdos1206.CubeAPDescent
