import Submission.CubeApproximation
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three

/-!
# Cubic rigidity and residual-support obstructions for powerful triples

This file proves, without admissions:
* signed integer and natural-number rigidity for `a³ + b³ = 2c³`;
* nonexistence of nonzero signed integer or natural solutions to `a³ + b³ = 4c³`;
* for every even `t ≥ 2`, every prime `p`, and arbitrary natural parameters,
  `t³ - t ≠ D³ (H³ 2^α p^β)²`;
* infinitely many excluded composite squarefree square factors `S = 2p`.

The cubic proofs use complete infinite descent on `|c|`.  Mathlib supplies the
principal-ideal-domain property, integral power basis, and unit classification
of the third cyclotomic ring.  Integer coordinates are developed explicitly.
In the unramified branch the three descent factors are `r+s`, `2r-s`, `r-2s`;
in the ramified branch they are `r`, `s`, `r-s`.  Both branches prove a strict
height decrease, including preservation of the nontriviality condition for
coefficient two.  Common factors are removed by a separate minimality argument.

For the residual-support application, evenness makes the consecutive entries
pairwise coprime.  The endpoints avoid 2; an endpoint avoiding `p` is a cube.
If `p` occurs at an endpoint, the center is `2^j u³` with `j < 3`, and the cubic
rigidity excludes its cube neighbor, using the required divisibility by four.
Cube factors of `S` are absorbed into `D`, with no squarefreeness requirement.

This is a family of unconditional EMW helpers, NOT a resolution of the
unrestricted powerful-triple conjecture.  `Submission.Spec` is not imported,
and the existing submission files are not modified.
-/

namespace Erdos364.CubicObstruction

open NumberField IsCyclotomicExtension.Rat.Three

/- ## The Eisenstein ring and explicit integer coordinates -/

namespace Eisenstein

abbrev K := CyclotomicField 3 ℚ
abbrev E := 𝓞 K

noncomputable instance : NumberField K := IsCyclotomicExtension.numberField {3} ℚ K
noncomputable instance : IsPrincipalIdealRing E := IsCyclotomicExtension.Rat.three_pid K

noncomputable def root := IsCyclotomicExtension.zeta 3 ℚ K
lemma root_primitive : IsPrimitiveRoot root 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K
noncomputable def ω : E := root_primitive.toInteger
noncomputable def lambda : E := ω - 1

lemma omega_def : root_primitive.toInteger = ω := rfl

lemma omega_sq : ω ^ 2 = -ω - 1 := eta_sq root_primitive
lemma omega_cube : ω ^ 3 = 1 := root_primitive.toInteger_cube_eq_one
lemma lambda_prime : Prime lambda := root_primitive.zeta_sub_one_prime'
lemma lambda_sq : lambda ^ 2 = -3 * ω := by
  dsimp [lambda]
  linear_combination omega_sq

noncomputable def basis : Module.Basis (Fin 2) ℤ E :=
  root_primitive.integralPowerBasis.basis.reindex
    (finCongr (by simp [IsPrimitiveRoot.integralPowerBasis_dim, Nat.totient_prime Nat.prime_three]))

lemma basis_apply (i : Fin 2) : basis i = ω ^ i.val := by
  simp [basis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    IsPrimitiveRoot.integralPowerBasis_gen, ω]

lemma basis_zero : basis 0 = 1 := by simp [basis_apply]
lemma basis_one : basis 1 = ω := by simp [basis_apply]

noncomputable def pair (a b : ℤ) : E := (a : E) + (b : E) * ω

lemma pair_smul (a b : ℤ) : pair a b = a • basis 0 + b • basis 1 := by
  simp [pair, basis_zero, basis_one, Algebra.smul_def]

lemma pair_coords (a b : ℤ) : basis.equivFun (pair a b) = ![a, b] := by
  rw [pair_smul]
  ext i
  rw [map_add, map_smul, map_smul]
  fin_cases i <;> simp only [Pi.add_apply, Pi.smul_apply, Module.Basis.equivFun_self]
    <;> norm_num

lemma pair_inj {a b c d : ℤ} (h : pair a b = pair c d) : a = c ∧ b = d := by
  have hh := congrArg basis.equivFun h
  rw [pair_coords, pair_coords] at hh
  exact ⟨congrFun hh 0, congrFun hh 1⟩

lemma exists_pair (x : E) : ∃ a b : ℤ, x = pair a b := by
  refine ⟨basis.equivFun x 0, basis.equivFun x 1, ?_⟩
  rw [pair_smul]
  simpa only [Fin.sum_univ_two] using (basis.sum_equivFun x).symm

lemma pair_zero : pair 0 0 = 0 := by simp [pair]
lemma pair_ne_zero {a b : ℤ} (h : a ≠ 0 ∨ b ≠ 0) : pair a b ≠ 0 := by
  intro hz
  have hh := pair_inj (hz.trans pair_zero.symm)
  rcases h with ha | hb
  · exact ha hh.1
  · exact hb hh.2

lemma pair_int_mul (n a b : ℤ) : (n : E) * pair a b = pair (n * a) (n * b) := by
  simp only [pair, Int.cast_mul]
  ring

lemma int_dvd_pair_iff {n a b : ℤ} : (n : E) ∣ pair a b ↔ n ∣ a ∧ n ∣ b := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨r, s, rfl⟩ := exists_pair x
    rw [pair_int_mul] at hx
    have hh := pair_inj hx
    exact ⟨⟨r, hh.1⟩, ⟨s, hh.2⟩⟩
  · rintro ⟨⟨r, rfl⟩, ⟨s, rfl⟩⟩
    exact ⟨pair r s, (pair_int_mul n r s).symm⟩

lemma lambda_dvd_int_iff (a : ℤ) : lambda ∣ (a : E) ↔ 3 ∣ a := by
  have hnorm : Algebra.norm ℤ lambda = 3 :=
    root_primitive.norm_toInteger_sub_one_of_prime_ne_two' (by decide)
  rw [← Ideal.norm_dvd_iff (by rw [hnorm]; exact Int.prime_three), hnorm]

lemma lambda_dvd_pair_iff (a b : ℤ) : lambda ∣ pair a b ↔ 3 ∣ a + b := by
  have heq : pair a b = ((a + b : ℤ) : E) + lambda * b := by
    simp only [pair, lambda, Int.cast_add]
    ring
  rw [heq, dvd_add_left (dvd_mul_right lambda (b : E)), lambda_dvd_int_iff]


lemma omega_unit : IsUnit ω := root_primitive.toInteger_isPrimitiveRoot.isUnit (by decide)

lemma pair_neg (a b : ℤ) : -pair a b = pair (-a) (-b) := by
  simp only [pair, Int.cast_neg]
  ring

lemma pair_mul (a b c d : ℤ) :
    pair a b * pair c d = pair (a * c - b * d) (a * d + b * c - b * d) := by
  simp only [pair, Int.cast_add, Int.cast_sub, Int.cast_mul]
  linear_combination (b : E) * (d : E) * omega_sq

lemma omega_mul_pair (a b : ℤ) : ω * pair a b = pair (-b) (a - b) := by
  have hw : ω = pair 0 1 := by simp [pair]
  rw [hw, pair_mul]
  congr 1 <;> ring

lemma omega_sq_mul_pair (a b : ℤ) : ω ^ 2 * pair a b = pair (b - a) (-a) := by
  rw [pow_two, mul_assoc, omega_mul_pair, omega_mul_pair]
  congr 1 <;> ring

lemma lambda_mul_pair (a b : ℤ) : lambda * pair a b = pair (-a - b) (a - 2 * b) := by
  have hl : lambda = pair (-1) 1 := by simp [lambda, pair]; ring
  rw [hl, pair_mul]
  congr 1 <;> ring

def cubeA (r s : ℤ) : ℤ := r ^ 3 + s ^ 3 - 3 * r * s ^ 2
def cubeB (r s : ℤ) : ℤ := 3 * r * s * (r - s)
def qnorm (r s : ℤ) : ℤ := r ^ 2 - r * s + s ^ 2

lemma pair_cube (r s : ℤ) : (pair r s) ^ 3 = pair (cubeA r s) (cubeB r s) := by
  rw [show (pair r s) ^ 3 = pair r s * pair r s * pair r s by ring, pair_mul, pair_mul]
  congr 1 <;> simp only [cubeA, cubeB] <;> ring

noncomputable def conj (a b : ℤ) : E := (a : E) + (b : E) * ω ^ 2

lemma conj_eq_pair (a b : ℤ) : conj a b = pair (a - b) (-b) := by
  simp only [conj, pair, omega_sq, Int.cast_sub, Int.cast_neg]
  ring

lemma pair_mul_conj (a b : ℤ) : pair a b * conj a b = (qnorm a b : E) := by
  rw [conj_eq_pair, pair_mul]
  simp [pair, qnorm]
  ring

lemma factorization (a b : ℤ) :
    ((a + b : ℤ) : E) * pair a b * conj a b = ((a ^ 3 + b ^ 3 : ℤ) : E) := by
  rw [mul_assoc, pair_mul_conj]
  simp only [qnorm, Int.cast_add, Int.cast_sub, Int.cast_pow, Int.cast_mul]
  ring

lemma norm_cube (r s : ℤ) : qnorm (cubeA r s) (cubeB r s) = qnorm r s ^ 3 := by
  unfold qnorm cubeA cubeB
  ring

lemma norm_omega (a b : ℤ) : qnorm (-b) (a - b) = qnorm a b := by unfold qnorm; ring
lemma norm_omega_sq (a b : ℤ) : qnorm (b - a) (-a) = qnorm a b := by unfold qnorm; ring
lemma norm_lambda (a b : ℤ) : qnorm (-a - b) (a - 2 * b) = 3 * qnorm a b := by
  unfold qnorm
  ring

lemma norm_pos {r s : ℤ} (h : r ≠ 0 ∨ s ≠ 0) : 0 < qnorm r s := by
  unfold qnorm
  rcases h with hr | hs
  · nlinarith [sq_nonneg s, sq_nonneg (r - s), sq_pos_of_ne_zero hr]
  · nlinarith [sq_nonneg r, sq_nonneg (r - s), sq_pos_of_ne_zero hs]

lemma common_prime_sum {a b : ℤ} (hab : IsCoprime a b) {p : E} (hp : Prime p)
    (hpa : p ∣ pair a b) (hps : p ∣ ((a + b : ℤ) : E)) : Associated p lambda := by
  have hpb : ¬p ∣ (b : E) := by
    intro hpb
    have hpa' : p ∣ (a : E) := by
      convert dvd_sub hpa (dvd_mul_of_dvd_left hpb ω) using 1
      simp only [pair]
      ring
    exact hp.not_unit ((hab.intCast : IsCoprime (a : E) (b : E)).isUnit_of_dvd' hpa' hpb)
  have hd : p ∣ lambda * (b : E) := by
    convert dvd_sub hpa hps using 1
    simp only [pair, lambda, Int.cast_add]
    ring
  exact hp.associated_of_dvd lambda_prime ((hp.dvd_mul.mp hd).resolve_right hpb)

lemma common_prime_conj {a b : ℤ} (hab : IsCoprime a b) {p : E} (hp : Prime p)
    (hpa : p ∣ pair a b) (hpc : p ∣ conj a b) : Associated p lambda := by
  have hpb : ¬p ∣ (b : E) := by
    intro hpb
    have hpa' : p ∣ (a : E) := by
      convert dvd_sub hpa (dvd_mul_of_dvd_left hpb ω) using 1
      simp only [pair]
      ring
    exact hp.not_unit ((hab.intCast : IsCoprime (a : E) (b : E)).isUnit_of_dvd' hpa' hpb)
  have hd : p ∣ ω * (lambda * (b : E)) := by
    convert dvd_sub hpc hpa using 1
    simp only [pair, conj, lambda]
    ring
  rw [omega_unit.dvd_mul_left] at hd
  exact hp.associated_of_dvd lambda_prime ((hp.dvd_mul.mp hd).resolve_right hpb)

lemma coprime_coords_of_cube {a b r s : ℤ} (hab : IsCoprime a b) {m : E}
    (h : pair a b = m * pair r s ^ 3) : IsCoprime r s := by
  refine isCoprime_of_prime_dvd ?_ (fun p hp hpr hps => ?_)
  · rintro ⟨rfl, rfl⟩
    have hh : a = 0 ∧ b = 0 := pair_inj (by simpa [pair_zero] using h)
    rcases hab.ne_zero_or_ne_zero with ha | hb
    · exact ha hh.1
    · exact hb hh.2
  · have hd : (p : E) ∣ pair r s := int_dvd_pair_iff.mpr ⟨hpr, hps⟩
    have hd' : (p : E) ∣ pair a b := by
      rw [h]
      exact dvd_mul_of_dvd_right (dvd_pow hd (by decide : 3 ≠ 0)) m
    obtain ⟨hpa, hpb⟩ := int_dvd_pair_iff.mp hd'
    exact hp.not_unit (hab.isUnit_of_dvd' hpa hpb)

end Eisenstein


/- ## Primitive integer arithmetic and congruences -/

namespace Arithmetic

open Eisenstein

lemma coefficient_pos {n : ℤ} (hn : n = 2 ∨ n = 4) : 0 < n := by omega

lemma sum_even {n a b c : ℤ} (hn : n = 2 ∨ n = 4)
    (h : a ^ 3 + b ^ 3 = n * c ^ 3) : 2 ∣ a + b := by
  have hh : (a : ZMod 2) ^ 3 + (b : ZMod 2) ^ 3 = (n : ZMod 2) * (c : ZMod 2) ^ 3 := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow] using
      congrArg (Int.cast : ℤ → ZMod 2) h
  have hc (x : ZMod 2) : x ^ 3 = x := by revert x; decide
  have hn' : (n : ZMod 2) = 0 := by rcases hn with rfl | rfl <;> decide
  have hs : ((a + b : ℤ) : ZMod 2) = 0 := by simpa [hc, hn'] using hh
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hs

lemma entries_odd {n a b c : ℤ} (hn : n = 2 ∨ n = 4) (hab : IsCoprime a b)
    (h : a ^ 3 + b ^ 3 = n * c ^ 3) : ¬2 ∣ a ∧ ¬2 ∣ b := by
  have hs := sum_even hn h
  constructor
  · intro ha
    have hb : 2 ∣ b := by simpa using dvd_sub hs ha
    exact Int.prime_two.not_unit (hab.isUnit_of_dvd' ha hb)
  · intro hb
    have ha : 2 ∣ a := by simpa using dvd_sub hs hb
    exact Int.prime_two.not_unit (hab.isUnit_of_dvd' ha hb)

lemma norm_coprime_two {a b : ℤ} (ha : ¬2 ∣ a) (hb : ¬2 ∣ b) :
    IsCoprime 2 (qnorm a b) := by
  have ha' : a % 2 = 1 := by rw [Int.dvd_iff_emod_eq_zero] at ha; omega
  have hb' : b % 2 = 1 := by rw [Int.dvd_iff_emod_eq_zero] at hb; omega
  apply Int.prime_two.coprime_iff_not_dvd.mpr
  rw [Int.dvd_iff_emod_eq_zero]
  norm_num [qnorm, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod, ha', hb']

lemma norm_coprime_coefficient {n a b : ℤ} (hn : n = 2 ∨ n = 4)
    (ha : ¬2 ∣ a) (hb : ¬2 ∣ b) : IsCoprime n (qnorm a b) := by
  have hh := norm_coprime_two ha hb
  rcases hn with rfl | rfl
  · exact hh
  · simpa using (hh.pow_left (m := 2))

lemma sum_three_iff_c {n a b c : ℤ} (hn : n = 2 ∨ n = 4)
    (h : a ^ 3 + b ^ 3 = n * c ^ 3) : 3 ∣ a + b ↔ 3 ∣ c := by
  have hh : (a : ZMod 3) ^ 3 + (b : ZMod 3) ^ 3 = (n : ZMod 3) * (c : ZMod 3) ^ 3 := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow] using
      congrArg (Int.cast : ℤ → ZMod 3) h
  have H₂ : ∀ x y z : ZMod 3, x ^ 3 + y ^ 3 = 2 * z ^ 3 → (x + y = 0 ↔ z = 0) := by decide
  have H₄ : ∀ x y z : ZMod 3, x ^ 3 + y ^ 3 = 4 * z ^ 3 → (x + y = 0 ↔ z = 0) := by decide
  have hi : (a : ZMod 3) + (b : ZMod 3) = 0 ↔ (c : ZMod 3) = 0 := by
    rcases hn with rfl | rfl
    · exact H₂ _ _ _ hh
    · exact H₄ _ _ _ hh
  simpa only [← Int.cast_add, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_ofNat] using hi

lemma unramified_entries {n a b c : ℤ} (hn : n = 2 ∨ n = 4)
    (h : a ^ 3 + b ^ 3 = n * c ^ 3) (hs : ¬3 ∣ a + b) :
    n = 2 ∧ ¬3 ∣ a ∧ ¬3 ∣ b := by
  let f : ZMod 9 →+* ZMod 3 := ZMod.castHom (by decide : 3 ∣ 9) (ZMod 3)
  have hh : (a : ZMod 9) ^ 3 + (b : ZMod 9) ^ 3 = (n : ZMod 9) * (c : ZMod 9) ^ 3 := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow] using
      congrArg (Int.cast : ℤ → ZMod 9) h
  have hs' : f ((a : ZMod 9) + (b : ZMod 9)) ≠ 0 := by
    simpa only [ne_eq, map_add, map_intCast, ← Int.cast_add, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_ofNat] using hs
  have H₂ : ∀ x y z : ZMod 9, x ^ 3 + y ^ 3 = 2 * z ^ 3 → f (x + y) ≠ 0 →
      f x ≠ 0 ∧ f y ≠ 0 := by decide
  have H₄ : ∀ x y z : ZMod 9, x ^ 3 + y ^ 3 = 4 * z ^ 3 → f (x + y) = 0 := by decide
  rcases hn with rfl | rfl
  · refine ⟨rfl, ?_⟩
    simpa only [ne_eq, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_ofNat] using H₂ _ _ _ hh hs'
  · exact (hs' (H₄ _ _ _ hh)).elim

lemma ramified_entries {a b : ℤ} (hab : IsCoprime a b) (hs : 3 ∣ a + b) :
    ¬3 ∣ a ∧ ¬3 ∣ b := by
  constructor
  · intro ha
    have hb : 3 ∣ b := by simpa using dvd_sub hs ha
    exact Int.prime_three.not_unit (hab.isUnit_of_dvd' ha hb)
  · intro hb
    have ha : 3 ∣ a := by simpa using dvd_sub hs hb
    exact Int.prime_three.not_unit (hab.isUnit_of_dvd' ha hb)

lemma ramified_sum_nine {n a b c : ℤ} (hn : n = 2 ∨ n = 4) (hab : IsCoprime a b)
    (h : a ^ 3 + b ^ 3 = n * c ^ 3) (hs : 3 ∣ a + b) : 9 ∣ a + b := by
  obtain ⟨k, hk⟩ := hs
  obtain ⟨w, hw⟩ := (sum_three_iff_c hn h).mp ⟨k, hk⟩
  have he := ramified_entries hab ⟨k, hk⟩
  let q : ℤ := 3 * k ^ 2 - a * b
  have hq : ¬3 ∣ q := by
    intro hd
    have hd' : 3 ∣ a * b := by
      convert dvd_sub (dvd_mul_right (3 : ℤ) (k ^ 2)) hd using 1
      dsimp [q]
      ring
    exact (Int.prime_three.dvd_mul.mp hd').elim he.1 he.2
  have hQ : qnorm a b = 3 * q := by
    dsimp [qnorm, q]
    linear_combination (a + b + 3 * k) * hk
  have hf : (a + b) * qnorm a b = n * c ^ 3 := by
    dsimp [qnorm]
    linear_combination h
  have hf' : q * (a + b) = 9 * (n * w ^ 3) := by
    rw [hQ, hw] at hf
    nlinarith only [hf]
  exact Int.prime_three.pow_dvd_of_dvd_mul_left 2 hq (by
    simpa using (show (3 : ℤ) ^ 2 ∣ q * (a + b) from ⟨n * w ^ 3, hf'⟩))

lemma common_prime_dvd_c {n a b c p : ℤ} (hn : n = 2 ∨ n = 4) (hp : Prime p)
    (h : a ^ 3 + b ^ 3 = n * c ^ 3) (ha : p ∣ a) (hb : p ∣ b) : p ∣ c := by
  by_cases hpn : p ∣ n
  · have hp2 : p ∣ 2 := by
      rcases hn with rfl | rfl
      · exact hpn
      · exact hp.dvd_of_dvd_pow (show p ∣ (2 : ℤ) ^ 2 from by norm_num; exact hpn)
    have hassoc := hp.associated_of_dvd Int.prime_two hp2
    have ha2 : 2 ∣ a := hassoc.dvd_iff_dvd_left.mp ha
    have hb2 : 2 ∣ b := hassoc.dvd_iff_dvd_left.mp hb
    obtain ⟨u, rfl⟩ := ha2
    obtain ⟨v, rfl⟩ := hb2
    have hc3 : 2 ∣ c ^ 3 := by
      rcases hn with rfl | rfl
      · refine ⟨2 * (u ^ 3 + v ^ 3), ?_⟩
        nlinarith only [h]
      · refine ⟨u ^ 3 + v ^ 3, ?_⟩
        nlinarith only [h]
    exact hassoc.dvd_iff_dvd_left.mpr (Int.prime_two.dvd_of_dvd_pow hc3)
  · have hd : p ∣ n * c ^ 3 := h ▸ dvd_add (dvd_pow ha (by decide : 3 ≠ 0))
      (dvd_pow hb (by decide : 3 ≠ 0))
    exact hp.dvd_of_dvd_pow ((hp.dvd_mul.mp hd).resolve_left hpn)

lemma int_cube_factor {a b c : ℤ} (hab : IsCoprime a b) (h : a * b = c ^ 3) :
    ∃ r : ℤ, a = r ^ 3 := by
  obtain ⟨r, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hab h
  have hunit : (u : ℤ) = 1 ∨ (u : ℤ) = -1 := Int.isUnit_iff.mp u.isUnit
  rcases hunit with hu1 | hu1
  · exact ⟨r, by simpa [hu1] using hu.symm⟩
  · exact ⟨-r, by rw [hu1] at hu; linear_combination -hu⟩

lemma quotient_is_cube {n v c s : ℤ} (hn : n ≠ 0) (hv : v ≠ 0)
    (hns : n ∣ s) (h : s * v ^ 3 = n * c ^ 3) :
    ∃ u : ℤ, s = n * u ^ 3 ∧ c = v * u := by
  obtain ⟨w, hw⟩ := hns
  have hh : w * v ^ 3 = c ^ 3 := by
    apply (mul_left_inj' hn).mp
    rw [hw] at h
    linear_combination h
  have hvc : v ∣ c := (Int.pow_dvd_pow_iff (by decide : 3 ≠ 0)).mp ⟨w, by nlinarith only [hh]⟩
  obtain ⟨u, hu⟩ := hvc
  have hw' : w = u ^ 3 := by
    apply (mul_right_inj' (pow_ne_zero 3 hv)).mp
    rw [hu] at hh
    linear_combination hh
  exact ⟨u, by rw [hw, hw'], hu⟩

end Arithmetic


namespace Eisenstein

open Arithmetic

lemma coprime_pair_coefficient {n a b c : ℤ} (hn : n = 2 ∨ n = 4)
    (hab : IsCoprime a b) (h : a ^ 3 + b ^ 3 = n * c ^ 3) :
    IsCoprime (pair a b) (n : E) := by
  have ho := entries_odd hn hab h
  have hQ : IsCoprime (n : E) (qnorm a b : E) :=
    (norm_coprime_coefficient hn ho.1 ho.2).intCast
  rw [← pair_mul_conj] at hQ
  exact hQ.of_mul_right_left.symm

lemma cube_associated_unramified {n a b c : ℤ} (hn : n = 2 ∨ n = 4)
    (hab : IsCoprime a b) (h : a ^ 3 + b ^ 3 = n * c ^ 3) (hs : ¬3 ∣ a + b) :
    ∃ (u : Eˣ) (z : E), pair a b = u * z ^ 3 := by
  have hA : pair a b ≠ 0 := pair_ne_zero hab.ne_zero_or_ne_zero
  have hl : ¬lambda ∣ pair a b := by rwa [lambda_dvd_pair_iff]
  have hAS : IsCoprime (pair a b) ((a + b : ℤ) : E) := by
    refine isCoprime_of_prime_dvd (fun hh => hA hh.1) (fun p hp hpa hps => ?_)
    exact hl ((common_prime_sum hab hp hpa hps).dvd_iff_dvd_left.mp hpa)
  have hAC : IsCoprime (pair a b) (conj a b) := by
    refine isCoprime_of_prime_dvd (fun hh => hA hh.1) (fun p hp hpa hpc => ?_)
    exact hl ((common_prime_conj hab hp hpa hpc).dvd_iff_dvd_left.mp hpa)
  have hAN := coprime_pair_coefficient hn hab h
  have hcop := (hAC.mul_right hAS).mul_right (hAN.pow_right (n := 2))
  have he : ((a + b : ℤ) : E) * pair a b * conj a b = (n : E) * (c : E) ^ 3 := by
    rw [factorization]
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_mul] using congrArg (Int.cast : ℤ → E) h
  have he' : pair a b * (conj a b * ((a + b : ℤ) : E) * (n : E) ^ 2) =
      ((n : E) * (c : E)) ^ 3 := by
    linear_combination (n : E) ^ 2 * he
  obtain ⟨z, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hcop he'
  exact ⟨u, z, by rw [← hu]; ring⟩

lemma lambda_sq_dvd_three : lambda ^ 2 ∣ (3 : E) := by
  refine ⟨-ω ^ 2, ?_⟩
  rw [lambda_sq]
  linear_combination -3 * omega_cube

lemma lambda_sq_dvd_int {a : ℤ} (ha : 3 ∣ a) : lambda ^ 2 ∣ (a : E) := by
  apply dvd_trans lambda_sq_dvd_three
  obtain ⟨r, hr⟩ := ha
  refine ⟨(r : E), ?_⟩
  simpa only [Int.cast_mul, Int.cast_ofNat] using congrArg (Int.cast : ℤ → E) hr

lemma lambda_sq_not_dvd_pair {a b : ℤ} (hs : 3 ∣ a + b) (hb : ¬3 ∣ b) :
    ¬lambda ^ 2 ∣ pair a b := by
  intro hd
  have hS := lambda_sq_dvd_int hs
  have hd' : lambda ^ 2 ∣ lambda * (b : E) := by
    convert dvd_sub hd hS using 1
    simp only [pair, lambda, Int.cast_add]
    ring
  rw [pow_two, mul_dvd_mul_iff_left lambda_prime.ne_zero] at hd'
  exact hb ((lambda_dvd_int_iff b).mp hd')

lemma lambda_dvd_conj_iff (a b : ℤ) : lambda ∣ conj a b ↔ 3 ∣ a + b := by
  rw [conj_eq_pair, lambda_dvd_pair_iff]
  constructor
  · intro hd
    convert dvd_add hd (dvd_mul_right (3 : ℤ) b) using 1
    ring
  · intro hd
    convert dvd_sub hd (dvd_mul_right (3 : ℤ) b) using 1
    ring

lemma cube_associated_ramified {n a b c : ℤ} (hn : n = 2 ∨ n = 4)
    (hab : IsCoprime a b) (h : a ^ 3 + b ^ 3 = n * c ^ 3) (hs : 3 ∣ a + b) :
    ∃ (u : Eˣ) (z : E), pair a b = u * lambda * z ^ 3 := by
  have he := ramified_entries hab hs
  have hA2 := lambda_sq_not_dvd_pair hs he.2
  have hC2 : ¬lambda ^ 2 ∣ conj a b := by
    rw [conj_eq_pair]
    apply lambda_sq_not_dvd_pair
    · convert dvd_sub hs (dvd_mul_right (3 : ℤ) b) using 1
      ring
    · simpa using he.2
  obtain ⟨y, hy⟩ := (lambda_dvd_pair_iff a b).mpr hs
  obtain ⟨z, hz⟩ := (lambda_dvd_conj_iff a b).mpr hs
  have hyl : ¬lambda ∣ y := by
    intro hd
    apply hA2
    rw [hy, pow_two]
    exact mul_dvd_mul_left lambda hd
  have hzl : ¬lambda ∣ z := by
    intro hd
    apply hC2
    rw [hz, pow_two]
    exact mul_dvd_mul_left lambda hd
  have hy0 : y ≠ 0 := by intro hzero; exact hyl (by simp [hzero])
  have hyA : y ∣ pair a b := by rw [hy]; exact dvd_mul_left y lambda
  have hzC : z ∣ conj a b := by rw [hz]; exact dvd_mul_left z lambda
  have hyz : IsCoprime y z := by
    refine isCoprime_of_prime_dvd (fun hh => hy0 hh.1) (fun p hp hpy hpz => ?_)
    exact hyl ((common_prime_conj hab hp (dvd_trans hpy hyA) (dvd_trans hpz hzC)).dvd_iff_dvd_left.mp hpy)
  have hyS : IsCoprime y ((a + b : ℤ) : E) := by
    refine isCoprime_of_prime_dvd (fun hh => hy0 hh.1) (fun p hp hpy hpS => ?_)
    exact hyl ((common_prime_sum hab hp (dvd_trans hpy hyA) hpS).dvd_iff_dvd_left.mp hpy)
  have hyn : IsCoprime y (n : E) := (coprime_pair_coefficient hn hab h).of_isCoprime_of_dvd_left hyA
  have hyl' : IsCoprime y lambda := (lambda_prime.coprime_iff_not_dvd.mpr hyl).symm
  have hc : lambda ∣ (c : E) := by
    apply dvd_trans (dvd_trans (dvd_pow_self lambda (by decide : 2 ≠ 0)) lambda_sq_dvd_three)
    obtain ⟨r, hr⟩ := (sum_three_iff_c hn h).mp hs
    refine ⟨(r : E), ?_⟩
    simpa only [Int.cast_mul, Int.cast_ofNat] using congrArg (Int.cast : ℤ → E) hr
  obtain ⟨w, hw⟩ := hc
  have hf : ((a + b : ℤ) : E) * pair a b * conj a b = (n : E) * (c : E) ^ 3 := by
    rw [factorization]
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_mul] using congrArg (Int.cast : ℤ → E) h
  have hf' : y * z * ((a + b : ℤ) : E) = (n : E) * lambda * w ^ 3 := by
    apply (mul_left_inj' (pow_ne_zero 2 lambda_prime.ne_zero)).mp
    rw [hy, hz, hw] at hf
    linear_combination hf
  have hf'' : y * (z * ((a + b : ℤ) : E) * (n : E) ^ 2 * lambda ^ 2) =
      ((n : E) * lambda * w) ^ 3 := by
    linear_combination (n : E) ^ 2 * lambda ^ 2 * hf'
  have hcop := ((hyz.mul_right hyS).mul_right (hyn.pow_right (n := 2))).mul_right
    (hyl'.pow_right (n := 2))
  obtain ⟨v, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hcop hf''
  exact ⟨u, v, by rw [hy, ← hu]; ring⟩

lemma cubeA_not_three {r s : ℤ} (hrs : ¬3 ∣ r + s) : ¬3 ∣ cubeA r s := by
  intro hd
  have hd' : ((cubeA r s : ℤ) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
  have hc (x : ZMod 3) : x ^ 3 = x := by revert x; decide
  have hcast : ((cubeA r s : ℤ) : ZMod 3) = ((r + s : ℤ) : ZMod 3) := by
    simp only [cubeA, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    rw [show (3 : ZMod 3) = 0 by decide]
    simp [hc]
  exact hrs ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (hcast.symm.trans hd'))

lemma cube_unramified {a b : ℤ} (ha : ¬3 ∣ a) (hb : ¬3 ∣ b)
    (h : ∃ (u : Eˣ) (z : E), pair a b = u * z ^ 3) :
    ∃ z : E, pair a b = ω ^ 2 * z ^ 3 := by
  obtain ⟨u, z, h⟩ := h
  obtain ⟨r, s, rfl⟩ := exists_pair z
  have hu := Units.mem root_primitive u
  fin_cases hu
  · have hh := pair_inj (by simpa only [Units.val_one, one_mul, pair_cube] using h)
    exact (hb ⟨r * s * (r - s), by rw [hh.2]; unfold cubeB; ring⟩).elim
  · have hh := pair_inj (by simpa only [Units.val_neg, Units.val_one, neg_one_mul,
        pair_cube, pair_neg] using h)
    exact (hb ⟨-(r * s * (r - s)), by rw [hh.2]; unfold cubeB; ring⟩).elim
  · have hh := pair_inj (by simpa only [IsUnit.unit_spec, omega_def, pair_cube, omega_mul_pair] using h)
    exact (ha ⟨-(r * s * (r - s)), by rw [hh.1]; unfold cubeB; ring⟩).elim
  · have hh := pair_inj (by simpa only [Units.val_neg, IsUnit.unit_spec, omega_def, neg_mul,
        pair_cube, omega_mul_pair, pair_neg] using h)
    exact (ha ⟨r * s * (r - s), by rw [hh.1]; unfold cubeB; ring⟩).elim
  · exact ⟨pair r s, by simpa only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, omega_def] using h⟩
  · refine ⟨-pair r s, ?_⟩
    have hh : pair a b = -(ω ^ 2 * pair r s ^ 3) := by
      simpa only [Units.val_neg, Units.val_pow_eq_pow_val, IsUnit.unit_spec, omega_def, neg_mul] using h
    rw [hh]
    ring


lemma cubeB_three (r s : ℤ) : 3 ∣ cubeB r s := by
  exact ⟨r * s * (r - s), by unfold cubeB; ring⟩

lemma three_dvd_of_nine_dvd_three_mul {x : ℤ} (h : 9 ∣ 3 * x) : 3 ∣ x := by
  apply (mul_dvd_mul_iff_left (by decide : (3 : ℤ) ≠ 0)).mp
  simpa using h

lemma lambda_not_dvd_ramified_base {a b : ℤ} {u z : E}
    (h : pair a b = u * lambda * z ^ 3) (h2 : ¬lambda ^ 2 ∣ pair a b) : ¬lambda ∣ z := by
  rintro ⟨w, hw⟩
  apply h2
  refine ⟨u * lambda ^ 2 * w ^ 3, ?_⟩
  rw [h, hw]
  ring

lemma cube_ramified {a b : ℤ} (h9 : 9 ∣ a + b) (h2 : ¬lambda ^ 2 ∣ pair a b)
    (h : ∃ (u : Eˣ) (z : E), pair a b = u * lambda * z ^ 3) :
    ∃ z : E, pair a b = lambda * z ^ 3 := by
  obtain ⟨u, z, h⟩ := h
  have hzl := lambda_not_dvd_ramified_base h h2
  obtain ⟨r, s, rfl⟩ := exists_pair z
  have hA : ¬3 ∣ cubeA r s := cubeA_not_three (by rwa [lambda_dvd_pair_iff] at hzl)
  have hB := cubeB_three r s
  have hu := Units.mem root_primitive u
  fin_cases hu
  · exact ⟨pair r s, by simpa only [Units.val_one, one_mul] using h⟩
  · refine ⟨-pair r s, ?_⟩
    have hh : pair a b = -(lambda * pair r s ^ 3) := by
      simpa only [Units.val_neg, Units.val_one, neg_one_mul, neg_mul, one_mul] using h
    rw [hh]
    ring
  · have hh : pair a b = ω * (lambda * pair r s ^ 3) := by
      simpa only [IsUnit.unit_spec, omega_def, mul_assoc] using h
    rw [pair_cube, lambda_mul_pair, omega_mul_pair] at hh
    have hc := pair_inj hh
    have hd : 9 ∣ 3 * (cubeA r s - cubeB r s) := by
      rw [hc.1, hc.2] at h9
      convert h9.neg_right using 1
      ring
    exact (hA (by convert dvd_add (three_dvd_of_nine_dvd_three_mul hd) hB using 1; ring)).elim
  · have hh : pair a b = -(ω * (lambda * pair r s ^ 3)) := by
      simpa only [Units.val_neg, IsUnit.unit_spec, omega_def, mul_assoc, neg_mul] using h
    rw [pair_cube, lambda_mul_pair, omega_mul_pair, pair_neg] at hh
    have hc := pair_inj hh
    have hd : 9 ∣ 3 * (cubeA r s - cubeB r s) := by
      rw [hc.1, hc.2] at h9
      convert h9 using 1
      ring
    exact (hA (by convert dvd_add (three_dvd_of_nine_dvd_three_mul hd) hB using 1; ring)).elim
  · have hh : pair a b = ω ^ 2 * (lambda * pair r s ^ 3) := by
      simpa only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, omega_def, mul_assoc] using h
    rw [pair_cube, lambda_mul_pair, omega_sq_mul_pair] at hh
    have hc := pair_inj hh
    have hd : 9 ∣ 3 * cubeA r s := by
      rw [hc.1, hc.2] at h9
      convert h9 using 1
      ring
    exact (hA (three_dvd_of_nine_dvd_three_mul hd)).elim
  · have hh : pair a b = -(ω ^ 2 * (lambda * pair r s ^ 3)) := by
      simpa only [Units.val_neg, Units.val_pow_eq_pow_val, IsUnit.unit_spec, omega_def,
        mul_assoc, neg_mul] using h
    rw [pair_cube, lambda_mul_pair, omega_sq_mul_pair, pair_neg] at hh
    have hc := pair_inj hh
    have hd : 9 ∣ 3 * cubeA r s := by
      rw [hc.1, hc.2] at h9
      convert h9.neg_right using 1
      ring
    exact (hA (three_dvd_of_nine_dvd_three_mul hd)).elim

lemma unramified_parameters {n a b c : ℤ} (hn : n = 2 ∨ n = 4) (hab : IsCoprime a b)
    (h : a ^ 3 + b ^ 3 = n * c ^ 3) (hs : ¬3 ∣ a + b) :
    ∃ r s : ℤ, IsCoprime r s ∧ ¬3 ∣ r + s ∧
      a = cubeB r s - cubeA r s ∧ b = -cubeA r s ∧ qnorm a b = qnorm r s ^ 3 := by
  have he := unramified_entries hn h hs
  obtain ⟨z, hz⟩ := cube_unramified he.2.1 he.2.2 (cube_associated_unramified hn hab h hs)
  obtain ⟨r, s, rfl⟩ := exists_pair z
  have hc := coprime_coords_of_cube hab hz
  have hl : ¬lambda ∣ pair r s := by
    intro hd
    apply hs
    rw [← lambda_dvd_pair_iff a b, hz]
    exact dvd_mul_of_dvd_right (dvd_pow hd (by decide : 3 ≠ 0)) (ω ^ 2)
  have hcoeff : a = cubeB r s - cubeA r s ∧ b = -cubeA r s :=
    pair_inj (by simpa only [pair_cube, omega_sq_mul_pair] using hz)
  refine ⟨r, s, hc, by rwa [lambda_dvd_pair_iff] at hl, hcoeff.1, hcoeff.2, ?_⟩
  rw [hcoeff.1, hcoeff.2, norm_omega_sq, norm_cube]

lemma ramified_parameters {n a b c : ℤ} (hn : n = 2 ∨ n = 4) (hab : IsCoprime a b)
    (h : a ^ 3 + b ^ 3 = n * c ^ 3) (hs : 3 ∣ a + b) :
    ∃ r s : ℤ, IsCoprime r s ∧ ¬3 ∣ r + s ∧
      a = -cubeA r s - cubeB r s ∧ b = cubeA r s - 2 * cubeB r s ∧
      qnorm a b = 3 * qnorm r s ^ 3 := by
  have he := ramified_entries hab hs
  have h2 := lambda_sq_not_dvd_pair hs he.2
  obtain ⟨z, hz⟩ := cube_ramified (ramified_sum_nine hn hab h hs) h2
    (cube_associated_ramified hn hab h hs)
  obtain ⟨r, s, rfl⟩ := exists_pair z
  have hz' : pair a b = (1 : E) * lambda * pair r s ^ 3 := by simpa using hz
  have hc := coprime_coords_of_cube hab hz
  have hl := lambda_not_dvd_ramified_base hz' h2
  have hcoeff : a = -cubeA r s - cubeB r s ∧ b = cubeA r s - 2 * cubeB r s :=
    pair_inj (by simpa only [pair_cube, lambda_mul_pair] using hz)
  refine ⟨r, s, hc, by rwa [lambda_dvd_pair_iff] at hl, hcoeff.1, hcoeff.2, ?_⟩
  rw [hcoeff.1, hcoeff.2, norm_lambda, norm_cube]

end Eisenstein


/-- A nonzero cubic solution, with the diagonal solutions removed for coefficient two. -/
structure BadCubic (n a b c : ℤ) : Prop where
  left_ne : a ≠ 0
  right_ne : b ≠ 0
  center_ne : c ≠ 0
  equation : a ^ 3 + b ^ 3 = n * c ^ 3
  nontrivial : n = 2 → a ≠ b

namespace Arithmetic

lemma coefficient_coprime {n x : ℤ} (hn : n = 2 ∨ n = 4) (hx : ¬2 ∣ x) : IsCoprime n x := by
  have hh := Int.prime_two.coprime_iff_not_dvd.mpr hx
  rcases hn with rfl | rfl
  · exact hh
  · simpa using (hh.pow_left (m := 2))

lemma cube_factors_three {L M R u : ℤ}
    (hLM : IsCoprime L M) (hLR : IsCoprime L R) (hMR : IsCoprime M R)
    (h : L * M * R = u ^ 3) : ∃ x y z : ℤ, L = x ^ 3 ∧ M = y ^ 3 ∧ R = z ^ 3 := by
  obtain ⟨x, hx⟩ := int_cube_factor (hLM.mul_right hLR) (by simpa [mul_assoc] using h)
  obtain ⟨y, hy⟩ := int_cube_factor (hLM.symm.mul_right hMR)
    (show M * (L * R) = u ^ 3 by linear_combination h)
  obtain ⟨z, hz⟩ := int_cube_factor (hLR.symm.mul_right hMR.symm)
    (show R * (L * M) = u ^ 3 by linear_combination h)
  exact ⟨x, y, z, hx, hy, hz⟩

lemma split_coefficient_left {n L M R u : ℤ} (hn : n = 2 ∨ n = 4)
    (hLM : IsCoprime L M) (hLR : IsCoprime L R) (hMR : IsCoprime M R)
    (h : L * M * R = n * u ^ 3) (hL : 2 ∣ L) :
    ∃ x y z : ℤ, L = n * x ^ 3 ∧ M = y ^ 3 ∧ R = z ^ 3 := by
  have hM : ¬2 ∣ M := fun hd => Int.prime_two.not_unit (hLM.isUnit_of_dvd' hL hd)
  have hR : ¬2 ∣ R := fun hd => Int.prime_two.not_unit (hLR.isUnit_of_dvd' hL hd)
  have hncop := (coefficient_coprime hn hM).mul_right (coefficient_coprime hn hR)
  have hnL : n ∣ L := hncop.dvd_of_dvd_mul_right (show n ∣ L * (M * R) from
    ⟨u ^ 3, by linear_combination h⟩)
  obtain ⟨w, hw⟩ := hnL
  have hwL : w ∣ L := ⟨n, by rw [hw]; ring⟩
  have hprod : w * M * R = u ^ 3 := by
    apply (mul_left_inj' (coefficient_pos hn).ne').mp
    rw [hw] at h
    linear_combination h
  obtain ⟨x, y, z, hx, hy, hz⟩ := cube_factors_three
    (hLM.of_isCoprime_of_dvd_left hwL) (hLR.of_isCoprime_of_dvd_left hwL) hMR hprod
  exact ⟨x, y, z, by rw [hw, hx], hy, hz⟩

lemma split_coefficient {n L M R u : ℤ} (hn : n = 2 ∨ n = 4)
    (hLM : IsCoprime L M) (hLR : IsCoprime L R) (hMR : IsCoprime M R)
    (h : L * M * R = n * u ^ 3) :
    (∃ x y z : ℤ, L = n * x ^ 3 ∧ M = y ^ 3 ∧ R = z ^ 3) ∨
    (∃ x y z : ℤ, L = x ^ 3 ∧ M = n * y ^ 3 ∧ R = z ^ 3) ∨
    (∃ x y z : ℤ, L = x ^ 3 ∧ M = y ^ 3 ∧ R = n * z ^ 3) := by
  have h2n : 2 ∣ n := by rcases hn with rfl | rfl <;> norm_num
  have h2prod : 2 ∣ L * M * R := h ▸ dvd_mul_of_dvd_left h2n (u ^ 3)
  rcases Int.prime_two.dvd_mul.mp h2prod with hLM2 | hR
  · rcases Int.prime_two.dvd_mul.mp hLM2 with hL | hM
    · exact Or.inl (split_coefficient_left hn hLM hLR hMR h hL)
    · obtain ⟨y, x, z, hy, hx, hz⟩ := split_coefficient_left hn hLM.symm hMR hLR
        (show M * L * R = n * u ^ 3 by linear_combination h) hM
      exact Or.inr (Or.inl ⟨x, y, z, hx, hy, hz⟩)
  · obtain ⟨z, x, y, hz, hx, hy⟩ := split_coefficient_left hn hLR.symm hMR.symm hLM
      (show R * L * M = n * u ^ 3 by linear_combination h) hR
    exact Or.inr (Or.inr ⟨x, y, z, hx, hy, hz⟩)

lemma solution_of_three_factors {n L M R u : ℤ} (hn : n = 2 ∨ n = 4)
    (hLM : IsCoprime L M) (hLR : IsCoprime L R) (hMR : IsCoprime M R)
    (h : L * M * R = n * u ^ 3) (hrel : L + R = M)
    (hL : L ≠ 0) (hM : M ≠ 0) (hR : R ≠ 0)
    (hguard : n = 2 → L ≠ R ∧ L + M ≠ 0 ∧ M + R ≠ 0) :
    ∃ a b c : ℤ, BadCubic n a b c ∧
      (L = n * c ^ 3 ∨ M = n * c ^ 3 ∨ R = n * c ^ 3) := by
  rcases split_coefficient hn hLM hLR hMR h with hf | hf | hf
  · obtain ⟨x, y, z, hx, hy, hz⟩ := hf
    have hx0 : x ≠ 0 := by intro he; apply hL; simp [hx, he]
    have hy0 : y ≠ 0 := by intro he; apply hM; simp [hy, he]
    have hz0 : z ≠ 0 := by intro he; apply hR; simp [hz, he]
    refine ⟨y, -z, x, ⟨hy0, neg_ne_zero.mpr hz0, hx0, ?_, ?_⟩, Or.inl hx⟩
    · rw [hx, hy, hz] at hrel
      linear_combination -hrel
    · intro hn2 he
      apply (hguard hn2).2.2
      rw [hy, hz, he]
      ring
  · obtain ⟨x, y, z, hx, hy, hz⟩ := hf
    have hx0 : x ≠ 0 := by intro he; apply hL; simp [hx, he]
    have hy0 : y ≠ 0 := by intro he; apply hM; simp [hy, he]
    have hz0 : z ≠ 0 := by intro he; apply hR; simp [hz, he]
    refine ⟨x, z, y, ⟨hx0, hz0, hy0, ?_, ?_⟩, Or.inr (Or.inl hy)⟩
    · rw [hx, hy, hz] at hrel
      linear_combination hrel
    · intro hn2 he
      apply (hguard hn2).1
      rw [hx, hz, he]
  · obtain ⟨x, y, z, hx, hy, hz⟩ := hf
    have hx0 : x ≠ 0 := by intro he; apply hL; simp [hx, he]
    have hy0 : y ≠ 0 := by intro he; apply hM; simp [hy, he]
    have hz0 : z ≠ 0 := by intro he; apply hR; simp [hz, he]
    refine ⟨y, -x, z, ⟨hy0, neg_ne_zero.mpr hx0, hz0, ?_, ?_⟩, Or.inr (Or.inr hz)⟩
    · rw [hx, hy, hz] at hrel
      linear_combination -hrel
    · intro hn2 he
      apply (hguard hn2).2.1
      rw [hx, hy, he]
      ring

end Arithmetic


namespace Arithmetic

open Eisenstein

lemma coprime_of_triple_divisibility {r s L M : ℤ} (hrs : IsCoprime r s) (hL : ¬3 ∣ L)
    (hdet : ∀ p : ℤ, p ∣ L → p ∣ M → p ∣ 3 * r ∧ p ∣ 3 * s) : IsCoprime L M := by
  refine isCoprime_of_prime_dvd ?_ (fun p hp hpL hpM => ?_)
  · intro hz
    exact hL (by simp [hz.1])
  · obtain ⟨hpr, hps⟩ := hdet p hpL hpM
    by_cases hp3 : p ∣ 3
    · exact hL ((hp.associated_of_dvd Int.prime_three hp3).dvd_iff_dvd_left.mp hpL)
    · have hpr' := (hp.dvd_mul.mp hpr).resolve_left hp3
      have hps' := (hp.dvd_mul.mp hps).resolve_left hp3
      exact hp.not_unit (hrs.isUnit_of_dvd' hpr' hps')

lemma unramified_coprime_factors {r s : ℤ} (hrs : IsCoprime r s) (h3 : ¬3 ∣ r + s) :
    IsCoprime (r + s) (2 * r - s) ∧ IsCoprime (r + s) (r - 2 * s) ∧
      IsCoprime (2 * r - s) (r - 2 * s) := by
  have hL2 : ¬3 ∣ 2 * r - s := by
    intro hd
    apply h3
    convert dvd_sub (dvd_mul_right (3 : ℤ) r) hd using 1
    ring
  refine ⟨?_, ?_, ?_⟩
  · apply coprime_of_triple_divisibility hrs h3
    intro p hpL hpM
    constructor
    · convert dvd_add hpL hpM using 1; ring
    · convert dvd_sub (dvd_mul_of_dvd_left hpL 2) hpM using 1; ring
  · apply coprime_of_triple_divisibility hrs h3
    intro p hpL hpM
    constructor
    · convert dvd_add (dvd_mul_of_dvd_left hpL 2) hpM using 1; ring
    · convert dvd_sub hpL hpM using 1; ring
  · apply coprime_of_triple_divisibility hrs hL2
    intro p hpL hpM
    constructor
    · convert dvd_sub (dvd_mul_of_dvd_left hpL 2) hpM using 1; ring
    · convert dvd_sub hpL (dvd_mul_of_dvd_left hpM 2) using 1; ring

lemma unramified_bounds (r s : ℤ) :
    (r + s) ^ 2 ≤ 4 * qnorm r s ∧ (2 * r - s) ^ 2 ≤ 4 * qnorm r s ∧
      (r - 2 * s) ^ 2 ≤ 4 * qnorm r s := by
  unfold qnorm
  exact ⟨by nlinarith [sq_nonneg (r - s)], by nlinarith [sq_nonneg s],
    by nlinarith [sq_nonneg r]⟩

lemma ramified_bounds (r s : ℤ) :
    3 * r ^ 2 ≤ 4 * qnorm r s ∧ 3 * s ^ 2 ≤ 4 * qnorm r s ∧
      3 * (r - s) ^ 2 ≤ 4 * qnorm r s := by
  unfold qnorm
  exact ⟨by nlinarith [sq_nonneg (r - 2 * s)], by nlinarith [sq_nonneg (2 * r - s)],
    by nlinarith [sq_nonneg (r + s)]⟩

lemma sixth_power_abs_bound {c v : ℤ} (hv : 0 ≤ v) (h : c ^ 6 ≤ v) :
    c.natAbs ^ 6 ≤ v.natAbs := by
  have hh : (c.natAbs : ℤ) ^ 6 ≤ (v.natAbs : ℤ) := by
    rw [Int.natCast_natAbs, (by decide : Even 6).pow_abs, Int.natAbs_of_nonneg hv]
    exact h
  exact_mod_cast hh

lemma unramified_height_decrease {c v C : ℤ} (hv : 2 ≤ v) (hC : C ≠ 0)
    (hdiv : v ∣ C) (h : (2 * c ^ 3) ^ 2 ≤ 4 * v) : c.natAbs < C.natAbs := by
  have h6 : c ^ 6 ≤ v := by nlinarith only [h]
  have h6N := sixth_power_abs_bound (by omega : 0 ≤ v) h6
  have hv2 : 2 ≤ v.natAbs := by
    have hh : (2 : ℤ) ≤ (v.natAbs : ℤ) := by rwa [Int.natAbs_of_nonneg (by omega)]
    exact_mod_cast hh
  have hc : c.natAbs < v.natAbs := by
    by_contra hn
    have hp := (Nat.pow_le_pow_left (by omega : v.natAbs ≤ c.natAbs) 6).trans h6N
    have hp' : v.natAbs < v.natAbs ^ 6 := by
      simpa using Nat.pow_lt_pow_right (by omega : 1 < v.natAbs) (by decide : 1 < 6)
    omega
  exact hc.trans_le (Int.natAbs_le_of_dvd_ne_zero hdiv hC)

lemma ramified_height_decrease {n c v C : ℤ} (hn : n = 2 ∨ n = 4) (hv : 0 < v)
    (hC : C ≠ 0) (hdiv : 3 * v ∣ C) (h : 3 * (n * c ^ 3) ^ 2 ≤ 4 * v) :
    c.natAbs < C.natAbs := by
  have h6 : c ^ 6 ≤ v := by
    rcases hn with rfl | rfl <;> nlinarith [sq_nonneg (c ^ 3)]
  have h6N := sixth_power_abs_bound hv.le h6
  have hc : c.natAbs ≤ v.natAbs := (Nat.le_self_pow (by decide : 6 ≠ 0) _).trans h6N
  have hvN : 0 < v.natAbs := Int.natAbs_pos.mpr hv.ne'
  have hdivN : 3 * v.natAbs ≤ C.natAbs := by
    simpa [Int.natAbs_mul] using Int.natAbs_le_of_dvd_ne_zero hdiv hC
  omega

end Arithmetic

/- ## Complete infinite descent -/

private def MinimalBadCubic (n a b c : ℤ) : Prop :=
  BadCubic n a b c ∧ ∀ a' b' c' : ℤ, BadCubic n a' b' c' → c.natAbs ≤ c'.natAbs

private theorem exists_minimal_bad_cubic {n a b c : ℤ} (h : BadCubic n a b c) :
    ∃ a' b' c' : ℤ, MinimalBadCubic n a' b' c' := by
  classical
  have hex : ∃ m : ℕ, ∃ a' b' c' : ℤ, BadCubic n a' b' c' ∧ c'.natAbs = m :=
    ⟨c.natAbs, a, b, c, h, rfl⟩
  obtain ⟨a', b', c', hh, hc⟩ := Nat.find_spec hex
  refine ⟨a', b', c', hh, ?_⟩
  intro a'' b'' c'' hbad
  rw [hc]
  exact Nat.find_min' hex ⟨a'', b'', c'', hbad, rfl⟩

private theorem minimal_bad_cubic_coprime {n a b c : ℤ} (hn : n = 2 ∨ n = 4)
    (h : MinimalBadCubic n a b c) : IsCoprime a b := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hg
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hg
  have hpa' : (p : ℤ) ∣ a := Int.natCast_dvd.mpr hpa
  have hpb' : (p : ℤ) ∣ b := Int.natCast_dvd.mpr hpb
  have hp' : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hpc := Arithmetic.common_prime_dvd_c hn hp' h.1.equation hpa' hpb'
  obtain ⟨a', ha⟩ := hpa'
  obtain ⟨b', hb⟩ := hpb'
  obtain ⟨c', hc⟩ := hpc
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hh : BadCubic n a' b' c' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hz; apply h.1.left_ne; simp [ha, hz]
    · intro hz; apply h.1.right_ne; simp [hb, hz]
    · intro hz; apply h.1.center_ne; simp [hc, hz]
    · apply (mul_left_inj' (pow_ne_zero 3 hp0)).mp
      have he := h.1.equation
      rw [ha, hb, hc] at he
      linear_combination he
    · intro hn2 he
      apply h.1.nontrivial hn2
      rw [ha, hb, he]
  have hlt : c'.natAbs < c.natAbs := by
    rw [hc, Int.natAbs_mul, Int.natAbs_natCast]
    exact lt_mul_of_one_lt_left (Int.natAbs_pos.mpr hh.center_ne) hp.one_lt
  exact (not_le_of_gt hlt) (h.2 a' b' c' hh)


private theorem unramified_bad_cubic_descent {a b c : ℤ} (h : BadCubic 2 a b c)
    (hab : IsCoprime a b) (hs : ¬3 ∣ a + b) :
    ∃ a' b' c' : ℤ, BadCubic 2 a' b' c' ∧ c'.natAbs < c.natAbs := by
  open Eisenstein Arithmetic in
  obtain ⟨r, s, hrs, h3, ha, hb, hQ⟩ := unramified_parameters (Or.inl rfl) hab h.equation hs
  have hB : Eisenstein.cubeB r s ≠ 0 := by
    intro hd
    apply h.nontrivial rfl
    rw [ha, hb, hd]
    ring
  have hr : r ≠ 0 := by intro hz; apply hB; simp [Eisenstein.cubeB, hz]
  have hs' : s ≠ 0 := by intro hz; apply hB; simp [Eisenstein.cubeB, hz]
  have hrs' : r - s ≠ 0 := by intro hz; apply hB; simp [Eisenstein.cubeB, hz]
  have hv2 : 2 ≤ Eisenstein.qnorm r s := by
    have hr2 : 1 ≤ r ^ 2 := by have hh := sq_pos_of_ne_zero hr; omega
    have hs2 : 1 ≤ s ^ 2 := by have hh := sq_pos_of_ne_zero hs'; omega
    have hrs2 : 1 ≤ (r - s) ^ 2 := by have hh := sq_pos_of_ne_zero hrs'; omega
    unfold Eisenstein.qnorm
    nlinarith
  have hv0 : Eisenstein.qnorm r s ≠ 0 := by omega
  have hf : (a + b) * Eisenstein.qnorm a b = 2 * c ^ 3 := by
    unfold Eisenstein.qnorm
    linear_combination h.equation
  rw [hQ] at hf
  obtain ⟨u, hu, hcu⟩ := Arithmetic.quotient_is_cube (by decide : (2 : ℤ) ≠ 0) hv0
    (Arithmetic.sum_even (Or.inl rfl) h.equation) hf
  have hu0 : u ≠ 0 := by intro hz; apply h.center_ne; simp [hcu, hz]
  have hprod : (r + s) * (2 * r - s) * (r - 2 * s) = 2 * (-u) ^ 3 := by
    rw [ha, hb] at hu
    unfold Eisenstein.cubeA Eisenstein.cubeB at hu
    linear_combination -hu
  have hnon : ((r + s) ≠ 0 ∧ (2 * r - s) ≠ 0) ∧ (r - 2 * s) ≠ 0 := by
    simpa only [mul_ne_zero_iff] using
      (show (r + s) * (2 * r - s) * (r - 2 * s) ≠ 0 by
        rw [hprod]; exact mul_ne_zero (by decide) (pow_ne_zero 3 (neg_ne_zero.mpr hu0)))
  have hcop := Arithmetic.unramified_coprime_factors hrs h3
  have hguard : (2 : ℤ) = 2 → (r + s) ≠ (r - 2 * s) ∧
      (r + s) + (2 * r - s) ≠ 0 ∧ (2 * r - s) + (r - 2 * s) ≠ 0 := by
    intro _
    refine ⟨?_, ?_, ?_⟩
    · intro he; apply hs'; omega
    · intro he; apply hr; omega
    · intro he; apply hrs'; omega
  obtain ⟨a', b', c', hnew, hfactor⟩ := Arithmetic.solution_of_three_factors (Or.inl rfl)
    hcop.1 hcop.2.1 hcop.2.2 hprod (by ring) hnon.1.1 hnon.1.2 hnon.2 hguard
  have hbound : (2 * c' ^ 3) ^ 2 ≤ 4 * Eisenstein.qnorm r s := by
    have hh := Arithmetic.unramified_bounds r s
    rcases hfactor with hf' | hf' | hf'
    · rw [← hf']; exact hh.1
    · rw [← hf']; exact hh.2.1
    · rw [← hf']; exact hh.2.2
  exact ⟨a', b', c', hnew,
    Arithmetic.unramified_height_decrease hv2 h.center_ne ⟨u, hcu⟩ hbound⟩

private theorem ramified_bad_cubic_descent {n a b c : ℤ} (hn : n = 2 ∨ n = 4)
    (h : BadCubic n a b c) (hab : IsCoprime a b) (hs : 3 ∣ a + b) :
    ∃ a' b' c' : ℤ, BadCubic n a' b' c' ∧ c'.natAbs < c.natAbs := by
  obtain ⟨r, s, hrs, h3, ha, hb, hQ⟩ := Eisenstein.ramified_parameters hn hab h.equation hs
  have hv := Eisenstein.norm_pos hrs.ne_zero_or_ne_zero
  have ho := Arithmetic.entries_odd hn hab h.equation
  have hvQ : Eisenstein.qnorm r s ∣ Eisenstein.qnorm a b := by
    rw [hQ]
    exact dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 3 ≠ 0)) 3
  have hnV : IsCoprime n (Eisenstein.qnorm r s) :=
    (Arithmetic.norm_coprime_coefficient hn ho.1 ho.2).of_isCoprime_of_dvd_right hvQ
  obtain ⟨w, hw⟩ := (Arithmetic.sum_three_iff_c hn h.equation).mp hs
  have hsum : a + b = -9 * (r * s * (r - s)) := by
    rw [ha, hb]
    unfold Eisenstein.cubeA Eisenstein.cubeB
    ring
  have hf : (a + b) * Eisenstein.qnorm a b = n * c ^ 3 := by
    unfold Eisenstein.qnorm
    linear_combination h.equation
  have hf' : (-(r * s * (r - s))) * Eisenstein.qnorm r s ^ 3 = n * w ^ 3 := by
    rw [hsum, hQ, hw] at hf
    nlinarith only [hf]
  have hnR : n ∣ -(r * s * (r - s)) :=
    (hnV.pow_right (n := 3)).dvd_of_dvd_mul_right ⟨w ^ 3, hf'⟩
  obtain ⟨u, hu, hwu⟩ := Arithmetic.quotient_is_cube (Arithmetic.coefficient_pos hn).ne' hv.ne' hnR hf'
  have hcv : c = 3 * Eisenstein.qnorm r s * u := by rw [hw, hwu]; ring
  have hu0 : u ≠ 0 := by intro hz; apply h.center_ne; simp [hcv, hz]
  have hprod : s * r * (r - s) = n * (-u) ^ 3 := by linear_combination -hu
  have hnon : (s ≠ 0 ∧ r ≠ 0) ∧ r - s ≠ 0 := by
    simpa only [mul_ne_zero_iff] using (show s * r * (r - s) ≠ 0 by
      rw [hprod]
      exact mul_ne_zero (Arithmetic.coefficient_pos hn).ne' (pow_ne_zero 3 (neg_ne_zero.mpr hu0)))
  have hsr : IsCoprime s (r - s) := by
    convert hrs.symm.add_mul_right_right (-1) using 1
    ring
  have hrrs : IsCoprime r (r - s) := by
    convert hrs.neg_right.add_mul_right_right 1 using 1
    ring
  have hguard : n = 2 → s ≠ r - s ∧ s + r ≠ 0 ∧ r + (r - s) ≠ 0 := by
    intro _
    refine ⟨?_, ?_, ?_⟩
    · intro he; apply h3; refine ⟨s, ?_⟩; omega
    · intro he; apply h3; refine ⟨0, ?_⟩; omega
    · intro he; apply h3; refine ⟨r, ?_⟩; omega
  obtain ⟨a', b', c', hnew, hfactor⟩ := Arithmetic.solution_of_three_factors hn hrs.symm hsr hrrs
    hprod (by ring) hnon.1.1 hnon.1.2 hnon.2 hguard
  have hbound : 3 * (n * c' ^ 3) ^ 2 ≤ 4 * Eisenstein.qnorm r s := by
    have hh := Arithmetic.ramified_bounds r s
    rcases hfactor with hf'' | hf'' | hf''
    · rw [← hf'']; exact hh.2.1
    · rw [← hf'']; exact hh.1
    · rw [← hf'']; exact hh.2.2
  exact ⟨a', b', c', hnew,
    Arithmetic.ramified_height_decrease hn hv h.center_ne ⟨u, hcv⟩ hbound⟩

private theorem no_bad_cubic {n a b c : ℤ} (hn : n = 2 ∨ n = 4) : ¬BadCubic n a b c := by
  intro h
  obtain ⟨a', b', c', hmin⟩ := exists_minimal_bad_cubic h
  have hcop := minimal_bad_cubic_coprime hn hmin
  have hdesc : ∃ a'' b'' c'' : ℤ, BadCubic n a'' b'' c'' ∧ c''.natAbs < c'.natAbs := by
    by_cases hs : 3 ∣ a' + b'
    · exact ramified_bad_cubic_descent hn hmin.1 hcop hs
    · have hn2 := (Arithmetic.unramified_entries hn hmin.1.equation hs).1
      rw [hn2] at hmin ⊢
      exact unramified_bad_cubic_descent hmin.1 hcop hs
  obtain ⟨a'', b'', c'', hh, hlt⟩ := hdesc
  exact (not_le_of_gt hlt) (hmin.2 a'' b'' c'' hh)

/-- Classical cubic rigidity, proved by complete infinite descent in the Eisenstein ring. -/
theorem int_cube_add_cube_eq_two_mul_cube {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a ^ 3 + b ^ 3 = 2 * c ^ 3) : a = b ∧ b = c := by
  have hab : a = b := by
    by_contra hn
    exact no_bad_cubic (Or.inl rfl) ⟨ha, hb, hc, h, fun _ => hn⟩
  refine ⟨hab, (by decide : Odd 3).pow_injective ?_⟩
  rw [hab] at h
  nlinarith only [h]

/-- The coefficient-four cubic has no nonzero signed integral solution. -/
theorem int_cube_add_cube_ne_four_mul_cube {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a ^ 3 + b ^ 3 ≠ 4 * c ^ 3 := by
  intro h
  apply no_bad_cubic (Or.inr rfl)
  exact ⟨ha, hb, hc, h, by intro hn; norm_num at hn⟩

/-- Natural-number version of the coefficient-two rigidity. -/
theorem nat_cube_add_cube_eq_two_mul_cube {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a ^ 3 + b ^ 3 = 2 * c ^ 3) : a = b ∧ b = c := by
  have hh := int_cube_add_cube_eq_two_mul_cube (Int.natCast_ne_zero.mpr ha)
    (Int.natCast_ne_zero.mpr hb) (Int.natCast_ne_zero.mpr hc)
    (show (a : ℤ) ^ 3 + (b : ℤ) ^ 3 = 2 * (c : ℤ) ^ 3 by exact_mod_cast h)
  exact ⟨by exact_mod_cast hh.1, by exact_mod_cast hh.2⟩

/-- Natural-number version of the coefficient-four obstruction. -/
theorem nat_cube_add_cube_ne_four_mul_cube {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a ^ 3 + b ^ 3 ≠ 4 * c ^ 3 := by
  intro h
  apply int_cube_add_cube_ne_four_mul_cube (Int.natCast_ne_zero.mpr ha)
    (Int.natCast_ne_zero.mpr hb) (Int.natCast_ne_zero.mpr hc)
  exact_mod_cast h


/- ## Uniform residual-support exclusions -/

open Erdos364.PowerfulStructure Erdos364.AuxiliaryCubeApproximation

/-- Neither neighbor of a multiple of four with only a residual power of two is a cube. -/
theorem two_residual_center_neighbors_not_cubes {t u j x : ℕ} (ht : 2 ≤ t) (h4 : t % 4 = 0)
    (hj : j < 3) (hcenter : t = 2 ^ j * u ^ 3) : t - 1 ≠ x ^ 3 ∧ t + 1 ≠ x ^ 3 := by
  have hu : u ≠ 0 := by intro hz; simp [hz] at hcenter; omega
  have hxL (h : t - 1 = x ^ 3) : x ≠ 0 := by intro hz; simp [hz] at h; omega
  have hxR (h : t + 1 = x ^ 3) : x ≠ 0 := by intro hz; simp [hz] at h
  interval_cases j
  · norm_num at hcenter
    constructor
    · intro h
      exact cube_add_small_ne_cube (a := x) (b := u) (e := 1)
        (Nat.pos_of_ne_zero (hxL h)) (by decide) (by decide) (by omega)
    · intro h
      exact cube_add_small_ne_cube (a := u) (b := x) (e := 1)
        (Nat.pos_of_ne_zero hu) (by decide) (by decide) (by omega)
  · norm_num at hcenter
    constructor
    · intro h
      have hh := nat_cube_add_cube_eq_two_mul_cube (hxL h) (by decide : (1 : ℕ) ≠ 0) hu
        (show x ^ 3 + 1 ^ 3 = 2 * u ^ 3 by omega)
      have hu1 : u = 1 := hh.2.symm
      simp [hu1] at hcenter
      omega
    · intro h
      have hi : (x : ℤ) ^ 3 = 2 * (u : ℤ) ^ 3 + 1 := by
        exact_mod_cast (show x ^ 3 = 2 * u ^ 3 + 1 by omega)
      have hh := int_cube_add_cube_eq_two_mul_cube (Int.natCast_ne_zero.mpr (hxR h))
        (by decide : (-1 : ℤ) ≠ 0) (Int.natCast_ne_zero.mpr hu)
        (show (x : ℤ) ^ 3 + (-1) ^ 3 = 2 * (u : ℤ) ^ 3 by linear_combination hi)
      have hx0 : (0 : ℤ) ≤ x := Int.natCast_nonneg x
      omega
  · norm_num at hcenter
    constructor
    · intro h
      exact nat_cube_add_cube_ne_four_mul_cube (hxL h) (by decide : (1 : ℕ) ≠ 0) hu
        (show x ^ 3 + 1 ^ 3 = 4 * u ^ 3 by omega)
    · intro h
      have hi : (x : ℤ) ^ 3 = 4 * (u : ℤ) ^ 3 + 1 := by
        exact_mod_cast (show x ^ 3 = 4 * u ^ 3 + 1 by omega)
      exact int_cube_add_cube_ne_four_mul_cube (Int.natCast_ne_zero.mpr (hxR h))
        (by decide : (-1 : ℤ) ≠ 0) (Int.natCast_ne_zero.mpr hu)
        (show (x : ℤ) ^ 3 + (-1) ^ 3 = 4 * (u : ℤ) ^ 3 by linear_combination hi)

/-- If the sole possible odd residual prime avoids the center, the center is a cube
up to a power of two with exponent less than three. -/
theorem center_two_residual_normal_form {t D p α β : ℕ} (ht : 2 ≤ t) (he : Even t)
    (hp : Nat.Prime p) (hpt : ¬p ∣ t)
    (h : t ^ 3 - t = D ^ 3 * (2 ^ α * p ^ β) ^ 2) :
    ∃ j u : ℕ, j < 3 ∧ t = 2 ^ j * u ^ 3 := by
  obtain ⟨e, m, hm, htm⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : t ≠ 0)
  have hmt : m ∣ t := ⟨2 ^ e, by rw [htm]; ring⟩
  have hcop := centered_pairwise_coprime ht he
  have hmb : Nat.Coprime m ((t - 1) * (t + 1)) :=
    (hcop.1.symm.mul_right hcop.2.2).coprime_dvd_left hmt
  have hm2 : Nat.Coprime m 2 := Nat.coprime_two_right.mpr hm
  have hmp : Nat.Coprime m p :=
    (hp.coprime_iff_not_dvd.mpr hpt).symm.coprime_dvd_left hmt
  have hmcomp := (hm2.pow_right e).mul_right hmb
  have hmS := (hm2.pow_right α).mul_right (hmp.pow_right β)
  have hprod : m * (2 ^ e * ((t - 1) * (t + 1))) = D ^ 3 * (2 ^ α * p ^ β) ^ 2 := by
    calc
      _ = t * ((t - 1) * (t + 1)) := by rw [htm]; ring
      _ = t ^ 3 - t := by rw [cube_sub_self_eq_centered_product]; ring
      _ = _ := h
  obtain ⟨v, hv⟩ := cube_factor_of_cubic_product hmcomp hmS hprod
  have hpowers : (2 : ℕ) ^ e = 2 ^ (e % 3) * (2 ^ (e / 3)) ^ 3 := by
    calc
      (2 : ℕ) ^ e = 2 ^ (e % 3 + e / 3 * 3) := by rw [Nat.mod_add_div']
      _ = _ := by rw [pow_add, pow_mul]
  refine ⟨e % 3, 2 ^ (e / 3) * v, Nat.mod_lt _ (by decide), ?_⟩
  rw [htm, hv, hpowers, mul_pow]
  ring

private theorem prime_not_dvd_other_entry {p a b : ℕ} (hp : Nat.Prime p)
    (hab : Nat.Coprime a b) (hpa : p ∣ a) : ¬p ∣ b := by
  intro hpb
  apply hp.not_dvd_one
  have hh := Nat.dvd_gcd hpa hpb
  rwa [hab] at hh

/-- Uniform exclusion of residual support contained in `{2,p}`.  Neither `D` nor
`p` nor either exponent is bounded, and squarefreeness of `D` is unnecessary. -/
theorem even_cube_sub_self_ne_two_prime_support {t D p α β : ℕ}
    (ht : 2 ≤ t) (he : Even t) (hp : Nat.Prime p) :
    t ^ 3 - t ≠ D ^ 3 * (2 ^ α * p ^ β) ^ 2 := by
  intro h
  obtain ⟨_, _, hcop, h4, _, _, _⟩ := cubic_solution_structure ht he h
  have hcubes := centered_cubic_cube_factors ht he h
  have hLo : Odd (t - 1) := Nat.odd_iff.mpr (by have hh := Nat.even_iff.mp he; omega)
  have hRo : Odd (t + 1) := Nat.odd_iff.mpr (by have hh := Nat.even_iff.mp he; omega)
  have hLc (hnot : ¬p ∣ t - 1) : ∃ x : ℕ, t - 1 = x ^ 3 := by
    apply hcubes.1
    exact ((Nat.coprime_two_right.mpr hLo).pow_right α).mul_right
      ((hp.coprime_iff_not_dvd.mpr hnot).symm.pow_right β)
  have hRc (hnot : ¬p ∣ t + 1) : ∃ x : ℕ, t + 1 = x ^ 3 := by
    apply hcubes.2.2
    exact ((Nat.coprime_two_right.mpr hRo).pow_right α).mul_right
      ((hp.coprime_iff_not_dvd.mpr hnot).symm.pow_right β)
  by_cases hpL : p ∣ t - 1
  · have hpC := prime_not_dvd_other_entry hp hcop.1 hpL
    have hpR := prime_not_dvd_other_entry hp hcop.2.1 hpL
    obtain ⟨x, hx⟩ := hRc hpR
    obtain ⟨j, u, hj, hcenter⟩ := center_two_residual_normal_form ht he hp hpC h
    exact (two_residual_center_neighbors_not_cubes (x := x) ht h4 hj hcenter).2 hx
  · by_cases hpR : p ∣ t + 1
    · have hpC := prime_not_dvd_other_entry hp hcop.2.2.symm hpR
      obtain ⟨x, hx⟩ := hLc hpL
      obtain ⟨j, u, hj, hcenter⟩ := center_two_residual_normal_form ht he hp hpC h
      exact (two_residual_center_neighbors_not_cubes (x := x) ht h4 hj hcenter).1 hx
    · obtain ⟨x, hx⟩ := hLc hpL
      obtain ⟨y, hy⟩ := hRc hpR
      have hx0 : 0 < x := by
        apply Nat.pos_of_ne_zero
        intro hz
        simp [hz] at hx
        omega
      exact cube_add_small_ne_cube (a := x) (b := y) (e := 2) hx0 (by decide) (by decide) (by omega)

/-- Cube factors of `S` do not evade the uniform two-prime support obstruction. -/
theorem even_cube_sub_self_ne_two_prime_support_times_cube {t D H p α β : ℕ}
    (ht : 2 ≤ t) (he : Even t) (hp : Nat.Prime p) :
    t ^ 3 - t ≠ D ^ 3 * (H ^ 3 * 2 ^ α * p ^ β) ^ 2 := by
  intro h
  apply even_cube_sub_self_ne_two_prime_support (D := D * H ^ 2) (α := α) (β := β) ht he hp
  calc
    t ^ 3 - t = D ^ 3 * (H ^ 3 * 2 ^ α * p ^ β) ^ 2 := h
    _ = (D * H ^ 2) ^ 3 * (2 ^ α * p ^ β) ^ 2 := by ring

/-- The entire square-factor slice `S=2p` is excluded, uniformly in every prime `p`. -/
theorem not_exists_even_cubic_two_prime_square_factor (p : ℕ) (hp : Nat.Prime p) :
    ¬∃ t D : ℕ, Even t ∧ 2 ≤ t ∧ t ^ 3 - t = D ^ 3 * (2 * p) ^ 2 := by
  rintro ⟨t, D, he, ht, h⟩
  apply even_cube_sub_self_ne_two_prime_support (α := 1) (β := 1) ht he hp
  simpa using h

/-- Infinitely many composite positive squarefree square factors are excluded.
The witnesses are `2p` for arbitrarily large odd primes `p`. -/
theorem infinitely_many_excluded_composite_squarefree_square_factors :
    {S : ℕ | 1 < S ∧ Squarefree S ∧ ¬Nat.Prime S ∧
      ¬∃ t D : ℕ, Even t ∧ 2 ≤ t ∧ t ^ 3 - t = D ^ 3 * S ^ 2}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes (n + 3)
  have hp2 : p ≠ 2 := by omega
  have hcp : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm
  have hsf : Squarefree (2 * p) :=
    (Nat.squarefree_mul hcp).mpr ⟨Nat.prime_two.squarefree, hp.squarefree⟩
  refine ⟨2 * p, ⟨by omega, hsf, Nat.not_prime_mul (by decide : 2 ≠ 1) hp.ne_one,
    not_exists_even_cubic_two_prime_square_factor p hp⟩, by omega⟩

end Erdos364.CubicObstruction

#print axioms Erdos364.CubicObstruction.int_cube_add_cube_eq_two_mul_cube
#print axioms Erdos364.CubicObstruction.int_cube_add_cube_ne_four_mul_cube
#print axioms Erdos364.CubicObstruction.nat_cube_add_cube_eq_two_mul_cube
#print axioms Erdos364.CubicObstruction.nat_cube_add_cube_ne_four_mul_cube

#print axioms Erdos364.CubicObstruction.two_residual_center_neighbors_not_cubes
#print axioms Erdos364.CubicObstruction.center_two_residual_normal_form
#print axioms Erdos364.CubicObstruction.even_cube_sub_self_ne_two_prime_support
#print axioms Erdos364.CubicObstruction.even_cube_sub_self_ne_two_prime_support_times_cube
#print axioms Erdos364.CubicObstruction.not_exists_even_cubic_two_prime_square_factor
#print axioms Erdos364.CubicObstruction.infinitely_many_excluded_composite_squarefree_square_factors
