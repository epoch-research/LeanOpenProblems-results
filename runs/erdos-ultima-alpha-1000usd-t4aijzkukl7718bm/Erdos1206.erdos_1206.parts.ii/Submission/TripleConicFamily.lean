import Submission.PrimitiveCollisionMass

/-! A quadratic family of three equal positive cube differences.
This is an auxiliary counting family, not a settlement of Erdős 1206. -/

namespace Erdos1206.TripleConicFamily
open Finset
open scoped Classical
set_option maxHeartbeats 1000000

-- The coordinates are in strictly increasing order when u is positive.
def A (u v : ℕ) := 242004*u^2 + 24480*u*v + 612*v^2
def B (u v : ℕ) := 1839215*u^2 + 184200*u*v + 4605*v^2
def C (u v : ℕ) := 1915945*u^2 + 198120*u*v + 5115*v^2
def D (u v : ℕ) := 2175145*u^2 + 211080*u*v + 5115*v^2
def E (u v : ℕ) := 2365746*u^2 + 241020*u*v + 6138*v^2
def F (u v : ℕ) := 2545746*u^2 + 250020*u*v + 6138*v^2

def roots (u v : ℕ) : Fin 6 → ℕ :=
  ![A u v, B u v, C u v, D u v, E u v, F u v]

lemma identities (u v : ℕ) :
    A u v ^ 3 + E u v ^ 3 = B u v ^ 3 + C u v ^ 3 ∧
    A u v ^ 3 + F u v ^ 3 = B u v ^ 3 + D u v ^ 3 ∧
    C u v ^ 3 + F u v ^ 3 = D u v ^ 3 + E u v ^ 3 := by
  dsimp [A,B,C,D,E,F]
  constructor; ring
  constructor <;> ring

lemma ordered {u : ℕ} (hu : 0 < u) (v : ℕ) :
    0 < A u v ∧ A u v < B u v ∧ B u v < C u v ∧
      C u v < D u v ∧ D u v < E u v ∧ E u v < F u v := by
  have hsq : 0 < u^2 := pow_pos hu _
  dsimp [A,B,C,D,E,F]
  constructor; positivity
  constructor; nlinarith only [hsq]
  constructor; nlinarith only [hsq]
  constructor; nlinarith only [hsq]
  constructor <;> nlinarith only [hsq]

lemma roots_strictMono {u : ℕ} (hu : 0 < u) (v : ℕ) : StrictMono (roots u v) := by
  obtain ⟨ha,hab,hbc,hcd,hde,hef⟩ := ordered hu v
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [roots] <;> omega

lemma roots_pos {u : ℕ} (hu : 0 < u) (v : ℕ) (i : Fin 6) : 0 < roots u v i := by
  have ha := (ordered hu v).1
  have hm := (roots_strictMono hu v).monotone (show (0 : Fin 6) ≤ i from Fin.zero_le _)
  exact ha.trans_le hm

lemma roots_le_height {u : ℕ} (hu : 0 < u) (v : ℕ) (i : Fin 6) :
    roots u v i ≤ F u v := by
  exact (roots_strictMono hu v).monotone (show i ≤ (5 : Fin 6) by omega)

lemma height_bound {u v : ℕ} (h : u ≤ v) : F u v ≤ 2801904*v^2 := by
  have hu2 := Nat.pow_le_pow_left h 2
  have huv := Nat.mul_le_mul_right v h
  dsimp [F]
  nlinarith only [hu2,huv]

/-- This entire family is already met by the single divisor 5. -/
lemma five_dvd_B (u v : ℕ) : 5 ∣ B u v := by
  refine ⟨367843*u^2 + 36840*u*v + 921*v^2, ?_⟩
  dsimp [B]
  ring

/-- The first coordinate is an anisotropic quadratic form modulo 5. -/
lemma five_dvd_A_iff (u v : ℕ) : 5 ∣ A u v ↔ 5 ∣ u ∧ 5 ∣ v := by
  have hu : u%5 < 5 := Nat.mod_lt _ (by decide)
  have hv : v%5 < 5 := Nat.mod_lt _ (by decide)
  simp only [Nat.dvd_iff_mod_eq_zero]
  simp [A, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  interval_cases u%5 <;> interval_cases v%5 <;> norm_num

lemma five_not_dvd_A_of_coprime {u v : ℕ} (h : u.Coprime v) : ¬ 5 ∣ A u v := by
  intro ha
  obtain ⟨hu,hv⟩ := (five_dvd_A_iff u v).mp ha
  have hd := Nat.dvd_gcd hu hv
  rw [h.gcd_eq_one] at hd
  norm_num at hd

/-- With primitive parameters, dividing out any common integer factor of the
coordinates cannot remove the factor 5 from the second coordinate. -/
theorem five_survives_normalization {u v g a b : ℕ} (huv : u.Coprime v)
    (ha : A u v = g*a) (hb : B u v = g*b) : 5 ∣ b := by
  have hng : ¬ 5 ∣ g := by
    intro hg
    apply five_not_dvd_A_of_coprime huv
    rw [ha]
    exact dvd_mul_of_dvd_left hg a
  have hd := five_dvd_B u v
  rw [hb] at hd
  exact ((by decide : Nat.Prime 5).dvd_mul.mp hd).resolve_left hng

/-- Equality after possibly different positive dilations determines u/v. -/
lemma scaled_ratio {u v u' v' q r : ℕ} (hu : 0 < u) (hq : 0 < q)
    (ha : q*A u v = r*A u' v') (hb : q*B u v = r*B u' v')
    (hc : q*C u v = r*C u' v') (hd : q*D u v = r*D u' v') :
    u*v' = u'*v := by
  have hsq : q*u^2 = r*u'^2 := by
    dsimp [A,B] at ha hb
    nlinarith only [ha,hb]
  have hprod : q*u*v = r*u'*v' := by
    dsimp [C,D] at hc hd
    nlinarith only [hc,hd,hsq]
  have h₁ := congrArg (fun n : ℕ => n*v') hsq
  have h₂ := congrArg (fun n : ℕ => n*u') hprod
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hq hu)
  nlinarith only [h₁,h₂]

abbrev Index := (p : PrimitiveCollisionMass.LargePrime) × Fin (p.val-1)

def U (x : Index) := x.2.val+1
def V (x : Index) := x.1.val
def point (x : Index) : Fin 6 → ℕ := roots (U x) (V x)
def height (x : Index) := F (U x) (V x)

lemma u_pos (x : Index) : 0 < U x := by simp [U]
lemma u_lt_v (x : Index) : U x < V x := by
  have := x.2.isLt
  dsimp [U,V]
  omega
lemma height_pos (x : Index) : 0 < height x := by
  exact roots_pos (u_pos x) (V x) 5
lemma point_height_bound (x : Index) : height x ≤ 2801904*x.1.val^2 :=
  height_bound (u_lt_v x).le

lemma index_eq_of_ratio {x y : Index} (he : U x * V y = U y * V x) : x = y := by
  have hnot : ¬ V x ∣ U x := by
    intro hd
    have := Nat.le_of_dvd (u_pos x) hd
    have := u_lt_v x
    omega
  have hp : V x = V y := by
    have hd : V x ∣ U x * V y := by rw [he]; exact dvd_mul_left _ _
    have hd' := (x.1.property.1.dvd_mul.mp hd).resolve_left hnot
    exact (Nat.prime_dvd_prime_iff_eq x.1.property.1 y.1.property.1).mp hd'
  have hu : U x = U y := by
    rw [hp] at he
    exact Nat.eq_of_mul_eq_mul_right y.1.property.1.pos he
  cases x with | mk p j =>
    cases y with | mk p' j' =>
      have hpp : p = p' := Subtype.ext hp
      subst p'
      have hjj : j = j' := Fin.ext (by dsimp [U] at hu; omega)
      subst j'
      rfl

/-- No double-counting occurs between different family parameters or dilations.
The raw six-coordinate tuple need not be primitive. -/
lemma point_dilate_injective {x y : Index} {q r : ℕ} (hq : 0 < q)
    (he : (fun i => q*point x i) = (fun i => r*point y i)) : x = y ∧ q = r := by
  have ha := congrFun he 0
  have hb := congrFun he 1
  have hc := congrFun he 2
  have hd := congrFun he 3
  have hr := scaled_ratio (u_pos x) hq ha hb hc hd
  have hxy := index_eq_of_ratio hr
  subst y
  have hqr : q = r := Nat.eq_of_mul_eq_mul_right (roots_pos (u_pos x) (V x) 0) ha
  exact ⟨rfl,hqr⟩

lemma point_injective : Function.Injective point := by
  intro x y he
  exact (point_dilate_injective (q := 1) (r := 1) (by decide) (by simpa using he)).1

lemma reciprocal_heights_not_summable :
    ¬ Summable (fun x : Index => (1 : ℝ) / height x) := by
  let L : ℝ := 2801904
  have hL : 0 < L := by norm_num [L]
  have hblock (p : PrimitiveCollisionMass.LargePrime) :
      1/(2*L*(p.val : ℝ)) ≤ ∑ j : Fin (p.val-1), (1 : ℝ)/height ⟨p,j⟩ := by
    have hp : (0 : ℝ) < p.val := by exact_mod_cast p.property.1.pos
    have hpc : (p.val : ℝ) ≤ 2*(p.val-1 : ℕ) := by
      exact_mod_cast (show p.val ≤ 2*(p.val-1) by have := p.property.2; omega)
    calc
      _ ≤ ((p.val-1 : ℕ) : ℝ)/(L*(p.val : ℝ)^2) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        have hh := mul_le_mul_of_nonneg_right hpc (show 0 ≤ L*(p.val : ℝ) by positivity)
        nlinarith
      _ = ∑ _j : Fin (p.val-1), (1 : ℝ)/(L*(p.val : ℝ)^2) := by
        simp [div_eq_mul_inv]
      _ ≤ _ := by
        apply sum_le_sum
        intro j hj
        have hb : (height ⟨p,j⟩ : ℝ) ≤ L*(p.val : ℝ)^2 := by
          dsimp [L]
          exact_mod_cast point_height_bound ⟨p,j⟩
        have hd : (0 : ℝ) < height ⟨p,j⟩ := by exact_mod_cast height_pos ⟨p,j⟩
        exact one_div_le_one_div_of_le hd hb
  intro hs
  have hblocks := ((summable_sigma_of_nonneg
    (fun x : Index => (by positivity : (0 : ℝ) ≤ 1/height x))).mp hs).2
  have hsum : Summable (fun p : PrimitiveCollisionMass.LargePrime =>
      ∑ j : Fin (p.val-1), (1 : ℝ)/height ⟨p,j⟩) := by
    simpa only [tsum_fintype] using hblocks
  have hsmall : Summable (fun p : PrimitiveCollisionMass.LargePrime => 1/(2*L*(p.val : ℝ))) :=
    hsum.of_nonneg_of_le (fun _ => by positivity) hblock
  apply PrimitiveCollisionMass.large_prime_reciprocals_not_summable
  convert hsmall.mul_left (2*L) using 1
  funext p
  have hp : (p.val : ℝ) ≠ 0 := by exact_mod_cast p.property.1.ne_zero
  field_simp

#print axioms identities
#print axioms five_survives_normalization
#print axioms point_dilate_injective
#print axioms reciprocal_heights_not_summable
end Erdos1206.TripleConicFamily
