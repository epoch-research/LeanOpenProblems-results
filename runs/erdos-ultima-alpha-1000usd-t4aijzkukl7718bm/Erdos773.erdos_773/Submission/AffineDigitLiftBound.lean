import Submission.FloorParabolaLineBound
import Submission.ParabolaSquareLift

/-!
Height-sensitive bounds for affine high-digit parabola lifts. These apply
only to the explicitly specified digit condition, not to arbitrary Sidon
subsets of integer squares or arbitrary modular Sidon constructions.
-/
namespace Erdos773.AffineDigitLiftBound
open Finset FloorParabolaLineBound
set_option maxHeartbeats 2500000
noncomputable section

/-- The high base-p square digit is affine in the root residue. -/
def AffineDigits (p : ℕ) (a c : ZMod p) (A : Finset ℕ) : Prop :=
  ∀ n ∈ A, (digit p n : ZMod p)=a*n+c

lemma digit_decomposition {p : ℕ} (hp : 0<p) (b t : ℕ) :
    digit p (b+p*t)=digit p b+2*b*t+p*t^2 := by
  dsimp [digit]
  rw [show (b+p*t)^2=b^2+p*(2*b*t+p*t^2) by ring,Nat.add_mul_div_left _ _ hp]
  omega

def layer (A : Finset ℕ) (p t : ℕ) :=
  (A.filter (fun n => n/p=t)).image (fun n => n%p)

lemma layer_card (A : Finset ℕ) (p t : ℕ) :
    (layer A p t).card=(A.filter (fun n => n/p=t)).card := by
  apply card_image_of_injOn
  intro n hn m hm he
  have hn' := (mem_filter.mp hn).2
  have hm' := (mem_filter.mp hm).2
  have hd₁ := Nat.mod_add_div n p
  have hd₂ := Nat.mod_add_div m p
  change n%p=m%p at he
  rw [hn'] at hd₁
  rw [hm'] at hd₂
  omega

lemma layer_onLine {p : ℕ} (hp : 0<p) {a c : ZMod p} {A : Finset ℕ}
    (hA : AffineDigits p a c A) (t : ℕ) : OnLine p (a-2*t) c (layer A p t) := by
  intro b hb
  obtain ⟨n,hn,rfl⟩ := mem_image.mp hb
  obtain ⟨hn,ht⟩ := mem_filter.mp hn
  refine ⟨Nat.mod_lt _ hp,?_⟩
  have he : n=n%p+p*t := by rw [← ht]; exact (Nat.mod_add_div n p).symm
  have hh := hA n hn
  rw [he,digit_decomposition hp] at hh
  push_cast at hh
  simp only [ZMod.natCast_self,zero_mul,add_zero] at hh
  linear_combination hh

lemma layer_square_bound {p : ℕ} (hp : 0<p) {a c : ZMod p} {A : Finset ℕ}
    (hA : AffineDigits p a c A) (t : ℕ) :
    ((A.filter (fun n => n/p=t)).card : ℝ)^2 ≤ p*(5+2*Real.log p) := by
  rw [← layer_card]
  exact line_card_bound hp (layer_onLine hp hA t)

lemma card_partition {p N : ℕ} {A : Finset ℕ} (hN : ∀ n ∈ A, n≤N) :
    A.card=∑ t ∈ range (N/p+1), (A.filter (fun n => n/p=t)).card := by
  apply card_eq_sum_card_fiberwise
  intro n hn
  exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (hN n hn)))

/-- All quotient layers are accounted for, without assuming equidistribution. -/
theorem layered_square_bound {p N : ℕ} (hp : 0<p) {a c : ZMod p} {A : Finset ℕ}
    (hA : AffineDigits p a c A) (hN : ∀ n ∈ A, n≤N) :
    (A.card:ℝ)^2 ≤ ((N/p+1 : ℕ):ℝ)^2*p*(5+2*Real.log p) := by
  have hcard : (A.card:ℝ)=∑ t ∈ range (N/p+1), ((A.filter (fun n => n/p=t)).card:ℝ) := by
    exact_mod_cast card_partition hN
  have hsum : (∑ t ∈ range (N/p+1), ((A.filter (fun n => n/p=t)).card:ℝ)^2) ≤
      (N/p+1 : ℕ)*((p:ℝ)*(5+2*Real.log p)) := by
    calc
      _ ≤ ∑ _t ∈ range (N/p+1), (p:ℝ)*(5+2*Real.log p) :=
        sum_le_sum (fun t _ => layer_square_bound hp hA t)
      _ = _ := by simp
  calc
    (A.card:ℝ)^2 = (∑ t ∈ range (N/p+1), ((A.filter (fun n => n/p=t)).card:ℝ))^2 := by rw [hcard]
    _ ≤ (N/p+1 : ℕ)*(∑ t ∈ range (N/p+1), ((A.filter (fun n => n/p=t)).card:ℝ)^2) := by
      simpa using sq_sum_le_card_mul_sum_sq (s := range (N/p+1))
        (f := fun t => ((A.filter (fun n => n/p=t)).card:ℝ))
    _ ≤ (N/p+1 : ℕ)*((N/p+1 : ℕ)*((p:ℝ)*(5+2*Real.log p))) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = _ := by ring

lemma residue_card_bound {p : ℕ} (hp : 0<p) {A : Finset ℕ}
    (hinj : Set.InjOn (fun n => n%p) A) : A.card ≤ p := by
  have hs : A.image (fun n => n%p) ⊆ range p := by
    intro r hr
    obtain ⟨n,_,rfl⟩ := mem_image.mp hr
    exact mem_range.mpr (Nat.mod_lt _ hp)
  have hc := card_le_card hs
  rwa [card_image_of_injOn hinj,card_range] at hc

/-- A uniform 2/3-scale ceiling for residue-injective affine-digit lifts.
    The condition p<=N is explicit and essential to this conversion. -/
theorem cubic_bound {p N : ℕ} (hp : 0<p) (hpN : p≤N) {a c : ZMod p} {A : Finset ℕ}
    (hA : AffineDigits p a c A) (hN : ∀ n ∈ A, n≤N)
    (hinj : Set.InjOn (fun n => n%p) A) :
    (A.card:ℝ)^3 ≤ (N:ℝ)^2*(20+8*Real.log p) := by
  have hsq := layered_square_bound hp hA hN
  have hsize : (A.card:ℝ) ≤ p := by exact_mod_cast residue_card_bound hp hinj
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hL : 0 ≤ 5+2*Real.log (p:ℝ) := by
    have ht := Real.log_nonneg hp1
    linarith
  have hheight : p*(N/p+1) ≤ 2*N := by
    have hh := Nat.mul_div_le N p
    nlinarith
  have hhR : (p:ℝ)*(N/p+1 : ℕ) ≤ 2*N := by exact_mod_cast hheight
  have hheightSq := pow_le_pow_left₀ (show (0:ℝ) ≤ p*(N/p+1 : ℕ) by positivity) hhR 2
  calc
    (A.card:ℝ)^3 = (A.card:ℝ)^2*A.card := by ring
    _ ≤ (A.card:ℝ)^2*p := mul_le_mul_of_nonneg_left hsize (sq_nonneg _)
    _ ≤ (((N/p+1 : ℕ):ℝ)^2*p*(5+2*Real.log p))*p :=
      mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg _)
    _ = ((p:ℝ)*(N/p+1 : ℕ))^2*(5+2*Real.log p) := by ring
    _ ≤ ((2:ℝ)*N)^2*(5+2*Real.log p) := mul_le_mul_of_nonneg_right hheightSq hL
    _ = _ := by ring

/-- The affine digit condition determines the entire square residue modulo p²
    from the root residue modulo p. -/
lemma same_residue_square {p : ℕ} {a c : ZMod p} {A : Finset ℕ}
    (hA : AffineDigits p a c A) {n m : ℕ} (hn : n ∈ A) (hm : m ∈ A)
    (he : n%p=m%p) : n^2 ≡ m^2 [MOD p^2] := by
  have hnm : (n : ZMod p)=(m : ZMod p) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr he
  have hd : digit p n ≡ digit p m [MOD p] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [hA n hn,hA m hm,hnm]
  have hl : n^2%p=m^2%p := (show n ≡ m [MOD p] from he).pow 2
  have hh := (hd.mul_left' p).add_left (n^2%p)
  rw [hl] at hh
  have h₁ := Nat.mod_add_div (n^2) p
  have h₂ := Nat.mod_add_div (m^2) p
  dsimp [digit] at hh
  rw [← hl] at hh
  rw [h₁,hl,h₂] at hh
  simpa only [pow_two] using hh

lemma matching_residue_injective {p : ℕ} {a c : ZMod p} {A : Finset ℕ}
    (hA : AffineDigits p a c A) (hmatch : MatchedResidueLifting.PairMatching (p^2) A) :
    Set.InjOn (fun n => n%p) A := by
  intro n hn m hm he
  have hs := same_residue_square hA hn hm he
  rcases hmatch n hn n hn m hm m hm (hs.add hs) with h | h <;> exact h.1

/-- No unit or prime hypothesis is required for this modular-matching version. -/
theorem matching_cubic_bound {p N : ℕ} (hp : 0<p) (hpN : p≤N) {a c : ZMod p} {A : Finset ℕ}
    (hA : AffineDigits p a c A) (hN : ∀ n ∈ A, n≤N)
    (hmatch : MatchedResidueLifting.PairMatching (p^2) A) :
    (A.card:ℝ)^3 ≤ (N:ℝ)^2*(20+8*Real.log p) :=
  cubic_bound hp hpN hA hN (matching_residue_injective hA hmatch)

/-- Uniformly in the modulus and the affine parameters, this particular
    construction family has exponent at most two thirds. -/
theorem eventual_power_bound (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ p : ℕ, ∀ a c : ZMod p, ∀ A : Finset ℕ,
      0<p → p≤N → AffineDigits p a c A → (∀ n ∈ A, n≤N) →
      Set.InjOn (fun n => n%p) A → (A.card:ℝ) ≤ (N:ℝ)^(2/3+ε) := by
  have hlog := ((isLittleO_log_rpow_atTop (by linarith : 0<3*ε)).comp_tendsto
    tendsto_natCast_atTop_atTop).bound (by norm_num : (0:ℝ)<1/16)
  have hlarge : ∀ᶠ N : ℕ in Filter.atTop, (40:ℝ) ≤ (N:ℝ)^(3*ε) :=
    Filter.tendsto_atTop.mp
      ((tendsto_rpow_atTop (by linarith : 0<3*ε)).comp tendsto_natCast_atTop_atTop) 40
  filter_upwards [hlog,hlarge,Filter.eventually_ge_atTop 1] with N hlog hlarge hN
  intro p a c A hp hpN hA hheight hinj
  have hNR : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hlogN : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  simp only [Function.comp_def,Real.norm_eq_abs,abs_of_nonneg hlogN,
    abs_of_nonneg (Real.rpow_nonneg hNR.le _)] at hlog
  have hlogs : Real.log (p:ℝ) ≤ Real.log (N:ℝ) :=
    Real.log_le_log hpR (by exact_mod_cast hpN)
  have hc := cubic_bound hp hpN hA hheight hinj
  have hL : 20+8*Real.log (p:ℝ) ≤ (N:ℝ)^(3*ε) := by linarith
  apply le_of_pow_le_pow_left₀ (by decide : (3:ℕ)≠0) (by positivity)
  calc
    (A.card:ℝ)^3 ≤ (N:ℝ)^2*(20+8*Real.log p) := hc
    _ ≤ (N:ℝ)^2*(N:ℝ)^(3*ε) := mul_le_mul_of_nonneg_left hL (sq_nonneg _)
    _ = ((N:ℝ)^(2/3+ε))^3 := by
      rw [← Real.rpow_natCast (N:ℝ) 2,← Real.rpow_add hNR,
        ← Real.rpow_mul_natCast hNR.le]
      congr 1
      norm_num
      ring

/-- The previously constructed canonical parabola roots satisfy the
    affine high-digit condition, with slope one and intercept zero. -/
lemma parabola_affine_digits {p : ℕ} [Fact p.Prime] (h2 : (2:ZMod p)≠0)
    (B : Finset ℕ) (hB : ∀ b ∈ B, 0<b ∧ b<p) :
    AffineDigits p 1 0 (B.image (ParabolaSquareLift.root p)) := by
  intro n hn
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hn
  have hp := (Fact.out : p.Prime).pos
  have hh := (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    (ParabolaSquareLift.highDigit_congruence p b h2 (hB b hb).1 (hB b hb).2)
  change ((digit p b+2*b*ParabolaSquareLift.highDigit p b:ℕ):ZMod p)=b at hh
  rw [ParabolaSquareLift.root,digit_decomposition hp]
  push_cast at hh ⊢
  simp only [ZMod.natCast_self,zero_mul,add_zero,one_mul]
  exact hh

lemma parabola_residue_injective {p : ℕ} [Fact p.Prime]
    (B : Finset ℕ) (hB : ∀ b ∈ B, b<p) :
    Set.InjOn (fun n => n%p) (B.image (ParabolaSquareLift.root p)) := by
  intro n hn m hm he
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hn
  obtain ⟨d,hd,rfl⟩ := mem_image.mp hm
  change ParabolaSquareLift.root p b%p=ParabolaSquareLift.root p d%p at he
  rw [ParabolaSquareLift.root_mod p b (hB b hb),
    ParabolaSquareLift.root_mod p d (hB d hd)] at he
  exact congrArg (ParabolaSquareLift.root p) he

/-- Even arbitrary short-root truncations of this canonical lift obey the
    cubic ceiling. No half-band or pair-matching assumption is needed here. -/
theorem parabola_cubic_bound {p N : ℕ} [Fact p.Prime] (h2 : (2:ZMod p)≠0)
    (hpN : p≤N) (B : Finset ℕ) (hB : ∀ b ∈ B, 0<b ∧ b<p)
    (hheight : ∀ b ∈ B, ParabolaSquareLift.root p b≤N) :
    (B.card:ℝ)^3 ≤ (N:ℝ)^2*(20+8*Real.log p) := by
  have hh := cubic_bound (Fact.out : p.Prime).pos hpN
    (parabola_affine_digits h2 B hB)
    (show ∀ n ∈ B.image (ParabolaSquareLift.root p), n≤N from by
      intro n hn
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hn
      exact hheight b hb)
    (parabola_residue_injective B (fun b hb => (hB b hb).2))
  rwa [ParabolaSquareLift.lift_card p B (fun b hb => (hB b hb).2)] at hh

#print axioms digit_decomposition
#print axioms layer_onLine
#print axioms layered_square_bound
#print axioms cubic_bound
#print axioms same_residue_square
#print axioms matching_cubic_bound
#print axioms eventual_power_bound
#print axioms parabola_affine_digits
#print axioms parabola_cubic_bound
end
end Erdos773.AffineDigitLiftBound
