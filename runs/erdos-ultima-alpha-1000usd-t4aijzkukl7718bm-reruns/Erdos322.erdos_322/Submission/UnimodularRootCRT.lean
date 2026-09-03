import Submission.QuarticNonsingularDensity
import Submission.APReciprocalPrimes

/-! Primitive-at-the-modulus root sets, their exact CRT multiplicativity,
and unbounded normalized quartic density. -/
namespace Erdos322Research.UnimodularRootCRT
noncomputable section
open Finset QuarticNonsingularDensity
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

def Unimodular {k : ℕ} {R : Type*} [CommRing R] (x : Fin k → R) : Prop :=
  ∃ a : Fin k → R, ∑ i, a i*x i=1

abbrev URoots (k : ℕ) (R : Type*) [CommRing R] :=
  {x : Fin k → R // (∑ i, x i^k=0) ∧ Unimodular x}

def count (k q : ℕ) [NeZero q] : ℕ := Fintype.card (URoots k (ZMod q))

lemma unimodular_iff_ne_zero {k : ℕ} {R : Type*} [Field R] (x : Fin k → R) :
    Unimodular x ↔ x ≠ 0 := by
  constructor
  · rintro ⟨a,ha⟩ hx
    simp [hx] at ha
  · intro hx
    have hi : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    obtain ⟨i,hi⟩ := hi
    refine ⟨Pi.single i (x i)⁻¹,?_⟩
    simp [Pi.single_apply,hi]

lemma count_prime (k p : ℕ) [Fact p.Prime] :
    count k p=Fintype.card (NonzeroRoots k p) := by
  let e : URoots k (ZMod p) ≃ NonzeroRoots k p :=
    { toFun := fun x ↦ ⟨⟨x.val,x.property.1⟩,(unimodular_iff_ne_zero x.val).mp x.property.2⟩
      invFun := fun x ↦ ⟨x.val.val,x.val.property,(unimodular_iff_ne_zero x.val.val).mpr x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact Fintype.card_congr e

def rootsCongr (k : ℕ) {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : URoots k R ≃ URoots k S where
  toFun x := ⟨fun i ↦ e (x.val i),by
    constructor
    · simpa only [map_sum,map_pow,map_zero] using congrArg e x.property.1
    · obtain ⟨a,ha⟩ := x.property.2
      exact ⟨fun i ↦ e (a i),by simpa only [map_sum,map_mul,map_one] using congrArg e ha⟩⟩
  invFun x := ⟨fun i ↦ e.symm (x.val i),by
    constructor
    · simpa only [map_sum,map_pow,map_zero] using congrArg e.symm x.property.1
    · obtain ⟨a,ha⟩ := x.property.2
      exact ⟨fun i ↦ e.symm (a i),by simpa only [map_sum,map_mul,map_one] using congrArg e.symm ha⟩⟩
  left_inv x := by apply Subtype.ext; funext i; exact e.symm_apply_apply _
  right_inv x := by apply Subtype.ext; funext i; exact e.apply_symm_apply _

def rootsProd (k : ℕ) {R S : Type*} [CommRing R] [CommRing S] :
    URoots k (R × S) ≃ URoots k R × URoots k S where
  toFun x := (⟨fun i ↦ (x.val i).1,by
    constructor
    · simpa only [Prod.fst_sum,Prod.pow_fst,Prod.fst_zero] using congrArg Prod.fst x.property.1
    · obtain ⟨a,ha⟩ := x.property.2
      exact ⟨fun i ↦ (a i).1,by simpa only [Prod.fst_sum,Prod.fst_mul,Prod.fst_one] using congrArg Prod.fst ha⟩⟩,
    ⟨fun i ↦ (x.val i).2,by
    constructor
    · simpa only [Prod.snd_sum,Prod.pow_snd,Prod.snd_zero] using congrArg Prod.snd x.property.1
    · obtain ⟨a,ha⟩ := x.property.2
      exact ⟨fun i ↦ (a i).2,by simpa only [Prod.snd_sum,Prod.snd_mul,Prod.snd_one] using congrArg Prod.snd ha⟩⟩)
  invFun x := ⟨fun i ↦ (x.1.val i,x.2.val i),by
    constructor
    · apply Prod.ext
      · simpa only [Prod.fst_sum,Prod.pow_fst,Prod.fst_zero] using x.1.property.1
      · simpa only [Prod.snd_sum,Prod.pow_snd,Prod.snd_zero] using x.2.property.1
    · obtain ⟨a,ha⟩ := x.1.property.2
      obtain ⟨b,hb⟩ := x.2.property.2
      refine ⟨fun i ↦ (a i,b i),?_⟩
      apply Prod.ext
      · simpa only [Prod.fst_sum,Prod.fst_mul,Prod.fst_one] using ha
      · simpa only [Prod.snd_sum,Prod.snd_mul,Prod.snd_one] using hb⟩
  left_inv x := by apply Subtype.ext; funext i; rfl
  right_inv x := rfl

/-- CRT multiplicativity preserves primitivity at every prime of the modulus. -/
theorem count_mul (k m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) :
    count k (m*n)=count k m*count k n := by
  exact (Fintype.card_congr ((rootsCongr k (ZMod.chineseRemainder h)).trans (rootsProd k))).trans
    (Fintype.card_prod _ _)

lemma count_one (k : ℕ) : count k 1=1 := by
  have he : ∀ x : Fin k → ZMod 1, (∑ i, x i^k=0) ∧ Unimodular x := by
    intro x
    exact ⟨Subsingleton.elim _ _,0,Subsingleton.elim _ _⟩
  simp [count,URoots,he]

lemma sum_le_prod_one_add {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) : 1+∑ i ∈ S, f i ≤ ∏ i ∈ S, (1+f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha,Finset.prod_insert ha]
    have hfa := hf a (mem_insert_self a S)
    have hfS : ∀ i ∈ S, 0 ≤ f i := fun i hi ↦ hf i (mem_insert_of_mem hi)
    have hs := Finset.sum_nonneg hfS
    have hm := mul_le_mul_of_nonneg_left (ih hfS) (by linarith : 0≤1+f a)
    nlinarith

lemma exists_prime_product_gt {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) (C : ℝ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ (p : ZMod q)=a) ∧
      C < ∏ p ∈ S, (1+(1 : ℝ)/p) := by
  let f : ℕ → ℝ := fun n ↦ if n.Prime ∧ (n : ZMod q)=a then 1/n else 0
  have hns : ¬ Summable f := APReciprocalPrimes.not_summable_prime_reciprocals a ha
  have hf (n : ℕ) : 0 ≤ f n := by dsimp only [f]; split_ifs <;> positivity
  have hex : ∃ T : Finset ℕ, C < ∑ p ∈ T, f p := by
    by_contra hn
    push_neg at hn
    exact hns (summable_of_sum_le hf hn)
  obtain ⟨T,hT⟩ := hex
  let S : Finset ℕ := T.filter (fun n : ℕ ↦ n.Prime ∧ (n : ZMod q)=a)
  refine ⟨S,fun p hp ↦ (mem_filter.mp hp).2,?_⟩
  have hsum : ∑ p ∈ T, f p=∑ p ∈ S, (1 : ℝ)/p := by
    simp only [S,Finset.sum_filter,f]
  rw [hsum] at hT
  have h := sum_le_prod_one_add S (fun p : ℕ ↦ (1 : ℝ)/p) (fun _ _ ↦ by positivity)
  linarith

lemma prime_one_mod_eight (p : ℕ) (hp : p.Prime) (hc : (p : ZMod 8)=1) :
    8 ∣ p-1 ∧ 10 ≤ p := by
  have hm : p ≡ 1 [MOD 8] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hc
  have hp2 := hp.two_le
  have hd : 8 ∣ p-1 := Nat.modEq_zero_iff_dvd.mp (by
    simpa using Nat.ModEq.sub_right (by omega : 1≤p) (by omega : 1≤1) hm)
  refine ⟨hd,?_⟩
  by_contra hn
  have he : p=9 := by
    have hmod := hm
    change p%8=1%8 at hmod
    omega
  subst p
  norm_num at hp

lemma product_density (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ (p : ZMod 8)=1) :
    ∃ hq : NeZero (∏ p ∈ S, p),
      ((∏ p ∈ S, p : ℕ) : ℝ)^3*(∏ p ∈ S, (1+(1 : ℝ)/p)) ≤
        @count 4 (∏ p ∈ S, p) hq := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨⟨by simp⟩,?_⟩
    simp [count_one]
  | @insert p S hp ih =>
    have hpr := (hS p (mem_insert_self p S)).1
    letI : Fact p.Prime := ⟨hpr⟩
    have hS' : ∀ r ∈ S, r.Prime ∧ (r : ZMod 8)=1 := fun r hr ↦ hS r (mem_insert_of_mem hr)
    obtain ⟨hq,hqbound⟩ := ih hS'
    letI := hq
    have hcop : p.Coprime (∏ r ∈ S, r) := by
      apply Nat.Coprime.prod_right
      intro r hr
      exact (hpr.coprime_iff_not_dvd).mpr (by
        intro hd
        have he := (Nat.prime_dvd_prime_iff_eq hpr (hS' r hr).1).mp hd
        exact hp (he ▸ hr))
    have hd := prime_one_mod_eight p hpr (hS p (mem_insert_self p S)).2
    have hg := quartic_nonsingular_gain p hd.1 hd.2
    have hg' : (p : ℝ)^3*(1+(1 : ℝ)/p) ≤ count 4 p := by
      rw [count_prime]
      apply le_trans ?_ hg
      gcongr
      norm_num
    refine ⟨⟨by rw [Finset.prod_insert hp]; exact mul_ne_zero hpr.ne_zero hq.out⟩,?_⟩
    simp only [Finset.prod_insert hp,Nat.cast_mul,mul_pow,count_mul 4 p _ hcop]
    have hm := mul_le_mul hg' hqbound (by positivity) (by positivity)
    convert hm using 1
    ring

/-- The normalized count of roots primitive at the modulus is unbounded. -/
theorem unbounded_quartic_density (C : ℝ) :
    ∃ q : ℕ, ∃ hq : NeZero q, (q : ℝ)^3*C < @count 4 q hq := by
  obtain ⟨S,hS,hprod⟩ := exists_prime_product_gt (1 : ZMod 8) isUnit_one C
  obtain ⟨hq,hden⟩ := product_density S hS
  refine ⟨∏ p ∈ S, p,hq,?_⟩
  have hpos : (0 : ℝ)<((∏ p ∈ S, p : ℕ) : ℝ)^3 := by
    have hp : 0 < (∏ p ∈ S, p : ℕ) := Nat.pos_of_ne_zero hq.out
    positivity
  exact (mul_lt_mul_of_pos_left hprod hpos).trans_le hden

end
end Erdos322Research.UnimodularRootCRT
