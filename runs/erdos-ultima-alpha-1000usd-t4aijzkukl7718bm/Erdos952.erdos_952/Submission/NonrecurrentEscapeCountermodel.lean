import Submission.UniformSparseEscapeCountermodel
import Submission.WordUniqueBlocks

/-! A nonprime bounded-step path combining unique increment blocks, uniform
zero planar density, and uniform all-direction strip escape. These necessary
conditions, even together, do not settle the Gaussian moat conjecture. -/
namespace Erdos952Investigation
namespace NonrecurrentEscapeCountermodel
open UniformEscapeCountermodel (height sign sign_abs)
open UniformSparseEscapeCountermodel (UniformlySparse)
set_option maxHeartbeats 0

abbrev root (n : ℕ) : ℤ := Nat.sqrt n
abbrev rootStep (n : ℕ) : ℤ := root (n+1)-root n

lemma rootStep_bounds (n : ℕ) : 0 ≤ rootStep n ∧ rootStep n ≤ 1 := by
  have h1 : Nat.sqrt n ≤ Nat.sqrt (n+1) := Nat.sqrt_le_sqrt (Nat.le_succ n)
  have h2 : Nat.sqrt (n+1) ≤ Nat.sqrt n+1 := Nat.sqrt_succ_le_succ_sqrt n
  dsimp [rootStep,root]
  omega

lemma sqrt_add_sq_bound (n k : ℕ) : Nat.sqrt (n+k^2) ≤ Nat.sqrt n+k := by
  have hl := Nat.sqrt_le' (n+k^2)
  have hu := Nat.lt_succ_sqrt' n
  by_contra! hh
  have hs : (Nat.sqrt n+k+1)^2 ≤ (Nat.sqrt (n+k^2))^2 := by
    gcongr
    omega
  have hprod : 0 ≤ Nat.sqrt n*k := Nat.zero_le _
  nlinarith

lemma sqrt_far_interval (b L : ℕ) (hb : L^2 ≤ b) :
    Nat.sqrt (b+L) ≤ Nat.sqrt b+1 := by
  have hr : L ≤ Nat.sqrt b := Nat.le_sqrt'.mpr hb
  have hl := Nat.sqrt_le' (b+L)
  have hu := Nat.lt_succ_sqrt' b
  by_contra! hh
  have hs : (Nat.sqrt b+2)^2 ≤ (Nat.sqrt (b+L))^2 := by gcongr; omega
  nlinarith

/-- The square-root increments have no recurrent suffix: long enough fixed
prefixes contain at least two jumps, but sufficiently late windows of that
same length contain at most one. -/
lemma rootStep_no_recurrent_suffix : WordUniqueBlocks.NoRecurrentSuffix rootStep := by
  intro a
  let L := (a+2)^2
  refine ⟨L,L^2,?_⟩
  intro b hb
  by_contra! he
  have hsum (j : ℕ) (hj : j ≤ L) :
      root (b+j)-root b = root (a+j)-root a := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hjL : j < L := by omega
      have hh := he j hjL
      have hprev := ih (by omega)
      change root (b+j+1)-root (b+j) = root (a+j+1)-root (a+j) at hh
      change root (b+j+1)-root b = root (a+j+1)-root a
      omega
  have hlarge : a+2 ≤ Nat.sqrt (a+L) := Nat.le_sqrt'.mpr (by dsimp [L]; omega)
  have hasmall := Nat.sqrt_le_self a
  have hsmall := sqrt_far_interval b L hb
  have hs := hsum L le_rfl
  dsimp [root] at hs
  omega

def path (n : ℕ) : GaussianInt := ⟨n,10*height n+root n⟩

lemma path_injective : Function.Injective path := by
  intro i j hij
  exact Int.natCast_inj.mp (congrArg Zsqrtd.re hij)

lemma path_increment (n : ℕ) :
    path (n+1)-path n = (⟨1,10*sign n+rootStep n⟩ : GaussianInt) := by
  apply Zsqrtd.ext <;> simp [path,UniformEscapeCountermodel.height,rootStep] <;> ring

lemma path_step_bound (n : ℕ) : (path (n+1)-path n).norm < 123 := by
  have hr := rootStep_bounds n
  have hs := abs_le.mp (le_of_eq (sign_abs n))
  have hh : (10*sign n+rootStep n)^2 ≤ 121 := by nlinarith
  rw [path_increment,gaussian_norm_sq]
  dsimp
  omega

lemma rootStep_eq_of_increment_eq (a b : ℕ)
    (h : path (a+1)-path a = path (b+1)-path b) : rootStep a = rootStep b := by
  rw [path_increment,path_increment] at h
  have hh := congrArg Zsqrtd.im h
  change 10*sign a+rootStep a = 10*sign b+rootStep b at hh
  have ha := rootStep_bounds a
  have hb := rootStep_bounds b
  omega

lemma path_no_recurrent_suffix :
    WordUniqueBlocks.NoRecurrentSuffix (fun n => path (n+1)-path n) := by
  intro a
  obtain ⟨L,N,hN⟩ := rootStep_no_recurrent_suffix a
  refine ⟨L,N,?_⟩
  intro b hb
  obtain ⟨i,hi,hne⟩ := hN b hb
  exact ⟨i,hi,fun he => hne (rootStep_eq_of_increment_eq _ _ he)⟩

theorem path_unique_increment_blocks :
    ∀ a, ∃ L, 0 < L ∧ ∀ b,
      (∀ i < L, path (b+i+1)-path (b+i) = path (a+i+1)-path (a+i)) → b = a :=
  WordUniqueBlocks.unique_block path_no_recurrent_suffix

def projection (a b : ℝ) (n : ℕ) : ℝ :=
  a*(n : ℝ)+b*(10*(height n : ℝ)+(root n : ℝ))

lemma four_pow_eq_sq (k : ℕ) : 4^k = (2^k)^2 := by
  calc
    4^k = (2*2)^k := rfl
    _ = 2^k*2^k := mul_pow _ _ _
    _ = (2^k)^2 := by ring

lemma root_block_bounds (k n : ℕ) :
    0 ≤ (root (4^k*(n+1)) : ℝ)-(root (4^k*n) : ℝ) ∧
      (root (4^k*(n+1)) : ℝ)-(root (4^k*n) : ℝ) ≤ (2 : ℝ)^k := by
  have hl := Nat.sqrt_le_sqrt (Nat.mul_le_mul_left (4^k) (Nat.le_succ n))
  have hh : 4^k*(n+1) = 4^k*n+(2^k)^2 := by rw [← four_pow_eq_sq]; ring
  have hu : Nat.sqrt (4^k*(n+1)) ≤ Nat.sqrt (4^k*n)+2^k := by
    rw [hh]
    exact sqrt_add_sq_bound _ _
  dsimp [root]
  push_cast
  constructor
  · exact_mod_cast Nat.le_of_add_le_add_left (a := 0) (by simpa using hl)
  · have hu' : (Nat.sqrt (4^k*(n+1)) : ℝ) ≤ Nat.sqrt (4^k*n)+(2 : ℝ)^k := by
      exact_mod_cast hu
    linarith

lemma projection_block (k n : ℕ) (a b : ℝ) :
    projection a b (4^k*(n+1))-projection a b (4^k*n) =
      a*(4 : ℝ)^k+10*b*(2 : ℝ)^k*(sign n : ℝ)+
        b*((root (4^k*(n+1)) : ℝ)-(root (4^k*n) : ℝ)) := by
  have hh : (height (4^k*(n+1)) : ℝ)-(height (4^k*n) : ℝ) =
      (2 : ℝ)^k*(sign n : ℝ) := by
    exact_mod_cast UniformEscapeCountermodel.block_height_difference k n
  dsimp [projection]
  push_cast
  linear_combination 10*b*hh

/-- The square-root perturbation preserves uniform escape from every strip. -/
theorem uniform_projection_escape (B : ℝ) :
    ∃ K : ℕ, ∀ N : ℕ, ∀ a b : ℝ, max |a| |b| = 1 →
      ∃ i ≤ K, B < |projection a b (N+i)-projection a b N| := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (max (2*B+2) 2)
    (by norm_num : (1 : ℝ) < 2)
  have hkB : 2*B+2 < (2 : ℝ)^k := (le_max_left _ _).trans_lt hk
  have hk2 : 2 < (2 : ℝ)^k := (le_max_right _ _).trans_lt hk
  let Q : ℕ := 4^k
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨8*Q,?_⟩
  intro N a b hab
  by_contra! hbound
  have hbabs : |b| ≤ 1 := (le_max_right _ _).trans_eq hab
  let m := N/(4*Q)+1
  let j : ℕ → ℕ := fun t => Q*(4*m+t)
  have hindex (t : ℕ) (ht : t ≤ 4) : N ≤ j t ∧ j t ≤ N+8*Q := by
    have hdiv := Nat.mod_add_div N (4*Q)
    have hmod := Nat.mod_lt N (by omega : 0 < 4*Q)
    have hj : j t = (4*Q)*(N/(4*Q))+4*Q+Q*t := by dsimp [j,m]; ring
    have hmul := Nat.mul_le_mul_left Q ht
    rw [hj]
    constructor <;> omega
  have hwindow (t : ℕ) (ht : t ≤ 4) :
      |projection a b (j t)-projection a b N| ≤ B := by
    obtain ⟨hl,hu⟩ := hindex t ht
    have hh := hbound (j t-N) (by omega)
    simpa only [Nat.add_sub_of_le hl] using hh
  have hbetween (s t : ℕ) (hs : s ≤ 4) (ht : t ≤ 4) :
      |projection a b (j s)-projection a b (j t)| ≤ 2*B := by
    have he : projection a b (j s)-projection a b (j t) =
        (projection a b (j s)-projection a b N)+
          -(projection a b (j t)-projection a b N) := by ring
    rw [he]
    have hh := abs_add_le (projection a b (j s)-projection a b N)
      (-(projection a b (j t)-projection a b N))
    rw [abs_neg] at hh
    linarith [hwindow s hs,hwindow t ht]
  have herror (n : ℕ) :
      |b*((root (4^k*(n+1)) : ℝ)-(root (4^k*n) : ℝ))| ≤ (2 : ℝ)^k := by
    have hr := root_block_bounds k n
    rw [abs_mul,abs_of_nonneg hr.1]
    exact (mul_le_mul_of_nonneg_right hbabs hr.1).trans (by simpa using hr.2)
  have hbase (n : ℕ)
      (hn : |projection a b (4^k*(n+1))-projection a b (4^k*n)| ≤ 2*B) :
      |a*(4 : ℝ)^k+10*b*(2 : ℝ)^k*(sign n : ℝ)| ≤ 2*B+(2 : ℝ)^k := by
    calc
      _ = |(projection a b (4^k*(n+1))-projection a b (4^k*n))-
          b*((root (4^k*(n+1)) : ℝ)-(root (4^k*n) : ℝ))| := by
        rw [projection_block]; congr 1; ring
      _ ≤ |projection a b (4^k*(n+1))-projection a b (4^k*n)|+
          |b*((root (4^k*(n+1)) : ℝ)-(root (4^k*n) : ℝ))| := abs_sub _ _
      _ ≤ _ := add_le_add hn (herror n)
  have hs0 : sign (4*m) = sign m := by
    simpa using UniformEscapeCountermodel.sign_block m 0 (by decide)
  have hs3 : sign (4*m+3) = -sign m := by
    simpa using UniformEscapeCountermodel.sign_block m 3 (by decide)
  have hplus : |a*(4 : ℝ)^k+10*b*(2 : ℝ)^k*(sign m : ℝ)| ≤ 2*B+(2 : ℝ)^k := by
    simpa only [hs0] using hbase (4*m)
      (by simpa only [j,Q,Nat.add_zero] using hbetween 1 0 (by decide) (by decide))
  have hminus : |a*(4 : ℝ)^k-10*b*(2 : ℝ)^k*(sign m : ℝ)| ≤ 2*B+(2 : ℝ)^k := by
    simpa only [hs3,Int.cast_neg,mul_neg,sub_eq_add_neg] using hbase (4*m+3)
      (by simpa only [j,Q,show 4*m+3+1 = 4*m+4 by omega] using
        hbetween 4 3 (by decide) (by decide))
  have hp := abs_le.mp hplus
  have hm := abs_le.mp hminus
  have ha : |a*(4 : ℝ)^k| ≤ 2*B+(2 : ℝ)^k := abs_le.mpr ⟨by linarith,by linarith⟩
  have hb : |10*b*(2 : ℝ)^k*(sign m : ℝ)| ≤ 2*B+(2 : ℝ)^k :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  have hsign : |(sign m : ℝ)| = 1 := by exact_mod_cast sign_abs m
  rw [abs_mul,abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 4) k)] at ha
  simp only [abs_mul,hsign,mul_one,abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) k),
    abs_of_pos (by norm_num : (0 : ℝ) < 10)] at hb
  have hpow : (4 : ℝ)^k = ((2 : ℝ)^k)^2 := by exact_mod_cast four_pow_eq_sq k
  rcases le_total |a| |b| with hle | hle
  · rw [max_eq_right hle] at hab
    rw [hab] at hb
    nlinarith
  · rw [max_eq_left hle] at hab
    rw [hab,one_mul,hpow] at ha
    nlinarith

theorem path_uniform_escape (B : ℝ) :
    ∃ K : ℕ, ∀ N : ℕ, ∀ a b : ℝ, max |a| |b| = 1 →
      ∃ i ≤ K, B < |a*((path (N+i)-path N).re : ℝ)+b*((path (N+i)-path N).im : ℝ)| := by
  obtain ⟨K,hK⟩ := uniform_projection_escape B
  refine ⟨K,?_⟩
  intro N a b hab
  obtain ⟨i,hi,hh⟩ := hK N a b hab
  refine ⟨i,hi,?_⟩
  convert hh using 1
  congr 1
  simp only [path,Zsqrtd.re_sub,Zsqrtd.im_sub,Int.cast_sub,Int.cast_natCast,projection,
    Int.cast_add,Int.cast_mul,Int.cast_ofNat]
  ring

lemma path_square_card_le (z : GaussianInt) (R : ℕ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, |(path n).re-z.re| ≤ (R : ℤ) ∧
      |(path n).im-z.im| ≤ (R : ℤ)) : S.card ≤ 2*R+1 := by
  have hsub : S.image (fun n : ℕ => (n : ℤ)) ⊆
      Finset.Icc (z.re-(R : ℤ)) (z.re+(R : ℤ)) := by
    intro t ht
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ht
    have hh := (abs_le.mp (hS n hn).1)
    change -(R : ℤ) ≤ (n : ℤ)-z.re ∧ (n : ℤ)-z.re ≤ R at hh
    simp only [Finset.mem_Icc]
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective S (by intro i j h; exact Int.natCast_inj.mp h)] at hcard
  have hIcc : (Finset.Icc (z.re-(R : ℤ)) (z.re+(R : ℤ))).card = 2*R+1 := by
    rw [Int.card_Icc]
    omega
  rwa [hIcc] at hcard

theorem path_uniformly_sparse : UniformlySparse path := by
  intro ε hε
  obtain ⟨R₀,hR₀⟩ := exists_nat_gt (1/ε)
  have hmul : 1 < (R₀ : ℝ)*ε := (div_lt_iff₀ hε).mp hR₀
  refine ⟨R₀,?_⟩
  intro R hR z S hS
  have hcard : (S.card : ℝ) ≤ 2*(R : ℝ)+1 := by
    exact_mod_cast path_square_card_le z R S hS
  have hR' : (R₀ : ℝ) ≤ R := by exact_mod_cast hR
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hlarge : 1 ≤ ε*(2*(R : ℝ)+1) := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hlarge (by positivity : (0 : ℝ) ≤ 2*(R : ℝ)+1)
  nlinarith

/-- Every tail hits every residue modulo 5. Thus these geometric and word
properties do not provide even the basic arithmetic admissibility condition. -/
lemma path_hits_every_residue_mod_five (N : ℕ) (a b : ZMod 5) :
    ∃ n ≥ N, ((path n).re : ZMod 5) = a ∧ ((path n).im : ZMod 5) = b := by
  let k : ℕ := 5*(N+1)+b.val
  let t : ℕ := (a-b^2).val
  let n : ℕ := k^2+t
  have hk5 : 5 ≤ k := by dsimp [k]; omega
  have hkN : N ≤ k := by dsimp [k]; omega
  have ht5 : t < 5 := (a-b^2).val_lt
  have ht : t ≤ k+k := by omega
  have hsqrt : Nat.sqrt n = k := Nat.sqrt_add_eq' k ht
  have h5 : (5 : ZMod 5) = 0 := by decide
  have h10 : (10 : ZMod 5) = 0 := by decide
  have hkcast : (k : ZMod 5) = b := by simp [k,h5]
  have htcast : (t : ZMod 5) = a-b^2 := by simp [t]
  refine ⟨n,?_,?_,?_⟩
  · dsimp [n]
    nlinarith
  · change ((n : ℕ) : ZMod 5) = a
    dsimp [n]
    push_cast
    rw [hkcast,htcast]
    ring
  · change ((10*height n+root n : ℤ) : ZMod 5) = b
    calc
      _ = ((Nat.sqrt n : ℕ) : ZMod 5) := by push_cast; rw [h10]; simp
      _ = (k : ZMod 5) := by rw [hsqrt]
      _ = b := hkcast

theorem no_tail_admissible_mod_five (N : ℕ) :
    ¬ ∃ a b : ZMod 5, ∀ n ≥ N,
      (a+((path n).re : ZMod 5))^2+(b+((path n).im : ZMod 5))^2 ≠ 0 := by
  rintro ⟨a,b,hab⟩
  obtain ⟨n,hn,hr,hi⟩ := path_hits_every_residue_mod_five N (-a) (-b)
  exact hab n hn (by simp [hr,hi])

/-- All the listed non-arithmetic necessary conditions hold simultaneously.
This path is not admissible, and is not a disproof of the prime conjecture. -/
theorem combined_shortcut_counterexample :
    ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      (∀ n, (x (n+1)-x n).norm < 123) ∧ UniformlySparse x ∧
      (∀ a, ∃ L, 0 < L ∧ ∀ b,
        (∀ i < L, x (b+i+1)-x (b+i) = x (a+i+1)-x (a+i)) → b = a) ∧
      ∀ B : ℝ, ∃ K : ℕ, ∀ N : ℕ, ∀ a b : ℝ, max |a| |b| = 1 →
        ∃ i ≤ K, B < |a*((x (N+i)-x N).re : ℝ)+b*((x (N+i)-x N).im : ℝ)| :=
  ⟨path,path_injective,path_step_bound,path_uniformly_sparse,
    path_unique_increment_blocks,path_uniform_escape⟩

#print axioms no_tail_admissible_mod_five
#print axioms combined_shortcut_counterexample

#print axioms path_uniform_escape

#print axioms path_step_bound
#print axioms path_unique_increment_blocks

end NonrecurrentEscapeCountermodel
end Erdos952Investigation
