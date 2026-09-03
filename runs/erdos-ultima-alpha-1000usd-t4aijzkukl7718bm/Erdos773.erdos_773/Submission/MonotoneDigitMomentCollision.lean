import Submission.PrimeColorCollisions

/-!
Monotone digit vectors with a common digit sum and squared digit norm need
not have Sidon square values. This is an obstruction to a proposed sufficient
criterion, not a disproof of Erdős 773.
-/
namespace Erdos773.MonotoneDigitMomentCollision
open Finset Filter PrimeColorCollisions
noncomputable section
set_option maxHeartbeats 2000000

abbrev Word (d H : ℕ) := Fin d → Fin H

def digit {d H : ℕ} (w : Word d H) (i : Fin d) : ℕ :=
  (i.val+1)*H+(w i).val

def root {d H : ℕ} (B : ℕ) (w : Word d H) : ℕ :=
  Nat.ofDigits B (List.ofFn (digit w))

def roots (d H B : ℕ) : Finset ℕ := univ.image (root (d := d) (H := H) B)

lemma digit_bound {d H B : ℕ} (hB : (d+1)*H ≤ B) (w : Word d H) (i : Fin d) :
    digit w i < B := by
  have hw := (w i).isLt
  have hi := i.isLt
  have hm := Nat.mul_le_mul_right H (show i.val+1 ≤ d by omega)
  dsimp [digit]
  nlinarith

lemma digit_pos {d H : ℕ} (hH : 0 < H) (w : Word d H) (i : Fin d) :
    0 < digit w i := by
  dsimp [digit]
  have hh := Nat.mul_le_mul_right H (show 1 ≤ i.val+1 by omega)
  nlinarith

lemma digit_strictMono {d H : ℕ} (w : Word d H) : StrictMono (digit w) := by
  intro i j hij
  have hi := (w i).isLt
  have hm := Nat.mul_le_mul_right H (show i.val+2 ≤ j.val+1 by omega)
  dsimp [digit]
  nlinarith

lemma root_injective {d H B : ℕ} (hB1 : 1 < B) (hB : (d+1)*H ≤ B) :
    Function.Injective (root (d := d) (H := H) B) := by
  intro u v he
  have hh := Nat.ofDigits_inj_of_len_eq hB1 (by simp)
    (by simpa only [List.mem_ofFn] using fun a (ha : ∃ i, digit u i = a) =>
      ha.elim (fun i hi => hi ▸ digit_bound hB u i))
    (by simpa only [List.mem_ofFn] using fun a (ha : ∃ i, digit v i = a) =>
      ha.elim (fun i hi => hi ▸ digit_bound hB v i)) he
  have hf := List.ofFn_injective hh
  funext i
  apply Fin.ext
  have hi := congrFun hf i
  dsimp [digit] at hi
  omega

lemma root_bounds {d H B : ℕ} (hd : 0 < d) (hH : 0 < H)
    (hB1 : 1 < B) (hB : (d+1)*H ≤ B) (w : Word d H) :
    0 < root B w ∧ root B w < B^d := by
  constructor
  · have he : List.ofFn (digit w) = digit w ⟨0,hd⟩ ::
        List.ofFn (fun i : Fin (d-1) => digit w ⟨i.val+1, by have := i.isLt; omega⟩) := by
      cases d with
      | zero => omega
      | succ d => simp [List.ofFn_succ]; rfl
    rw [root,he,Nat.ofDigits_cons]
    have := digit_pos hH w ⟨0,hd⟩
    omega
  · have hh := Nat.ofDigits_lt_base_pow_length hB1
      (show ∀ a ∈ List.ofFn (digit w), a < B from by
        intro a ha
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
        exact digit_bound hB w i)
    simpa [root] using hh

lemma roots_card {d H B : ℕ} (hB1 : 1 < B) (hB : (d+1)*H ≤ B) :
    (roots d H B).card = H^d := by
  rw [roots,card_image_of_injective _ (root_injective hB1 hB)]
  simp

def moment {d H : ℕ} (w : Word d H) (k : ℕ) : ℕ := ∑ i, (digit w i)^k

lemma moment_bound {d H B : ℕ} (hB : (d+1)*H ≤ B) (w : Word d H) (k : ℕ) :
    moment w k ≤ d*B^k := by
  calc
    _ ≤ ∑ _i : Fin d, B^k :=
      sum_le_sum (fun i _ => Nat.pow_le_pow_left (digit_bound hB w i).le k)
    _ = _ := by simp

abbrev Color (d B : ℕ) := Fin (d*B+1) × Fin (d*B^2+1)

def wordColor {d H B : ℕ} (hB : (d+1)*H ≤ B) (w : Word d H) : Color d B :=
  (⟨moment w 1, Nat.lt_succ_of_le (by simpa using moment_bound hB w 1)⟩,
   ⟨moment w 2, Nat.lt_succ_of_le (moment_bound hB w 2)⟩)

lemma color_card_bound {d B : ℕ} (hd : 0 < d) (hB : 0 < B) :
    Fintype.card (Color d B) ≤ 4*d^2*B^3 := by
  simp only [Color,Fintype.card_prod,Fintype.card_fin]
  have h1 : 1 ≤ d*B := Nat.mul_pos hd hB
  have h2 : 1 ≤ d*B^2 := Nat.mul_pos hd (pow_pos hB _)
  have hh := Nat.mul_le_mul (show d*B+1 ≤ 2*(d*B) by omega)
    (show d*B^2+1 ≤ 2*(d*B^2) by omega)
  nlinarith only [hh]

/-- A finite counting criterion, with its strict numerical hypothesis explicit. -/
theorem collision_of_count {d H B : ℕ} (hd : 0 < d) (hH : 0 < H)
    (hB1 : 1 < B) (hB : (d+1)*H ≤ B)
    (hc : 16*(d : ℝ)^2*(B : ℝ)^3 *
      (maxSidonSubsetCard ((Icc 1 (B^d)).image (fun n : ℕ => n^2)) : ℝ) < (H : ℝ)^d) :
    ∃ a b c e : Word d H,
      a ≠ b ∧ a ≠ c ∧ a ≠ e ∧ b ≠ c ∧ b ≠ e ∧ c ≠ e ∧
      (root B a)^2+(root B b)^2=(root B c)^2+(root B e)^2 ∧
      (∀ k ∈ ({1,2} : Finset ℕ), moment a k = moment b k ∧
        moment a k = moment c k ∧ moment a k = moment e k) := by
  letI : NeZero H := ⟨hH.ne'⟩
  let f : ℕ → Color d B := fun n => wordColor hB (Function.invFun (root B) n)
  have hfr (w : Word d H) : f (root B w) = wordColor hB w := by
    dsimp [f]
    rw [Function.leftInverse_invFun (root_injective hB1 hB) w]
  have hA : roots d H B ⊆ Icc 1 (B^d) := by
    intro n hn
    obtain ⟨w,_,rfl⟩ := mem_image.mp hn
    have hb := root_bounds hd hH hB1 hB w
    exact mem_Icc.mpr ⟨hb.1,hb.2.le⟩
  have hcol : (Fintype.card (Color d B) : ℝ) ≤ 4*(d : ℝ)^2*(B : ℝ)^3 := by
    exact_mod_cast color_card_bound hd (by omega : 0 < B)
  have hcount : 4*(Fintype.card (Color d B) : ℝ)*
      (maxSidonSubsetCard ((Icc 1 (B^d)).image (fun n : ℕ => n^2)) : ℝ) <
        ((roots d H B).card : ℝ) := by
    rw [roots_card hB1 hB]
    push_cast
    have hh := mul_le_mul_of_nonneg_right hcol
      (show (0 : ℝ) ≤ maxSidonSubsetCard ((Icc 1 (B^d)).image (fun n : ℕ => n^2)) by positivity)
    nlinarith only [hh,hc]
  obtain ⟨a,ha,b,hb,c,hc,e,he,hab,hac,hae,hbc,hbe,hce,hs,habc,hacc,haec⟩ :=
    four_collision_of_card (roots d H B) (B^d) hA f hcount
  obtain ⟨a,_,rfl⟩ := mem_image.mp ha
  obtain ⟨b,_,rfl⟩ := mem_image.mp hb
  obtain ⟨c,_,rfl⟩ := mem_image.mp hc
  obtain ⟨e,_,rfl⟩ := mem_image.mp he
  refine ⟨a,b,c,e,fun h => hab (congrArg (root B) h),
    fun h => hac (congrArg (root B) h),fun h => hae (congrArg (root B) h),
    fun h => hbc (congrArg (root B) h),fun h => hbe (congrArg (root B) h),
    fun h => hce (congrArg (root B) h),hs,?_⟩
  rw [hfr a,hfr b] at habc
  rw [hfr a,hfr c] at hacc
  rw [hfr a,hfr e] at haec
  intro k hk
  simp only [mem_insert,mem_singleton] at hk
  rcases hk with rfl | rfl
  · exact ⟨congrArg (fun x : Color d B => x.1.val) habc,
      congrArg (fun x : Color d B => x.1.val) hacc,
      congrArg (fun x : Color d B => x.1.val) haec⟩
  · exact ⟨congrArg (fun x : Color d B => x.2.val) habc,
      congrArg (fun x : Color d B => x.2.val) hacc,
      congrArg (fun x : Color d B => x.2.val) haec⟩

/-- Explicit radices for the obstruction. The dimension grows with the radix. -/
def width (d : ℕ) : ℕ := 2^(d^2)
def radix (d : ℕ) : ℕ := (d+1)*width d

lemma width_pos (d : ℕ) : 0 < width d := by unfold width; positivity
lemma radix_pos (d : ℕ) : 0 < radix d := by
  have := width_pos d
  unfold radix
  positivity

private lemma logarithmic_estimates {d : ℕ} (hd : 100000000000000 ≤ d) :
    (d : ℝ)^2/2 ≤ Real.log (radix d : ℝ) ∧
    Real.log (radix d : ℝ) ≤ 2*(d : ℝ)^2 ∧
    Real.log (Real.log ((radix d : ℝ)^d)) ≤ (d : ℝ)/16384 := by
  have hdR : (100000000000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith only [hdR]
  have h2lo : (1/2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    linarith
  have h2hi : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hplus : Real.log ((d : ℝ)+1) ≤ d := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (d : ℝ)+1)
    linarith
  have hplus0 : 0 ≤ Real.log ((d : ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
  have hlogB : Real.log (radix d : ℝ) = Real.log ((d : ℝ)+1)+(d : ℝ)^2*Real.log 2 := by
    simp only [radix,width,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat]
    rw [Real.log_mul (by positivity) (by positivity),Real.log_pow]
    push_cast
    rfl
  have hlow : (d : ℝ)^2/2 ≤ Real.log (radix d : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left h2lo (sq_nonneg (d : ℝ))
    linarith only [hlogB,hh,hplus0]
  have hhigh : Real.log (radix d : ℝ) ≤ 2*(d : ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left h2hi (sq_nonneg (d : ℝ))
    nlinarith only [hlogB,hh,hplus,hdR]
  refine ⟨hlow,hhigh,?_⟩
  have hNlog : Real.log ((radix d : ℝ)^d) ≤ 2*(d : ℝ)^3 := by
    rw [Real.log_pow]
    have hh := mul_le_mul_of_nonneg_left hhigh hd0.le
    nlinarith only [hh]
  have hNpos : 0 < Real.log ((radix d : ℝ)^d) := by
    rw [Real.log_pow]
    exact mul_pos hd0 (lt_of_lt_of_le (by positivity) hlow)
  have hloglog := Real.log_le_log hNpos hNlog
  have he : Real.log (2*(d : ℝ)^3) = Real.log 2+3*Real.log (d : ℝ) := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hd0.ne'),Real.log_pow]
    norm_num
  rw [he] at hloglog
  have hroot : Real.sqrt (d : ℝ) ≤ (d : ℝ)/1000000 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    have hh := mul_nonneg (show (0 : ℝ) ≤ (d : ℝ)-1000000000000 by linarith only [hdR]) hd0.le
    nlinarith only [hh]
  have hlogroot := Real.log_le_rpow_div hd0.le (by norm_num : (0 : ℝ)<1/2)
  rw [← Real.sqrt_eq_rpow] at hlogroot
  linarith only [hloglog,h2hi,hlogroot,hroot,hdR]

/-- The strict counting inequality is genuinely supplied, using the proved
primorial upper bound rather than a numerical or solver certificate. -/
theorem count_gap {d : ℕ} (hd : 100000000000000 ≤ d) :
    16*(d : ℝ)^2*(radix d : ℝ)^3 *
      (maxSidonSubsetCard ((Icc 1 ((radix d)^d)).image (fun n : ℕ => n^2)) : ℝ) <
        (width d : ℝ)^d := by
  let B := radix d
  let H := width d
  let N := B^d
  have hdR : (100000000000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ)<d := by linarith only [hdR]
  have hB0 : (0 : ℝ)<B := by exact_mod_cast radix_pos d
  have hH0 : (0 : ℝ)<H := by exact_mod_cast width_pos d
  have hN0 : (0 : ℝ)<N := by
    dsimp only [N]
    exact_mod_cast pow_pos (radix_pos d) d
  have hB128 : 128 ≤ B := by
    have he : 7 ≤ d^2 := by nlinarith only [hd]
    have hh : 128 ≤ width d := by
      exact (by norm_num : 128 ≤ (2 : ℕ)^7).trans (Nat.pow_le_pow_right (by norm_num) he)
    have hm : width d ≤ (d+1)*width d := by
      have ht := Nat.mul_le_mul_right (width d) (show 1 ≤ d+1 by omega)
      simpa using ht
    exact hh.trans hm
  have hNbig : 128^128 ≤ N := by
    exact (Nat.pow_le_pow_left hB128 128).trans (Nat.pow_le_pow_right (by omega) (by omega : 128 ≤ d))
  have hup := square_sidon_primorial_upper N hNbig
  obtain ⟨hBloglo,hBloghi,hNloglog⟩ := logarithmic_estimates hd
  change (d : ℝ)^2/2 ≤ Real.log (B : ℝ) at hBloglo
  change Real.log (B : ℝ) ≤ 2*(d : ℝ)^2 at hBloghi
  have hNlog : Real.log (N : ℝ) = (d : ℝ)*Real.log (B : ℝ) := by
    simp [N,Real.log_pow]
  have hNl : (d : ℝ)^3/2 ≤ Real.log (N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hBloglo hd0.le
    nlinarith only [hh,hNlog]
  have hNl1 : 1 < Real.log (N : ℝ) := by
    have hm := mul_nonneg (show (0 : ℝ) ≤ (d : ℝ)-2 by linarith only [hdR]) (sq_nonneg (d : ℝ))
    nlinarith only [hNl,hm,hdR]
  have hloglog0 := Real.log_pos hNl1
  have hLL : Real.log (Real.log (N : ℝ)) ≤ (d : ℝ)/16384 := by
    simpa only [N,Nat.cast_pow] using hNloglog
  let L : ℝ := Real.log (N : ℝ)/(512*Real.log (Real.log (N : ℝ)))
  have hL : 16*(d : ℝ)^2 ≤ L := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<512*Real.log (Real.log (N : ℝ)))).mpr
    have hm := mul_le_mul_of_nonneg_left hLL (by positivity : (0 : ℝ) ≤ 8192*(d : ℝ)^2)
    nlinarith only [hm,hNl]
  have hlogH : Real.log (B : ℝ) = Real.log ((d : ℝ)+1)+Real.log (H : ℝ) := by
    change Real.log (radix d : ℝ) = _
    simp only [radix,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    exact Real.log_mul (by positivity) hH0.ne'
  have hplus : Real.log ((d : ℝ)+1) ≤ d := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ)<(d : ℝ)+1)
    linarith
  have hdlog : Real.log (d : ℝ) ≤ d := by
    have := Real.log_le_sub_one_of_pos hd0
    linarith
  have h32 : Real.log (32 : ℝ) ≤ 5 := by
    have hh : Real.log (32 : ℝ) = 5*Real.log 2 := by
      rw [show (32 : ℝ)=2^5 by norm_num,Real.log_pow]
      norm_num
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    linarith
  have hstrict : 32*(d : ℝ)^2*(B : ℝ)^3*(N : ℝ)*Real.exp (-L) < (H : ℝ)^d := by
    apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
    have he : Real.log (32*(d : ℝ)^2*(B : ℝ)^3*(N : ℝ)*Real.exp (-L)) =
        Real.log 32+2*Real.log (d : ℝ)+3*Real.log (B : ℝ)+Real.log (N : ℝ)-L := by
      rw [Real.log_mul (by positivity) (by positivity),Real.log_exp,
        Real.log_mul (by positivity) hN0.ne',Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_pow]
      norm_num
      ring
    rw [he,Real.log_pow,hNlog,hlogH]
    have hm := mul_le_mul_of_nonneg_left hplus hd0.le
    nlinarith only [h32,hdlog,hBloghi,hlogH,hL,hm,hdR]
  have hmul := mul_le_mul_of_nonneg_left hup
    (by positivity : (0 : ℝ) ≤ 16*(d : ℝ)^2*(B : ℝ)^3)
  change 16*(d : ℝ)^2*(B : ℝ)^3 *
    (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) : ℝ) < (H : ℝ)^d
  dsimp only [L] at hstrict
  rw [← neg_div] at hstrict
  nlinarith only [hmul,hstrict]

/-- Infinitely many dimensions and growing radices give actual collisions
inside strictly increasing digit vectors with both moments identical.
No conclusion about the maximum Sidon subset of all squares is negated. -/
theorem collision (d : ℕ) (hd : 100000000000000 ≤ d) :
    ∃ a b c e : Word d (width d),
      a ≠ b ∧ a ≠ c ∧ a ≠ e ∧ b ≠ c ∧ b ≠ e ∧ c ≠ e ∧
      (root (radix d) a)^2+(root (radix d) b)^2 =
        (root (radix d) c)^2+(root (radix d) e)^2 ∧
      (∀ k ∈ ({1,2} : Finset ℕ), moment a k = moment b k ∧
        moment a k = moment c k ∧ moment a k = moment e k) := by
  apply collision_of_count (by omega) (width_pos d) _ le_rfl (count_gap hd)
  have hh := width_pos d
  change 1 < (d+1)*width d
  nlinarith only [hh,hd]

#print axioms digit_strictMono
#print axioms collision_of_count
#print axioms count_gap
#print axioms collision

end
end Erdos773.MonotoneDigitMomentCollision
