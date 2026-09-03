import Submission.DeletedBinaryProfileExplore
import Submission.ExponentialProfileParametersExplore

/-! An explicit nonempty regime for uniform codegree deletion. The codegree
threshold is the absolute constant 236, while the main scale grows cubically
in the logarithm of the coarse interval length. -/
namespace Erdos66TripleDeletionParameters
open Filter Erdos66ConstantProfile
open scoped Topology
set_option maxHeartbeats 2200000

noncomputable def shift (m : ℝ) : ℕ := ⌈Real.exp (4*m)⌉₊
noncomputable def length (m : ℝ) : ℕ := ⌊Real.exp (12*m)⌋₊
noncomputable def start (m ε : ℝ) : ℕ := ⌈64*(shift m : ℝ)^2/ε^2⌉₊

lemma shift_b_bound (m : ℝ) : b (shift m) ≤ Real.exp (-2*m) := by
  have hs : Real.exp (4*m) ≤ (shift m : ℝ)+1 := by
    have hh := Nat.le_ceil (Real.exp (4*m))
    dsimp [shift]
    linarith
  have hb := b_square_bound (shift m)
  have hm := (mul_le_mul_of_nonneg_right hs (sq_nonneg (b (shift m)))).trans hb
  have he : Real.exp (4*m)=Real.exp (2*m)^2 := by
    rw [←Real.exp_nat_mul]; congr 1; norm_num; ring
  rw [he] at hm
  have hh : b (shift m)*Real.exp (2*m) ≤ 1 := by
    nlinarith [mul_nonneg (b_pos (shift m)).le (Real.exp_pos (2*m)).le]
  have he' : Real.exp (-2*m)=1/Real.exp (2*m) := by
    rw [show -2*m=-(2*m) by ring,Real.exp_neg,one_div]
  rw [he']
  exact (le_div_iff₀ (Real.exp_pos _)).mpr hh

lemma cube_root_bound (m : ℝ) (hm : 1 ≤ m) : m^3*Real.sqrt (m^3) ≤ m^5 := by
  have h34 : m^3 ≤ m^4 := pow_le_pow_right₀ hm (by norm_num)
  have hroot : Real.sqrt (m^3) ≤ m^2 := (Real.sqrt_le_iff).mpr ⟨sq_nonneg m,by nlinarith only [h34]⟩
  have hh := mul_le_mul_of_nonneg_left hroot (show 0 ≤ m^3 by positivity)
  nlinarith only [hh]

lemma cutoff_prefactor (m : ℝ) (hm : 0 ≤ m) :
    2*(length m : ℝ)+1 ≤ 3*Real.exp (12*m) := by
  have hf := Nat.floor_le (Real.exp_pos (12*m)).le
  have he := Real.one_le_exp (show 0 ≤ 12*m by positivity)
  dsimp [length]
  linarith

lemma triple_exponent_le_one (m : ℝ) (hm : 1 ≤ m) (hpoly : m^5 ≤ Real.exp m) :
    (Real.exp (9*(m/9))-1)*(m^3*Real.sqrt (m^3)*b (shift m)) ≤ 1 := by
  have hn : 0 ≤ m^3*Real.sqrt (m^3)*b (shift m) :=
    mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (b_pos _).le
  have hw := mul_le_mul (cube_root_bound m hm) (shift_b_bound m) (b_pos _).le
    (show 0 ≤ m^5 by positivity)
  have he : Real.exp (9*(m/9))-1 ≤ Real.exp m := by ring_nf; linarith
  have hh := mul_le_mul he hw hn (Real.exp_pos _).le
  have hid : Real.exp m*(m^5*Real.exp (-2*m))=m^5*Real.exp (-m) := by
    rw [mul_left_comm,←Real.exp_add]
    congr 2
    ring
  rw [hid] at hh
  have hlast := mul_le_mul_of_nonneg_right hpoly (Real.exp_pos (-m)).le
  rw [←Real.exp_add,add_neg_cancel,Real.exp_zero] at hlast
  exact hh.trans hlast

lemma codegree_budget_le (m : ℝ) (hm : 1 ≤ m) (hpoly : m^5 ≤ Real.exp m) :
    (2*(length m : ℝ)+1)^2 * Real.exp ((2-(236 : ℝ))*(m/9)+
      (Real.exp (9*(m/9))-1)*(m^3*Real.sqrt (m^3)*b (shift m))) ≤
        9*Real.exp (1-2*m) := by
  have hp := cutoff_prefactor m (by linarith)
  have hp2 := (sq_le_sq₀ (show 0 ≤ 2*(length m : ℝ)+1 by positivity) (by positivity)).mpr hp
  have hexp : (3*Real.exp (12*m))^2=9*Real.exp (24*m) := by
    have he : Real.exp (12*m)^2=Real.exp (24*m) := by
      rw [←Real.exp_nat_mul]; congr 1; norm_num; ring
    rw [mul_pow,he]
    norm_num
  rw [hexp] at hp2
  have hterm := triple_exponent_le_one m hm hpoly
  have harg : (2-(236 : ℝ))*(m/9)+
      (Real.exp (9*(m/9))-1)*(m^3*Real.sqrt (m^3)*b (shift m)) ≤ -26*m+1 := by linarith
  have hh := mul_le_mul hp2 (Real.exp_le_exp.mpr harg) (Real.exp_pos _).le (by positivity)
  convert hh using 1
  rw [mul_assoc,←Real.exp_add]
  congr 2
  ring

lemma unsigned_budget_le (m ε : ℝ) (hm : 1 ≤ m) (hcoef : 6656 ≤ ε^2*m^2) :
    6*(2*(length m : ℝ)+1)*Real.exp (-ε^2*(m^3+1)/512) ≤ 18*Real.exp (-m) := by
  have hpre : 6*(2*(length m : ℝ)+1) ≤ 18*Real.exp (12*m) := by
    linarith [cutoff_prefactor m (by linarith)]
  have hmul := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ m by linarith)
  have harg : -ε^2*(m^3+1)/512 ≤ -13*m := by nlinarith [sq_nonneg ε]
  have hh := mul_le_mul hpre (Real.exp_le_exp.mpr harg) (Real.exp_pos _).le (by positivity)
  convert hh using 1
  rw [mul_assoc,←Real.exp_add]
  congr 2
  ring

lemma log_length_bound (m : ℝ) (hm : 0 ≤ m) :
    0 ≤ Real.log (((length m+1 : ℕ) : ℝ)) ∧ Real.log (((length m+1 : ℕ) : ℝ)) ≤ 12*m+1 := by
  constructor
  · apply Real.log_nonneg
    push_cast
    have hh := Nat.cast_nonneg (α := ℝ) (length m)
    linarith
  · apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have hh := cutoff_prefactor m hm
    have hf := Nat.floor_le (Real.exp_pos (12*m)).le
    have he := Real.one_le_exp (show 0 ≤ 12*m by positivity)
    have he1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    rw [Real.exp_add]
    push_cast
    have hprod := mul_le_mul_of_nonneg_left he1 (Real.exp_pos (12*m)).le
    dsimp [length] at *
    linarith

lemma collateral_bound (m ε : ℝ) (hm : 1 ≤ m) (hε : 0<ε)
    (hcoef : 11841536 ≤ ε^3*m) :
    2*(128*(1+Real.log (((length m+1 : ℕ) : ℝ)))^2/ε^2)*236 ≤ ε*m^3 := by
  have ⟨hlog0,hlog⟩ := log_length_bound m (by linarith)
  have hs : (1+Real.log (((length m+1 : ℕ) : ℝ)))^2 ≤ 196*m^2 := by
    have hbase : 1+Real.log (((length m+1 : ℕ) : ℝ)) ≤ 14*m := by linarith
    nlinarith
  have he : 0<ε^2 := sq_pos_of_pos hε
  apply (mul_le_mul_iff_right₀ he).mp
  have hid : ε^2*(2*(128*(1+Real.log (((length m+1 : ℕ) : ℝ)))^2/ε^2)*236)=
      60416*(1+Real.log (((length m+1 : ℕ) : ℝ)))^2 := by field_simp; ring
  rw [hid]
  have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg m)
  nlinarith

lemma start_condition (m ε : ℝ) (hε : 0<ε) :
    64*(shift m : ℝ)^2 ≤ ε^2*((start m ε : ℝ)+1) := by
  have hh := (div_le_iff₀ (sq_pos_of_pos hε)).mp (Nat.le_ceil (64*(shift m : ℝ)^2/ε^2))
  dsimp [start]
  nlinarith [sq_nonneg ε]

lemma start_upper (m ε : ℝ) (hm : 0 ≤ m) (hε : 0<ε) :
    (start m ε : ℝ)+3 ≤ (256/ε^2+4)*Real.exp (8*m) := by
  have hh := Erdos66ExponentialProfileParameters.start_upper (Real.exp (4*m)) ε
    (Real.one_le_exp (by positivity)) hε
  have he : Real.exp (4*m)^2=Real.exp (8*m) := by
    rw [←Real.exp_nat_mul]; congr 1; norm_num; ring
  rw [he] at hh
  exact hh

lemma length_lower (m : ℝ) (hm : 1 ≤ m) : Real.exp (11*m) ≤ (length m : ℝ) := by
  have hf := Nat.lt_floor_add_one (Real.exp (12*m))
  have he1 : 2 ≤ Real.exp m := by linarith [Real.add_one_le_exp m]
  have he2 : 1 ≤ Real.exp (11*m) := Real.one_le_exp (by linarith)
  have hprod := mul_le_mul_of_nonneg_left he1 (Real.exp_pos (11*m)).le
  have he : Real.exp (12*m)=Real.exp (11*m)*Real.exp m := by
    rw [←Real.exp_add]; congr 1; ring
  dsimp [length]
  rw [he] at hf ⊢
  linarith

/-- At these parameters the unsigned and codegree selection budgets are
jointly below one and the total deletion loss is at most ε times the main
scale. The initial cutoff is exponentially smaller than the final cutoff. -/
theorem eventually_parameters (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ m : ℝ in atTop,
      1 ≤ m ∧ 1 ≤ m^3 ∧ 8 ≤ ε*m^3 ∧
      m^3 ≤ (shift m : ℝ)+1 ∧
      64*(shift m : ℝ)^2 ≤ ε^2*((start m ε : ℝ)+1) ∧
      (start m ε : ℝ)+3 ≤ Real.exp (10*m) ∧
      Real.exp (11*m) ≤ (length m : ℝ) ∧
      6*(2*(length m : ℝ)+1)*Real.exp (-ε^2*(m^3+1)/512) +
        (2*(length m : ℝ)+1)^2*Real.exp ((2-(236 : ℝ))*(m/9)+
          (Real.exp (9*(m/9))-1)*(m^3*Real.sqrt (m^3)*b (shift m))) < 1 ∧
      2*(128*(1+Real.log (((length m+1 : ℕ) : ℝ)))^2/ε^2)*236 ≤ ε*m^3 := by
  have hp5 := (isLittleO_pow_exp_pos_mul_atTop 5 (by norm_num : (0 : ℝ)<1)).bound (by norm_num : (0 : ℝ)<1)
  have hp3 := (isLittleO_pow_exp_pos_mul_atTop 3 (by norm_num : (0 : ℝ)<4)).bound (by norm_num : (0 : ℝ)<1)
  have hcoef := (tendsto_id.const_mul_atTop (sq_pos_of_pos hε)).eventually_ge_atTop 6656
  have hcoll := (tendsto_id.const_mul_atTop (pow_pos hε 3)).eventually_ge_atTop 11841536
  have hlarge := (tendsto_id.const_mul_atTop hε).eventually_ge_atTop 8
  have hstart := (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ)<2))).eventually_ge_atTop
    (256/ε^2+4)
  have hd1 : Tendsto (fun m : ℝ ↦ Real.exp (-m)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have harg : Tendsto (fun m : ℝ ↦ 1-2*m) atTop atBot := by
    convert tendsto_atBot_add_const_left atTop 1
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ)<2))) using 1
  have hd2 : Tendsto (fun m : ℝ ↦ Real.exp (1-2*m)) atTop (𝓝 0) := Real.tendsto_exp_atBot.comp harg
  have hd : Tendsto (fun m : ℝ ↦ 18*Real.exp (-m)+9*Real.exp (1-2*m)) atTop (𝓝 0) := by
    convert (hd1.const_mul 18).add (hd2.const_mul 9) using 1 <;> norm_num
  filter_upwards [eventually_ge_atTop (1 : ℝ),hp5,hp3,hcoef,hcoll,hlarge,hstart,
    hd.eventually_lt_const (by norm_num : (0 : ℝ)<1)] with m hm hp5 hp3 hcoef hcoll hlarge hstart hd
  dsimp only [id,Function.comp_def] at hcoef hcoll hlarge hstart
  have hm0 : 0 ≤ m := by linarith
  have hm3 : 1 ≤ m^3 := one_le_pow₀ hm
  have hm13 : m ≤ m^3 := by simpa only [pow_one] using pow_le_pow_right₀ hm (by norm_num : (1 : ℕ) ≤ 3)
  have hp5' : m^5 ≤ Real.exp m := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ m^5 by positivity),
      abs_of_pos (Real.exp_pos _),one_mul] using hp5
  have hp3' : m^3 ≤ Real.exp (4*m) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ m^3 by positivity),
      abs_of_pos (Real.exp_pos _),one_mul] using hp3
  have hs : m^3 ≤ (shift m : ℝ)+1 := by
    have hh := Nat.le_ceil (Real.exp (4*m))
    dsimp [shift]
    linarith
  have hstart' : (start m ε : ℝ)+3 ≤ Real.exp (10*m) := by
    have hh := mul_le_mul_of_nonneg_right hstart (Real.exp_pos (8*m)).le
    have he : Real.exp (2*m)*Real.exp (8*m)=Real.exp (10*m) := by rw [←Real.exp_add]; congr 1; ring
    rw [he] at hh
    exact (start_upper m ε hm0 hε).trans hh
  have hcoef' : 6656 ≤ ε^2*m^2 := by
    have hpow : m ≤ m^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hpow (sq_nonneg ε)]
  have hb := unsigned_budget_le m ε hm hcoef'
  have hc := codegree_budget_le m hm hp5'
  refine ⟨hm,hm3,?_,hs,start_condition m ε hε,hstart',length_lower m hm,by linarith,
    collateral_bound m ε hm hε hcoll⟩
  nlinarith

/-- Actual profiles with no signed exceptions and a vanishing relative
collateral cost. This remains a finite theorem: T consists of unsigned holes. -/
theorem eventually_deleted_profiles (ε : ℝ) (hε : 0<ε) (hε1 : ε ≤ 1) :
    ∀ᶠ m : ℝ in atTop, ∀ (p : ℕ) [Fact p.Prime], p≠2 → 4*(length m+1)<p →
      ∃ (a : ZMod p) (T E : Finset ℕ), E ⊆ Finset.range (length m+1) ∧
        (∀ i<length m+1, a+(i : ZMod p) ≠ 0) ∧
        (∀ q<2*(length m+1), 2*a+(q : ZMod p) ≠ 0) ∧
        (T.card : ℝ) ≤ 128*(1+Real.log (((length m+1 : ℕ) : ℝ)))^2/ε^2 ∧
        (∀ q∈T, ε*((shift m : ℝ)+1)<4*((q : ℝ)+1)) ∧
        (∀ q∈T, AdditiveCombinatorics.sumRep (E : Set ℕ) q=0) ∧
        (∀ q, (AdditiveCombinatorics.sumRep (E : Set ℕ) q : ℝ) ≤ (1+ε)*m^3) ∧
        (∀ q, start m ε ≤ q → q ≤ length m → q∉T →
          |(AdditiveCombinatorics.sumRep (E : Set ℕ) q : ℝ)-m^3| < 2*ε*m^3) ∧
        (∀ q, q ≤ 2*length m →
          |Erdos66RealWeightedCharacterEnergy.signedFiber (length m+1)
            (Erdos66AffineRootAggregate.selectedWeight E) a q| < 2*ε*m^3) := by
  filter_upwards [eventually_parameters ε hε] with m hm
  obtain ⟨hm,hm3,hlarge,hs,hstart,_,_,hsmall,hcoll⟩ := hm
  intro p hp hp2 hpL
  obtain ⟨a,T,E,hE,ha,hop,hT,hloc,hzero,hu,hl,hsgn⟩ :=
    Erdos66DeletedBinaryProfile.exists_deleted_binary_profile p hp2 (shift m) (start m ε) (length m) 236
      hpL (m^3) ε (m/9) (by positivity) hm3 hε hε1 hlarge hs hstart hsmall
  have hc : 2*(T.card : ℝ)*236 ≤ ε*m^3 := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT (by norm_num : (0 : ℝ) ≤ 2))
      (by norm_num : (0 : ℝ) ≤ 236)
    exact hh.trans hcoll
  refine ⟨a,T,E,hE,ha,hop,hT,hloc,hzero,hu,?_,?_⟩
  · intro q hq₀ hq hqT
    have hh := hl q hq₀ hq hqT
    norm_num only [Nat.cast_ofNat] at hh
    nlinarith
  · intro q hq
    have hh := hsgn q hq
    norm_num only [Nat.cast_ofNat] at hh
    nlinarith

end Erdos66TripleDeletionParameters
