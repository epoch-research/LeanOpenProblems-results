import FormalConjecturesUtil

/-! The exact full allowed-digit permutation carrier. Its size and height are
proved here. Integer square-Sidonness is NOT proved and is retained as an
explicit hypothesis in the transfer theorem. -/
namespace Erdos773.AllowedAlphabetCandidate
open Finset Filter
noncomputable section
set_option maxHeartbeats 2000000

/-- The allowed lower digits are 6,12,...,6(h+1), all below this radix. -/
def base (h : ℕ) : ℕ := 6*h+7

def word (h : ℕ) (σ : Equiv.Perm (Fin h)) : List ℕ :=
  6 :: (List.ofFn (fun i : Fin h => 6*((σ i).val+2)) ++ [1])

def root (h : ℕ) (σ : Equiv.Perm (Fin h)) : ℕ := Nat.ofDigits (base h) (word h σ)

def height (h : ℕ) : ℕ := (base h)^(h+2)

def roots (h : ℕ) : Finset ℕ := univ.image (root h)

def squares (h : ℕ) : Finset ℕ := (roots h).image (fun n => n^2)

lemma base_gt_one (h : ℕ) : 1 < base h := by unfold base; omega

lemma word_length (h : ℕ) (σ : Equiv.Perm (Fin h)) : (word h σ).length = h+2 := by
  simp [word]

lemma canonical_digits (h : ℕ) (σ : Equiv.Perm (Fin h)) :
    ∀ d ∈ word h σ, d < base h := by
  intro d hd
  simp only [word, List.mem_cons, List.mem_append, List.mem_ofFn, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | ⟨i,rfl⟩ | rfl
  · unfold base; omega
  · have hi := (σ i).isLt
    unfold base
    omega
  · exact base_gt_one h

lemma root_pos (h : ℕ) (σ : Equiv.Perm (Fin h)) : 0 < root h σ := by
  simp only [root, word, Nat.ofDigits_cons]
  omega

lemma root_lt_height (h : ℕ) (σ : Equiv.Perm (Fin h)) : root h σ < height h := by
  have hh := Nat.ofDigits_lt_base_pow_length (base_gt_one h) (canonical_digits h σ)
  simpa only [word_length, root, height] using hh

lemma root_injective (h : ℕ) : Function.Injective (root h) := by
  intro σ τ he
  have hw := Nat.ofDigits_inj_of_len_eq (base_gt_one h)
    (by rw [word_length,word_length]) (canonical_digits h σ) (canonical_digits h τ) he
  have hf := List.ofFn_injective (List.append_cancel_right (List.cons.inj hw).2)
  apply Equiv.ext
  intro i
  apply Fin.ext
  have hi := congrFun hf i
  omega

lemma roots_card (h : ℕ) : (roots h).card = h.factorial := by
  rw [roots, card_image_of_injective _ (root_injective h)]
  simp [Fintype.card_perm]

lemma square_injective : Function.Injective (fun n : ℕ => n^2) := by
  intro a b h
  nlinarith

lemma squares_card (h : ℕ) : (squares h).card = h.factorial := by
  rw [squares, card_image_of_injective _ square_injective, roots_card]

lemma height_pos (h : ℕ) : 0 < height h := by
  exact pow_pos (by have := base_gt_one h; omega) _

lemma index_lt_height (h : ℕ) : h < height h := by
  have hb : h < base h := by unfold base; omega
  exact hb.trans_le (Nat.le_pow (by omega : 0 < h+2))

lemma height_mono : Monotone height := by
  intro a b hab
  have hb : base a ≤ base b := by unfold base; omega
  exact (Nat.pow_le_pow_left hb _).trans
    (Nat.pow_le_pow_right (by have := base_gt_one b; omega) (by omega))

/-- The arithmetic counting half of the candidate; Sidonness is an assumption. -/
theorem finite_lower {h N : ℕ} (hN : height h ≤ N)
    (hS : IsSidon (squares h : Set ℕ)) :
    h.factorial ≤ maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) := by
  have hsub : squares h ⊆ (Icc 1 N).image (fun n : ℕ => n^2) := by
    intro n hn
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hn
    obtain ⟨σ,_,rfl⟩ := mem_image.mp hr
    exact mem_image.mpr ⟨root h σ, mem_Icc.mpr
      ⟨root_pos h σ, (root_lt_height h σ).le.trans hN⟩,rfl⟩
  rw [← squares_card h]
  exact Finset.le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_powerset.mpr hsub,hS⟩)

lemma log_factorial_lower {h : ℕ} (hh : 1 ≤ h) :
    (h:ℝ)*Real.log h-h ≤ Real.log (h.factorial : ℝ) := by
  have hs := Stirling.le_log_factorial_stirling (by omega : h ≠ 0)
  have hl : 0 ≤ Real.log (h:ℝ) := Real.log_nonneg (by exact_mod_cast hh)
  have hp : 0 ≤ Real.log (2*Real.pi) :=
    Real.log_nonneg (by have := Real.pi_gt_three; linarith)
  linarith

lemma log_height_successor_upper {h : ℕ} (hh : 1 ≤ h) :
    Real.log (height (h+1) : ℝ) ≤ ((h:ℝ)+3)*(Real.log h+18) := by
  have hx : (0:ℝ)<h := by exact_mod_cast hh
  have hb : (base (h+1) : ℝ) ≤ 19*(h:ℝ) := by
    simp only [base, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    have hh' : (1:ℝ)≤h := by exact_mod_cast hh
    linarith
  have hl : Real.log (base (h+1) : ℝ) ≤ Real.log (h:ℝ)+18 := by
    calc
      _ ≤ Real.log (19*(h:ℝ)) :=
        Real.log_le_log (by exact_mod_cast lt_trans (by omega : 0<1) (base_gt_one (h+1))) hb
      _ = Real.log 19 + Real.log (h:ℝ) := by rw [Real.log_mul (by norm_num) hx.ne']
      _ ≤ _ := by have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<19); linarith
  simp only [height, Nat.cast_pow, Real.log_pow]
  push_cast
  nlinarith

/-- Explicit sufficient numerical conditions for the factorial count to
exceed the desired power even at the NEXT height. This supplies interpolation slack. -/
lemma factorial_power_lower {h : ℕ} {ε : ℝ} (hh : 3 ≤ h) (he : 0 < ε) (he1 : ε < 1)
    (heh : 6 ≤ ε*h) (hel : 74 ≤ ε*Real.log h) :
    (height (h+1) : ℝ)^(1-ε) ≤ (h.factorial : ℝ) := by
  have hx : (0:ℝ)<h := by exact_mod_cast (show 0<h by omega)
  have hx3 : (3:ℝ)≤h := by exact_mod_cast hh
  have hl : 0 ≤ Real.log (h:ℝ) := Real.log_nonneg (by linarith)
  have hL := log_height_successor_upper (show 1≤h by omega)
  have hF := log_factorial_lower (show 1≤h by omega)
  have hprod1 := mul_le_mul_of_nonneg_right heh hl
  have hprod2 := mul_le_mul_of_nonneg_right hel hx.le
  have hbudget : 3*Real.log (h:ℝ)+37*h ≤ ε*h*Real.log h := by nlinarith
  have hcoarse : Real.log (height (h+1) : ℝ) ≤
      (h:ℝ)*Real.log h+3*Real.log h+36*h := by nlinarith
  have hnon : 0 ≤ ε*(3*Real.log (h:ℝ)+36*h) := by positivity
  have hlog : (1-ε)*Real.log (height (h+1) : ℝ) ≤ Real.log (h.factorial : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hcoarse (by linarith : 0≤1-ε)
    nlinarith
  have hheight : (0:ℝ)<height (h+1) := by exact_mod_cast height_pos (h+1)
  have hfac : (0:ℝ)<h.factorial := by exact_mod_cast Nat.factorial_pos h
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hheight _) hfac).mp
  rwa [Real.log_rpow hheight]

lemma eventual_factorial_power (ε : ℝ) (he : 0<ε) (he1 : ε<1) :
    ∀ᶠ h : ℕ in atTop,
      (height (h+1) : ℝ)^(1-ε) ≤ (h.factorial : ℝ) := by
  have hh : Tendsto (fun h : ℕ => ε*(h:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop he
  have hl : Tendsto (fun h : ℕ => ε*Real.log (h:ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop he
  filter_upwards [eventually_ge_atTop 3,hh.eventually_ge_atTop 6,hl.eventually_ge_atTop 74]
    with h hh heh hel
  exact factorial_power_lower hh he he1 heh hel

/-- The complete lower alphabet is permuted; this is not an arbitrary
histogram with omitted or repeated allowed digits. -/
lemma word_perm (h : ℕ) (σ : Equiv.Perm (Fin h)) :
    (word h σ).Perm (word h (Equiv.refl (Fin h))) := by
  apply List.Perm.cons
  apply List.Perm.append_right
  exact σ.ofFn_comp_perm (fun i : Fin h => 6*(i.val+2))

/-- Conditional reduction to this particular candidate. The hypothesis is
NOT proved in this file. If it holds eventually, the original conjecture
follows at every sufficiently large integer height, not just selected heights. -/
theorem near_linear_of_eventually_sidon
    (hSidon : ∀ᶠ h : ℕ in atTop, IsSidon (squares h : Set ℕ)) :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (N : ℝ)^(1-ε) ≤
        (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) : ℝ) := by
  intro ε hε
  let δ := min ε (1/2 : ℝ)
  have hδ : 0<δ := lt_min hε (by norm_num)
  have hδε : δ≤ε := min_le_left _ _
  have hδ1 : δ<1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨H,hH⟩ := eventually_atTop.mp
    ((eventual_factorial_power δ hδ hδ1).and hSidon)
  filter_upwards [eventually_ge_atTop (height H)] with N hN
  classical
  have hex : ∃ j : ℕ, N < height j := ⟨N,index_lt_height N⟩
  let j := Nat.find hex
  have hjN : N < height j := Nat.find_spec hex
  have hHj : H < j := by
    by_contra! hj
    exact (not_lt_of_ge ((height_mono hj).trans hN)) hjN
  have hj0 : 0<j := by omega
  let h := j-1
  have hj : h+1=j := Nat.sub_add_cancel (by omega)
  have hhH : H≤h := by omega
  have hhj : h<j := Nat.sub_lt hj0 (by omega)
  have hhN : height h ≤ N := Nat.le_of_not_lt (Nat.find_min hex hhj)
  have hnext : N≤height (h+1) := by rw [hj]; exact hjN.le
  have hN1 : (1:ℝ)≤N := by
    exact_mod_cast ((height_pos H).trans_le hN)
  have hfac := (hH h hhH).1
  have hs := (hH h hhH).2
  have hmax := finite_lower hhN hs
  calc
    (N:ℝ)^(1-ε) ≤ (N:ℝ)^(1-δ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    _ ≤ (height (h+1):ℝ)^(1-δ) := Real.rpow_le_rpow
      (Nat.cast_nonneg N) (by exact_mod_cast hnext) (by linarith)
    _ ≤ (h.factorial:ℝ) := hfac
    _ ≤ (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)):ℝ) := by
      exact_mod_cast hmax

#print axioms root_injective
#print axioms squares_card
#print axioms finite_lower
#print axioms factorial_power_lower
#print axioms eventual_factorial_power
#print axioms word_perm
#print axioms near_linear_of_eventually_sidon
end
end Erdos773.AllowedAlphabetCandidate
