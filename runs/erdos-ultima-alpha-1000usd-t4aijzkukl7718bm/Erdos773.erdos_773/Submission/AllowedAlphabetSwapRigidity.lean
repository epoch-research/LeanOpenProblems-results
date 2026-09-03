import Submission.AllowedAlphabetCandidate

/-! Uniqueness for square differences having a single-transposition shape.
This is a restricted criterion, not Sidonness of all digit permutations. -/
namespace Erdos773.AllowedAlphabetSwapRigidity
noncomputable section
set_option maxHeartbeats 2000000

lemma base_coprime_twelve (h : ℕ) : IsCoprime (6*(h : ℤ)+7) 12 := by
  refine ⟨6*(h : ℤ)+7, -(3*(h : ℤ)^2+7*h+4), ?_⟩
  ring

lemma core_congr {B x z u : ℤ} {k : ℕ} (hk : k ≠ 0)
    (hx : x ≡ 6 [ZMOD B]) (hz : z ≡ 6 [ZMOD B]) :
    u*(B^k-1)*(x+z) ≡ -12*u [ZMOD B] := by
  have hp : B^k ≡ 0 [ZMOD B] := Int.modEq_zero_iff_dvd.mpr (dvd_pow_self B hk)
  have hc := ((Int.ModEq.refl u).mul (hp.sub (Int.ModEq.refl 1))).mul (hx.add hz)
  convert hc using 1; ring

lemma core_not_dvd {B x z u : ℤ} {k : ℕ} (hcop : IsCoprime B 12)
    (hu : 0 < u) (hub : u < B) (hk : k ≠ 0)
    (hx : x ≡ 6 [ZMOD B]) (hz : z ≡ 6 [ZMOD B]) :
    ¬ B ∣ u*(B^k-1)*(x+z) := by
  intro hd
  have hneg := (core_congr hk hx hz).dvd_iff.mp hd
  have hm : B ∣ 12*u := by simpa only [neg_mul, dvd_neg] using hneg
  have hz := Int.eq_zero_of_abs_lt_dvd (hcop.dvd_of_dvd_mul_left hm)
    (by rwa [abs_of_pos hu])
  omega

lemma equal_power_index {B a b : ℤ} {i j : ℕ} (hB : B ≠ 0)
    (ha : ¬ B ∣ a) (hb : ¬ B ∣ b) (he : B^i*a = B^j*b) : i = j := by
  have not_lt {i j : ℕ} {a b : ℤ} (ha : ¬ B ∣ a)
      (he : B^i*a = B^j*b) (hij : i < j) : False := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij.le
    have hd : d ≠ 0 := by omega
    rw [pow_add, mul_assoc] at he
    have he' := mul_left_cancel₀ (pow_ne_zero i hB) he
    exact ha (he' ▸ dvd_mul_of_dvd_left (dvd_pow_self B hd) b)
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (not_lt ha he h)
  · exact h
  · exact False.elim (not_lt hb he.symm h)

lemma equal_gap_exponent {B L S T : ℤ} {k l : ℕ} (hB : 2 ≤ B)
    (hS : 2*L ≤ S ∧ S < 4*L) (hT : 2*L ≤ T ∧ T < 4*L)
    (hk : 0 < k) (hl : 0 < l)
    (he : (B^k-1)*S = (B^l-1)*T) : k = l := by
  have not_lt {k l : ℕ} {S T : ℤ} (hk : 0 < k)
      (hS : S < 4*L) (hT : 2*L ≤ T)
      (he : (B^k-1)*S = (B^l-1)*T) (hkl : k < l) : False := by
    have hp : 0 < B^k-1 := by
      have hh := pow_lt_pow_right₀ (by omega : 1 < B) hk
      simpa only [pow_zero] using (sub_pos.mpr hh)
    have hp' : B*B^k ≤ B^l := by
      simpa only [pow_succ, mul_comm] using
        pow_le_pow_right₀ (by omega : 1 ≤ B) (by omega : k+1 ≤ l)
    have hgap : 2*(B^k-1) ≤ B^l-1 := by
      have hh := mul_le_mul_of_nonneg_right hB hp.le
      nlinarith
    have hT0 : 0 < T := by omega
    have hh := mul_le_mul_of_nonneg_right hgap hT0.le
    have hST : S < 2*T := by omega
    have hstrict := mul_lt_mul_of_pos_left hST hp
    nlinarith
  rcases lt_trichotomy k l with h | h | h
  · exact False.elim (not_lt hk hS.2 hT.1 he h)
  · exact h
  · exact False.elim (not_lt hl hT.2 hS.1 he.symm h)

/-- Two positive differences with one-swap shapes have the same endpoints.
The radix need not be prime. The hypotheses on its coprimality and the gap
coefficients are essential to the lowest-position argument. -/
theorem single_swap_rigidity {B L x y z w u v : ℤ} {i j k l : ℕ}
    (hB : 2 ≤ B) (hcop : IsCoprime B 12) (_hL : 0 < L)
    (hxL : L ≤ x ∧ x < 2*L) (hyL : L ≤ y ∧ y < 2*L)
    (hzL : L ≤ z ∧ z < 2*L) (hwL : L ≤ w ∧ w < 2*L)
    (hx : x ≡ 6 [ZMOD B]) (hy : y ≡ 6 [ZMOD B])
    (hz : z ≡ 6 [ZMOD B]) (hw : w ≡ 6 [ZMOD B])
    (hu : 0 < u) (hub : u < B) (hv : 0 < v) (hvb : v < B)
    (hk : 0 < k) (hl : 0 < l)
    (hxz : x-z = 6*u*B^i*(B^k-1)) (hwy : w-y = 6*v*B^j*(B^l-1))
    (hnorm : x^2+y^2 = z^2+w^2) :
    i = j ∧ u = v ∧ k = l ∧ x = w ∧ z = y := by
  have hB0 : B ≠ 0 := by omega
  have h6 : (6:ℤ)*(B^i*(u*(B^k-1)*(x+z))) =
      6*(B^j*(v*(B^l-1)*(w+y))) := by
    calc
      _ = (x-z)*(x+z) := by rw [hxz]; ring
      _ = (w-y)*(w+y) := by nlinarith
      _ = _ := by rw [hwy]; ring
  have he := mul_left_cancel₀ (by norm_num : (6:ℤ) ≠ 0) h6
  have hij := equal_power_index hB0 (core_not_dvd hcop hu hub hk.ne' hx hz)
    (core_not_dvd hcop hv hvb hl.ne' hw hy) he
  subst j
  have hc := mul_left_cancel₀ (pow_ne_zero i hB0) he
  have hmod : -12*u ≡ -12*v [ZMOD B] :=
    (core_congr hk.ne' hx hz).symm.trans
      (hc ▸ core_congr hl.ne' hw hy)
  have hdiv : B ∣ 12*(u-v) := by
    convert hmod.dvd using 1; ring
  have huv : u = v := by
    have hh := Int.eq_zero_of_abs_lt_dvd (hcop.dvd_of_dvd_mul_left hdiv)
      (by rw [abs_lt]; omega)
    omega
  subst v
  have hc' : (B^k-1)*(x+z) = (B^l-1)*(w+y) := by
    apply mul_left_cancel₀ hu.ne'
    simpa only [mul_assoc] using hc
  have hkl := equal_gap_exponent hB
    (by constructor <;> omega : 2*L ≤ x+z ∧ x+z < 4*L)
    (by constructor <;> omega : 2*L ≤ w+y ∧ w+y < 4*L) hk hl hc'
  subst l
  have hgap : B^k-1 ≠ 0 := by
    have hh := pow_lt_pow_right₀ (by omega : 1 < B) hk
    simp only [pow_zero] at hh
    omega
  have hsum := mul_left_cancel₀ hgap hc'
  exact ⟨rfl,rfl,rfl,by omega,by omega⟩

open AllowedAlphabetCandidate

lemma leading_range (h : ℕ) (σ : Equiv.Perm (Fin h)) :
    (base h)^(h+1) ≤ root h σ ∧ root h σ < 2*(base h)^(h+1) := by
  let lower := 6 :: List.ofFn (fun i : Fin h => 6*((σ i).val+2))
  have hlen : lower.length = h+1 := by simp [lower]
  have hdigits : ∀ d ∈ lower, d < base h := by
    intro d hd
    apply canonical_digits h σ d
    have hw : word h σ = lower ++ [1] := rfl
    rw [hw]
    exact List.mem_append_left _ hd
  have hsmall : Nat.ofDigits (base h) lower < (base h)^(h+1) := by
    simpa only [hlen] using Nat.ofDigits_lt_base_pow_length (base_gt_one h) hdigits
  have hroot : root h σ = Nat.ofDigits (base h) lower+(base h)^(h+1) := by
    change Nat.ofDigits (base h) (lower ++ [1]) = _
    rw [Nat.ofDigits_append, hlen]
    simp
  rw [hroot]
  omega

lemma constant_residue (h : ℕ) (σ : Equiv.Perm (Fin h)) :
    (root h σ : ℤ) ≡ 6 [ZMOD (base h : ℤ)] := by
  apply Int.modEq_iff_dvd.mpr
  simp only [root, word, Nat.ofDigits_cons, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  refine ⟨-((Nat.ofDigits (base h)
    (List.ofFn (fun i : Fin h => 6*((σ i).val+2)) ++ [1]) : ℕ) : ℤ), ?_⟩
  ring

lemma ofDigits_ofFn (B : ℕ) {h : ℕ} (f : Fin h → ℕ) :
    Nat.ofDigits B (List.ofFn f) = ∑ i, f i * B^i.val := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [List.ofFn_succ, Nat.ofDigits_cons, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

lemma root_sum (h : ℕ) (σ : Equiv.Perm (Fin h)) :
    (root h σ : ℤ) = 6+(base h : ℤ)^ (h+1) +
      6*(base h : ℤ)*(∑ i : Fin h, ((σ i).val+2 : ℤ)*(base h : ℤ)^i.val) := by
  simp only [root, word, Nat.ofDigits_cons, Nat.ofDigits_append,
    List.length_ofFn, Nat.ofDigits_nil, ofDigits_ofFn,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_sum,
    mul_zero, add_zero, mul_one]
  simp_rw [mul_assoc]
  rw [pow_succ, ← Finset.mul_sum]
  ring

lemma transposition_difference {h : ℕ} (σ : Equiv.Perm (Fin h))
    (a b : Fin h) (hab : a < b) :
    (root h σ : ℤ) - root h (σ * Equiv.swap a b) =
      6*((σ b).val-(σ a).val : ℤ)*(base h : ℤ)^(a.val+1)*
        ((base h : ℤ)^(b.val-a.val)-1) := by
  have hne : a ≠ b := ne_of_lt hab
  have hd : (∑ i : Fin h, ((σ i).val+2 : ℤ)*(base h : ℤ)^i.val) -
      (∑ i : Fin h, (((σ * Equiv.swap a b) i).val+2 : ℤ)*(base h : ℤ)^i.val) =
      ((σ b).val-(σ a).val : ℤ)*((base h : ℤ)^b.val-(base h : ℤ)^a.val) := by
    rw [← Finset.sum_sub_distrib]
    have he (i : Fin h) :
        ((σ i).val+2 : ℤ)*(base h : ℤ)^i.val -
          (((σ * Equiv.swap a b) i).val+2 : ℤ)*(base h : ℤ)^i.val =
        (if i=a then ((σ a).val-(σ b).val : ℤ)*(base h : ℤ)^a.val else 0)+
        (if i=b then ((σ b).val-(σ a).val : ℤ)*(base h : ℤ)^b.val else 0) := by
      by_cases hia : i=a
      · subst i; simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, if_true, if_neg hne]
        ring
      · by_cases hib : i=b
        · subst i
          simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right, if_neg hia, if_true]
          ring
        · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hia hib,
            if_neg hia, if_neg hib, sub_self, add_zero]
    rw [Finset.sum_congr rfl (fun i _ => he i), Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [root_sum, root_sum]
  have hp : (base h : ℤ)^b.val = (base h : ℤ)^a.val*(base h : ℤ)^(b.val-a.val) := by
    rw [← pow_add, Nat.add_sub_of_le (show a.val ≤ b.val from hab.le)]
  have hf := congrArg (fun t : ℤ => 6*(base h : ℤ)*t) hd
  rw [hp] at hf
  rw [pow_succ]
  linear_combination hf

/-- Actual increasing digit swaps cannot give two different representations
of one positive square difference inside the full allowed alphabet family. -/
theorem transposition_rigidity {h : ℕ} (σ τ : Equiv.Perm (Fin h))
    (a b c d : Fin h) (hab : a < b) (hcd : c < d)
    (hσ : σ a < σ b) (hτ : τ c < τ d)
    (he : (root h σ)^2+(root h (τ * Equiv.swap c d))^2 =
      (root h (σ * Equiv.swap a b))^2+(root h τ)^2) :
    σ = τ ∧ σ * Equiv.swap a b = τ * Equiv.swap c d ∧ a = c ∧ b = d := by
  let B : ℤ := base h
  let L : ℤ := B^(h+1)
  have hB : 2 ≤ B := by dsimp [B, base]; omega
  have hcop : IsCoprime B 12 := by
    simpa only [B, base, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using base_coprime_twelve h
  have hL : 0 < L := pow_pos (by omega : 0 < B) _
  have hR (ρ : Equiv.Perm (Fin h)) : L ≤ (root h ρ : ℤ) ∧ (root h ρ : ℤ) < 2*L := by
    dsimp [L, B]
    exact_mod_cast leading_range h ρ
  have hu : 0 < ((σ b).val-(σ a).val : ℤ) := by
    apply sub_pos.mpr
    exact_mod_cast (show (σ a).val < (σ b).val from hσ)
  have hv : 0 < ((τ d).val-(τ c).val : ℤ) := by
    apply sub_pos.mpr
    exact_mod_cast (show (τ c).val < (τ d).val from hτ)
  have hub : ((σ b).val-(σ a).val : ℤ) < B := by
    have hh := (σ b).isLt
    dsimp [B,base]; omega
  have hvb : ((τ d).val-(τ c).val : ℤ) < B := by
    have hh := (τ d).isLt
    dsimp [B,base]; omega
  have hk : 0 < b.val-a.val := Nat.sub_pos_of_lt hab
  have hl : 0 < d.val-c.val := Nat.sub_pos_of_lt hcd
  have hn : (root h σ : ℤ)^2+(root h (τ * Equiv.swap c d) : ℤ)^2 =
      (root h (σ * Equiv.swap a b) : ℤ)^2+(root h τ : ℤ)^2 := by exact_mod_cast he
  obtain ⟨hij, _, hkl, hx, hz⟩ := single_swap_rigidity hB hcop hL
    (hR σ) (hR (τ * Equiv.swap c d)) (hR (σ * Equiv.swap a b)) (hR τ)
    (constant_residue h σ) (constant_residue h (τ * Equiv.swap c d))
    (constant_residue h (σ * Equiv.swap a b)) (constant_residue h τ)
    hu hub hv hvb hk hl (transposition_difference σ a b hab)
    (transposition_difference τ c d hcd) hn
  refine ⟨root_injective h (by exact_mod_cast hx),
    root_injective h (by exact_mod_cast hz), Fin.ext (by omega), Fin.ext (by omega)⟩

#print axioms single_swap_rigidity
#print axioms leading_range
#print axioms constant_residue
#print axioms transposition_difference
#print axioms transposition_rigidity
end
end Erdos773.AllowedAlphabetSwapRigidity
