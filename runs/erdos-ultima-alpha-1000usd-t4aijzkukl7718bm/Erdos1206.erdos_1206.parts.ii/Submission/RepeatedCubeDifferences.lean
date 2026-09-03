import FormalConjecturesUtil

/-!
Repeated rational cubic differences. This auxiliary file does not settle the
positive-natural-density conjecture.
-/

namespace Erdos1206.RepeatedCubeDifferences

/-- Homogeneous tangent construction on `a^3-b^3 = 7*c^3`. -/
def tangent (v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (v.1 * (v.1^3 - 2*v.2.1^3),
   -v.2.1 * (2*v.1^3-v.2.1^3),
   v.2.2 * (v.1^3+v.2.1^3))

def orbit : ℕ → ℤ × ℤ × ℤ
  | 0 => (73,17,38)
  | n+1 => tangent (orbit n)

abbrev numA (n : ℕ) : ℤ := (orbit n).1
abbrev numB (n : ℕ) : ℤ := (orbit n).2.1
abbrev denom (n : ℕ) : ℤ := (orbit n).2.2

lemma tangent_identity (a b : ℤ) :
    (a*(a^3-2*b^3))^3 - (-b*(2*a^3-b^3))^3 =
      (a^3-b^3)*(a^3+b^3)^3 := by ring

lemma orbit_identity (n : ℕ) : numA n ^ 3 - numB n ^ 3 = 7 * denom n ^ 3 := by
  induction n with
  | zero => norm_num [numA, numB, denom, orbit]
  | succ n ih =>
    change (numA n * (numA n ^ 3 - 2 * numB n ^ 3)) ^ 3 -
      (-numB n * (2 * numA n ^ 3 - numB n ^ 3)) ^ 3 =
      7 * (denom n * (numA n ^ 3 + numB n ^ 3)) ^ 3
    rw [tangent_identity, ih]
    ring

lemma orbit_mod_four (n : ℕ) :
    (numA n % 4 = 1 ∧ numB n % 4 = 1) ∨
      (numA n % 4 = 3 ∧ numB n % 4 = 3) := by
  induction n with
  | zero => norm_num [numA, numB, orbit]
  | succ n ih =>
    right
    change (numA n * (numA n ^ 3 - 2 * numB n ^ 3)) % 4 = 3 ∧
      (-numB n * (2 * numA n ^ 3 - numB n ^ 3)) % 4 = 3
    rcases ih with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · have ha' : numA n ≡ 1 [ZMOD 4] := ha
      have hb' : numB n ≡ 1 [ZMOD 4] := hb
      have hA := ha'.mul ((ha'.pow 3).sub ((Int.ModEq.refl 2).mul (hb'.pow 3)))
      have hB := hb'.neg.mul (((Int.ModEq.refl 2).mul (ha'.pow 3)).sub (hb'.pow 3))
      exact ⟨by simpa [Int.ModEq] using hA, by simpa [Int.ModEq] using hB⟩
    · have ha' : numA n ≡ 3 [ZMOD 4] := ha
      have hb' : numB n ≡ 3 [ZMOD 4] := hb
      have hA := ha'.mul ((ha'.pow 3).sub ((Int.ModEq.refl 2).mul (hb'.pow 3)))
      have hB := hb'.neg.mul (((Int.ModEq.refl 2).mul (ha'.pow 3)).sub (hb'.pow 3))
      exact ⟨by simpa [Int.ModEq] using hA, by simpa [Int.ModEq] using hB⟩

lemma nums_odd (n : ℕ) : numA n % 2 = 1 ∧ numB n % 2 = 1 := by
  rcases orbit_mod_four n with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> omega

lemma tangent_den_mod_four (n : ℕ) :
    (numA n ^ 3 + numB n ^ 3) % 4 = 2 := by
  rcases orbit_mod_four n with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
    norm_num [Int.add_emod, pow_succ, Int.mul_emod, ha, hb]

lemma denom_ne_zero (n : ℕ) : denom n ≠ 0 := by
  induction n with
  | zero => norm_num [denom, orbit]
  | succ n ih =>
    change denom n * (numA n ^ 3 + numB n ^ 3) ≠ 0
    apply mul_ne_zero ih
    have := tangent_den_mod_four n
    intro h
    rw [h] at this
    norm_num at this

lemma denom_dvd_succ (n : ℕ) : denom n ∣ denom (n+1) := by
  change denom n ∣ denom n * _
  exact dvd_mul_right _ _

lemma twice_denom_dvd_succ (n : ℕ) : 2 * denom n ∣ denom (n+1) := by
  have he : 2 ∣ numA n ^ 3 + numB n ^ 3 := by
    apply Int.dvd_of_emod_eq_zero
    have := tangent_den_mod_four n
    omega
  obtain ⟨k,hk⟩ := he
  refine ⟨k, ?_⟩
  change denom n * (numA n ^ 3 + numB n ^ 3) = 2 * denom n * k
  rw [hk]
  ring

lemma denom_dvd_of_le {i j : ℕ} (hij : i ≤ j) : denom i ∣ denom j := by
  induction j, hij using Nat.le_induction with
  | base => exact dvd_refl _
  | succ j hij ih => exact ih.trans (denom_dvd_succ j)

lemma twice_denom_dvd_of_lt {i j : ℕ} (hij : i < j) : 2 * denom i ∣ denom j :=
  (twice_denom_dvd_succ i).trans (denom_dvd_of_le hij)

def rootA (n : ℕ) : ℚ := (numA n : ℚ) / denom n

def rootB (n : ℕ) : ℚ := (numB n : ℚ) / denom n

lemma rational_identity (n : ℕ) : rootA n ^ 3 - rootB n ^ 3 = 7 := by
  have hc : (denom n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (denom_ne_zero n)
  have hi : (numA n : ℚ) ^ 3 - (numB n : ℚ) ^ 3 = 7 * (denom n : ℚ) ^ 3 := by
    exact_mod_cast orbit_identity n
  dsimp only [rootA, rootB]
  field_simp
  simpa [mul_comm] using hi

lemma odd_fraction_ne {a b c d k : ℤ} (hc : c ≠ 0) (hd : d ≠ 0)
    (hb : b % 2 = 1) (hdk : d = 2*c*k) :
    (a : ℚ) / c ≠ (b : ℚ) / d := by
  intro he
  have hcQ : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hdQ : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
  have he' : a*d=b*c := by
    exact_mod_cast (div_eq_div_iff hcQ hdQ).mp he
  rw [hdk] at he'
  have he'' : c*(2*a*k)=c*b := by nlinarith only [he']
  have heq : 2*a*k=b := mul_left_cancel₀ hc he''
  have hdvd : 2 ∣ b := by rw [← heq]; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hz := Int.emod_eq_zero_of_dvd hdvd
  omega

lemma rootA_injective : Function.Injective rootA := by
  intro i j he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨k,hk⟩ := twice_denom_dvd_of_lt h
    exact odd_fraction_ne (denom_ne_zero i) (denom_ne_zero j) (nums_odd j).1 hk he
  · obtain ⟨k,hk⟩ := twice_denom_dvd_of_lt h
    exact odd_fraction_ne (denom_ne_zero j) (denom_ne_zero i) (nums_odd i).1 hk he.symm

lemma rootB_injective : Function.Injective rootB := by
  intro i j he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨k,hk⟩ := twice_denom_dvd_of_lt h
    exact odd_fraction_ne (denom_ne_zero i) (denom_ne_zero j) (nums_odd j).2 hk he
  · obtain ⟨k,hk⟩ := twice_denom_dvd_of_lt h
    exact odd_fraction_ne (denom_ne_zero j) (denom_ne_zero i) (nums_odd i).2 hk he.symm

lemma rootA_ne_zero (n : ℕ) : rootA n ≠ 0 := by
  apply div_ne_zero
  · apply Int.cast_ne_zero.mpr
    have := (nums_odd n).1
    intro h
    rw [h] at this
    norm_num at this
  · exact Int.cast_ne_zero.mpr (denom_ne_zero n)

lemma rootB_ne_zero (n : ℕ) : rootB n ≠ 0 := by
  apply div_ne_zero
  · apply Int.cast_ne_zero.mpr
    have := (nums_odd n).2
    intro h
    rw [h] at this
    norm_num at this
  · exact Int.cast_ne_zero.mpr (denom_ne_zero n)

lemma rootB_lt_rootA (n : ℕ) : rootB n < rootA n := by
  apply (Odd.pow_lt_pow (by decide : Odd 3)).mp
  linarith [rational_identity n]

lemma root_cube_sum_ne_zero (n : ℕ) : rootA n ^ 3 + rootB n ^ 3 ≠ 0 := by
  have hs : numA n ^ 3 + numB n ^ 3 ≠ 0 := by
    have := tangent_den_mod_four n
    intro h
    rw [h] at this
    norm_num at this
  have hc : (denom n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (denom_ne_zero n)
  have hsQ : (numA n : ℚ)^3 + (numB n : ℚ)^3 ≠ 0 := by exact_mod_cast hs
  dsimp only [rootA, rootB]
  rw [div_pow, div_pow, ← add_div]
  exact div_ne_zero hsQ (pow_ne_zero _ hc)

lemma rootA_succ (n : ℕ) : rootA (n+1) =
    rootA n * (rootA n^3-2*rootB n^3) / (rootA n^3+rootB n^3) := by
  have hc : (denom n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (denom_ne_zero n)
  have hs : (numA n : ℚ)^3+(numB n : ℚ)^3 ≠ 0 := by
    have h := root_cube_sum_ne_zero n
    dsimp only [rootA, rootB] at h
    rw [div_pow, div_pow, ← add_div] at h
    exact (div_ne_zero_iff.mp h).1
  change ((numA n * (numA n^3-2*numB n^3) : ℤ) : ℚ) /
    ↑(denom n * (numA n^3+numB n^3)) = _
  dsimp only [rootA, rootB]
  push_cast
  field_simp

lemma rootB_succ (n : ℕ) : rootB (n+1) =
    -rootB n * (2*rootA n^3-rootB n^3) / (rootA n^3+rootB n^3) := by
  have hc : (denom n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (denom_ne_zero n)
  have hs : (numA n : ℚ)^3+(numB n : ℚ)^3 ≠ 0 := by
    have h := root_cube_sum_ne_zero n
    dsimp only [rootA, rootB] at h
    rw [div_pow, div_pow, ← add_div] at h
    exact (div_ne_zero_iff.mp h).1
  change ((-numB n * (2*numA n^3-numB n^3) : ℤ) : ℚ) /
    ↑(denom n * (numA n^3+numB n^3)) = _
  dsimp only [rootA, rootB]
  push_cast
  field_simp

lemma same_sign_or_succ (n : ℕ) :
    0 < rootA n * rootB n ∨ 0 < rootA (n+1) * rootB (n+1) := by
  by_cases h : 0 < rootA n * rootB n
  · exact Or.inl h
  right
  have hlt := rootB_lt_rootA n
  have hprod : rootA n * rootB n < 0 :=
    lt_of_le_of_ne (le_of_not_gt h) (mul_ne_zero (rootA_ne_zero n) (rootB_ne_zero n))
  have ha : 0 < rootA n := by
    rcases mul_neg_iff.mp hprod with h | h
    · exact h.1
    · linarith [h.1, h.2]
  have hb : rootB n < 0 := (mul_neg_iff.mp hprod).resolve_right (by rintro ⟨h,_⟩; linarith)
    |>.2
  have ha3 : 0 < rootA n^3 := pow_pos ha 3
  have hb3 : rootB n^3 < 0 := (Odd.pow_neg_iff (by decide : Odd 3)).mpr hb
  rw [rootA_succ, rootB_succ, div_mul_div_comm]
  apply div_pos
  · exact mul_pos (mul_pos ha (by linarith)) (mul_pos (neg_pos.mpr hb) (by linarith))
  · exact mul_self_pos.mpr (root_cube_sum_ne_zero n)

/-- There are infinitely many positive rational pairs whose cubes differ by seven. -/
theorem infinite_positive_cube_difference :
    {b : ℚ | 0 < b ∧ ∃ a : ℚ, 0 < a ∧ a^3-b^3=7}.Infinite := by
  let P : Set ℕ := {n | 0 < rootB n}
  let Q : Set ℕ := {n | rootA n < 0}
  have hun : (P ∪ Q).Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro N
    have hmem (n : ℕ) (h : 0 < rootA n * rootB n) : n ∈ P ∪ Q := by
      rcases mul_pos_iff.mp h with h | h
      · exact Or.inl h.2
      · exact Or.inr h.1
    rcases same_sign_or_succ (N+1) with h | h
    · exact ⟨N+1, hmem _ h, by omega⟩
    · exact ⟨N+2, hmem _ h, by omega⟩
  rcases Set.infinite_union.mp hun with hp | hq
  · have him : (rootB '' P).Infinite := hp.image rootB_injective.injOn
    apply him.mono
    rintro b ⟨n, hn, rfl⟩
    exact ⟨hn, rootA n, lt_trans hn (rootB_lt_rootA n), rational_identity n⟩
  · have hinj : Function.Injective (fun n => -rootA n) :=
      neg_injective.comp rootA_injective
    have him : ((fun n => -rootA n) '' Q).Infinite := hq.image hinj.injOn
    apply him.mono
    rintro b ⟨n, hn, rfl⟩
    refine ⟨neg_pos.mpr hn, -rootB n, neg_pos.mpr (lt_trans (rootB_lt_rootA n) hn), ?_⟩
    have := rational_identity n
    nlinarith

/-- Finite Sidon extraction with one fixed translation also kept disjoint. -/
lemma finite_sidon_translate_disjoint (V : Set ℚ) (hV : V.Infinite) (k : ℕ) :
    ∃ U : Finset ℚ, (U : Set ℚ) ⊆ V ∧ U.card = k ∧ IsSidon (U : Set ℚ) ∧
      ∀ v ∈ U, ∀ w ∈ U, v+7 ≠ w := by
  classical
  induction k with
  | zero => exact ⟨∅, by simp, by simp, by simp [IsSidon], by simp⟩
  | succ k ih =>
    obtain ⟨U,hUV,hcard,hSid,hdis⟩ := ih
    let halfSums := (U ×ˢ U).image (fun z : ℚ × ℚ => (z.1+z.2)/2)
    let completions := (U ×ˢ (U ×ˢ U)).image
      (fun z : ℚ × (ℚ × ℚ) => z.2.1+z.2.2-z.1)
    let forbidden := U ∪ halfSums ∪ completions ∪
      U.image (fun z => z+7) ∪ U.image (fun z => z-7)
    obtain ⟨v,hvV,hv⟩ := hV.exists_notMem_finset forbidden
    have hvU : v ∉ U := by intro h; exact hv (by simp only [forbidden, Finset.mem_union]; tauto)
    have hvH : v ∉ halfSums := by intro h; exact hv (by simp only [forbidden, Finset.mem_union]; tauto)
    have hvC : v ∉ completions := by intro h; exact hv (by simp only [forbidden, Finset.mem_union]; tauto)
    have hvplus : v ∉ U.image (fun z => z+7) := by
      intro h; exact hv (by simp only [forbidden, Finset.mem_union]; tauto)
    have hvminus : v ∉ U.image (fun z => z-7) := by
      intro h; exact hv (by simp only [forbidden, Finset.mem_union]; tauto)
    refine ⟨insert v U, ?_, by simp [hvU,hcard], ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hvV
      · exact hUV hw
    · have h := (Set.IsSidon.insert hSid).mpr (Or.inr (by
        intro a ha b hb
        refine ⟨?_, ?_⟩
        · intro he
          apply hvH
          exact Finset.mem_image.mpr ⟨(a,b), Finset.mem_product.mpr ⟨ha,hb⟩,
            by dsimp; linarith⟩
        · intro c hc he
          apply hvC
          exact Finset.mem_image.mpr ⟨(a,b,c),
            Finset.mem_product.mpr ⟨ha,Finset.mem_product.mpr ⟨hb,hc⟩⟩,
            by dsimp; linarith⟩))
      simpa only [Finset.coe_insert, Set.union_singleton] using h
    · intro x hx y hy
      rcases Finset.mem_insert.mp hx with hxv | hxU
      · subst x
        rcases Finset.mem_insert.mp hy with hyv | hyU
        · subst y; norm_num
        · intro he
          apply hvminus
          exact Finset.mem_image.mpr ⟨y,hyU,by linarith⟩
      · rcases Finset.mem_insert.mp hy with hyv | hyU
        · subst y
          intro he
          exact hvplus (Finset.mem_image.mpr ⟨x,hxU,he⟩)
        · exact hdis x hxU y hyU

/-- Arbitrarily large disjoint rational cube-Sidon sets with all the paired
cubic differences equal. In particular, Sidonness of the two pieces alone
cannot bound mixed collisions linearly in their combined cardinality. -/
theorem rational_sidon_pairs (k : ℕ) :
    ∃ a b : Fin k → ℚ,
      Function.Injective a ∧ Function.Injective b ∧
      (∀ i, 0 < a i ∧ 0 < b i ∧ (a i)^3-(b i)^3=7) ∧
      (∀ i j, a i ≠ b j) ∧
      IsSidon ((fun x : ℚ => x^3) '' Set.range a) ∧
      IsSidon ((fun x : ℚ => x^3) '' Set.range b) := by
  classical
  let R : Set ℚ := {b : ℚ | 0 < b ∧ ∃ a : ℚ, 0 < a ∧ a^3-b^3=7}
  let V : Set ℚ := (fun x : ℚ => x^3) '' R
  have hpow : Function.Injective (fun x : ℚ => x^3) :=
    (Odd.strictMono_pow (by decide : Odd 3)).injective
  have hV : V.Infinite := infinite_positive_cube_difference.image hpow.injOn
  obtain ⟨U,hUV,hcard,hSid,hdis⟩ := finite_sidon_translate_disjoint V hV k
  let e : Fin k ≃ U := (Finset.equivFinOfCardEq hcard).symm
  let u : Fin k → ℚ := fun i => (e i).val
  have hu (i : Fin k) : u i ∈ U := (e i).property
  have hui : Function.Injective u := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  have hchoose (i : Fin k) : ∃ a b : ℚ, 0 < a ∧ 0 < b ∧ a^3-b^3=7 ∧ b^3=u i := by
    obtain ⟨b,hb,hbe⟩ := hUV (hu i)
    obtain ⟨hbpos,a,hapos,he⟩ := hb
    exact ⟨a,b,hapos,hbpos,he,hbe⟩
  choose a b ha hb he hbe using hchoose
  have hae (i : Fin k) : (a i)^3=u i+7 := by linarith [he i, hbe i]
  have hai : Function.Injective a := by
    intro i j hij
    apply hui
    have h := congrArg (fun x : ℚ => x^3) hij
    simp only [hae] at h
    linarith
  have hbi : Function.Injective b := by
    intro i j hij
    apply hui
    have h := congrArg (fun x : ℚ => x^3) hij
    simpa only [hbe] using h
  refine ⟨a,b,hai,hbi,fun i => ⟨ha i,hb i,he i⟩,?_,?_,?_⟩
  · intro i j hij
    have h := congrArg (fun x : ℚ => x^3) hij
    simp only [hae,hbe] at h
    exact hdis (u i) (hu i) (u j) (hu j) h
  · rintro _ ⟨_,⟨i,rfl⟩,rfl⟩ _ ⟨_,⟨j,rfl⟩,rfl⟩
      _ ⟨_,⟨l,rfl⟩,rfl⟩ _ ⟨_,⟨m,rfl⟩,rfl⟩ heq
    have h : u i+u l=u j+u m := by
      simp only [hae] at heq
      linarith
    rcases hSid _ (hu i) _ (hu j) _ (hu l) _ (hu m) h with h | h
    · left; simp only [hae]; exact ⟨by rw [h.1], by rw [h.2]⟩
    · right; simp only [hae]; exact ⟨by rw [h.1], by rw [h.2]⟩
  · rintro _ ⟨_,⟨i,rfl⟩,rfl⟩ _ ⟨_,⟨j,rfl⟩,rfl⟩
      _ ⟨_,⟨l,rfl⟩,rfl⟩ _ ⟨_,⟨m,rfl⟩,rfl⟩ heq
    simp only [hbe] at heq ⊢
    exact hSid _ (hu i) _ (hu j) _ (hu l) _ (hu m) heq

lemma common_positive_denominator {ι : Type*} [Fintype ι]
    (f : ι → ℚ) (hf : ∀ i, 0 < f i) :
    ∃ D : ℕ, 0 < D ∧ ∃ t : ι → ℕ,
      (∀ i, 0 < t i) ∧ ∀ i, (t i : ℚ) = (D : ℚ)*f i := by
  classical
  let D : ℕ := ∏ i, (f i).den
  have hD : 0 < D := Finset.prod_pos (fun i _ => Rat.den_pos (f i))
  have hex (i : ι) : ∃ t : ℕ, 0 < t ∧ (t : ℚ) = (D : ℚ)*f i := by
    have hd : (f i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨m,hm⟩ := hd
    have hmpos : 0 < m := by
      by_contra h
      have hm0 : m=0 := by omega
      rw [hm0,mul_zero] at hm
      omega
    have hnum : 0 < (f i).num := Rat.num_pos.mpr (hf i)
    have hn : ((f i).num.toNat : ℚ) = (f i).num := by
      exact_mod_cast Int.toNat_of_nonneg hnum.le
    refine ⟨(f i).num.toNat*m, Nat.mul_pos (by omega) hmpos, ?_⟩
    push_cast
    rw [hn,hm]
    push_cast
    have he := Rat.den_mul_eq_num (f i)
    calc
      (↑(f i).num : ℚ) * m = ((f i).den * f i) * m := by rw [he]
      _ = (f i).den * m * f i := by ring
  choose t ht he using hex
  exact ⟨D,hD,t,ht,he⟩

lemma scaled_nat_cube_sidon {ι : Type*} (f : ι → ℚ) (g : ι → ℕ)
    {D : ℕ} (hD : 0 < D) (he : ∀ i, (g i : ℚ)=(D : ℚ)*f i)
    (hs : IsSidon ((fun x : ℚ => x^3) '' Set.range f)) :
    IsSidon ((fun x : ℕ => x^3) '' Set.range g) := by
  have hd : (D : ℚ)^3 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hD.ne')
  have ht (i j : ι) (h : (f i)^3=(f j)^3) : (g i)^3=(g j)^3 := by
    have hQ : (g i : ℚ)^3=(g j : ℚ)^3 := by
      rw [he,he,mul_pow,mul_pow,h]
    exact_mod_cast hQ
  rintro _ ⟨_,⟨i,rfl⟩,rfl⟩ _ ⟨_,⟨j,rfl⟩,rfl⟩
    _ ⟨_,⟨l,rfl⟩,rfl⟩ _ ⟨_,⟨m,rfl⟩,rfl⟩ heq
  have heQ : (g i : ℚ)^3+(g l : ℚ)^3=(g j : ℚ)^3+(g m : ℚ)^3 := by
    exact_mod_cast heq
  simp only [he,mul_pow,← mul_add] at heQ
  have heF := mul_left_cancel₀ hd heQ
  rcases hs _ ⟨_,⟨i,rfl⟩,rfl⟩ _ ⟨_,⟨j,rfl⟩,rfl⟩
    _ ⟨_,⟨l,rfl⟩,rfl⟩ _ ⟨_,⟨m,rfl⟩,rfl⟩ heF with h | h
  · exact Or.inl ⟨ht _ _ h.1,ht _ _ h.2⟩
  · exact Or.inr ⟨ht _ _ h.1,ht _ _ h.2⟩

/-- Two disjoint sets of `k` positive integral roots can each have Sidon cubes,
while supporting every cross-pair identity
`a(i)^3+b(j)^3=a(j)^3+b(i)^3`. The common scaling depends on `k`. -/
theorem natural_sidon_pairs (k : ℕ) :
    ∃ D : ℕ, 0 < D ∧ ∃ a b : Fin k → ℕ,
      Function.Injective a ∧ Function.Injective b ∧
      (∀ i, 0 < a i ∧ 0 < b i ∧ (a i)^3=(b i)^3+7*D^3) ∧
      (∀ i j, a i ≠ b j) ∧
      IsSidon ((fun x : ℕ => x^3) '' Set.range a) ∧
      IsSidon ((fun x : ℕ => x^3) '' Set.range b) := by
  classical
  obtain ⟨a,b,hai,hbi,hpos,hdis,hsa,hsb⟩ := rational_sidon_pairs k
  let f : Fin k ⊕ Fin k → ℚ := Sum.elim a b
  have hf : ∀ i, 0 < f i := by
    intro i
    cases i with
    | inl i => exact (hpos i).1
    | inr i => exact (hpos i).2.1
  obtain ⟨D,hD,t,ht,he⟩ := common_positive_denominator f hf
  let A : Fin k → ℕ := fun i => t (Sum.inl i)
  let B : Fin k → ℕ := fun i => t (Sum.inr i)
  have hA (i : Fin k) : (A i : ℚ)=(D : ℚ)*a i := he (Sum.inl i)
  have hB (i : Fin k) : (B i : ℚ)=(D : ℚ)*b i := he (Sum.inr i)
  have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hAi : Function.Injective A := by
    intro i j hij
    apply hai
    have hh : (A i : ℚ)=(A j : ℚ) := congrArg Nat.cast hij
    rw [hA,hA] at hh
    exact mul_left_cancel₀ hDQ hh
  have hBi : Function.Injective B := by
    intro i j hij
    apply hbi
    have hh : (B i : ℚ)=(B j : ℚ) := congrArg Nat.cast hij
    rw [hB,hB] at hh
    exact mul_left_cancel₀ hDQ hh
  refine ⟨D,hD,A,B,hAi,hBi,?_,?_,
    scaled_nat_cube_sidon a A hD hA hsa,scaled_nat_cube_sidon b B hD hB hsb⟩
  · intro i
    refine ⟨ht (Sum.inl i),ht (Sum.inr i),?_⟩
    have hi : (a i)^3=(b i)^3+7 := by linarith [(hpos i).2.2]
    have hh : (A i : ℚ)^3=(B i : ℚ)^3+7*(D : ℚ)^3 := by
      rw [hA,hB,mul_pow,mul_pow,hi]
      ring
    exact_mod_cast hh
  · intro i j hij
    apply hdis i j
    have hh : (A i : ℚ)=(B j : ℚ) := congrArg Nat.cast hij
    rw [hA,hB] at hh
    exact mul_left_cancel₀ hDQ hh

/-- No bound linear in the two cardinalities can control all mixed collisions,
even when each piece separately has Sidon cubes. This is a cardinality result,
not a bound in terms of the largest root. -/
theorem mixed_collisions_not_cardinality_linear (C : ℕ) :
    ∃ S T : Finset ℕ, Disjoint S T ∧
      (∀ n ∈ S ∪ T, 0 < n) ∧
      IsSidon ((fun n : ℕ => n^3) '' (S : Set ℕ)) ∧
      IsSidon ((fun n : ℕ => n^3) '' (T : Set ℕ)) ∧
      ∃ E : Finset ((ℕ × ℕ) × (ℕ × ℕ)),
        C*(S.card+T.card) < E.card ∧
        ∀ e ∈ E, e.1.1 ∈ S ∧ e.1.2 ∈ T ∧ e.2.1 ∈ S ∧ e.2.2 ∈ T ∧
          e.1.1 ≠ e.2.1 ∧ e.1.2 ≠ e.2.2 ∧
          e.1.1^3+e.2.2^3=e.1.2^3+e.2.1^3 := by
  classical
  let k := 2*C+2
  obtain ⟨D,hD,a,b,hai,hbi,hpos,hdis,hsa,hsb⟩ := natural_sidon_pairs k
  let S := Finset.univ.image a
  let T := Finset.univ.image b
  have hS : (S : Set ℕ)=Set.range a := by simp [S]
  have hT : (T : Set ℕ)=Set.range b := by simp [T]
  have hcS : S.card=k := by simp [S,Finset.card_image_of_injective _ hai]
  have hcT : T.card=k := by simp [T,Finset.card_image_of_injective _ hbi]
  let F : Fin k × Fin k → (ℕ × ℕ) × (ℕ × ℕ) :=
    fun z => ((a z.1,b z.1),(a z.2,b z.2))
  have hFi : Function.Injective F := by
    intro x y h
    apply Prod.ext
    · apply hai
      exact congrArg (fun z : (ℕ × ℕ) × (ℕ × ℕ) => z.1.1) h
    · apply hai
      exact congrArg (fun z : (ℕ × ℕ) × (ℕ × ℕ) => z.2.1) h
  let E := (Finset.univ : Finset (Fin k)).offDiag.image F
  have hcE : E.card=k*k-k := by
    simp [E,Finset.card_image_of_injective _ hFi,Finset.offDiag_card]
  refine ⟨S,T,?_,?_,by rwa [hS],by rwa [hT],E,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro n hn hnT
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hn
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hnT
    exact hdis i j (hi.trans hj.symm)
  · intro n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hn
      exact (hpos i).1
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hn
      exact (hpos i).2.1
  · rw [hcS,hcT,hcE]
    have hk : k=2*C+2 := rfl
    have hkk : k ≤ k*k := by nlinarith
    have := Nat.sub_add_cancel hkk
    nlinarith
  · intro e he
    obtain ⟨⟨i,j⟩,hij,rfl⟩ := Finset.mem_image.mp he
    have hij' : i ≠ j := (Finset.mem_offDiag.mp hij).2.2
    refine ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,
      Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,
      Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,
      Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,
      fun h => hij' (hai h),fun h => hij' (hbi h),?_⟩
    dsimp [F]
    have hi := (hpos i).2.2
    have hj := (hpos j).2.2
    omega

#print axioms infinite_positive_cube_difference
#print axioms rational_sidon_pairs
#print axioms natural_sidon_pairs
#print axioms mixed_collisions_not_cardinality_linear

end Erdos1206.RepeatedCubeDifferences
