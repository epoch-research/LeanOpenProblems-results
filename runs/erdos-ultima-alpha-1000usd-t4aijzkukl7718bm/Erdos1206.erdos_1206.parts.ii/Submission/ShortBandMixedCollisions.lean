import Submission.BoundedCubeDifferences

/-! Mixed collision obstructions in narrow, separated bands.
No positive-density or prefix-height claim is made. -/

namespace Erdos1206.ShortBandMixedCollisions
open BoundedCubeDifferences
open scoped Classical
set_option maxHeartbeats 1000000

lemma mate_lt {b : ℚ} (hb : b∈roots) : b < mate b := by
  apply (Odd.pow_lt_pow (by decide : Odd 3)).mp
  linarith [(mate_spec hb).2]

lemma mate_le_add_two {b : ℚ} (hb : b∈roots) : mate b ≤ b+2 := by
  apply (Odd.pow_le_pow (by decide : Odd 3)).mp
  nlinarith [(mate_spec hb).2, sq_nonneg b, hb.1]

lemma mate_increment {b d : ℚ} (hb : b∈roots) (hd : d∈roots) (hbd : b≤d) :
    mate b ≤ mate d ∧ mate d-mate b ≤ d-b := by
  have hab := mate_lt hb
  have hcd := mate_lt hd
  have h₁ := (mate_spec hb).2
  have h₂ := (mate_spec hd).2
  constructor
  · apply (Odd.pow_le_pow (by decide : Odd 3)).mp
    have hpow := (Odd.pow_le_pow (by decide : Odd 3)).mpr hbd
    linarith
  · have hid : (mate b+d-b)^3-(mate d)^3 =
        3*(d-b)*(mate b-b)*(mate b+d) := by
      linear_combination h₁-h₂
    have hpos : 0≤3*(d-b)*(mate b-b)*(mate b+d) := by
      apply mul_nonneg
      · exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hbd))
          (sub_nonneg.mpr hab.le)
      · linarith [hb.1,hd.1]
    have hp : (mate d)^3≤(mate b+d-b)^3 := by linarith
    have hc := (Odd.pow_le_pow (by decide : Odd 3)).mp hp
    linarith

lemma mate_distance {b d : ℚ} (hb : b∈roots) (hd : d∈roots) :
    |mate b-mate d|≤|b-d| := by
  rcases le_total b d with h | h
  · obtain ⟨h₁,h₂⟩ := mate_increment hb hd h
    rw [abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)]
    linarith
  · obtain ⟨h₁,h₂⟩ := mate_increment hd hb h
    rw [abs_of_nonneg (by linarith),abs_of_nonneg (by linarith)]
    exact h₂

lemma bounded_gap {b : ℚ} (hb : b∈boundedRoots) :
    1/1000000000000 < mate b-b := by
  have hba := mate_lt hb.1
  have ha0 := (mate_spec hb.1).1
  have hb0 := hb.1.1
  have ha : mate b≤100002 := (mate_le_add_two hb.1).trans (by linarith [hb.2.2])
  have hq : (mate b)^2+mate b*b+b^2≤1000000000000 := by
    have h₁ : (mate b)^2≤100002^2 := pow_le_pow_left₀ ha0.le ha 2
    have h₂ : b^2≤100000^2 := pow_le_pow_left₀ hb0.le hb.2.2 2
    have h₃ : mate b*b≤100002*100000 := mul_le_mul ha hb.2.2 hb0.le (by norm_num)
    nlinarith
  have hid : (mate b-b)*((mate b)^2+mate b*b+b^2)=7 := by
    nlinarith only [(mate_spec hb.1).2]
  by_contra hn
  have hg : mate b-b≤1/1000000000000 := le_of_not_gt hn
  have hh : (7 : ℚ)≤1 := calc
    7 = (mate b-b)*((mate b)^2+mate b*b+b^2) := hid.symm
    _ ≤ (1/1000000000000)*((mate b)^2+mate b*b+b^2) :=
      mul_le_mul_of_nonneg_right hg (by positivity)
    _ ≤ (1/1000000000000)*1000000000000 :=
      mul_le_mul_of_nonneg_left hq (by norm_num)
    _ = 1 := by norm_num
  norm_num at hh

lemma infinite_small_diameter {δ : ℚ} (hδ : 0<δ) :
    ∃ V : Set ℚ, V.Infinite ∧ V⊆boundedRoots ∧
      ∀ b∈V, ∀ d∈V, |b-d|<δ := by
  let N : ℕ := ⌊100000/δ⌋₊
  let V : ℕ → Set ℚ := fun n => {b | b∈boundedRoots ∧ ⌊b/δ⌋₊=n}
  have hcover : boundedRoots ⊆ ⋃ n∈Set.Icc 0 N, V n := by
    intro b hb
    have hn : ⌊b/δ⌋₊≤N := Nat.floor_mono (div_le_div_of_nonneg_right hb.2.2 hδ.le)
    exact Set.mem_iUnion₂.mpr ⟨⌊b/δ⌋₊,⟨Nat.zero_le _,hn⟩,hb,rfl⟩
  have hex : ∃ n∈Set.Icc 0 N, (V n).Infinite := by
    by_contra h
    push_neg at h
    have hf := (Set.finite_Icc 0 N).biUnion (fun n hn => h n hn)
    exact bounded_roots_infinite (hf.subset hcover)
  obtain ⟨n,_,hn⟩ := hex
  refine ⟨V n,hn,fun _ h => h.1,?_⟩
  intro b hb d hd
  have hb0 : 0≤b/δ := div_nonneg hb.1.1.1.le hδ.le
  have hd0 : 0≤d/δ := div_nonneg hd.1.1.1.le hδ.le
  have hbL : (n : ℚ)*δ≤b := by
    have h := Nat.floor_le hb0
    rw [hb.2] at h
    exact (le_div_iff₀ hδ).mp h
  have hdL : (n : ℚ)*δ≤d := by
    have h := Nat.floor_le hd0
    rw [hd.2] at h
    exact (le_div_iff₀ hδ).mp h
  have hbU : b<((n : ℚ)+1)*δ := by
    have h := Nat.lt_floor_add_one (b/δ)
    rw [hb.2] at h
    exact (div_lt_iff₀ hδ).mp h
  have hdU : d<((n : ℚ)+1)*δ := by
    have h := Nat.lt_floor_add_one (d/δ)
    rw [hd.2] at h
    exact (div_lt_iff₀ hδ).mp h
  exact abs_lt.mpr ⟨by nlinarith,by nlinarith⟩

/-- An infinite family of paired roots can be confined to two disjoint
bands of arbitrarily small relative width. -/
theorem infinite_narrow_pairs (K : ℕ) :
    ∃ V : Set ℚ, V.Infinite ∧ V⊆boundedRoots ∧
      (∀ b∈V, ∀ d∈V, b < mate d) ∧
      ∀ b∈V, ∀ d∈V,
        (K : ℚ)*b≤(K+1)*d ∧ (K : ℚ)*mate b≤(K+1)*mate d := by
  let δ : ℚ := 1/(1000000000000000*((K : ℚ)+1))
  have hK : (0 : ℚ)≤K := Nat.cast_nonneg _
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδsmall : δ≤1/1000000000000000 := by
    dsimp [δ]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have hKδ : (K : ℚ)*δ≤1/1000000000000000 := by
    have hmul : δ*(1000000000000000*((K : ℚ)+1))=1 := by
      dsimp [δ]
      field_simp
    nlinarith
  obtain ⟨V,hV,hVR,hdiam⟩ := infinite_small_diameter hδ
  refine ⟨V,hV,hVR,?_,?_⟩
  · intro b hb d hd
    have hclose := (abs_lt.mp (hdiam b hb d hd)).2
    have hgap := bounded_gap (hVR hd)
    linarith
  · intro b hb d hd
    have hclose := (abs_lt.mp (hdiam b hb d hd)).2
    have hupper : mate b-mate d<δ :=
      (le_abs_self _).trans_lt ((mate_distance (hVR hb).1 (hVR hd).1).trans_lt (hdiam b hb d hd))
    have hlow := (hVR hd).2.1
    have hmate := mate_lt (hVR hd).1
    have h₁ := mul_le_mul_of_nonneg_left hclose.le hK
    have h₂ := mul_le_mul_of_nonneg_left hupper.le hK
    constructor <;> nlinarith


/-- Finite separately Sidon pieces retaining the narrow-band control. -/
theorem rational_narrow_sidon_pairs (K k : ℕ) :
    ∃ a b : Fin k → ℚ, Function.Injective a ∧ Function.Injective b ∧
      (∀ i, 0<a i ∧ 0<b i ∧ (a i)^3-(b i)^3=7) ∧
      (∀ i j, b i<a j) ∧
      (∀ i j, (K : ℚ)*a i≤(K+1)*a j ∧ (K : ℚ)*b i≤(K+1)*b j) ∧
      (∀ i j, a i≤100000000000*b j) ∧
      IsSidon ((fun x : ℚ => x^3) '' Set.range a) ∧
      IsSidon ((fun x : ℚ => x^3) '' Set.range b) := by
  obtain ⟨V,hV,hVB,hsep,hnarrow⟩ := infinite_narrow_pairs K
  have hVR : V⊆roots := fun _ h => (hVB h).1
  let W : Set ℚ := (fun x : ℚ => x^3) '' V
  have hpow : Function.Injective (fun x : ℚ => x^3) :=
    (Odd.strictMono_pow (by decide : Odd 3)).injective
  have hW : W.Infinite := hV.image hpow.injOn
  obtain ⟨U,hUW,hcard,hSid,_⟩ :=
    RepeatedCubeDifferences.finite_sidon_translate_disjoint W hW k
  let e : Fin k ≃ U := (Finset.equivFinOfCardEq hcard).symm
  let u : Fin k → ℚ := fun i => (e i).val
  have hu (i : Fin k) : u i∈U := (e i).property
  have hui : Function.Injective u := fun i j h => e.injective (Subtype.ext h)
  have hex (i : Fin k) : ∃ b∈V, b^3=u i := hUW (hu i)
  choose b hb hbe using hex
  let a : Fin k → ℚ := fun i => mate (b i)
  have he (i : Fin k) : (a i)^3-(b i)^3=7 := (mate_spec (hVR (hb i))).2
  have hae (i : Fin k) : (a i)^3=u i+7 := by linarith [he i,hbe i]
  have hai : Function.Injective a := by
    intro i j hij
    apply hui
    have h := congrArg (fun x : ℚ => x^3) hij
    simpa only [hae,add_left_inj] using h
  have hbi : Function.Injective b := by
    intro i j hij
    apply hui
    have h := congrArg (fun x : ℚ => x^3) hij
    simpa only [hbe] using h
  refine ⟨a,b,hai,hbi,fun i => ⟨(mate_spec (hVR (hb i))).1,(hVR (hb i)).1,he i⟩,
    fun i j => hsep _ (hb i) _ (hb j),?_,?_,?_,?_⟩
  · intro i j
    exact (hnarrow _ (hb i) _ (hb j)).symm
  · intro i j
    have h₁ := mate_le_add_two (hVR (hb i))
    have h₂ := (hVB (hb i)).2.2
    have h₃ := (hVB (hb j)).2.1
    dsimp only [a]
    nlinarith
  · rintro _ ⟨_,⟨i,rfl⟩,rfl⟩ _ ⟨_,⟨j,rfl⟩,rfl⟩
      _ ⟨_,⟨l,rfl⟩,rfl⟩ _ ⟨_,⟨m,rfl⟩,rfl⟩ heq
    have h : u i+u l=u j+u m := by simp only [hae] at heq; linarith
    rcases hSid _ (hu i) _ (hu j) _ (hu l) _ (hu m) h with h | h
    · left; simp only [hae]; exact ⟨by rw [h.1],by rw [h.2]⟩
    · right; simp only [hae]; exact ⟨by rw [h.1],by rw [h.2]⟩
  · rintro _ ⟨_,⟨i,rfl⟩,rfl⟩ _ ⟨_,⟨j,rfl⟩,rfl⟩
      _ ⟨_,⟨l,rfl⟩,rfl⟩ _ ⟨_,⟨m,rfl⟩,rfl⟩ heq
    simp only [hbe] at heq ⊢
    exact hSid _ (hu i) _ (hu j) _ (hu l) _ (hu m) heq

/-- Clearing denominators preserves the narrow-band condition. There is
no bound on the common denominator in terms of the number of points. -/
theorem natural_narrow_sidon_pairs (K k : ℕ) :
    ∃ D : ℕ, 0<D ∧ ∃ a b : Fin k → ℕ,
      Function.Injective a ∧ Function.Injective b ∧
      (∀ i, 0<a i ∧ 0<b i ∧ (a i)^3=(b i)^3+7*D^3) ∧
      (∀ i j, b i<a j) ∧
      (∀ i j, K*a i≤(K+1)*a j ∧ K*b i≤(K+1)*b j) ∧
      (∀ i j, a i≤100000000000*b j) ∧
      IsSidon ((fun x : ℕ => x^3) '' Set.range a) ∧
      IsSidon ((fun x : ℕ => x^3) '' Set.range b) := by
  obtain ⟨a,b,hai,hbi,hpos,hsep,hnarrow,hcoarse,hsa,hsb⟩ := rational_narrow_sidon_pairs K k
  let f : Fin k ⊕ Fin k → ℚ := Sum.elim a b
  have hf : ∀ i, 0<f i := by
    intro i
    cases i with
    | inl i => exact (hpos i).1
    | inr i => exact (hpos i).2.1
  obtain ⟨D,hD,t,ht,he⟩ := RepeatedCubeDifferences.common_positive_denominator f hf
  let A : Fin k → ℕ := fun i => t (Sum.inl i)
  let B : Fin k → ℕ := fun i => t (Sum.inr i)
  have hA (i : Fin k) : (A i : ℚ)=(D : ℚ)*a i := he (Sum.inl i)
  have hB (i : Fin k) : (B i : ℚ)=(D : ℚ)*b i := he (Sum.inr i)
  have hDQ : (0 : ℚ)<D := by exact_mod_cast hD
  have hAi : Function.Injective A := by
    intro i j hij
    apply hai
    have hh : (A i : ℚ)=(A j : ℚ) := congrArg Nat.cast hij
    rw [hA,hA] at hh
    exact mul_left_cancel₀ hDQ.ne' hh
  have hBi : Function.Injective B := by
    intro i j hij
    apply hbi
    have hh : (B i : ℚ)=(B j : ℚ) := congrArg Nat.cast hij
    rw [hB,hB] at hh
    exact mul_left_cancel₀ hDQ.ne' hh
  refine ⟨D,hD,A,B,hAi,hBi,?_,?_,?_,?_,
    RepeatedCubeDifferences.scaled_nat_cube_sidon a A hD hA hsa,
    RepeatedCubeDifferences.scaled_nat_cube_sidon b B hD hB hsb⟩
  · intro i
    refine ⟨ht (Sum.inl i),ht (Sum.inr i),?_⟩
    have hi : (a i)^3=(b i)^3+7 := by linarith [(hpos i).2.2]
    have hh : (A i : ℚ)^3=(B i : ℚ)^3+7*(D : ℚ)^3 := by
      rw [hA,hB,mul_pow,mul_pow,hi]
      ring
    exact_mod_cast hh
  · intro i j
    have hh : (B i : ℚ)<A j := by
      rw [hB,hA]
      exact mul_lt_mul_of_pos_left (hsep i j) hDQ
    exact_mod_cast hh
  · intro i j
    have h₁ := mul_le_mul_of_nonneg_left (hnarrow i j).1 hDQ.le
    have h₂ := mul_le_mul_of_nonneg_left (hnarrow i j).2 hDQ.le
    have h₁' : (K : ℚ)*(A i : ℚ)≤((K : ℚ)+1)*(A j : ℚ) := by
      rw [hA,hA]
      nlinarith only [h₁]
    have h₂' : (K : ℚ)*(B i : ℚ)≤((K : ℚ)+1)*(B j : ℚ) := by
      rw [hB,hB]
      nlinarith only [h₂]
    exact ⟨by exact_mod_cast h₁',by exact_mod_cast h₂'⟩
  · intro i j
    have h := mul_le_mul_of_nonneg_left (hcoarse i j) hDQ.le
    have hh : (A i : ℚ)≤100000000000*(B j : ℚ) := by
      rw [hA,hB]
      nlinarith only [h]
    exact_mod_cast hh

/-- Narrow and separated bands, even with a uniform bound on their ratio,
do not give a mixed-collision bound linear in the two cardinalities.
This does not rule out a bound linear in the largest root. -/
theorem narrow_mixed_collisions_not_cardinality_linear (K C : ℕ) :
    ∃ S T : Finset ℕ, Disjoint S T ∧
      (∀ n ∈ S ∪ T, 0 < n) ∧
      (∀ t∈T, ∀ s∈S, t<s ∧ s≤100000000000*t) ∧
      (∀ x∈S, ∀ y∈S, K*x≤(K+1)*y) ∧
      (∀ x∈T, ∀ y∈T, K*x≤(K+1)*y) ∧
      IsSidon ((fun n : ℕ => n^3) '' (S : Set ℕ)) ∧
      IsSidon ((fun n : ℕ => n^3) '' (T : Set ℕ)) ∧
      ∃ E : Finset ((ℕ × ℕ) × (ℕ × ℕ)),
        C*(S.card+T.card) < E.card ∧
        ∀ e ∈ E, e.1.1 ∈ S ∧ e.1.2 ∈ T ∧ e.2.1 ∈ S ∧ e.2.2 ∈ T ∧
          e.1.1 ≠ e.2.1 ∧ e.1.2 ≠ e.2.2 ∧
          e.1.1^3+e.2.2^3=e.1.2^3+e.2.1^3 := by
  classical
  let k := 2*C+2
  obtain ⟨D,hD,a,b,hai,hbi,hpos,hsep,hnarrow,hcoarse,hsa,hsb⟩ := natural_narrow_sidon_pairs K k
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
  refine ⟨S,T,?_,?_,?_,?_,?_,by rwa [hS],by rwa [hT],E,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro n hn hnT
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hn
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hnT
    have hh := hsep j i
    rw [hi,hj] at hh
    exact (lt_irrefl _ hh)
  · intro n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hn
      exact (hpos i).1
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hn
      exact (hpos i).2.1
  · intro t ht s hs
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs
    exact ⟨hsep i j,hcoarse j i⟩
  · intro x hx y hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
    exact (hnarrow i j).1
  · intro x hx y hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
    exact (hnarrow i j).2
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


#print axioms infinite_narrow_pairs
#print axioms rational_narrow_sidon_pairs
#print axioms natural_narrow_sidon_pairs
#print axioms narrow_mixed_collisions_not_cardinality_linear

end Erdos1206.ShortBandMixedCollisions
