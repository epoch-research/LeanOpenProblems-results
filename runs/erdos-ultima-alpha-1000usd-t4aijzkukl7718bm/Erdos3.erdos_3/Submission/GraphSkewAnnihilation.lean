import Submission.SmallDoublingAnnihilation

/-! Applying small-doubling sampling to a difference-compatible frequency
graph controls all biased skew phases simultaneously. -/
namespace Erdos3GraphSkewAnnihilation
open Finset Erdos3FrequencyGraph Erdos3FiniteFourier Erdos3TwistedCorrelationEnergy
  Erdos3AntidiagonalTwistedEnergy Erdos3AveragedAntisymmetry
  Erdos3SmallDoublingAnnihilation
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def graphSkewCharacter (F : G → AddChar G ℂ) (d : G) :
    AddChar (G × AddChar G ℂ) ℂ where
  toFun p := p.2 d*conj (F d p.1)
  map_zero_eq_one' := by simp
  map_add_eq_mul' p q := by
    simp only [Prod.fst_add,Prod.snd_add,AddChar.add_apply,AddChar.map_add_eq_mul,map_mul]
    ring

lemma graphSkewCharacter_apply (F : G → AddChar G ℂ) (d x : G) :
    graphSkewCharacter F d (x,F x) = skewPhase F x d := rfl

lemma graphSkewCharacter_difference (T : Finset G) (F : G → AddChar G ℂ)
    (hF : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t)
    {s t : G} (hs : s ∈ T) (ht : t ∈ T) (d : G) :
    graphSkewCharacter F d ((s,F s)-(t,F t)) = skewPhase F (s-t) d := by
  change (F s-F t) d*conj (F d (s-t)) = F (s-t) d*conj (F d (s-t))
  rw [hF s hs t ht]

noncomputable def graphEquiv (T : Finset G) (F : G → AddChar G ℂ) :
    T ≃ frequencyGraph T F where
  toFun x := ⟨(x,F x),(mem_frequencyGraph T F _).mpr ⟨x.property,rfl⟩⟩
  invFun p := ⟨p.val.1,((mem_frequencyGraph T F _).mp p.property).1⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact ((mem_frequencyGraph T F _).mp p.property).2.symm

lemma graphSkewCharacter_mean (T : Finset G) (F : G → AddChar G ℂ) (d : G) :
    meanChar (frequencyGraph T F) (graphSkewCharacter F d) =
      𝔼 x : T, skewPhase F x d :=
  (Fintype.expect_equiv (graphEquiv T F) _ _ (fun _ ↦ rfl)).symm

lemma compatible_freiman (T : Finset G) (F : G → AddChar G ℂ)
    (hF : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t)
    {a b c d : G} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hd : d ∈ T)
    (he : a+b = c+d) : F a+F b = F c+F d := by
  have hdif : a-c = d-b := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using he
  have hh : F a-F c = F d-F b := by rw [← hF a ha c hc,hdif,hF d hd b hb]
  have := sub_eq_sub_iff_add_eq_add.mp hh
  simpa only [add_comm] using this

lemma graph_add_card_le (T : Finset G) (F : G → AddChar G ℂ)
    (hF : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t) :
    (frequencyGraph T F+frequencyGraph T F).card ≤ Fintype.card G := by
  have hinj : Set.InjOn Prod.fst (↑(frequencyGraph T F+frequencyGraph T F) : Set (G × AddChar G ℂ)) := by
    intro p hp q hq he
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hp
    obtain ⟨c,hc,d,hd,rfl⟩ := mem_add.mp hq
    obtain ⟨ha,haF⟩ := (mem_frequencyGraph T F a).mp ha
    obtain ⟨hb,hbF⟩ := (mem_frequencyGraph T F b).mp hb
    obtain ⟨hc,hcF⟩ := (mem_frequencyGraph T F c).mp hc
    obtain ⟨hd,hdF⟩ := (mem_frequencyGraph T F d).mp hd
    apply Prod.ext he
    change a.2+b.2 = c.2+d.2
    rw [haF,hbF,hcF,hdF]
    exact compatible_freiman T F hF ha hb hc hd he
  simpa only [card_univ] using
    card_le_card_of_injOn Prod.fst (fun _ _ ↦ mem_univ _) hinj

lemma graph_sub_card_le (T : Finset G) (F : G → AddChar G ℂ)
    (hF : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t) :
    (frequencyGraph T F-frequencyGraph T F).card ≤ Fintype.card G := by
  have hinj : Set.InjOn Prod.fst (↑(frequencyGraph T F-frequencyGraph T F) : Set (G × AddChar G ℂ)) := by
    intro p hp q hq he
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_sub.mp hp
    obtain ⟨c,hc,d,hd,rfl⟩ := mem_sub.mp hq
    obtain ⟨ha,haF⟩ := (mem_frequencyGraph T F a).mp ha
    obtain ⟨hb,hbF⟩ := (mem_frequencyGraph T F b).mp hb
    obtain ⟨hc,hcF⟩ := (mem_frequencyGraph T F c).mp hc
    obtain ⟨hd,hdF⟩ := (mem_frequencyGraph T F d).mp hd
    apply Prod.ext he
    change a.2-b.2 = c.2-d.2
    rw [haF,hbF,hcF,hdF,← hF a.1 ha b.1 hb,← hF c.1 hc d.1 hd]
    exact congrArg F he
  simpa only [card_univ] using
    card_le_card_of_injOn Prod.fst (fun _ _ ↦ mem_univ _) hinj

lemma localSkewBias_eq_mean (T : Finset G) (hT : T.Nonempty)
    (F : G → AddChar G ℂ) (d : G) :
    localSkewBias T F d = (((T.card : ℝ)/(Fintype.card G : ℝ) : ℝ) : ℂ)*
      (𝔼 x : T, skewPhase F x d) := by
  have hT0 : (T.card : ℂ) ≠ 0 := by exact_mod_cast hT.card_pos.ne'
  simp only [localSkewBias,Fintype.expect_eq_sum_div_card,Fintype.card_coe,
    Complex.ofReal_div,Complex.ofReal_natCast]
  rw [sum_coe_sort T (fun x ↦ skewPhase F x d)]
  simp only [sum_ite_mem,univ_inter]
  field_simp

/-- Sampling the graph controls all its biased skew characters simultaneously.
The size loss is measured against |G|, not |G x dual(G)|. -/
theorem exists_skew_almost_annihilators (T : Finset G) (hT : T.Nonempty)
    (F : G → AddChar G ℂ) (hF : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t)
    {n : ℕ} (hn : 0 < n) :
    ∃ X : Finset G, X.Nonempty ∧ X ⊆ T ∧
      T.card^n*T.card ≤ 2*(Fintype.card G)^n*X.card ∧
      ∀ s ∈ X, ∀ t ∈ X, ∀ d : G,
        (n : ℝ)*(T.card : ℝ)*‖skewPhase F (s-t) d-1‖^2*
          ‖𝔼 x : T, skewPhase F x d‖^4 ≤ 16*(Fintype.card G : ℝ) := by
  let A := frequencyGraph T F
  have hA : A.Nonempty := by
    obtain ⟨x,hx⟩ := hT
    exact ⟨(x,F x),(mem_frequencyGraph T F _).mpr ⟨hx,rfl⟩⟩
  obtain ⟨Y,hY,hsub,hsize,hper⟩ := exists_spectrum_almost_annihilators A hA hn
  let X := Y.image Prod.fst
  have hinj : Set.InjOn Prod.fst (Y : Set (G × AddChar G ℂ)) := by
    intro a ha b hb he
    apply Prod.ext he
    have haF := ((mem_frequencyGraph T F a).mp (hsub ha)).2
    have hbF := ((mem_frequencyGraph T F b).mp (hsub hb)).2
    rw [haF,hbF,he]
  have hXcard : X.card = Y.card := card_image_of_injOn hinj
  have hXT : X ⊆ T := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
    exact ((mem_frequencyGraph T F p).mp (hsub hp)).1
  have hmem {x : G} (hx : x ∈ X) : (x,F x) ∈ Y := by
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
    have he : (p.1,F p.1) = p := Prod.ext rfl ((mem_frequencyGraph T F p).mp (hsub hp)).2.symm
    rwa [he]
  refine ⟨X,image_nonempty.mpr hY,hXT,?_,?_⟩
  · rw [card_frequencyGraph] at hsize
    rw [hXcard]
    exact hsize.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2
      (Nat.pow_le_pow_left (graph_add_card_le T F hF) n)))
  · intro s hs t ht d
    have hp := hper (s,F s) (hmem hs) (t,F t) (hmem ht) (graphSkewCharacter F d)
    rw [graphSkewCharacter_difference T F hF (hXT hs) (hXT ht),graphSkewCharacter_mean,
      card_frequencyGraph] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast graph_sub_card_le T F hF) (by norm_num))

/-- Parameterized simultaneous annihilation of every skew phase with
normalized bias at least eta. -/
theorem exists_biased_skew_annihilators (T : Finset G) (hT : T.Nonempty)
    (F : G → AddChar G ℂ) (hF : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t)
    {n : ℕ} (hn : 0 < n) {η ε : ℝ} (hη : 0 < η) (hε : 0 ≤ ε)
    (hcost : 16*(Fintype.card G : ℝ) ≤ (n : ℝ)*(T.card : ℝ)*η^4*ε^2) :
    ∃ X : Finset G, X.Nonempty ∧ X ⊆ T ∧
      T.card^n*T.card ≤ 2*(Fintype.card G)^n*X.card ∧
      ∀ s ∈ X, ∀ t ∈ X, ∀ d : G,
        η ≤ ‖𝔼 x : T, skewPhase F x d‖ → ‖skewPhase F (s-t) d-1‖ ≤ ε := by
  obtain ⟨X,hX,hsub,hsize,hper⟩ := exists_skew_almost_annihilators T hT F hF hn
  refine ⟨X,hX,hsub,hsize,?_⟩
  intro s hs t ht d hd
  have hp := hper s hs t ht d
  have hη4 := pow_le_pow_left₀ hη.le hd 4
  have hl : (n : ℝ)*(T.card : ℝ)*η^4*‖skewPhase F (s-t) d-1‖^2 ≤
      (n : ℝ)*(T.card : ℝ)*‖skewPhase F (s-t) d-1‖^2*‖𝔼 x : T, skewPhase F x d‖^4 := by
    calc
      _ = (n : ℝ)*(T.card : ℝ)*‖skewPhase F (s-t) d-1‖^2*η^4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hη4 (by positivity)
  have hc : 0 < (n : ℝ)*(T.card : ℝ)*η^4 := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hTR : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
    positivity
  exact (sq_le_sq₀ (norm_nonneg _) hε).mp
    ((mul_le_mul_iff_right₀ hc).mp (hl.trans (hp.trans hcost)))

#print axioms exists_skew_almost_annihilators
#print axioms exists_biased_skew_annihilators
end Erdos3GraphSkewAnnihilation
