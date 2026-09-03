import FormalConjecturesUtil

/-! A uniform finite pigeonhole lemma for short real-score bands. -/
namespace Erdos1206.FiniteShortBandSelection
open Finset
open scoped Classical

lemma finite_cover {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r) :
    ∃ C : Finset ℝ,C.Nonempty ∧ ∀ x : ℝ,|x| ≤ R → ∃ c ∈ C,|x-c| < r := by
  obtain ⟨T,hT,hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_Icc : IsCompact (Set.Icc (-R) R)).totallyBounded r hr
  have hc (x : ℝ) (hx : |x| ≤ R) : ∃ c ∈ T,|x-c| < r := by
    have hh := hcover (abs_le.mp hx)
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hh
    obtain ⟨hc,hh⟩ := Set.mem_iUnion.mp hc
    exact ⟨c,hc,by simpa only [Metric.mem_ball,Real.dist_eq] using hh⟩
  refine ⟨hT.toFinset,?_,fun x hx => ?_⟩
  · obtain ⟨c,hc,_⟩ := hc 0 (by simpa using hR)
    exact ⟨c,hT.mem_toFinset.mpr hc⟩
  · obtain ⟨c,hc,hxc⟩ := hc x hx
    exact ⟨c,hT.mem_toFinset.mpr hc,hxc⟩

lemma many_bounded {α : Type*} (S : Finset α) (f : α → ℝ) {E R : ℝ}
    (hE : 0 ≤ E) (hR : 0 < R) (hRE : 2*E < R^2)
    (hm : (∑n∈S,f n^2) ≤ E*S.card) :
    (S.card:ℝ)/2 ≤ ((S.filter (fun n => |f n| ≤ R)).card:ℝ) := by
  let B := S.filter (fun n => ¬ |f n| ≤ R)
  have hB : (B.card:ℝ)*R^2 ≤ E*S.card := by
    calc
      _ = ∑_n∈B,R^2 := by simp
      _ ≤ ∑n∈B,f n^2 := by
        apply sum_le_sum
        intro n hn
        have hh : R < |f n| := lt_of_not_ge (mem_filter.mp hn).2
        simpa only [sq_abs] using (sq_le_sq₀ hR.le (abs_nonneg _)).mpr hh.le
      _ ≤ ∑n∈S,f n^2 := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := hm
  have hcard : (((S.filter (fun n => |f n| ≤ R)).card:ℝ)+(B.card:ℝ))=S.card := by
    exact_mod_cast card_filter_add_card_filter_not (s := S) (fun n => |f n| ≤ R)
  have hb0 : (0:ℝ) ≤ B.card := by positivity
  have hs0 : (0:ℝ) ≤ S.card := by positivity
  have hs : (B.card:ℝ) ≤ (S.card:ℝ)/2 := by
    by_contra! hh
    have hbpos : (0:ℝ) < B.card := by linarith
    nlinarith
  linarith

/-- The positive proportion depends only on the radius and moment bound,
not on the finite sample or the particular score. -/
theorem exists_uniform_band {E r : ℝ} (hE : 0 ≤ E) (hr : 0 < r) :
    ∃ δ : ℝ,0 < δ ∧ δ ≤ 1 ∧ ∃ C : Finset ℝ,∀ {α : Type*} (S : Finset α),
      S.Nonempty → ∀ f : α → ℝ,(∑n∈S,f n^2) ≤ E*S.card →
        ∃ c ∈ C,δ*S.card ≤ ((S.filter (fun n => |f n-c| < r)).card:ℝ) := by
  let R := Real.sqrt (2*E+1)
  have hR : 0 < R := Real.sqrt_pos.mpr (by positivity)
  have hR2 : R^2=2*E+1 := Real.sq_sqrt (by positivity)
  obtain ⟨C,hC,hcover⟩ := finite_cover hR.le hr
  let δ : ℝ := 1/(2*C.card)
  have hCc : (0:ℝ) < C.card := by exact_mod_cast card_pos.mpr hC
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℝ) < 2*C.card)).mpr
    have hh : (1:ℝ) ≤ C.card := by exact_mod_cast card_pos.mpr hC
    linarith
  refine ⟨δ,hδ,hδ1,C,fun {α} S _hS f hm => ?_⟩
  let G := S.filter (fun n => |f n| ≤ R)
  let B (c : ℝ) := S.filter (fun n => |f n-c| < r)
  have hG := many_bounded S f hE hR (by linarith) hm
  have hsub : G ⊆ C.biUnion B := by
    intro n hn
    obtain ⟨hnS,hbound⟩ := mem_filter.mp hn
    obtain ⟨c,hc,hfc⟩ := hcover (f n) hbound
    exact mem_biUnion.mpr ⟨c,hc,mem_filter.mpr ⟨hnS,hfc⟩⟩
  have hsum : (G.card:ℝ) ≤ ∑c∈C,((B c).card:ℝ) := by
    exact_mod_cast (card_le_card hsub).trans (card_biUnion_le)
  by_contra! hbad
  have hh : (∑c∈C,((B c).card:ℝ)) < ∑_c∈C,δ*S.card := by
    apply sum_lt_sum (fun c hc => (hbad c hc).le)
    obtain ⟨c,hc⟩ := hC
    exact ⟨c,hc,hbad c hc⟩
  have he : (∑_c∈C,δ*S.card)=(S.card:ℝ)/2 := by
    simp only [sum_const,nsmul_eq_mul,δ]
    field_simp
  rw [he] at hh
  exact (not_lt_of_ge hG) (hsum.trans_lt hh)

#print axioms exists_uniform_band
end Erdos1206.FiniteShortBandSelection
