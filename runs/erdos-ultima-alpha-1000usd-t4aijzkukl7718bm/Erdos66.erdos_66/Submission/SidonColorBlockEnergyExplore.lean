import FormalConjecturesUtil

/-! A short-difference budget for Sidon-colored integer sets. This supplies
necessary conditions on a possible component construction, not a witness or
a disproof of Erdős 66. -/
namespace Erdos66SidonColorBlockEnergy
open scoped Classical
set_option maxHeartbeats 1200000

/-- Within each color, nonzero positive differences identify their ordered
endpoints uniquely. -/
def DistinctColorDifferences {I : Type*} (S : Finset ℕ) (col : ℕ → I) : Prop :=
  ∀ a∈S, ∀ b∈S, ∀ c∈S, ∀ d∈S, a<b → c<d →
    col a=col b → col c=col d → col a=col c → b-a=d-c → a=c ∧ b=d

/-- The usual unordered-sum Sidon condition in each color implies the
positive-difference formulation used below. -/
lemma distinctColorDifferences_of_unique_sums {I : Type*}
    (S : Finset ℕ) (col : ℕ → I)
    (hsum : ∀ a∈S, ∀ b∈S, ∀ c∈S, ∀ d∈S,
      col a=col b → col c=col d → col a=col c → a+b=c+d →
        (a=c ∧ b=d) ∨ (a=d ∧ b=c)) : DistinctColorDifferences S col := by
  intro a ha b hb c hc d hd hab hcd habc hcdc hacc hdiff
  have he : a+d=b+c := by omega
  have hadc : col a=col d := hacc.trans hcdc
  have hbcc : col b=col c := habc.symm.trans hacc
  rcases hsum a ha d hd b hb c hc hadc hbcc habc he with hh | hh
  · omega
  · exact ⟨hh.1,hh.2.symm⟩

noncomputable def sameCellPairs {I : Type*} (S : Finset ℕ) (col : ℕ → I) (u : ℕ) : Finset (ℕ × ℕ) :=
  (S ×ˢ S).filter (fun ab ↦ col ab.1=col ab.2 ∧ ab.1/u=ab.2/u)

lemma mem_sameCellPairs {I : Type*} {S : Finset ℕ} {col : ℕ → I} {u : ℕ} {ab : ℕ × ℕ} :
    ab∈sameCellPairs S col u ↔ ab.1∈S ∧ ab.2∈S ∧ col ab.1=col ab.2 ∧ ab.1/u=ab.2/u := by
  simp only [sameCellPairs,Finset.mem_filter,Finset.mem_product]
  tauto

lemma same_bin_difference_lt {a b u : ℕ} (hu : 0<u) (hab : a<b) (hbin : a/u=b/u) : b-a<u := by
  have ha := Nat.mod_add_div a u
  have hb := Nat.mod_add_div b u
  have har := Nat.mod_lt a hu
  have hbr := Nat.mod_lt b hu
  rw [hbin] at ha
  omega

lemma forward_pairs_bound {I : Type*} [Fintype I]
    (S : Finset ℕ) (col : ℕ → I) (hcol : DistinctColorDifferences S col)
    (u : ℕ) (hu : 0<u) :
    ((sameCellPairs S col u).filter (fun ab ↦ ab.1<ab.2)).card ≤ Fintype.card I*u := by
  let P := (sameCellPairs S col u).filter (fun ab ↦ ab.1<ab.2)
  let e : ℕ × ℕ → I × ℕ := fun ab ↦ (col ab.1,ab.2-ab.1)
  have hinj : Set.InjOn e (P : Set (ℕ × ℕ)) := by
    intro ab hab cd hcd he
    obtain ⟨hab,hablt⟩ := Finset.mem_filter.mp hab
    obtain ⟨hcd,hcdlt⟩ := Finset.mem_filter.mp hcd
    obtain ⟨ha,hb,habcol,habbin⟩ := mem_sameCellPairs.mp hab
    obtain ⟨hc,hd,hcdcol,hcdbin⟩ := mem_sameCellPairs.mp hcd
    obtain ⟨he1,he2⟩ := hcol ab.1 ha ab.2 hb cd.1 hc cd.2 hd hablt hcdlt
      habcol hcdcol (congrArg Prod.fst he) (congrArg Prod.snd he)
    exact Prod.ext he1 he2
  have hsub : P.image e ⊆ (Finset.univ : Finset I) ×ˢ Finset.range u := by
    intro z hz
    obtain ⟨ab,hab,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hab,hablt⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha,hb,hcol,hbin⟩ := mem_sameCellPairs.mp hab
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_range.mpr
      (same_bin_difference_lt hu hablt hbin)⟩
  calc
    _ = (P.image e).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((Finset.univ : Finset I) ×ˢ Finset.range u).card := Finset.card_le_card hsub
    _ = _ := by simp

lemma sameCellPairs_card {I : Type*} (S : Finset ℕ) (col : ℕ → I) (u : ℕ) :
    (sameCellPairs S col u).card = S.card+
      2*((sameCellPairs S col u).filter (fun ab ↦ ab.1<ab.2)).card := by
  let P := sameCellPairs S col u
  let L := P.filter (fun ab ↦ ab.1<ab.2)
  let R := P.filter (fun ab ↦ ab.2<ab.1)
  let D := P.filter (fun ab ↦ ab.1=ab.2)
  have hswap : L.image Prod.swap=R := by
    ext ab
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨cd,hcd,rfl⟩
      obtain ⟨hcd,hlt⟩ := Finset.mem_filter.mp hcd
      obtain ⟨hc,hd,hcol,hbin⟩ := mem_sameCellPairs.mp hcd
      exact Finset.mem_filter.mpr ⟨mem_sameCellPairs.mpr ⟨hd,hc,hcol.symm,hbin.symm⟩,hlt⟩
    · intro hab
      obtain ⟨hab,hlt⟩ := Finset.mem_filter.mp hab
      obtain ⟨ha,hb,hcol,hbin⟩ := mem_sameCellPairs.mp hab
      exact ⟨ab.swap,Finset.mem_filter.mpr ⟨mem_sameCellPairs.mpr ⟨hb,ha,hcol.symm,hbin.symm⟩,hlt⟩,rfl⟩
  have hR : R.card=L.card := by rw [← hswap,Finset.card_image_of_injective _ Prod.swap_injective]
  have hdiag : S.image (fun a ↦ (a,a))=D := by
    ext ab
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact Finset.mem_filter.mpr ⟨mem_sameCellPairs.mpr ⟨ha,ha,rfl,rfl⟩,rfl⟩
    · intro hab
      obtain ⟨hab,he⟩ := Finset.mem_filter.mp hab
      exact ⟨ab.1,(mem_sameCellPairs.mp hab).1,Prod.ext rfl he⟩
  have hD : D.card=S.card := by
    rw [← hdiag,Finset.card_image_of_injective _ (fun a b he ↦ congrArg Prod.fst he)]
  have hnot : P.filter (fun ab ↦ ¬ab.1<ab.2)=D ∪ R := by
    ext ab
    simp only [D,R,Finset.mem_filter,Finset.mem_union]
    constructor
    · rintro ⟨hp,hlt⟩
      by_cases he : ab.1=ab.2
      · exact Or.inl ⟨hp,he⟩
      · exact Or.inr ⟨hp,by omega⟩
    · rintro (⟨hp,he⟩ | ⟨hp,hlt⟩) <;> exact ⟨hp,by omega⟩
  have hdis : Disjoint D R := by
    apply Finset.disjoint_left.mpr
    intro ab hd hr
    have he := (Finset.mem_filter.mp hd).2
    have hlt := (Finset.mem_filter.mp hr).2
    omega
  have hh := Finset.card_filter_add_card_filter_not (s := P) (p := fun ab ↦ ab.1<ab.2)
  rw [hnot,Finset.card_union_of_disjoint hdis,hD,hR] at hh
  change P.card=S.card+2*L.card
  change L.card+(S.card+L.card)=P.card at hh
  omega

lemma sameCellPairs_bound {I : Type*} [Fintype I]
    (S : Finset ℕ) (col : ℕ → I) (hcol : DistinctColorDifferences S col)
    (u : ℕ) (hu : 0<u) :
    (sameCellPairs S col u).card ≤ S.card+2*Fintype.card I*u := by
  rw [sameCellPairs_card]
  have hh := forward_pairs_bound S col hcol u hu
  nlinarith

lemma partial_fiber_square_sum {X J : Type*} [DecidableEq X] [DecidableEq J]
    (S : Finset X) (f : X → J) (T : Finset J) :
    ∑ j∈T, ((S.filter (fun x ↦ f x=j)).card)^2 ≤
      ((S ×ˢ S).filter (fun xy ↦ f xy.1=f xy.2)).card := by
  let P := (S ×ˢ S).filter (fun xy ↦ f xy.1=f xy.2)
  have hf (j : J) : (P.filter (fun xy ↦ f xy.1=j))=
      (S.filter (fun x ↦ f x=j)) ×ˢ (S.filter (fun x ↦ f x=j)) := by
    ext xy
    simp only [P,Finset.mem_filter,Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨ha,hb⟩,he⟩,hj⟩
      exact ⟨⟨ha,hj⟩,hb,he.symm.trans hj⟩
    · rintro ⟨⟨ha,haj⟩,⟨hb,hbj⟩⟩
      exact ⟨⟨⟨ha,hb⟩,haj.trans hbj.symm⟩,haj⟩
  have hs := Finset.sum_card_fiberwise_eq_card_filter P T (fun xy ↦ f xy.1)
  simp only [hf,Finset.card_product,← pow_two] at hs
  rw [hs]
  exact Finset.card_le_card (Finset.filter_subset _ _)

noncomputable def binMass (S : Finset ℕ) (u b : ℕ) : ℕ := (S.filter (fun a ↦ a/u=b)).card

lemma bin_color_cauchy {I : Type*} [Fintype I]
    (S : Finset ℕ) (col : ℕ → I) (u b : ℕ) :
    (binMass S u b : ℝ)^2 ≤ (Fintype.card I : ℝ)*
      ∑ i : I, (((S.filter (fun a ↦ col a=i ∧ a/u=b)).card : ℝ)^2) := by
  have hf (i : I) : ((S.filter (fun a ↦ a/u=b)).filter (fun a ↦ col a=i))=
      S.filter (fun a ↦ col a=i ∧ a/u=b) := by ext a; simp only [Finset.mem_filter]; tauto
  have hs := Finset.card_eq_sum_card_fiberwise (s := S.filter (fun a ↦ a/u=b))
    (t := (Finset.univ : Finset I)) (f := col) (fun a ha ↦ Finset.mem_univ _)
  simp only [hf] at hs
  have hsR : (binMass S u b : ℝ)=∑ i : I, ((S.filter (fun a ↦ col a=i ∧ a/u=b)).card : ℝ) := by
    exact_mod_cast hs
  rw [hsR]
  exact sq_sum_le_card_mul_sum_sq

/-- Across ANY selected integer blocks of common width u, the squared
occupancies of a set colored into m distinct-difference classes have total
at most m|S|+2m²u. -/
theorem block_energy_bound {I : Type*} [Fintype I]
    (S : Finset ℕ) (col : ℕ → I) (hcol : DistinctColorDifferences S col)
    (u : ℕ) (hu : 0<u) (B : Finset ℕ) :
    (∑ b∈B, (binMass S u b : ℝ)^2) ≤
      (Fintype.card I : ℝ)*S.card+2*(Fintype.card I : ℝ)^2*u := by
  have hcs := Finset.sum_le_sum (s := B) (fun b hb ↦ bin_color_cauchy S col u b)
  rw [← Finset.mul_sum] at hcs
  have hf := partial_fiber_square_sum S (fun a ↦ (col a,a/u)) ((Finset.univ : Finset I) ×ˢ B)
  have he : ((S ×ˢ S).filter (fun xy ↦ (col xy.1,xy.1/u)=(col xy.2,xy.2/u)))=
      sameCellPairs S col u := by ext xy; simp only [sameCellPairs,Finset.mem_filter,Prod.mk.injEq]
  rw [he,Finset.sum_product] at hf
  have hfR : (∑ i : I, ∑ b∈B, (((S.filter (fun a ↦ col a=i ∧ a/u=b)).card : ℝ)^2)) ≤
      (sameCellPairs S col u).card := by
    have hh : (∑ i : I, ∑ b∈B, (((S.filter (fun a ↦ (col a,a/u)=(i,b))).card : ℝ)^2)) ≤
        (sameCellPairs S col u).card := by exact_mod_cast hf
    simpa only [Prod.mk.injEq] using hh
  rw [Finset.sum_comm] at hfR
  have hb : ((sameCellPairs S col u).card : ℝ) ≤
      S.card+2*(Fintype.card I : ℝ)*u := by exact_mod_cast sameCellPairs_bound S col hcol u hu
  have hm := mul_le_mul_of_nonneg_left (hfR.trans hb) (Nat.cast_nonneg (α := ℝ) (Fintype.card I))
  nlinarith

end Erdos66SidonColorBlockEnergy
