import Submission.SidonGridExplore

/-! Dense finite bounded-sum grids can have arbitrarily high Sidon coloring
number. This is an obstruction to an auxiliary extraction inference only. -/
namespace Erdos66DenseSidonGrid
open Erdos66NaturalSidonExtraction Erdos66SidonGrid
  Erdos66SidonColorBlockEnergy AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 2000000

lemma unordered_of_sum_sq {F : Type*} [Field F] (h2 : (2:F)≠0)
    {a b c d : F} (hs : a+b=c+d) (hq : a^2+b^2=c^2+d^2) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have hp : 2*((a-c)*(a-d))=0 := by
    linear_combination hq - (b-a+c+d)*hs
  have hh : (a-c)*(a-d)=0 := (mul_eq_zero.mp hp).resolve_left h2
  rcases mul_eq_zero.mp hh with hc | hd
  · left
    have he := sub_eq_zero.mp hc
    exact ⟨he, by rw [he] at hs; exact add_left_cancel hs⟩
  · right
    have he := sub_eq_zero.mp hd
    refine ⟨he,?_⟩
    rw [he,add_comm c d] at hs
    exact add_left_cancel hs

noncomputable def point (p : ℕ) (x : ZMod p) : ℕ :=
  x.val+2*p*(x^2).val

noncomputable def parabola (p : ℕ) [NeZero p] : Finset ℕ :=
  Finset.univ.image (point p)

lemma point_injective (p : ℕ) [NeZero p] : Function.Injective (point p) := by
  have hp : 0<p := Nat.pos_of_ne_zero (NeZero.ne p)
  intro x y he
  have hx := x.val_lt
  have hy := y.val_lt
  have hh := congrArg (fun n : ℕ ↦ n%(2*p)) he
  simp only [point,Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (show x.val<2*p by omega),
    Nat.mod_eq_of_lt (show y.val<2*p by omega)] at hh
  exact ZMod.val_injective p hh

lemma parabola_card (p : ℕ) [NeZero p] : (parabola p).card=p := by
  rw [parabola,Finset.card_image_of_injective _ (point_injective p),Finset.card_univ]
  exact ZMod.card p

lemma point_lt (p : ℕ) [NeZero p] (x : ZMod p) : point p x<2*p^2 := by
  have hp : 0<p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hx := x.val_lt
  have hq := (x^2).val_lt
  dsimp [point]
  nlinarith

lemma parabola_lt (p : ℕ) [NeZero p] {a : ℕ} (ha : a∈parabola p) : a<2*p^2 := by
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp ha
  exact point_lt p x

lemma parabola_sidon (p : ℕ) [Fact p.Prime] (hp2 : p≠2) : NatSidon (parabola p) := by
  intro a ha b hb c hc d hd he
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hd
  have hp : 0<p := (Fact.out : p.Prime).pos
  have hab : a.val+b.val<2*p := by have := a.val_lt; have := b.val_lt; omega
  have hcd : c.val+d.val<2*p := by have := c.val_lt; have := d.val_lt; omega
  have he' : (a.val+b.val)+(2*p)*((a^2).val+(b^2).val)=
      (c.val+d.val)+(2*p)*((c^2).val+(d^2).val) := by
    dsimp [point] at he
    nlinarith
  have hm := congrArg (fun n : ℕ ↦ n%(2*p)) he'
  have hq := congrArg (fun n : ℕ ↦ n/(2*p)) he'
  simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hab,Nat.mod_eq_of_lt hcd] at hm
  simp only [Nat.add_mul_div_left _ _ (show 0<2*p by omega),
    Nat.div_eq_of_lt hab,Nat.div_eq_of_lt hcd,zero_add] at hq
  have hs : a+b=c+d := by
    have hh := congrArg (fun n : ℕ ↦ (n : ZMod p)) hm
    simpa only [Nat.cast_add,ZMod.natCast_zmod_val] using hh
  have hsq : a^2+b^2=c^2+d^2 := by
    have hh := congrArg (fun n : ℕ ↦ (n : ZMod p)) hq
    simpa only [Nat.cast_add,ZMod.natCast_zmod_val] using hh
  have h2 : (2 : ZMod p)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  rcases unordered_of_sum_sq h2 hs hsq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp

noncomputable def denseGrid (p : ℕ) [NeZero p] : Finset ℕ :=
  grid (parabola p) (parabola p) (4*p^2)

lemma denseGrid_card (p : ℕ) [NeZero p] : (denseGrid p).card=p^2 := by
  have hp : 0<p := Nat.pos_of_ne_zero (NeZero.ne p)
  dsimp [denseGrid,grid]
  rw [Finset.card_image_of_injective _ (encode_injective _ _ _ (by positivity)
    (fun x hx ↦ by have := parabola_lt p hx; nlinarith)),Finset.card_univ,
    Fintype.card_prod,Fintype.card_coe,parabola_card,pow_two]

lemma denseGrid_lt (p : ℕ) [NeZero p] {a : ℕ} (ha : a∈denseGrid p) : a<8*p^4 := by
  obtain ⟨⟨x,y⟩,_,rfl⟩ := Finset.mem_image.mp ha
  have hx := parabola_lt p x.property
  have hy := parabola_lt p y.property
  have hp : 0<p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hpq : 0<p^2 := pow_pos hp _
  change x.val+4*p^2*y.val<8*p^4
  have hyy : y.val+1≤2*p^2 := by omega
  have hmul := Nat.mul_le_mul_left (4*p^2) hyy
  nlinarith [sq_nonneg (p^2 : ℤ)]

lemma denseGrid_rep_le_four (p : ℕ) [Fact p.Prime] (hp2 : p≠2) (n : ℕ) :
    sumRep (denseGrid p : Set ℕ) n≤4 := by
  have hp : 0<p := (Fact.out : p.Prime).pos
  apply grid_rep_le_four _ _ (parabola_sidon p hp2) (parabola_sidon p hp2)
    (4*p^2) (by positivity)
  · intro x hx
    have := parabola_lt p hx
    nlinarith
  · intro x hx y hy
    have := parabola_lt p hx
    have := parabola_lt p hy
    omega

lemma grid_subset_left {X X' Y : Finset ℕ} (hX : X⊆X') (M : ℕ) :
    grid X Y M⊆grid X' Y M := by
  intro a ha
  obtain ⟨⟨x,y⟩,_,rfl⟩ := Finset.mem_image.mp ha
  exact Finset.mem_image.mpr ⟨(⟨x.val,hX x.property⟩,y),Finset.mem_univ _,rfl⟩

lemma distinctColorDifferences_mono {I : Type*} {S T : Finset ℕ} {col : ℕ → I}
    (hST : S⊆T) (h : DistinctColorDifferences T col) : DistinctColorDifferences S col := by
  intro a ha b hb c hc d hd
  exact h a (hST ha) b (hST hb) c (hST hc) d (hST hd)

lemma denseGrid_not_sidon_colored (p m : ℕ) [NeZero p]
    (hpm : m*(m+1)^2<p) (col : ℕ → Fin m) :
    ¬DistinctColorDifferences (denseGrid p) col := by
  have hp : 0<p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hm : m+1≤(parabola p).card := by
    rw [parabola_card]
    nlinarith [sq_nonneg (m : ℤ)]
  obtain ⟨R,hRX,hRc⟩ := Finset.exists_subset_card_eq hm
  intro hcol
  have hRcol := distinctColorDifferences_mono (grid_subset_left hRX (4*p^2)) hcol
  apply grid_not_sidon_colored R (parabola p) (4*p^2) (by positivity)
    (fun x hx ↦ by have := parabola_lt p (hRX hx); nlinarith) m
    (by omega) (by rw [hRc,parabola_card]; nlinarith) col hRcol

/-- Even a square-root-dense prefix with global ordered representation cap
four need not admit any fixed number of Sidon colors. -/
theorem exists_dense_cap_four_not_sidon_colored (m : ℕ) :
    ∃ p : ℕ, p.Prime ∧ 2<p ∧ ∃ S : Finset ℕ,
      S.card=p^2 ∧ (∀ a∈S, a<8*p^4) ∧
      (∀ n : ℕ, sumRep (S : Set ℕ) n≤4) ∧
      ∀ col : ℕ → Fin m, ¬DistinctColorDifferences S col := by
  obtain ⟨p,hp,hprime⟩ := Nat.exists_infinite_primes (max 3 (m*(m+1)^2+1))
  letI : Fact p.Prime := ⟨hprime⟩
  have hp3 : 2<p := by omega
  have hpm : m*(m+1)^2<p := by omega
  exact ⟨p,hprime,hp3,denseGrid p,denseGrid_card p,
    fun a ha ↦ denseGrid_lt p ha,denseGrid_rep_le_four p (by omega),
    denseGrid_not_sidon_colored p m hpm⟩

end Erdos66DenseSidonGrid
