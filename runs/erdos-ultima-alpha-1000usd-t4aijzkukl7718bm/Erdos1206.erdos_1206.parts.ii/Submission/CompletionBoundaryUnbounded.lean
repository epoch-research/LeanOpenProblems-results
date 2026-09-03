import FormalConjecturesUtil

/-!
A proposed uniform completion-boundary bound is false. This file concerns
finite cube-Sidon sets only, and is not a disproof of Erdős 1206.
-/

namespace Erdos1206
namespace CompletionBoundary
open Finset

/-- Multiplicative separation of the selected roots. -/
def Separated (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a < b → 2 * a < b

lemma separated_sidon {S : Finset ℕ} (hS : Separated S) : IsSidon (S : Set ℕ) := by
  induction S using Finset.induction_on_max with
  | h0 => simp [IsSidon]
  | @step a S hmax ih =>
    have hsep : Separated S := fun x hx y hy hxy =>
      hS x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hxy
    have hs := ih hsep
    have hbig (x : ℕ) (hx : x ∈ S) : 2 * x < a :=
      hS x (mem_insert_of_mem hx) a (mem_insert_self _ _) (hmax x hx)
    have hu : IsSidon ((S : Set ℕ) ∪ {a}) := (Set.IsSidon.insert hs).mpr <| Or.inr (by
      intro x hx y hy
      refine ⟨?_, ?_⟩
      · have := hbig x hx; have := hbig y hy; omega
      · intro z hz
        have := hbig y hy; have := hbig z hz; omega)
    simpa only [coe_insert, Set.union_singleton] using hu

lemma separated_cubes_sidon {S : Finset ℕ} (hS : Separated S) :
    IsSidon ((fun a : ℕ => a ^ 3) '' (S : Set ℕ)) := by
  have hs : Separated (S.image (fun a => a ^ 3)) := by
    rintro x hx y hy hxy
    rcases mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases mem_image.mp hy with ⟨b, hb, rfl⟩
    have hab : a < b := by
      by_contra h
      have := Nat.pow_le_pow_left (show b ≤ a by omega) 3
      omega
    have hpow := Nat.pow_lt_pow_left (hS a ha b hb hab) (by decide : 3 ≠ 0)
    simp only [mul_pow] at hpow
    norm_num at hpow
    omega
  simpa only [coe_image] using separated_sidon hs

/-- Every listed outside root has a nontrivial collision with selected roots. -/
def BoundaryWitnesses (S B : Finset ℕ) : Prop :=
  Disjoint S B ∧ ∀ b ∈ B, ∃ a ∈ S, ∃ c ∈ S, ∃ d ∈ S,
    b ^ 3 + a ^ 3 = c ^ 3 + d ^ 3

def scaleFn (u v : ℕ) (i : Fin 3) (n : ℕ) : ℕ :=
  (if i.val = 0 then 1 else if i.val = 1 then u else v) * n

def tripleDilate (u v : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (univ ×ˢ S).image (fun z : Fin 3 × ℕ => scaleFn u v z.1 z.2)

lemma mem_tripleDilate {u v x : ℕ} {S : Finset ℕ} :
    x ∈ tripleDilate u v S ↔ ∃ i : Fin 3, ∃ s ∈ S, scaleFn u v i s = x := by
  simp [tripleDilate, mem_image, Prod.exists]

lemma scaleFn_pos {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (i : Fin 3)
    {n : ℕ} (hn : 0 < n) : 0 < scaleFn u v i n := by
  fin_cases i <;> simp_all [scaleFn]

lemma scaleFn_injective {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (i : Fin 3) :
    Function.Injective (scaleFn u v i) := by
  intro a b hab
  fin_cases i <;> norm_num [scaleFn] at hab
  · exact hab
  · rcases hab with h | h
    · exact h
    · omega
  · rcases hab with h | h
    · exact h
    · omega

lemma scaleFn_cross_lt {M u v a b : ℕ} (hM : 0 < M) (hu : 2 * M < u)
    (hv : 2 * u * M < v) (ha : a ≤ M) (hb : 0 < b)
    {i j : Fin 3} (hij : i < j) : 2 * scaleFn u v i a < scaleFn u v j b := by
  have hu0 : 0 < u := by omega
  have huM : M ≤ u * M := Nat.le_mul_of_pos_left M hu0
  have hub : u ≤ u * b := Nat.le_mul_of_pos_right u hb
  have hvb : v ≤ v * b := Nat.le_mul_of_pos_right v hb
  have hua : u * a ≤ u * M := Nat.mul_le_mul_left u ha
  fin_cases i, j
  all_goals try { norm_num at hij }
  all_goals norm_num [scaleFn]
  all_goals nlinarith

lemma tripleDilate_injOn {T : Finset ℕ} {M u v : ℕ}
    (hT : ∀ t ∈ T, 0 < t ∧ t ≤ M) (hM : 0 < M)
    (hu : 2 * M < u) (hv : 2 * u * M < v) :
    Set.InjOn (fun z : Fin 3 × ℕ => scaleFn u v z.1 z.2) (↑((Finset.univ : Finset (Fin 3)) ×ˢ T) : Set (Fin 3 × ℕ)) := by
  intro x hx y hy he
  rcases x with ⟨i,a⟩
  rcases y with ⟨j,b⟩
  have ha := hT a (mem_product.mp hx).2
  have hb := hT b (mem_product.mp hy).2
  have hij : i = j := by
    rcases lt_trichotomy i j with h | h | h
    · have hh := scaleFn_cross_lt hM hu hv ha.2 hb.1 h
      dsimp only at he
      omega
    · exact h
    · have hh := scaleFn_cross_lt hM hu hv hb.2 ha.1 h
      dsimp only at he
      omega
  subst j
  have hab : a = b := scaleFn_injective (by omega) (by nlinarith) i he
  simp [hab]

lemma tripleDilate_card {T : Finset ℕ} {M u v : ℕ}
    (hT : ∀ t ∈ T, 0 < t ∧ t ≤ M) (hM : 0 < M)
    (hu : 2 * M < u) (hv : 2 * u * M < v) :
    (tripleDilate u v T).card = 3 * T.card := by
  rw [tripleDilate, card_image_iff.mpr (tripleDilate_injOn hT hM hu hv)]
  simp

lemma tripleDilate_separated {S : Finset ℕ} {M u v : ℕ}
    (hS : Separated S) (hT : ∀ t ∈ S, 0 < t ∧ t ≤ M) (hM : 0 < M)
    (hu : 2 * M < u) (hv : 2 * u * M < v) : Separated (tripleDilate u v S) := by
  rintro x hx y hy hxy
  rcases mem_tripleDilate.mp hx with ⟨i,a,ha,rfl⟩
  rcases mem_tripleDilate.mp hy with ⟨j,b,hb,rfl⟩
  rcases lt_trichotomy i j with h | h | h
  · exact scaleFn_cross_lt hM hu hv (hT a ha).2 (hT b hb).1 h
  · subst j
    have hu0 : 0 < u := by omega
    have hv0 : 0 < v := by nlinarith
    fin_cases i <;> norm_num [scaleFn] at hxy ⊢
    · exact hS a ha b hb hxy
    · have hab := (Nat.mul_lt_mul_left hu0).mp hxy
      have hh := Nat.mul_lt_mul_of_pos_left (hS a ha b hb hab) hu0
      nlinarith only [hh]
    · have hab := (Nat.mul_lt_mul_left hv0).mp hxy
      have hh := Nat.mul_lt_mul_of_pos_left (hS a ha b hb hab) hv0
      nlinarith only [hh]
  · have hh := scaleFn_cross_lt hM hu hv (hT b hb).2 (hT a ha).1 h
    omega

lemma tripleDilate_mono {u v : ℕ} {S T : Finset ℕ} (h : S ⊆ T) :
    tripleDilate u v S ⊆ tripleDilate u v T := by
  intro x hx
  rcases mem_tripleDilate.mp hx with ⟨i,s,hs,rfl⟩
  exact mem_tripleDilate.mpr ⟨i,s,h hs,rfl⟩

lemma mem_tripleDilate_zero {u v a : ℕ} {S : Finset ℕ} (ha : a ∈ S) :
    a ∈ tripleDilate u v S := by
  exact mem_tripleDilate.mpr ⟨0,a,ha,by simp [scaleFn]⟩

lemma mem_tripleDilate_one {u v a : ℕ} {S : Finset ℕ} (ha : a ∈ S) :
    u*a ∈ tripleDilate u v S := by
  exact mem_tripleDilate.mpr ⟨1,a,ha,by simp [scaleFn]⟩

lemma mem_tripleDilate_two {u v a : ℕ} {S : Finset ℕ} (ha : a ∈ S) :
    v*a ∈ tripleDilate u v S := by
  exact mem_tripleDilate.mpr ⟨2,a,ha,by simp [scaleFn]⟩

lemma tripleDilate_disjoint {S B : Finset ℕ} {M u v : ℕ}
    (hT : ∀ t ∈ S ∪ B, 0 < t ∧ t ≤ M) (hM : 0 < M)
    (hu : 2 * M < u) (hv : 2 * u * M < v) (hSB : Disjoint S B) :
    Disjoint (tripleDilate u v S) (tripleDilate u v B) := by
  apply disjoint_left.mpr
  intro x hx hy
  rcases mem_tripleDilate.mp hx with ⟨i,a,ha,rfl⟩
  rcases mem_tripleDilate.mp hy with ⟨j,b,hb,he⟩
  have hh := tripleDilate_injOn hT hM hu hv
    (show (j,b) ∈ ((univ : Finset (Fin 3)) ×ˢ (S ∪ B)) from
      mem_product.mpr ⟨mem_univ _,mem_union_right _ hb⟩)
    (show (i,a) ∈ ((univ : Finset (Fin 3)) ×ˢ (S ∪ B)) from
      mem_product.mpr ⟨mem_univ _,mem_union_left _ ha⟩) he
  have hab : b = a := congrArg Prod.snd hh
  exact disjoint_left.mp hSB ha (hab ▸ hb)

lemma extension_parameters (M : ℕ) (hM : 0 < M) :
    ∃ u v w : ℕ, 2*M < u ∧ 2*u*M < v ∧ v < w ∧
      1 + w^3 = u^3 + v^3 ∧
      ∀ x, 0 < x → x ≤ M → ∀ y, 0 < y → y ≤ M → v*x ≠ w*y := by
  let t := 4*(M+1)
  let q := 3*t^3
  let r := 3*t
  let u := 3*q+1
  let v := q*r
  let w := (q+1)*r
  have ht : 0 < t := by dsimp [t]; omega
  have hq : M < q := by dsimp [q,t]; nlinarith [sq_nonneg (M+1)]
  have hr : 8*M < r := by dsimp [r,t]; omega
  have hq0 : 0 < q := by omega
  have huq : u ≤ 4*q := by dsimp [u]; omega
  have hu : 2*M < u := by dsimp [u]; omega
  have hv : 2*u*M < v := by
    have := Nat.mul_lt_mul_of_pos_left hr hq0
    have := Nat.mul_le_mul_right (2*M) huq
    dsimp [v]
    nlinarith
  refine ⟨u,v,w,hu,hv,?_,?_,?_⟩
  · dsimp [v,w]; nlinarith
  · dsimp [u,v,w,q,r]; ring
  · intro x hx hxM y hy hyM he
    have he' : q*x = (q+1)*y := by
      have hh : r*(q*x) = r*((q+1)*y) := by
        dsimp [v,w] at he
        nlinarith only [he]
      exact (Nat.mul_left_cancel_iff (by omega : 0 < r)).mp hh
    have hd : q ∣ y := by
      have h1 : q ∣ (q+1)*y := he' ▸ dvd_mul_right q x
      have h2 : q ∣ q*y := dvd_mul_right q y
      have h3 : (q+1)*y = q*y+y := by ring
      rw [h3] at h1
      exact (Nat.dvd_add_right h2).mp h1
    have := Nat.le_of_dvd hy hd
    omega

lemma extra_disjoint {T S : Finset ℕ} {M u v w : ℕ}
    (hT : ∀ t ∈ T, 0 < t ∧ t ≤ M) (hS : S ⊆ T) (hM : 0 < M)
    (hu : 2*M < u) (hv : 2*u*M < v) (hw : v < w)
    (hne : ∀ x, 0 < x → x ≤ M → ∀ y, 0 < y → y ≤ M → v*x ≠ w*y) :
    Disjoint (tripleDilate u v T) (S.image (w * ·)) := by
  apply disjoint_left.mpr
  intro z hz hz'
  rcases mem_tripleDilate.mp hz with ⟨i,x,hx,rfl⟩
  rcases mem_image.mp hz' with ⟨y,hy,he⟩
  have hx' := hT x hx
  have hy' := hT y (hS hy)
  have hu0 : 0 < u := by omega
  have hw0 : 0 < w := by omega
  have hwy : w ≤ w*y := Nat.le_mul_of_pos_right _ hy'.1
  have hux : u*x ≤ u*M := Nat.mul_le_mul_left _ hx'.2
  have huM : M ≤ u*M := Nat.le_mul_of_pos_left _ hu0
  fin_cases i <;> norm_num [scaleFn] at he
  · nlinarith
  · nlinarith
  · exact hne x hx'.1 hx'.2 y hy'.1 hy'.2 he.symm

/-- One stage increases the boundary/selected ratio by exactly one third. -/
lemma extension {S B : Finset ℕ} (hpos : ∀ t ∈ S ∪ B, 0 < t)
    (hsep : Separated S) (hwit : BoundaryWitnesses S B) :
    ∃ S' B' : Finset ℕ,
      (∀ t ∈ S' ∪ B', 0 < t) ∧ Separated S' ∧ BoundaryWitnesses S' B' ∧
      S'.card = 3*S.card ∧ B'.card = 3*B.card + S.card := by
  let T := S ∪ B
  let M := T.sup id + 1
  have hM : 0 < M := by dsimp [M]; omega
  have hT : ∀ t ∈ T, 0 < t ∧ t ≤ M := by
    intro t ht
    refine ⟨hpos t ht, ?_⟩
    have := le_sup (f := id) ht
    dsimp [M]; exact le_trans this (Nat.le_succ _)
  rcases extension_parameters M hM with ⟨u,v,w,hu,hv,hw,hidentity,hne⟩
  have hu0 : 0 < u := by omega
  have hv0 : 0 < v := by nlinarith
  have hw0 : 0 < w := by omega
  let S' := tripleDilate u v S
  let B₀ := tripleDilate u v B
  let E := S.image (w * ·)
  have hS : S ⊆ T := subset_union_left
  have hB : B ⊆ T := subset_union_right
  have hboundsS : ∀ t ∈ S, 0 < t ∧ t ≤ M := fun t ht => hT t (hS ht)
  have hboundsB : ∀ t ∈ B, 0 < t ∧ t ≤ M := fun t ht => hT t (hB ht)
  have hdis := extra_disjoint hT hS hM hu hv hw hne
  have hdisS : Disjoint S' E := hdis.mono_left (tripleDilate_mono hS)
  have hdisB : Disjoint B₀ E := hdis.mono_left (tripleDilate_mono hB)
  refine ⟨S',B₀ ∪ E,?_,tripleDilate_separated hsep hboundsS hM hu hv,?_,
    tripleDilate_card hboundsS hM hu hv,?_⟩
  · intro t ht
    rcases mem_union.mp ht with ht | ht
    · rcases mem_tripleDilate.mp ht with ⟨i,a,ha,rfl⟩
      exact scaleFn_pos hu0 hv0 i (hboundsS a ha).1
    · rcases mem_union.mp ht with ht | ht
      · rcases mem_tripleDilate.mp ht with ⟨i,a,ha,rfl⟩
        exact scaleFn_pos hu0 hv0 i (hboundsB a ha).1
      · rcases mem_image.mp ht with ⟨a,ha,rfl⟩
        exact Nat.mul_pos hw0 (hboundsS a ha).1
  · refine ⟨disjoint_union_right.mpr ⟨tripleDilate_disjoint hT hM hu hv hwit.1,hdisS⟩,?_⟩
    intro b hb
    rcases mem_union.mp hb with hb | hb
    · rcases mem_tripleDilate.mp hb with ⟨i,b₀,hb₀,rfl⟩
      rcases hwit.2 b₀ hb₀ with ⟨a,ha,c,hc,d,hd,he⟩
      refine ⟨scaleFn u v i a,mem_tripleDilate.mpr ⟨i,a,ha,rfl⟩,
        scaleFn u v i c,mem_tripleDilate.mpr ⟨i,c,hc,rfl⟩,
        scaleFn u v i d,mem_tripleDilate.mpr ⟨i,d,hd,rfl⟩,?_⟩
      simp only [scaleFn, mul_pow]
      nlinarith only [congrArg (fun n =>
        (if i.val = 0 then 1 else if i.val = 1 then u else v)^3 * n) he]
    · rcases mem_image.mp hb with ⟨a,ha,rfl⟩
      refine ⟨a,mem_tripleDilate_zero ha,u*a,mem_tripleDilate_one ha,
        v*a,mem_tripleDilate_two ha,?_⟩
      simp only [mul_pow]
      nlinarith only [congrArg (fun n => n*a^3) hidentity]
  · rw [card_union_of_disjoint hdisB]
    have hE : E.card = S.card := card_image_of_injective _ (mul_right_injective₀ hw0.ne')
    rw [hE, tripleDilate_card hboundsB hM hu hv]

lemma stages (k : ℕ) : ∃ S B : Finset ℕ,
    (∀ t ∈ S ∪ B, 0 < t) ∧ Separated S ∧ BoundaryWitnesses S B ∧
    S.card = 3^k ∧ 3*B.card = k*S.card := by
  induction k with
  | zero =>
    refine ⟨{1},∅,?_,?_,?_,?_,?_⟩
    · simp
    · simp [Separated]
    · simp [BoundaryWitnesses]
    · simp
    · simp
  | succ k ih =>
    rcases ih with ⟨S,B,hpos,hsep,hwit,hS,hB⟩
    rcases extension hpos hsep hwit with ⟨S',B',hpos',hsep',hwit',hS',hB'⟩
    refine ⟨S',B',hpos',hsep',hwit',?_,?_⟩
    · rw [hS',hS,pow_succ]; omega
    · rw [hB',hS']; nlinarith only [hB]

/-- No universal linear bound holds for all completion boundaries. This is not
an obstruction to positive-density cube-Sidon sets. -/
theorem completion_boundary_unbounded (C : ℕ) :
    ∃ S B : Finset ℕ,
      IsSidon ((fun a : ℕ => a^3) '' (S : Set ℕ)) ∧
      BoundaryWitnesses S B ∧ C*S.card < B.card := by
  rcases stages (3*C+1) with ⟨S,B,hpos,hsep,hwit,hS,hB⟩
  refine ⟨S,B,separated_cubes_sidon hsep,hwit,?_⟩
  have hcard : 0 < S.card := by rw [hS]; positivity
  nlinarith only [hB,hcard]

#print axioms completion_boundary_unbounded

end CompletionBoundary
end Erdos1206
