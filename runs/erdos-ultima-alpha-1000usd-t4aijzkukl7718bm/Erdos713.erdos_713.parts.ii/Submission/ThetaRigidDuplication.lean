import FormalConjecturesUtil
import Submission.BinaryTriangleIncidence
import Submission.ThetaRigidHeavyMatching

/-! Duplicating columns of a girth-eight incidence system. This refutes
an auxiliary uncharged heavy-pair bound even with rigid row intersections.
It does not refute the light-pair density gap or settle Erdős 713. -/
open Finset
open scoped Classical
namespace Erdos713ThetaRigidDuplication
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaHeavyMatching Erdos713ThetaRigidHeavyMatching
set_option maxHeartbeats 2000000
variable {A B : Type*}

def Dup (L : A → B → Prop) (a : A) (b : B × Fin 2) : Prop := L a b.1

theorem no_theta (L : A → B → Prop)
    (hfour : ∀ {a b : A} {i j : B}, a ≠ b → L a i → L a j → L b i → L b j → i = j)
    (hsix : ∀ {a b c : A} {i j k : B}, a ≠ b → a ≠ c → b ≠ c →
      L a i → L b i → L b j → L c j → L c k → L a k → i = j) :
    ¬ HasTheta (Dup L) := by
  rintro ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩
  have hn (i j : Fin 3) (hij : i ≠ j) : a i ≠ a j := fun he => hij (ha he)
  have h01 : (b 0).1 = (b 1).1 := hfour (hn 0 1 (by decide)) h00 h01 h10 h11
  have h03 : (b 0).1 = (b 3).1 := hsix (hn 0 1 (by decide)) (hn 0 2 (by decide))
    (hn 1 2 (by decide)) h00 h10 h13 h23 h22 h02
  let k : Fin 3 → Fin 4 := ![0,1,3]
  have hk : Function.Injective k := by decide
  have hbase (i : Fin 3) : (b (k i)).1 = (b 0).1 := by
    fin_cases i
    · rfl
    · exact h01.symm
    · exact h03.symm
  have hi : Function.Injective (fun i : Fin 3 => (b (k i)).2) := by
    intro i j he
    exact hk (hb (Prod.ext ((hbase i).trans (hbase j).symm) he))
  have hc := Fintype.card_le_of_injective _ hi
  norm_num at hc

variable [Fintype A] [Fintype B]

omit [Fintype A] in
theorem rigid (L : A → B → Prop)
    (hfour : ∀ {a b : A} {i j : B}, a ≠ b → L a i → L a j → L b i → L b j → i = j)
    (a b : A) (hab : a ≠ b) : (row (Dup L) a ∩ row (Dup L) b).card ≤ 2 := by
  let S := row (Dup L) a ∩ row (Dup L) b
  let f : S → Fin 2 := fun x => x.val.2
  have hi : Function.Injective f := by
    intro x y he
    have hx := mem_inter.mp x.property
    have hy := mem_inter.mp y.property
    have hbase := hfour hab ((mem_row (Dup L) a x.val).mp hx.1)
      ((mem_row (Dup L) a y.val).mp hy.1) ((mem_row (Dup L) b x.val).mp hx.2)
      ((mem_row (Dup L) b y.val).mp hy.2)
    exact Subtype.ext (Prod.ext hbase he)
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hi

noncomputable def dupPair (b : B) : Pair (B × Fin 2) :=
  ⟨{(b,0),(b,1)},mem_powersetCard.mpr ⟨subset_univ _,by simp⟩⟩

lemma supports_dupPair (L : A → B → Prop) (b : B) :
    supports (Dup L) (dupPair b) = univ.filter (fun a => L a b) := by
  ext a
  simp [mem_supports,dupPair,insert_subset_iff,singleton_subset_iff,mem_row,Dup]

lemma dupPair_injective : Function.Injective (@dupPair B _) := by
  intro b c he
  have hm : (b,0) ∈ (dupPair c).val := he ▸ (show (b,0) ∈ (dupPair b).val by simp [dupPair])
  simpa [dupPair] using hm

/-- Every original column of degree at least three gives a different
heavy unordered pair. Diagonal ordered pairs play no role in this count. -/
theorem heavy_pair_lower (L : A → B → Prop) (hc : ∀ b, 3 ≤ Nat.card {a // L a b}) :
    Nat.card B ≤ Nat.card (HeavyPair (Dup L)) := by
  let f : B → HeavyPair (Dup L) := fun b => ⟨dupPair b,by
    rw [supports_dupPair]
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using hc b⟩
  have hi : Function.Injective f := by
    intro b c he
    exact dupPair_injective (congrArg Subtype.val he)
  exact Nat.card_le_card_of_injective f hi

omit [Fintype A] [Fintype B] in
lemma column_degree (L : A → B → Prop) (b : B × Fin 2) :
    Nat.card {a // Dup L a b} = Nat.card {a // L a b.1} := rfl

omit [Fintype A] in
lemma row_card (L : A → B → Prop) (a : A) :
    (row (Dup L) a).card = 2 * Nat.card {b // L a b} := by
  have he : row (Dup L) a = (univ.filter (fun b => L a b)).product (univ : Finset (Fin 2)) := by
    ext b
    simp [mem_row,Dup]
  rw [he]
  calc
    _ = (univ.filter (fun b => L a b)).card * (univ : Finset (Fin 2)).card :=
      Finset.card_product _ _
    _ = _ := by simp [Nat.card_eq_fintype_card,Fintype.card_subtype,mul_comm]

omit [Fintype B] in
lemma codegree_le_one (L : A → B → Prop)
    (hfour : ∀ {a b : A} {i j : B}, a ≠ b → L a i → L a j → L b i → L b j → i = j)
    (x y : B × Fin 2) (hxy : x.1 ≠ y.1) : codegree (Dup L) x y ≤ 1 := by
  rw [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have ha' := (mem_filter.mp ha).2
  have hb' := (mem_filter.mp hb).2
  by_contra hab
  exact hxy (hfour hab ha'.1 ha'.2 hb'.1 hb'.2)

omit [Fintype B] in
lemma light_iff (L : A → B → Prop)
    (hfour : ∀ {a b : A} {i j : B}, a ≠ b → L a i → L a j → L b i → L b j → i = j)
    (hc : ∀ b, 3 ≤ Nat.card {a // L a b}) (x y : B × Fin 2) :
    codegree (Dup L) x y ≤ 2 ↔ x.1 ≠ y.1 := by
  constructor
  · intro hl he
    have hh := hc y.1
    have heq : codegree (Dup L) x y = Nat.card {a // L a y.1} := by
      simp only [codegree,Dup,he,and_self]
    rw [heq] at hl
    omega
  · intro he
    exact (codegree_le_one L hfour x y he).trans (by decide)

/-- The light count includes all ordered pairs, including diagonals,
exactly as in the density-gap target. -/
theorem light_card (L : A → B → Prop)
    (hfour : ∀ {a b : A} {i j : B}, a ≠ b → L a i → L a j → L b i → L b j → i = j)
    (hc : ∀ b, 3 ≤ Nat.card {a // L a b}) :
    Nat.card {p : (B × Fin 2) × (B × Fin 2) // codegree (Dup L) p.1 p.2 ≤ 2} =
      Nat.card B * (Nat.card B - 1) * 4 := by
  let e : {p : (B × Fin 2) × (B × Fin 2) // codegree (Dup L) p.1 p.2 ≤ 2} ≃
      {p : B × B // p.1 ≠ p.2} × (Fin 2 × Fin 2) := {
    toFun := fun p => (⟨(p.val.1.1,p.val.2.1),
      (light_iff L hfour hc _ _).mp p.property⟩,(p.val.1.2,p.val.2.2))
    invFun := fun p => ⟨((p.1.val.1,p.2.1),(p.1.val.2,p.2.2)),
      (light_iff L hfour hc _ _).mpr p.1.property⟩
    left_inv := fun p => by apply Subtype.ext; rfl
    right_inv := fun p => by cases p; rfl }
  have ho : Nat.card {p : B × B // p.1 ≠ p.2} = Nat.card B*(Nat.card B-1) := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    have he : (univ : Finset (B × B)).filter (fun p => p.1 ≠ p.2) =
        (univ : Finset B).offDiag := by ext p; simp
    rw [he,offDiag_card]
    simp only [card_univ,Nat.card_eq_fintype_card,Nat.mul_sub_left_distrib,Nat.mul_one]
  rw [Nat.card_congr e,Nat.card_prod,ho]
  simp only [Nat.card_prod,Nat.card_fin]

/-- These examples have a large light-pair budget; they do not refute the
quadratic density-gap assertion. -/
theorem light_half (L : A → B → Prop)
    (hfour : ∀ {a b : A} {i j : B}, a ≠ b → L a i → L a j → L b i → L b j → i = j)
    (hc : ∀ b, 3 ≤ Nat.card {a // L a b}) (hB : 2 ≤ Nat.card B) :
    (Nat.card (B × Fin 2))^2 ≤
      2*Nat.card {p : (B × Fin 2) × (B × Fin 2) // codegree (Dup L) p.1 p.2 ≤ 2} := by
  rw [light_card L hfour hc,Nat.card_prod,Nat.card_fin]
  have hh : Nat.card B - 1 + 1 = Nat.card B := Nat.sub_add_cancel (by omega)
  nlinarith

omit [Fintype A] [Fintype B] in
lemma binary_row_card (d : ℕ) (a : Erdos713BinaryTriangles.Rows d) :
    Nat.card {b : Erdos713BinaryTriangles.Columns d // Erdos713BinaryTriangles.Inc a b} = 2^d := by
  let e : {b : Erdos713BinaryTriangles.Columns d // Erdos713BinaryTriangles.Inc a b} ≃
      Erdos713BinaryTriangles.Slopes d := {
    toFun := fun b => b.val.2
    invFun := fun s => ⟨((fun j => a.2 j - (a.1.val : ZMod 3)*(s j).val),s),by
      change a.2 = _
      funext j
      dsimp [Erdos713BinaryTriangles.value]
      ring⟩
    left_inv := by
      intro b
      apply Subtype.ext
      refine Prod.ext ?_ rfl
      funext j
      have h := congr_fun b.property j
      change a.2 j = b.val.1 j + (a.1.val : ZMod 3)*(b.val.2 j).val at h
      change a.2 j - (a.1.val : ZMod 3)*(b.val.2 j).val = b.val.1 j
      linear_combination h
    right_inv := fun s => rfl }
  rw [Nat.card_congr e]
  simp [Erdos713BinaryTriangles.Slopes,Nat.card_eq_fintype_card]

/-- Even with rigidity, all column degrees equal to three, and arbitrarily
large uniform row degree, heavy unordered pairs have unbounded row ratio. -/
theorem exists_counterexample (C N : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop) (r : ℕ),
      ¬ HasTheta R ∧ (∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2) ∧
      0 < Nat.card A ∧ N ≤ r ∧ (∀ a, (row R a).card = r) ∧
      (∀ b, Nat.card {a // R a b} = 3) ∧
      (Nat.card B)^2 ≤ 2*Nat.card {p : B × B // codegree R p.1 p.2 ≤ 2} ∧
      C * Nat.card A < Nat.card (HeavyPair R) := by
  classical
  let d := 3*C+N+1
  let A := Erdos713BinaryTriangles.Rows d
  let B := Erdos713BinaryTriangles.Columns d
  let L : A → B → Prop := Erdos713BinaryTriangles.Inc
  have hrows : Nat.card A = 3*3^d := Erdos713BinaryTriangles.rows_card d
  have hcols : Nat.card B = 3^d*2^d := Erdos713BinaryTriangles.columns_card d
  have hdeg (b : B) : Nat.card {a : A // L a b} = 3 := Erdos713BinaryTriangles.column_card b
  have hp : 0 < (3 : ℕ)^d := pow_pos (by decide) _
  have hpow : d < 2^d := Nat.lt_two_pow_self
  have hbig : C*Nat.card A < Nat.card B := by
    rw [hrows,hcols]
    have hh := Nat.mul_lt_mul_of_pos_left (show 3*C < 2^d from (show 3*C ≤ d by dsimp [d]; omega).trans_lt hpow) hp
    nlinarith only [hh]
  refine ⟨A,B × Fin 2,inferInstance,inferInstance,Dup L,2*2^d,
    no_theta L Erdos713BinaryTriangles.no_four Erdos713BinaryTriangles.no_six,
    ?_,?_,?_,?_,?_,?_,?_⟩
  · intro a b hab
    have hh := rigid L Erdos713BinaryTriangles.no_four a b hab
    convert hh using 1
    congr 1
    ext x
    simp
  · rw [hrows]
    positivity
  · have hn : N ≤ d := by dsimp [d]; omega
    omega
  · intro a
    rw [row_card,binary_row_card]
  · intro b
    exact hdeg b.1
  · apply light_half L Erdos713BinaryTriangles.no_four (fun b => (hdeg b).ge)
    have hd : 1 ≤ d := by dsimp [d]; omega
    have htwo : 2 ≤ 2^d := by omega
    rw [hcols]
    nlinarith only [htwo,hp]
  · exact hbig.trans_le (heavy_pair_lower L (fun b => (hdeg b).ge))

/-- In particular, rigidity alone does not give an injection of heavy
unordered pairs into rows, even without requiring supporting rows. -/
theorem exists_no_matching :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ (∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2) ∧
      (∀ b, Nat.card {a // R a b} = 3) ∧
      ¬ ∃ f : HeavyPair R → A, Function.Injective f := by
  obtain ⟨A,B,iA,iB,R,r,hf,hr,hm,hN,hrows,hcols,hlight,hbig⟩ := exists_counterexample 1 4
  refine ⟨A,B,iA,iB,R,hf,hr,hcols,?_⟩
  rintro ⟨f,hi⟩
  have hc := Nat.card_le_card_of_injective f hi
  simp only [one_mul] at hbig
  exact (not_le_of_gt hbig) hc

/-- Negation of an auxiliary bound, not the negation of Erdős 713. -/
theorem no_rigid_row_bound :
    ¬ ∃ C : ℕ, ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R → (∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2) →
      (∀ b, Nat.card {a // R a b} = 3) → Nat.card (HeavyPair R) ≤ C*Nat.card A := by
  rintro ⟨C,hC⟩
  obtain ⟨A,B,iA,iB,R,r,hf,hr,hm,hN,hrows,hcols,hlight,hbig⟩ := exists_counterexample C 4
  exact (not_le_of_gt hbig) (hC A B R hf hr hcols)

#print axioms no_theta
#print axioms rigid
#print axioms light_card
#print axioms light_half
#print axioms exists_counterexample
#print axioms exists_no_matching
#print axioms no_rigid_row_bound
end Erdos713ThetaRigidDuplication
