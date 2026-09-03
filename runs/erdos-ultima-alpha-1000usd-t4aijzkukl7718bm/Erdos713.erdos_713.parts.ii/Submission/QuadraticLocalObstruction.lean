import FormalConjecturesUtil
import Submission.GlobalLightPairs

/-! Quadratic evaluation relations refute a proposed local bound for the
oriented K33-minus-edge pattern, even with regular columns capped by the
column count. This does not refute the corresponding THETA-free estimate,
nor the original rationality conjecture. -/
open Finset
namespace Erdos713QuadraticLocal
open Erdos713GlobalLight
set_option maxHeartbeats 2000000
variable {F : Type*} [Field F]

abbrev Rows (F : Type*) := F × F × F
abbrev Cols (F : Type*) := F × F

def value (a : Rows F) (t : F) : F := a.1+a.2.1*t+a.2.2*t^2
def incidence (a : Rows F) (p : Cols F) : Prop := value a p.1 = p.2

def HasK23 {A B : Type*} (R : A → B → Prop) : Prop :=
  ∃ a b : A, a ≠ b ∧ ∃ p : Fin 3 → B, Function.Injective p ∧
    ∀ i, R a (p i) ∧ R b (p i)

def HasAlmost33 {A B : Type*} (R : A → B → Prop) : Prop :=
  ∃ (a : Fin 3 → A) (b : Fin 3 → B), Function.Injective a ∧ Function.Injective b ∧
    ∀ i j, (i,j) ≠ (2,2) → R (a i) (b j)

lemma HasAlmost33.hasK23 {A B : Type*} {R : A → B → Prop} (h : HasAlmost33 R) :
    HasK23 R := by
  obtain ⟨a,b,ha,hb,hab⟩ := h
  refine ⟨a 0,a 1,ha.ne (by decide),b,hb,?_⟩
  intro i
  exact ⟨hab 0 i (by simp),hab 1 i (by simp)⟩

lemma eq_of_three_values {a b : Rows F} {x y z : F}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : value a x = value b x) (hy : value a y = value b y)
    (hz : value a z = value b z) : a = b := by
  dsimp only [value] at hx hy hz
  have h1 : (x-y)*((a.2.1-b.2.1)+(x+y)*(a.2.2-b.2.2)) = 0 := by
    linear_combination hx-hy
  have h2 : (x-z)*((a.2.1-b.2.1)+(x+z)*(a.2.2-b.2.2)) = 0 := by
    linear_combination hx-hz
  have hh1 := (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hxy)
  have hh2 := (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hxz)
  have h3 : (y-z)*(a.2.2-b.2.2) = 0 := by linear_combination hh1-hh2
  have hc : a.2.2 = b.2.2 := sub_eq_zero.mp
    ((mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hyz))
  have hb : a.2.1 = b.2.1 := by simpa only [hc,sub_self,mul_zero,add_zero,sub_eq_zero] using hh1
  have ha : a.1 = b.1 := by
    rw [hb,hc] at hx
    exact add_right_cancel (add_right_cancel hx)
  exact Prod.ext ha (Prod.ext hb hc)

lemma no_K23 : ¬ HasK23 (incidence (F := F)) := by
  rintro ⟨a,b,hab,p,hp,hR⟩
  have ht {i j : Fin 3} (hij : i ≠ j) : (p i).1 ≠ (p j).1 := by
    intro hh
    apply hij
    apply hp
    refine Prod.ext hh ?_
    exact (hR i).1.symm.trans ((congrArg (value a) hh).trans (hR j).1)
  apply hab
  exact eq_of_three_values (ht (by decide : (0 : Fin 3) ≠ 1))
    (ht (by decide : (0 : Fin 3) ≠ 2)) (ht (by decide : (1 : Fin 3) ≠ 2))
    ((hR 0).1.trans (hR 0).2.symm) ((hR 1).1.trans (hR 1).2.symm)
    ((hR 2).1.trans (hR 2).2.symm)

lemma no_almost33 : ¬ HasAlmost33 (incidence (F := F)) :=
  fun h => no_K23 h.hasK23

def rowEquiv (a : Rows F) : F ≃ {p : Cols F // incidence a p} where
  toFun t := ⟨(t,value a t),rfl⟩
  invFun p := p.val.1
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext rfl p.property)

def columnEquiv (p : Cols F) : (F × F) ≃ {a : Rows F // incidence a p} where
  toFun bc := ⟨(p.2-bc.1*p.1-bc.2*p.1^2,bc.1,bc.2),by dsimp [incidence,value]; ring⟩
  invFun a := a.val.2
  left_inv _ := rfl
  right_inv a := by
    apply Subtype.ext
    refine Prod.ext ?_ rfl
    have hh := a.property
    dsimp [incidence,value] at hh
    dsimp
    linear_combination -hh

def edgeEquiv : (Rows F × F) ≃ {p : Rows F × Cols F // incidence p.1 p.2} where
  toFun p := ⟨(p.1,(p.2,value p.1 p.2)),rfl⟩
  invFun p := (p.val.1,p.val.2.1)
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext rfl (Prod.ext rfl p.property))

lemma row_card [Fintype F] (a : Rows F) : Nat.card {p // incidence a p} = Nat.card F :=
  (Nat.card_congr (rowEquiv a)).symm

lemma column_card [Fintype F] (p : Cols F) : Nat.card {a // incidence a p} = (Nat.card F)^2 := by
  rw [← Nat.card_congr (columnEquiv p),Nat.card_prod,pow_two]

lemma edges_card [Fintype F] :
    Nat.card {p : Rows F × Cols F // incidence p.1 p.2} = (Nat.card F)^4 := by
  rw [← Nat.card_congr (edgeEquiv (F := F))]
  simp only [Rows,Nat.card_prod]
  ring

/-- With distinct evaluation parameters, the quadratic coefficient is free. -/
lemma codegree_lower [Fintype F] (p q : Cols F) (hpq : p.1 ≠ q.1) :
    Nat.card F ≤ codegree incidence p q := by
  let lin (c : F) := (p.2-q.2-c*(p.1^2-q.1^2))/(p.1-q.1)
  let f : F → {a : Rows F // incidence a p ∧ incidence a q} := fun c =>
    ⟨(p.2-lin c*p.1-c*p.1^2,lin c,c),by dsimp [incidence,value]; ring,by
      dsimp [incidence,value,lin]
      field_simp [sub_ne_zero.mpr hpq]
      ring⟩
  have hf : Function.Injective f := by
    intro c d hh
    exact congrArg (fun a : {a : Rows F // incidence a p ∧ incidence a q} => a.val.2.2) hh
  exact Nat.card_le_card_of_injective f hf

noncomputable def lightCount [Fintype F] : ℕ :=
  Nat.card {p : Cols F × Cols F // codegree incidence p.1 p.2 ≤ 2}

lemma light_card_le [Fintype F] (hF : 3 ≤ Nat.card F) : lightCount (F := F) ≤ (Nat.card F)^3 := by
  classical
  let T := {p : Cols F × Cols F // codegree incidence p.1 p.2 ≤ 2}
  have ht (p : T) : p.val.1.1 = p.val.2.1 := by
    by_contra hh
    have hc := codegree_lower p.val.1 p.val.2 hh
    have hp := p.property
    omega
  let f : T → F × F × F := fun p => (p.val.1.1,p.val.1.2,p.val.2.2)
  have hf : Function.Injective f := by
    intro p q hh
    apply Subtype.ext
    have h1 := congrArg Prod.fst hh
    have h2 := congrArg (fun z : F × F × F => z.2.1) hh
    have h3 := congrArg (fun z : F × F × F => z.2.2) hh
    exact Prod.ext (Prod.ext h1 h2) (Prod.ext ((ht p).symm.trans (h1.trans (ht q))) h3)
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [lightCount,T,Nat.card_prod,pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using hc

noncomputable def pairCount {A B : Type*} (R : A → B → Prop) : ℕ :=
  Nat.card {p : B × B // codegree R p.1 p.2 ≤ 2}

lemma exists_capped_counterexample (N : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop) (r S : ℕ),
      0 < r ∧ ¬ HasAlmost33 R ∧
      (∀ a, Nat.card {b // R a b} = r) ∧
      (∀ b, Nat.card {a // R a b} = Nat.card B) ∧
      Nat.card A ≤ (Nat.card B)^2 ∧ Nat.card A ≤ S^2 ∧ pairCount R ≤ S^2 ∧
      N*(Nat.card A+Nat.card B*S) < Nat.card {p : A × B // R p.1 p.2} := by
  classical
  obtain ⟨q,hq,hprime⟩ := Nat.exists_infinite_primes ((10*N+10)^2)
  haveI : Fact q.Prime := ⟨hprime⟩
  have hq3 : 3 ≤ q := by
    have hmin : 10 ≤ 10*N+10 := by omega
    nlinarith only [hq,hmin]
  have hqpos : 0 < q := by omega
  let t := Nat.sqrt q
  have ht : 10*N+10 ≤ t := Nat.le_sqrt.mpr (by nlinarith only [hq])
  have ht2 : t^2 ≤ q := by simpa only [pow_two] using Nat.sqrt_le q
  have htq : q ≤ (t+1)^2 := (Nat.lt_succ_sqrt' q).le
  have hNt : N*(t+2) < q := by nlinarith
  let S := q*(t+1)
  have hM : q^3 ≤ (q^2)^2 := by
    calc
      _ ≤ q^3*q := Nat.le_mul_of_pos_right _ hqpos
      _ = _ := by ring
  have hS : q^3 ≤ S^2 := by
    calc
      _ = q^2*q := by ring
      _ ≤ q^2*(t+1)^2 := Nat.mul_le_mul_left _ htq
      _ = S^2 := by dsimp [S]; ring
  have hMany : N*(q^3+q^2*S) < q^4 := by
    calc
      _ = (N*(t+2))*q^3 := by dsimp [S]; ring
      _ < q*q^3 := Nat.mul_lt_mul_of_pos_right hNt (by positivity)
      _ = _ := by ring
  have hRows : Nat.card (Rows (ZMod q)) = q^3 := by simp [Rows,pow_succ]; ring
  have hCols : Nat.card (Cols (ZMod q)) = q^2 := by simp [Cols,pow_two]
  have hLight : pairCount (incidence (F := ZMod q)) ≤ q^3 := by
    simpa only [pairCount,lightCount,Nat.card_zmod] using
      light_card_le (F := ZMod q) (by simpa only [Nat.card_zmod] using hq3)
  refine ⟨Rows (ZMod q),Cols (ZMod q),inferInstance,inferInstance,incidence,q,S,
    hqpos,no_almost33,?_,?_,?_,?_,hLight.trans hS,?_⟩
  · intro a
    simpa only [Nat.card_zmod] using row_card a
  · intro b
    simpa only [hCols,Nat.card_zmod] using column_card b
  · simpa only [hRows,hCols] using hM
  · simpa only [hRows] using hS
  · simpa only [hRows,hCols,edges_card,Nat.card_zmod] using hMany

lemma no_capped_unbalanced_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasAlmost33 R → Nat.card A ≤ (Nat.card B)^2 →
      (∀ b, Nat.card {a // R a b} = Nat.card B) →
      (Nat.card {p : A × B // R p.1 p.2} : ℝ) ≤
        C*((Nat.card A : ℝ)+(Nat.card B : ℝ)*Real.sqrt (Nat.card A)) := by
  rintro ⟨C,hC,hBound⟩
  obtain ⟨N,hN⟩ := exists_nat_gt C
  obtain ⟨A,B,instA,instB,R,r,S,hr,hFree,hRow,hCol,hCap,hS,_,hMany⟩ := exists_capped_counterexample N
  have hs : Real.sqrt (Nat.card A) ≤ (S : ℝ) := Real.sqrt_le_iff.mpr
    ⟨by positivity,by exact_mod_cast hS⟩
  have hUpper : (Nat.card {p : A × B // R p.1 p.2} : ℝ) ≤
      (N : ℝ)*((Nat.card A : ℝ)+(Nat.card B : ℝ)*S) := by
    calc
      _ ≤ C*((Nat.card A : ℝ)+(Nat.card B : ℝ)*Real.sqrt (Nat.card A)) := hBound A B R hFree hCap hCol
      _ ≤ C*((Nat.card A : ℝ)+(Nat.card B : ℝ)*S) := mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))) hC.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hN.le (by positivity)
  have hLower : (N : ℝ)*((Nat.card A : ℝ)+(Nat.card B : ℝ)*S) <
      (Nat.card {p : A × B // R p.1 p.2} : ℝ) := by exact_mod_cast hMany
  exact (not_lt_of_ge hUpper) hLower

lemma no_capped_weighted_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasAlmost33 R → Nat.card A ≤ (Nat.card B)^2 →
      (∀ b, Nat.card {a // R a b} = Nat.card B) →
      (Nat.card {p : A × B // R p.1 p.2} : ℝ) ≤
        C*((Nat.card A : ℝ)+(Nat.card B : ℝ)*Real.sqrt (pairCount R)) := by
  rintro ⟨C,hC,hBound⟩
  obtain ⟨N,hN⟩ := exists_nat_gt C
  obtain ⟨A,B,instA,instB,R,r,S,hr,hFree,hRow,hCol,hCap,_,hS,hMany⟩ := exists_capped_counterexample N
  have hs : Real.sqrt (pairCount R) ≤ (S : ℝ) := Real.sqrt_le_iff.mpr
    ⟨by positivity,by exact_mod_cast hS⟩
  have hUpper : (Nat.card {p : A × B // R p.1 p.2} : ℝ) ≤
      (N : ℝ)*((Nat.card A : ℝ)+(Nat.card B : ℝ)*S) := by
    calc
      _ ≤ C*((Nat.card A : ℝ)+(Nat.card B : ℝ)*Real.sqrt (pairCount R)) := hBound A B R hFree hCap hCol
      _ ≤ C*((Nat.card A : ℝ)+(Nat.card B : ℝ)*S) := mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))) hC.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hN.le (by positivity)
  have hLower : (N : ℝ)*((Nat.card A : ℝ)+(Nat.card B : ℝ)*S) <
      (Nat.card {p : A × B // R p.1 p.2} : ℝ) := by exact_mod_cast hMany
  exact (not_lt_of_ge hUpper) hLower

#print axioms eq_of_three_values
#print axioms no_K23
#print axioms no_almost33
#print axioms column_card
#print axioms edges_card
#print axioms light_card_le
#print axioms exists_capped_counterexample
#print axioms no_capped_unbalanced_bound
#print axioms no_capped_weighted_bound
end Erdos713QuadraticLocal
