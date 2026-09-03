import FormalConjecturesUtil
import Submission.ThetaGram

/-! Counting the fixed-Gram construction. The auxiliary oriented unbalanced
square-root bound is false. This does not negate the main conjecture. -/
open Finset
namespace Erdos713ThetaGram
set_option maxHeartbeats 2000000

abbrev NatCoeffs (d N : ℕ) := Fin 3 → Fin d → Fin N

def toReal {d N : ℕ} (f : NatCoeffs d N) : Coeffs (Fin d) :=
  fun i v => (f i v).val

lemma toReal_injective (d N : ℕ) : Function.Injective (toReal (d := d) (N := N)) := by
  intro f g h
  funext i v
  apply Fin.ext
  have hh := congr_fun (congr_fun h i) v
  change ((f i v).val : ℝ) = ((g i v).val : ℝ) at hh
  exact_mod_cast hh

abbrev GramCode (d N : ℕ) := Fin 3 × Fin 3 → Fin (d*N^2+1)

def gramCode {d N : ℕ} (f : NatCoeffs d N) : GramCode d N := fun p =>
  ⟨∑ v, (f p.1 v).val*(f p.2 v).val, by
    have hh : (∑ v, (f p.1 v).val*(f p.2 v).val) ≤ d*N^2 := by
      calc
        _ ≤ ∑ _ : Fin d, N*N := sum_le_sum (fun v _ => Nat.mul_le_mul (f p.1 v).isLt.le (f p.2 v).isLt.le)
        _ = _ := by simp [pow_two]
    omega⟩

lemma sameGram_of_code_eq {d N : ℕ} {f g : NatCoeffs d N}
    (h : gramCode f = gramCode g) : SameGram (toReal f) (toReal g) := by
  intro i j
  have hh := congrArg Fin.val (congr_fun h (i,j))
  change (∑ v, (f i v).val*(f j v).val) = ∑ v, (g i v).val*(g j v).val at hh
  change (∑ v, ((f i v).val : ℝ)*((f j v).val : ℝ)) =
    ∑ v, ((g i v).val : ℝ)*((g j v).val : ℝ)
  exact_mod_cast hh

abbrev ColBound (r N : ℕ) := (1+r+r^2)*N
abbrev Columns (d r N : ℕ) := Fin r × (Fin d → Fin (ColBound r N))

def evalFin {d r N : ℕ} (f : NatCoeffs d N) (i : Fin r) : Fin d → Fin (ColBound r N) := fun v =>
  ⟨(f 0 v).val + (i.val+1)*(f 1 v).val + (i.val+1)^2*(f 2 v).val, by
    have hi : i.val+1 ≤ r := i.isLt
    have h1 := Nat.mul_le_mul hi (f 1 v).isLt.le
    have h2 := Nat.mul_le_mul (Nat.pow_le_pow_left hi 2) (f 2 v).isLt.le
    have h0 := (f 0 v).isLt
    dsimp only [ColBound]
    nlinarith⟩

def colToReal {d r N : ℕ} (b : Columns d r N) : Fin r × (Fin d → ℝ) :=
  (b.1,fun v => (b.2 v).val)

lemma colToReal_injective (d r N : ℕ) : Function.Injective (colToReal (d := d) (r := r) (N := N)) := by
  intro b c h
  have hfst : b.1 = c.1 := by
    simpa only [colToReal] using congrArg Prod.fst h
  refine Prod.ext hfst ?_
  funext v
  apply Fin.ext
  have hh := congr_fun (congrArg Prod.snd h) v
  change ((b.2 v).val : ℝ) = ((c.2 v).val : ℝ) at hh
  exact_mod_cast hh

lemma eval_toReal {d r N : ℕ} (f : NatCoeffs d N) (i : Fin r) :
    eval (toReal f) ((i.val : ℝ)+1) = fun v => ((evalFin f i v).val : ℝ) := by
  funext v
  simp [eval,toReal,evalFin]

abbrev Fiber {d N : ℕ} (g : GramCode d N) := {f : NatCoeffs d N // gramCode f = g}

def incidence {d r N : ℕ} (g : GramCode d N) (a : Fiber g) (b : Columns d r N) : Prop :=
  evalFin a.val b.1 = b.2

lemma incidence_real {d r N : ℕ} (g : GramCode d N) {a : Fiber g} {b : Columns d r N}
    (h : incidence g a b) :
    eval (toReal a.val) ((b.1.val : ℝ)+1) = (colToReal b).2 := by
  rw [eval_toReal]
  change (fun v => ((evalFin a.val b.1 v).val : ℝ)) = _
  change evalFin a.val b.1 = b.2 at h
  rw [h]
  rfl

lemma incidence_no_theta {d r N : ℕ} (g : GramCode d N) :
    ¬ HasTheta (incidence (r := r) g) := by
  have hno := no_theta_of_gram (fun a : Fiber g => toReal a.val)
    ((toReal_injective d N).comp Subtype.val_injective)
    (fun a b => sameGram_of_code_eq (a.prop.trans b.prop.symm))
    (fun i : Fin r => (i.val : ℝ)+1) (by
      intro i j h
      apply Fin.ext
      have hh : (i.val : ℝ) = j.val := by linarith
      exact_mod_cast hh)
  rintro ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩
  apply hno
  refine ⟨a,colToReal ∘ b,ha,(colToReal_injective d r N).comp hb,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | exact incidence_real g h00
    | exact incidence_real g h10
    | exact incidence_real g h01
    | exact incidence_real g h11
    | exact incidence_real g h02
    | exact incidence_real g h22
    | exact incidence_real g h13
    | exact incidence_real g h23

noncomputable def rowEquiv {d r N : ℕ} (g : GramCode d N) (a : Fiber g) :
    Fin r ≃ {b : Columns d r N // incidence g a b} where
  toFun i := ⟨(i,evalFin a.val i),rfl⟩
  invFun b := b.val.1
  left_inv _ := rfl
  right_inv b := by
    apply Subtype.ext
    exact Prod.ext rfl b.prop

noncomputable def edgeEquiv {d r N : ℕ} (g : GramCode d N) :
    (Fiber g × Fin r) ≃ {p : Fiber g × Columns d r N // incidence g p.1 p.2} where
  toFun p := ⟨(p.1,(p.2,evalFin p.1.val p.2)),rfl⟩
  invFun p := (p.val.1,p.val.2.1)
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl (Prod.ext rfl p.prop)

lemma row_card {d r N : ℕ} (g : GramCode d N) (a : Fiber g) :
    Nat.card {b : Columns d r N // incidence g a b} = r := by
  rw [← Nat.card_congr (rowEquiv g a),Nat.card_fin]

lemma edge_card {d r N : ℕ} (g : GramCode d N) :
    Nat.card {p : Fiber g × Columns d r N // incidence g p.1 p.2} = Nat.card (Fiber g)*r := by
  rw [← Nat.card_congr (edgeEquiv (r := r) g),Nat.card_prod,Nat.card_fin]

lemma count_gap {N r A L : ℕ} (hN : 0 < N) (hBig : 20^9*L*r^2*A^38 < N) :
    (19*N^2+1)^9 * (L*(r*(A*N)^19)^2) < (N^19)^3 := by
  have h1 : 1 ≤ N^2 := Nat.one_le_pow _ _ hN
  have hg : (19*N^2+1)^9 ≤ 20^9*N^18 := by
    calc
      _ ≤ (20*N^2)^9 := Nat.pow_le_pow_left (by omega) 9
      _ = _ := by ring
  calc
    _ ≤ (20^9*N^18)*(L*(r*(A*N)^19)^2) := Nat.mul_le_mul_right _ hg
    _ = (20^9*L*r^2*A^38)*N^56 := by ring
    _ < N*N^56 := Nat.mul_lt_mul_of_pos_right hBig (Nat.pow_pos hN)
    _ = _ := by ring

lemma exists_large_fiber (r L : ℕ) :
    ∃ (N : ℕ) (g : GramCode 19 N), 0 < N ∧
      L*(Fintype.card (Columns 19 r N))^2 < Fintype.card (Fiber g) := by
  classical
  let N := 20^9*L*r^2*(1+r+r^2)^38+1
  have hN : 0 < N := by dsimp [N]; omega
  have hBig : 20^9*L*r^2*(1+r+r^2)^38 < N := by dsimp [N]; omega
  have hh := count_gap (r := r) (A := 1+r+r^2) hN hBig
  have hCount : Fintype.card (GramCode 19 N) * (L*(Fintype.card (Columns 19 r N))^2) <
      Fintype.card (NatCoeffs 19 N) := by
    simpa only [GramCode,Columns,NatCoeffs,Fintype.card_fun,Fintype.card_prod,Fintype.card_fin,
      ColBound] using hh
  obtain ⟨g,hg⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (gramCode (d := 19) (N := N)) hCount
  refine ⟨N,g,hN,?_⟩
  simpa only [Fiber,Fintype.card_subtype] using hg

lemma exists_oriented_counterexamples (r L : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ L*(Nat.card B)^2 < Nat.card A ∧
      (∀ a, Nat.card {b // R a b} = r) ∧
      Nat.card {p : A × B // R p.1 p.2} = Nat.card A*r := by
  classical
  obtain ⟨N,g,hN,hg⟩ := exists_large_fiber r L
  refine ⟨Fiber g,Columns 19 r N,inferInstance,inferInstance,incidence g,
    incidence_no_theta g,?_,row_card g,edge_card g⟩
  simpa only [Nat.card_eq_fintype_card] using hg

lemma no_unbalanced_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R →
        (Nat.card {p : A × B // R p.1 p.2} : ℝ) ≤
          C*((Nat.card A : ℝ)+(Nat.card B : ℝ)*Real.sqrt (Nat.card A)) := by
  rintro ⟨C,hC,hBound⟩
  obtain ⟨r,hr⟩ := exists_nat_gt (2*C)
  obtain ⟨A,B,instA,instB,R,hFree,hLarge,hRow,hEdges⟩ := exists_oriented_counterexamples r 1
  have hm : 0 < Nat.card A := by nlinarith
  have hmr : (0 : ℝ) < Nat.card A := by exact_mod_cast hm
  have hk : (Nat.card B : ℝ)^2 < Nat.card A := by exact_mod_cast (by simpa using hLarge)
  have hs : (Nat.card B : ℝ) < Real.sqrt (Nat.card A) :=
    (Real.lt_sqrt (Nat.cast_nonneg _)).mpr hk
  have hks : (Nat.card B : ℝ)*Real.sqrt (Nat.card A) ≤ Nat.card A := by
    have hh := mul_le_mul_of_nonneg_right hs.le (Real.sqrt_nonneg (Nat.card A))
    simpa only [← pow_two,Real.sq_sqrt hmr.le] using hh
  have hu := hBound A B R hFree
  rw [hEdges,Nat.cast_mul] at hu
  have hl := mul_lt_mul_of_pos_right hr hmr
  have hc := mul_le_mul_of_nonneg_left hks hC.le
  nlinarith

#print axioms no_unbalanced_bound

#print axioms incidence_no_theta
#print axioms exists_oriented_counterexamples
end Erdos713ThetaGram
