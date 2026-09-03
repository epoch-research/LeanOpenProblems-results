import Submission.No9Rounding

/-! Soundness of the rounded geometric interpolation operator. -/
namespace Erdos7No9Certificate
open scoped BigOperators
open Erdos7KilledSieve
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

def gridIndex (j : ℕ) : Fin nodes := ⟨j % nodes,Nat.mod_lt _ nodes_pos⟩
lemma gridIndex_val (j : ℕ) (hj : j < nodes) : (gridIndex j).val=j := Nat.mod_eq_of_lt hj

def cellLo (g : ℕ) (j : Fin nodes) : Fin nodes := gridIndex (cells (g+2) j.val).lo
def cellHi (g : ℕ) (j : Fin nodes) : Fin nodes := gridIndex ((cells (g+2) j.val).lo+1)
def gridZero : Fin nodes := ⟨0,nodes_pos⟩

lemma cell_geometry (d j : ℕ) (hd : 0 < d) (v : Cell) (hv : CellValid d j v) :
    (grid v.lo:ℚ) < grid (v.lo+1) ∧
    (grid v.lo:ℚ) ≤ (grid j:ℚ)/d ∧ (grid j:ℚ)/d ≤ grid (v.lo+1) := by
  rcases hv with ⟨hlo,hw,hwidth,hleft,hright⟩
  have hdQ : (0:ℚ) < d := by exact_mod_cast hd
  have hwQ : (0:ℚ) < v.width := by exact_mod_cast hw
  have hw' : (grid v.lo:ℚ)+v.width=grid (v.lo+1) := by exact_mod_cast hwidth
  have hl' : (grid j:ℚ)+v.left=d*grid (v.lo+1) := by exact_mod_cast hleft
  have hr' : (d:ℚ)*grid v.lo+v.right=grid j := by exact_mod_cast hright
  refine ⟨by linarith, (le_div_iff₀ hdQ).mpr ?_, (div_le_iff₀ hdQ).mpr ?_⟩
  · nlinarith [Nat.cast_nonneg (α:=ℚ) v.right]
  · nlinarith [Nat.cast_nonneg (α:=ℚ) v.left]

lemma grid_geometry (a : ℕ) (ha : a ≤ 17) (g : ℕ) (hg : g < a) (j : Fin nodes) :
    realGrid (cellLo g j) < realGrid (cellHi g j) ∧
    realGrid (cellLo g j) ≤ realGrid j/(g+2) ∧
    realGrid j/(g+2) ≤ realGrid (cellHi g j) := by
  have hv := cells_valid (g+2) j.val (by omega) (by omega) j.isLt
  have hlo := hv.1
  have hh := cell_geometry (g+2) j.val (by omega) _ hv
  simpa only [realGrid,cellLo,cellHi,gridIndex_val _ (by omega : (cells (g+2) j.val).lo < nodes),
    gridIndex_val _ hlo,Nat.cast_add,Nat.cast_ofNat] using hh

lemma cell_chord (h : ℕ → ℕ) (d j : ℕ) (hd : 0 < d) (v : Cell) (hv : CellValid d j v) :
    gridChord realGrid (gridIndex v.lo) (gridIndex (v.lo+1)) ((grid j:ℚ)/d) (realValues h) =
    ((v.left*h v.lo+v.right*h (v.lo+1):ℕ):ℚ)/((d:ℚ)*v.width*scale) := by
  rcases hv with ⟨hlo,hw,hwidth,hleft,hright⟩
  have hdQ : (d:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hwQ : (v.width:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hw)
  have hsQ : (scale:ℚ)≠0 := ne_of_gt scale_pos
  have hw' : (grid (v.lo+1):ℚ)-grid v.lo=v.width := by
    have hh : (grid v.lo:ℚ)+v.width=grid (v.lo+1) := by exact_mod_cast hwidth
    linarith
  have hl' : (v.left:ℚ)=d*grid (v.lo+1)-grid j := by
    have hh : (grid j:ℚ)+v.left=d*grid (v.lo+1) := by exact_mod_cast hleft
    linarith
  have hr' : (v.right:ℚ)=grid j-d*grid v.lo := by
    have hh : (d:ℚ)*grid v.lo+v.right=grid j := by exact_mod_cast hright
    linarith
  simp only [gridChord,realGrid,realValues,gridIndex_val _ (by omega : v.lo < nodes),
    gridIndex_val _ hlo,Nat.cast_add,Nat.cast_mul,hw']
  rw [hl',hr']
  field_simp
  <;> ring

lemma rounded_cell_term (p A B : ℕ) (hp : 1 < p) (hB : 0 < B)
    (h : ℕ → ℕ) (g : ℕ) (hg : g < 17) (j : Fin nodes) :
    ((A:ℚ)/B)*(p-1)*((p:ℚ)⁻¹)^(g+2)*(g+2)*
      gridChord realGrid (cellLo g j) (cellHi g j) (realGrid j/(g+2)) (realValues h) ≤
    (ceilDiv (A*(p-1)*interpNumerator h (g+2) j.val)
      (B*p^(g+2)*(cells (g+2) j.val).width):ℚ)/scale := by
  have hv := cells_valid (g+2) j.val (by omega) (by omega) j.isLt
  have hw := hv.2.1
  have hpQ : (p:ℚ)≠0 := by exact_mod_cast (by omega : p≠0)
  have hBq : (B:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hdQ : ((g:ℚ)+2)≠0 := by positivity
  have hwQ : ((cells (g+2) j.val).width:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hw)
  have hh := cell_chord h (g+2) j.val (by omega) _ hv
  simp only [Nat.cast_add,Nat.cast_ofNat] at hh
  change _*gridChord realGrid (gridIndex _) (gridIndex _) ((grid j.val:ℚ)/(g+2)) _ ≤ _
  rw [hh]
  have hr := div_le_div_of_nonneg_right
    (ceilDiv_bound (A*(p-1)*interpNumerator h (g+2) j.val)
      (B*p^(g+2)*(cells (g+2) j.val).width) (by positivity)) scale_pos.le
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_sub (by omega : 1 ≤ p),Nat.cast_one] at hr
  convert hr using 1
  dsimp [interpNumerator]
  simp only [Nat.cast_add,Nat.cast_mul,inv_pow]
  field_simp
  <;> ring

lemma foldl_range_add (f : ℕ → ℕ) (n : ℕ) :
    (List.range n).foldl (fun v g => v+f g) 0=∑ g∈Finset.range n,f g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,
      ih,Finset.sum_range_succ]

lemma rounded_tail_term (p R A B : ℕ) (hp : 1 < p) (hB : 0 < B) (h : ℕ → ℕ) :
    ((A:ℚ)/B)*((p:ℚ)⁻¹)^R*((R+1)+1/(p-1))*realValues h gridZero ≤
      (ceilDiv (A*((R+1)*(p-1)+1)*h 0) (B*p^R*(p-1)):ℚ)/scale := by
  have hpQ : (p:ℚ)≠0 := by exact_mod_cast (by omega : p≠0)
  have hp1 : (p:ℚ)-1≠0 := by
    have hh : (1:ℚ) < p := by exact_mod_cast hp
    linarith
  have hpNat : 0 < p-1 := by omega
  have hBq : (B:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hh := div_le_div_of_nonneg_right
    (ceilDiv_bound (A*((R+1)*(p-1)+1)*h 0) (B*p^R*(p-1)) (by positivity)) scale_pos.le
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_sub (by omega : 1 ≤ p),Nat.cast_add,Nat.cast_one] at hh
  convert hh using 1
  dsimp [realValues,gridZero]
  simp only [inv_pow]
  field_simp

noncomputable def realOperator (p R A B : ℕ) : Module.End ℚ (Fin nodes → ℚ) :=
  geometricGridOperator realGrid gridZero cellLo cellHi p (R-1) ((A:ℚ)/B)

lemma realOperator_monotone (p R A B : ℕ) (hp : 1 < p) (hR : R ≤ 18) :
    Monotone (realOperator p R A B) := by
  apply geometricGridOperator_monotone _ _ _ _ _ _ hp _ (by positivity)
  exact grid_geometry (R-1) (by omega)

lemma realOperator_one (p R A B : ℕ) (hp : 1 < p) (hR : R ≤ 18) :
    realOperator p R A B (fun _ => 1)=fun _ => geometricMeanNorm p ((A:ℚ)/B) := by
  apply geometricGridOperator_one _ _ _ _ _ _ hp
  intro g hg j
  exact (grid_geometry (R-1) (by omega) g hg j).1

lemma rounded_offdiag (p R A B : ℕ) (hp : 1 < p) (hR0 : 1 ≤ R) (hR1 : R ≤ 18)
    (hB : 0 < B) (h : ℕ → ℕ) :
    realOperator p R A B (realValues h) ≤ realValues (offdiag p R A B h) := by
  intro j
  change (∑ g∈Finset.range (R-1), ((A:ℚ)/B)*(p-1)*((p:ℚ)⁻¹)^(g+2)*(g+2)*
      gridChord realGrid (cellLo g j) (cellHi g j) (realGrid j/(g+2)) (realValues h))+
      ((A:ℚ)/B)*((p:ℚ)⁻¹)^(R-1+1)*(((R-1:ℕ):ℚ)+2+1/(p-1))*realValues h gridZero ≤ _
  have hRs : R-1+1=R := by omega
  have hRc : ((R-1:ℕ):ℚ)+2=(R:ℚ)+1 := by
    have hh : ((R-1:ℕ):ℚ)+1=R := by exact_mod_cast hRs
    linarith
  rw [hRs,hRc]
  dsimp only [realValues,offdiag]
  rw [foldl_range_add,Nat.cast_add,Nat.cast_sum,add_div,Finset.sum_div]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro g hg
    exact rounded_cell_term p A B hp hB h g (by have := Finset.mem_range.mp hg; omega) j
  · exact rounded_tail_term p R A B hp hB h

lemma rounded_diagonal (p A B : ℕ) (hp : 0 < p) (hB : 0 < B) (hA : A ≤ B*p)
    (h : ℕ → ℕ) (j : Fin nodes) :
    (1-((A:ℚ)/B)/p)*realValues h j ≤ (ceilDiv ((B*p-A)*h j.val) (B*p):ℚ)/scale := by
  have hpQ : (p:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hBq : (B:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hh := rounded_mul_bound (realValues h j) (h j.val) (B*p-A) (B*p) (by positivity) le_rfl
  simp only [Nat.cast_sub hA,Nat.cast_mul] at hh
  convert hh using 1
  field_simp

lemma rounded_rawValue (a : PrefixControl) (hp : 1 < a.p) (hp3 : a.p≠3)
    (hB : 0 < a.B) (hA : a.A ≤ a.B*a.p) (hR0 : 1 ≤ a.R) (hR1 : a.R ≤ 18)
    (h : ℕ → ℕ) :
    (fun j => (1-((a.A:ℚ)/a.B)/a.p)*realValues h j+
      realOperator a.p a.R a.A a.B (realValues h) j) ≤ realValues (rawValue a h) := by
  intro j
  have hh := add_le_add (rounded_diagonal a.p a.A a.B (by omega) hB hA h j)
    (rounded_offdiag a.p a.R a.A a.B hp hR0 hR1 hB h j)
  simpa only [rawValue,if_neg hp3,realValues,Nat.cast_add,add_div] using hh

#print axioms cell_chord
#print axioms rounded_offdiag
#print axioms rounded_rawValue
end Erdos7No9Certificate
