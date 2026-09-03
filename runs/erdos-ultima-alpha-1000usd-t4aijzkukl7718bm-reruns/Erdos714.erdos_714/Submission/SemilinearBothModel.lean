import Submission.SemilinearBothCertificate

/-! The actual guarded matrix graph used by the auxiliary finite certificate. -/

open Matrix SimpleGraph

macro "gf512%" z:term:max n:num : term => do
  let mut out ← `(term| (0 * $z))
  for i in [0:64] do
    if n.getNat.testBit i then
      let p ← `(term| $z ^ $(Lean.quote i))
      out ← `(term| $out + $p)
  return out

macro "mat512%" z:term:max a:num b:num c:num d:num : term =>
  `(term| !![gf512% $z $a, gf512% $z $b; gf512% $z $c, gf512% $z $d])

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos714BothModel

variable {K : Type*} [Field K] [CharP K 2]

abbrev M := Matrix (Fin 2) (Fin 2) K
abbrev U :=  Matrix.GeneralLinearGroup (Fin 2) K

def sigmaM (A : M (K := K)) : M (K := K) := A.map (fun x => x^32)

def semilinearNorm : ℕ → M (K := K) → M (K := K)
  | 0, _ => 1
  | n+1, A => A * semilinearNorm n (sigmaM A)

def trace2 : ℕ → K → K
  | 0, _ => 0
  | n+1, x => (trace2 n x)^2 + x

lemma trace2_as (n : ℕ) (x : K) : trace2 n (x^2+x) = x^(2^n)+x := by
  induction n with
  | zero => simp [trace2, CharTwo.add_self_eq_zero]
  | succ n ih =>
    change (trace2 n (x^2+x))^2 + (x^2+x) = x^(2^(n+1))+x
    rw [ih, add_pow_char _ _ 2, pow_succ]
    ring_nf
    reduce_mod_char!

lemma no_quadratic_root (hK : ∀ x : K, x^512 = x) (t d v : K)
    (ht : t*v = 1) (hd : trace2 9 (d*v^2) = 1) :
    ∀ x : K, x^2+t*x+d ≠ 0 := by
  intro x hx
  have hnorm : (x*v)^2 + x*v = d*v^2 := by
    have ht' : t*x*v^2 = x*v := by calc
      _ = (t*v)*(x*v) := by ring
      _ = _ := by rw [ht, one_mul]
    have he' : (x*v)^2 + x*v + d*v^2 = 0 := by
      calc
        _ = (x^2+t*x+d)*v^2 := by rw [add_mul, add_mul, ht']; ring
        _ = 0 := by rw [hx, zero_mul]
    have := congrArg (fun y : K => y+d*v^2) he'
    simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using this
  have ht0 : trace2 9 (d*v^2) = 0 := by
    rw [← hnorm, trace2_as]
    norm_num only [show (2 : ℕ)^9 = 512 by norm_num]
    rw [hK, CharTwo.add_self_eq_zero]
  exact zero_ne_one (ht0.symm.trans hd)

def elliptic (A : M (K := K)) : Prop := ∀ x : K, x^2+A.trace*x+A.det ≠ 0

def Good (A : M (K := K)) : Prop :=
  (A * sigmaM A).trace = 1 ∧ elliptic A ∧
    semilinearNorm 9 A = 1 ∧ elliptic (A * sigmaM A)

def graph : SimpleGraph (U (K := K) ⊕ U (K := K)) where
  Adj
    | Sum.inl g, Sum.inr h => Good ((↑g⁻¹ : M (K := K)) * (↑h : M (K := K)))
    | Sum.inr h, Sum.inl g => Good ((↑g⁻¹ : M (K := K)) * (↑h : M (K := K)))
    | _, _ => False
  symm := by intro a b; cases a <;> cases b <;> simp
  loopless := by intro a; cases a <;> simp

/-- Two-sided inverse certificates produce actual group vertices. -/
def glOfInv (A B : M (K := K)) (hAB : A*B = 1) (hBA : B*A = 1) : U (K := K) :=
  ⟨A, B, hAB, hBA⟩

omit [CharP K 2] in
theorem copy_of_matrices (R RI C CI : Fin 4 → M (K := K))
    (hR : ∀ i, R i * RI i = 1 ∧ RI i * R i = 1)
    (hC : ∀ i, C i * CI i = 1 ∧ CI i * C i = 1)
    (hiR : Function.Injective R) (hiC : Function.Injective C)
    (hgood : ∀ i j, Good (RI i * C j)) :
    (completeBipartiteGraph (Fin 4) (Fin 4)) ⊑ graph (K := K) := by
  let r (i : Fin 4) := glOfInv (R i) (RI i) (hR i).1 (hR i).2
  let c (i : Fin 4) := glOfInv (C i) (CI i) (hC i).1 (hC i).2
  have hr : Function.Injective r := by
    intro i j h
    exact hiR (congrArg (fun a : U (K := K) => (↑a : M (K := K))) h)
  have hc : Function.Injective c := by
    intro i j h
    exact hiC (congrArg (fun a : U (K := K) => (↑a : M (K := K))) h)
  refine ⟨⟨⟨Sum.map r c, ?_⟩, Sum.map_injective.mpr ⟨hr, hc⟩⟩⟩
  intro i j hij
  cases i with
  | inl i => cases j with
    | inl j => simp at hij
    | inr j => exact hgood i j
  | inr i => cases j with
    | inl j => exact hgood j i
    | inr j => simp at hij

end Erdos714BothModel
