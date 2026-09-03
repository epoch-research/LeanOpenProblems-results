import Submission.DigitLoopPeakExplore
import Submission.Explore
import Submission.TranslateExplore

/-! Ordinary sum peaks in polynomial graphs over square moduli. Nilpotent
increments make a polynomial affine on a residue class. This is a restricted
obstruction, not a negation of the Erdős 66 conjecture. -/
namespace Erdos66PolynomialGraphPeak
open AdditiveCombinatorics Polynomial
open scoped Classical Topology
set_option maxHeartbeats 1800000

noncomputable def graphEncode {M : ℕ} (f : ZMod M → ZMod M) (x : ZMod M) : ℕ :=
  x.val+M*(f x).val

noncomputable def graphSet {M : ℕ} (f : ZMod M → ZMod M) : Set ℕ :=
  Set.range (graphEncode f)

lemma graphEncode_injective {M : ℕ} [NeZero M] (f : ZMod M → ZMod M) :
    Function.Injective (graphEncode f) := by
  intro x y h
  have hh := congrArg (fun n : ℕ ↦ n%M) h
  simp only [graphEncode,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (ZMod.val_lt x),
    Nat.mod_eq_of_lt (ZMod.val_lt y)] at hh
  exact ZMod.val_injective M hh

lemma graphEncode_lt {M : ℕ} [NeZero M] (f : ZMod M → ZMod M) (x : ZMod M) :
    graphEncode f x<M^2 := by
  have hx := ZMod.val_lt x
  have hf := ZMod.val_lt (f x)
  have hM := NeZero.pos M
  dsimp [graphEncode]
  nlinarith

lemma nat_sum_two_lifts {M : ℕ} [NeZero M] (a b s : ZMod M) (he : a+b=s) :
    a.val+b.val=s.val ∨ a.val+b.val=s.val+M := by
  have hm : (a.val+b.val)%M=s.val := by rw [←ZMod.val_add,he]
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have hs := ZMod.val_lt s
  have hd := Nat.mod_add_div (a.val+b.val) M
  have hq : (a.val+b.val)/M<2 := (Nat.div_lt_iff_lt_mul (NeZero.pos M)).mpr (by omega)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hq) with h | h
  · rw [hm,h] at hd
    exact Or.inl (by omega)
  · rw [hm,h] at hd
    exact Or.inr (by omega)

/-- Modular central symmetry leaves at most two ordinary output sums. -/
theorem peak_of_modular_symmetry {M T : ℕ} [NeZero M]
    (f : ZMod M → ZMod M) (x : Fin T → ZMod M) (y : Fin T → ZMod M)
    (hinj : Function.Injective x) (X : ℕ) (s : ZMod M)
    (hX : ∀ i, (x i).val+(y i).val=X)
    (hs : ∀ i, f (x i)+f (y i)=s) :
    ∃ n : ℕ, n<2*M^2 ∧ T/2≤sumRep (graphSet f) n := by
  let S : Finset ℕ := {X+M*s.val,X+M*(s.val+M)}
  let g : Fin T → ℕ := fun i ↦ graphEncode f (x i)+graphEncode f (y i)
  have hg (i : Fin T) : g i∈S := by
    have hi := nat_sum_two_lifts (f (x i)) (f (y i)) s (hs i)
    have he : g i=X+M*((f (x i)).val+(f (y i)).val) := by
      dsimp [g,graphEncode]
      rw [←hX i]
      ring
    rcases hi with hi | hi <;> simp [he,hi,S]
  have hc : S.card≤2 := Finset.card_le_two
  have hnon : S.Nonempty := by simp [S]
  have hcard : S.card*(T/2)≤(Finset.univ : Finset (Fin T)).card := by
    simp only [Finset.card_univ,Fintype.card_fin]
    have hh := Nat.mul_le_mul_right (T/2) hc
    omega
  obtain ⟨n,hn,hfib⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := (Finset.univ : Finset (Fin T))) (t := S) (f := g)
    (fun i _ ↦ hg i) hnon hcard
  by_cases hT : T=0
  · subst T
    refine ⟨0,?_,by simp⟩
    have hM := NeZero.pos M
    positivity
  have hpos : 0<T/2 ∨ T=1 := by omega
  have hrep : T/2≤sumRep (graphSet f) n := by
    apply hfib.trans
    rw [sumRep_def]
    apply Finset.card_le_card_of_injOn (fun i ↦ (graphEncode f (x i),graphEncode f (y i)))
    · intro i hi
      change i∈Finset.univ.filter (fun j : Fin T ↦ g j=n) at hi
      have he := (Finset.mem_filter.mp hi).2
      change (graphEncode f (x i),graphEncode f (y i))∈
        (Finset.antidiagonal n).filter (fun p : ℕ×ℕ ↦ p.1∈graphSet f ∧ p.2∈graphSet f)
      simp only [Finset.mem_filter,Finset.mem_antidiagonal]
      exact ⟨he,⟨x i,rfl⟩,⟨y i,rfl⟩⟩
    · intro i hi j hj he
      exact hinj (graphEncode_injective f (congrArg Prod.fst he))
  rcases hpos with hpos | hpos
  · have hfibpos : 0<(Finset.univ.filter (fun i : Fin T ↦ g i=n)).card := by omega
    obtain ⟨i,hi⟩ := Finset.card_pos.mp hfibpos
    have he := (Finset.mem_filter.mp hi).2
    have h₁ := graphEncode_lt f (x i)
    have h₂ := graphEncode_lt f (y i)
    exact ⟨n,by dsimp [g] at he; omega,hrep⟩
  · subst T
    refine ⟨0,?_,by simp⟩
    have hM := NeZero.pos M
    positivity

lemma square_increment_zero (H : ℕ) : (H : ZMod (H^2))^2=0 := by
  rw [←Nat.cast_pow,ZMod.natCast_self]

/-- Polynomial graphs over Z/(H^2) have a peak at least floor(H/2), below
2 H^4. Even a single residue class of inputs produces the peak. -/
theorem exists_polynomial_graph_peak (H : ℕ) (hH : 0<H)
    (P : Polynomial (ZMod (H^2))) :
    ∃ n : ℕ, n<2*H^4 ∧ H/2≤sumRep (graphSet P.eval) n := by
  letI : NeZero (H^2) := ⟨by positivity⟩
  let x : Fin H → ZMod (H^2) := fun i ↦ ((H*i.val : ℕ):ZMod (H^2))
  let y : Fin H → ZMod (H^2) := fun i ↦ ((H*(H-1-i.val) : ℕ):ZMod (H^2))
  have hxi (i : Fin H) : H*i.val<H^2 := by nlinarith [i.isLt]
  have hyi (i : Fin H) : H*(H-1-i.val)<H^2 := by
    have hh : H-1-i.val<H := by omega
    nlinarith
  have hxval (i : Fin H) : (x i).val=H*i.val := by
    simp only [x,ZMod.val_natCast,Nat.mod_eq_of_lt (hxi i)]
  have hyval (i : Fin H) : (y i).val=H*(H-1-i.val) := by
    simp only [y,ZMod.val_natCast,Nat.mod_eq_of_lt (hyi i)]
  have hxinj : Function.Injective x := by
    intro i j he
    have hh := congrArg ZMod.val he
    rw [hxval, hxval] at hh
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left hH hh)
  have hsum (i : Fin H) : (x i).val+(y i).val=H*(H-1) := by
    rw [hxval,hyval,←Nat.mul_add]
    congr 1
    omega
  have hmodsum (i : Fin H) : x i+y i=((H*(H-1):ℕ):ZMod (H^2)) := by
    have he := congrArg (fun n : ℕ ↦ (n:ZMod (H^2))) (hsum i)
    simpa only [Nat.cast_add,ZMod.natCast_zmod_val] using he
  have hx2 (i : Fin H) : (x i)^2=0 := by
    simp only [x,Nat.cast_mul,mul_pow,square_increment_zero,zero_mul]
  have hy2 (i : Fin H) : (y i)^2=0 := by
    simp only [y,Nat.cast_mul,mul_pow,square_increment_zero,zero_mul]
  have heval (z : ZMod (H^2)) (hz : z^2=0) :
      P.eval z=P.eval 0+P.derivative.eval 0*z := by
    simpa only [zero_add] using P.eval_add_of_sq_eq_zero 0 z hz
  have hs (i : Fin H) : P.eval (x i)+P.eval (y i)=
      2*P.eval 0+P.derivative.eval 0*((H*(H-1):ℕ):ZMod (H^2)) := by
    rw [heval _ (hx2 i),heval _ (hy2 i),←hmodsum i]
    ring
  obtain ⟨n,hn,hr⟩ := peak_of_modular_symmetry P.eval x y hxinj (H*(H-1))
    (2*P.eval 0+P.derivative.eval 0*((H*(H-1):ℕ):ZMod (H^2))) hsum hs
  refine ⟨n,?_,hr⟩
  convert hn using 1 <;> ring

/-- The obstruction survives placing each graph in a new natural annulus;
the old graphs need not be nested or use the same polynomial. -/
theorem no_log_limit_of_polynomial_graph_family (A : Set ℕ)
    (hA : ∀ k : ℕ, ∃ (P : Polynomial (ZMod ((2^(k+1))^2)))
      (L : ℕ), L≤(2^(k+1))^4 ∧ Erdos66Translate.shift (graphSet P.eval) L⊆A) :
    ∀ c : ℝ, ¬Filter.Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n)
      Filter.atTop (𝓝 c) := by
  apply Erdos66DigitLoopPeak.no_log_limit_of_exponential_peaks A 16 64 (by norm_num)
  intro k
  obtain ⟨P,L,hL,hLA⟩ := hA k
  obtain ⟨n,hn,hr⟩ := exists_polynomial_graph_peak (2^(k+1)) (by positivity) P
  have hp : 2^(k+1)/2=2^k := by rw [pow_succ]; exact Nat.mul_div_cancel _ (by norm_num)
  rw [hp] at hr
  have hpow : (2^(k+1))^4=16*16^k := by
    rw [←pow_mul, Nat.mul_comm (k+1) 4, pow_mul, pow_succ]
    norm_num
    ring
  refine ⟨n+2*L,?_,?_⟩
  · rw [hpow] at hn hL
    omega
  · rw [←Erdos66Translate.sumRep_shift (graphSet P.eval) L n] at hr
    exact hr.trans (Erdos66Explore.sumRep_mono hLA _)

end Erdos66PolynomialGraphPeak
