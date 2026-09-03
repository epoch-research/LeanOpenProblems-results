import Submission.LinearOrbitObstruction

/-! Finite substitutions cannot generate the increments of an injective
Gaussian-prime path. The obstruction is an integer-linear orbit of prefix
sums, and does not settle the existence of arbitrary bounded-step paths. -/
namespace Erdos952Investigation
namespace MorphicIncrementObstruction

open LinearOrbitObstruction
set_option maxHeartbeats 0

variable {ι : Type*}

/-- The image of a letter under the n-th iterate of a substitution. -/
def word (σ : ι → List ι) : ℕ → ι → List ι
  | 0, a => [a]
  | n+1, a => (σ a).flatMap (word σ n)

lemma sum_map_flatMap {G : Type*} [AddMonoid G]
    (L : List ι) (f : ι → List G) :
    (L.flatMap f).sum = (L.map (fun a => (f a).sum)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

abbrev States (ι : Type*) := (ι → ℤ) × (ι → ℤ)

def transitionMap (σ : ι → List ι) : States ι →ₗ[ℤ] States ι where
  toFun v := (fun a => ((σ a).map v.1).sum, fun a => ((σ a).map v.2).sum)
  map_add' v w := by ext a <;> simp [Pi.add_def,List.sum_map_add]
  map_smul' c v := by ext a <;> simp [Pi.mul_def,List.sum_map_mul_left]

def observe (a : ι) : States ι →ₗ[ℤ] GaussianInt where
  toFun v := ⟨v.1 a,v.2 a⟩
  map_add' v w := by apply Zsqrtd.ext <;> rfl
  map_smul' c v := by apply Zsqrtd.ext <;> simp [zsmul_eq_mul]

def state (σ : ι → List ι) (code : ι → GaussianInt) (n : ℕ) : States ι :=
  (fun a => ((word σ n a).map (fun b => (code b).re)).sum,
    fun a => ((word σ n a).map (fun b => (code b).im)).sum)

lemma state_step (σ : ι → List ι) (code : ι → GaussianInt) (n : ℕ) :
    state σ code (n+1) = transitionMap σ (state σ code n) := by
  apply Prod.ext <;> funext a <;>
    simp only [state,word,List.map_flatMap,sum_map_flatMap,transitionMap,
      LinearMap.coe_mk,AddHom.coe_mk]

lemma state_pow (σ : ι → List ι) (code : ι → GaussianInt) (n : ℕ) :
    state σ code n = (transitionMap σ ^ n) (state σ code 0) := by
  induction n with
  | zero => simp
  | succ n ih => rw [state_step,ih,pow_succ',Module.End.mul_apply]

lemma observe_state (σ : ι → List ι) (code : ι → GaussianInt) (n : ℕ) (a : ι) :
    observe a (state σ code n) = ((word σ n a).map code).sum := by
  change (⟨((word σ n a).map (fun b => (code b).re)).sum,
    ((word σ n a).map (fun b => (code b).im)).sum⟩ : GaussianInt) = _
  generalize word σ n a = L
  induction L with
  | nil => apply Zsqrtd.ext <;> simp
  | cons b L ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [show (⟨(code b).re+(L.map (fun c => (code c).re)).sum,
        (code b).im+(L.map (fun c => (code c).im)).sum⟩ : GaussianInt) =
        code b+⟨(L.map (fun c => (code c).re)).sum,
          (L.map (fun c => (code c).im)).sum⟩ by rfl,ih]

lemma sum_increments (x : ℕ → GaussianInt) (L : ℕ) :
    ((List.range L).map (fun j => x (j+1)-x j)).sum = x L-x 0 := by
  induction L with
  | zero => simp
  | succ L ih => simp only [List.range_succ,List.map_append,List.sum_append,
      List.map_singleton,List.sum_singleton,ih]; abel

/-- Arbitrary finite substitutions, with distinct prefix lengths, cannot
encode the increments of an injective prime sequence. -/
theorem no_substitution_prefixes [Fintype ι]
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (σ : ι → List ι) (code : ι → GaussianInt) (a : ι)
    (hlen : Function.Injective (fun n => (word σ n a).length)) :
    ¬ ∀ n, (word σ n a).map code =
      (List.range (word σ n a).length).map (fun j => x (j+1)-x j) := by
  intro hprefix
  have hrep (n : ℕ) : x (word σ n a).length =
      x 0+observe a ((transitionMap σ ^ n) (state σ code 0)) := by
    rw [← state_pow,observe_state,hprefix,sum_increments]
    abel
  apply no_prime_linear_orbit (transitionMap σ) (observe a) (state σ code 0) (x 0)
  constructor
  · intro i j he
    apply hlen
    apply hx
    simpa only [hrep] using he
  · intro n
    rw [← hrep n]
    exact hp _

lemma word_step_left (σ : ι → List ι) (n : ℕ) (a : ι) :
    word σ (n+1) a = (word σ n a).flatMap σ := by
  induction n generalizing a with
  | zero => simp [word]
  | succ n ih =>
    change (σ a).flatMap (word σ (n+1)) = ((σ a).flatMap (word σ n)).flatMap σ
    rw [List.flatMap_assoc]
    congr 1
    funext b
    exact ih b

lemma word_prefix_succ (σ : ι → List ι) (a : ι) (tail : List ι)
    (hstart : σ a = a :: tail) (n : ℕ) :
    word σ n a <+: word σ (n+1) a := by
  rw [word,hstart,List.flatMap_cons]
  exact List.prefix_append _ _

/-- Prolongability and unbounded growth force strictly increasing lengths,
even if the substitution is allowed to erase other letters. -/
lemma word_length_strictMono (σ : ι → List ι) (a : ι) (tail : List ι)
    (hstart : σ a = a :: tail)
    (hgrow : ∀ L : ℕ, ∃ n : ℕ, L < (word σ n a).length) :
    StrictMono (fun n => (word σ n a).length) := by
  have hmono : Monotone (fun n => (word σ n a).length) :=
    monotone_nat_of_le_succ (fun n => (word_prefix_succ σ a tail hstart n).length_le)
  apply strictMono_nat_of_lt_succ
  intro n
  by_contra hn
  have hlen : (word σ n a).length = (word σ (n+1) a).length := by
    have hh : (word σ n a).length ≤ (word σ (n+1) a).length := hmono (Nat.le_succ n)
    omega
  have heq : word σ (n+1) a = word σ n a :=
    ((word_prefix_succ σ a tail hstart n).eq_of_length hlen).symm
  have hconst (k : ℕ) : word σ (n+k) a = word σ n a := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.add_succ,word_step_left,ih,← word_step_left,heq]
  obtain ⟨m,hm⟩ := hgrow (word σ n a).length
  by_cases hmn : m ≤ n
  · have hh : (word σ m a).length ≤ (word σ n a).length := hmono hmn
    omega
  · have hh := hconst (m-n)
    rw [Nat.add_sub_of_le (by omega : n ≤ m)] at hh
    rw [hh] at hm
    omega

/-- A growing prolongable substitution cannot describe arbitrarily long
increment prefixes of an injective Gaussian-prime sequence. Erasing
substitutions are included, provided their initial letter grows unboundedly. -/
theorem no_growing_substitution_prefixes [Fintype ι]
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (σ : ι → List ι) (code : ι → GaussianInt) (a : ι) (tail : List ι)
    (hstart : σ a = a :: tail)
    (hgrow : ∀ L : ℕ, ∃ n : ℕ, L < (word σ n a).length) :
    ¬ ∀ n, (word σ n a).map code =
      (List.range (word σ n a).length).map (fun j => x (j+1)-x j) := by
  exact no_substitution_prefixes x hx hp σ code a
    (word_length_strictMono σ a tail hstart hgrow).injective

/-- Here a morphic word is the letter-to-letter coding of the infinite word
specified by a growing prolongable substitution on a finite alphabet. -/
theorem no_morphic_increments [Fintype ι]
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (σ : ι → List ι) (code : ι → GaussianInt) (a : ι) (tail : List ι)
    (hstart : σ a = a :: tail)
    (hgrow : ∀ L : ℕ, ∃ n : ℕ, L < (word σ n a).length)
    (u : ℕ → ι)
    (hprefix : ∀ n, word σ n a =
      (List.range (word σ n a).length).map u) :
    ¬ ∀ j, x (j+1)-x j = code (u j) := by
  intro hinc
  apply no_growing_substitution_prefixes x hx hp σ code a tail hstart hgrow
  intro n
  have hh := congrArg (List.map code) (hprefix n)
  simpa only [List.map_map,Function.comp_def,← hinc] using hh

#print axioms no_substitution_prefixes
#print axioms word_length_strictMono
#print axioms no_morphic_increments

end MorphicIncrementObstruction
end Erdos952Investigation
