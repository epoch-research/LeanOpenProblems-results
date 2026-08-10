import FormalConjectures.Util.ProblemImports
open List Nat
private def run_lengths_nat : List ℕ → List ℕ
  | [] => []
  | l@(h :: _) =>
    let run_prefix := l.takeWhile (fun x => x = h)
    let rest := l.drop run_prefix.length
    run_prefix.length :: run_lengths_nat rest
termination_by l => l.length
def nruns (L : List ℕ) : ℕ := (run_lengths_nat L).length
@[simp] theorem nruns_nil : nruns [] = 0 := by simp [nruns, run_lengths_nat]
theorem nruns_dup (a:ℕ)(t:List ℕ) : nruns (a::a::t) = nruns (a::t) := by
  unfold nruns
  conv_lhs => rw [run_lengths_nat]
  conv_rhs => rw [run_lengths_nat]
  have htw : ((a::a::t).takeWhile (fun x => x = a)).length
           = ((a::t).takeWhile (fun x => x = a)).length + 1 := by
    rw [List.takeWhile_cons]; simp [Nat.add_comm]
  have hrest : (a::a::t).drop ((a::a::t).takeWhile (fun x => x = a)).length
             = (a::t).drop ((a::t).takeWhile (fun x => x = a)).length := by
    rw [htw, List.drop_succ_cons]
  simp only [List.length_cons, hrest]
theorem nruns_neq (a b:ℕ)(t:List ℕ)(hab : a ≠ b) : nruns (a::b::t) = nruns (b::t) + 1 := by
  unfold nruns
  conv_lhs => rw [run_lengths_nat]
  have htw : (a::b::t).takeWhile (fun x => x = a) = [a] := by
    rw [List.takeWhile_cons, List.takeWhile_cons]
    have hba : ¬ (b = a) := fun h => hab h.symm
    simp [hba]
  rw [htw]; simp [List.length_cons]
theorem nruns_cons2 (a b : ℕ) (t : List ℕ) :
    nruns (a :: b :: t) = nruns (b :: t) + (if a = b then 0 else 1) := by
  by_cases hab : a = b
  · subst hab; rw [nruns_dup]; simp
  · rw [nruns_neq a b t hab]; simp [hab]

theorem nruns_cons_pos (a:ℕ)(t:List ℕ) : 1 ≤ nruns (a::t) := by
  unfold nruns
  rw [run_lengths_nat]; simp

theorem nruns_singleton (x:ℕ) : nruns [x] = 1 := by
  simp [nruns, run_lengths_nat]

theorem nruns_append_cons (b : ℕ) (B : List ℕ) : ∀ (A : List ℕ) (hA : A ≠ []),
    nruns (A ++ b :: B) = nruns A + nruns (b :: B) - (if A.getLast hA = b then 1 else 0) := by
  intro A
  induction A with
  | nil => intro hA; exact absurd rfl hA
  | cons a A' ih =>
    intro _
    cases A' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.getLast_singleton]
      rw [nruns_cons2 a b B, nruns_singleton a]
      have := nruns_cons_pos b B
      by_cases hab : a = b <;> simp [hab] <;> omega
    | cons a2 A'' =>
      have hne : (a2 :: A'') ≠ [] := by simp
      have hcons : (a :: a2 :: A'') ++ b :: B = a :: ((a2 :: A'') ++ b :: B) := rfl
      rw [hcons]
      have hform : (a2 :: A'') ++ b :: B = a2 :: (A'' ++ b :: B) := rfl
      rw [hform, nruns_cons2 a a2 (A'' ++ b :: B), ← hform, ih hne]
      rw [nruns_cons2 a a2 A'']
      have hlast : (a :: a2 :: A'').getLast (by simp) = (a2 :: A'').getLast hne := by
        rw [List.getLast_cons]
      rw [hlast]
      have h1 := nruns_cons_pos a2 A''
      have h2 := nruns_cons_pos b B
      by_cases hg : (a2 :: A'').getLast hne = b <;>
        by_cases hab : a = a2 <;> simp [hg, hab] <;> omega
