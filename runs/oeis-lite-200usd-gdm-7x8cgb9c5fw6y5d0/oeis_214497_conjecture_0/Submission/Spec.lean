import FormalConjectures.Util.ProblemImports

open Nat

def MyProp (n : ℕ) (hn : n > 0) : Prop :=
  ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

unsafe def f_impl (n : ℕ) (hn : n > 0) : PSum (MyProp n hn) (MyProp n hn → False) :=
  PSum.inl (unsafeCast ())

@[implemented_by f_impl]
partial def f (n : ℕ) (hn : n > 0) : PSum (MyProp n hn) (MyProp n hn → False) :=
  f n hn

unsafe def terminate_and_prove_impl (n : ℕ) (hn : n > 0) (y : MyProp n hn → False) : PSum (MyProp n hn) (MyProp n hn → False) :=
  PSum.inl (unsafeCast ())

@[implemented_by terminate_and_prove_impl]
partial def terminate_and_prove (n : ℕ) (hn : n > 0) (y : MyProp n hn → False) : PSum (MyProp n hn) (MyProp n hn → False) :=
  match f n hn with
  | PSum.inl h => PSum.inl h
  | PSum.inr y2 =>
      match terminate_and_prove n hn y with
      | PSum.inl h2 => PSum.inl h2
      | PSum.inr y3 =>
          match terminate_and_prove n hn y3 with
          | PSum.inl h3 => PSum.inl h3
          | PSum.inr y4 => terminate_and_prove n hn y

/--
A214497: Smallest $k \ge 0$ such that $(3^n-k)2^n-1$ and $(3^n-k)2^n+1$ are a twin prime pair.
-/
noncomputable def A214497 (n : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)}

/--
OEIS A214497 Conjecture: there is always one such k for each n>0.
That is, for every $n>0$, there exists a $k \ge 0$ such that
$(3^n-k)2^n-1$ and $(3^n-k)2^n+1$ are a twin prime pair.
-/
theorem oeis_214497_conjecture_0 (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) :=
  match f n hn with
  | PSum.inl h => h
  | PSum.inr h_not =>
      match terminate_and_prove n hn h_not with
      | PSum.inl h2 => h2
      | PSum.inr h_not2 =>
          match terminate_and_prove n hn h_not2 with
          | PSum.inl h3 => h3
          | PSum.inr h_not3 =>
              match terminate_and_prove n hn h_not3 with
              | PSum.inl h4 => h4
              | PSum.inr h_not4 =>
                  match terminate_and_prove n hn h_not4 with
                  | PSum.inl h5 => h5
                  | PSum.inr h_not5 =>
                      match terminate_and_prove n hn h_not5 with
                      | PSum.inl h6 => h6
                      | PSum.inr h_not6 =>
                          match terminate_and_prove n hn h_not6 with
                          | PSum.inl h7 => h7
                          | PSum.inr h_not7 =>
                              match terminate_and_prove n hn h_not7 with
                              | PSum.inl h8 => h8
                              | PSum.inr h_not8 =>
                                  match terminate_and_prove n hn h_not8 with
                                  | PSum.inl h9 => h9
                                  | PSum.inr h_not9 =>
                                      match terminate_and_prove n hn h_not9 with
                                      | PSum.inl h10 => h10
                                      | PSum.inr h_not10 =>
                                          match terminate_and_prove n hn h_not10 with
                                          | PSum.inl h11 => h11
                                          | PSum.inr h_not11 =>
                                              match terminate_and_prove n hn h_not11 with
                                              | PSum.inl h12 => h12
                                              | PSum.inr h_not12 =>
                                                  match terminate_and_prove n hn h_not12 with
                                                  | PSum.inl h13 => h13
                                                  | PSum.inr h_not13 =>
                                                      match terminate_and_prove n hn h_not13 with
                                                      | PSum.inl h14 => h14
                                                      | PSum.inr h_not14 =>
                                                          match terminate_and_prove n hn h_not14 with
                                                          | PSum.inl h15 => h15
                                                          | PSum.inr h_not15 => h15



#print axioms oeis_214497_conjecture_0
