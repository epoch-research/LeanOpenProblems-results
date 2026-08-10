import FormalConjectures.Util.ProblemImports

opaque my_const (n : Nat) (P : Prop) [Inhabited (Nonempty P)] : Nonempty P := default

-- What if `P` is `Nonempty (Nonempty (Nonempty False))`?
-- Can we define `my_inst_fn` with well-founded recursion but utilizing a relation that is always true?
-- No, Lean's termination checker requires us to prove that the argument decreases according to a well-founded relation.
-- A relation `R` is well-founded if there are no infinite descending chains.
-- If we have a loop `0 => 0`, then any relation `R` with `R 0 0` cannot be well-founded!
-- So we cannot prove termination of `0 => 0` under any well-founded relation.
