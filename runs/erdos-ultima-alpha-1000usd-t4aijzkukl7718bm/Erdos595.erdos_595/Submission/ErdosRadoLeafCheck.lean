import Submission.InfiniteTriangleRamsey
#synth LinearOrder (ℕ ⊕ₗ ℕ)
#synth WellFoundedLT (ℕ ⊕ₗ ℕ)
#check Sum.Lex.inl_lt_inl_iff
#check Sum.Lex.not_inr_lt_inl
#check Sum.Lex.inr_lt_inr_iff
#check toLex_injective
#check ofLex
#check Sum.lex_wf
