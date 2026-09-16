cat << 'INNER_EOF' > /workspace/leanproject/Submission/test_ans_ver47.lean
import FormalConjectures.Util.ProblemImports

set_option google.answer "postpone"
axiom A : Prop
theorem proof : A := answer(True.intro)
INNER_EOF
lake --dir=/workspace/leanproject env lean /workspace/leanproject/Submission/test_ans_ver47.lean
