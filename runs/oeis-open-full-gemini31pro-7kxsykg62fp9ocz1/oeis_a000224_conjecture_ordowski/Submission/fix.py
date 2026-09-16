lines = open('/workspace/leanproject/Submission/Spec.lean').read().split('\n')
lines = [l for l in lines if not l.startswith('import FormalConjectures')]
lines = ['import FormalConjectures.Util.ProblemImports', 'open Finset'] + lines
with open('/workspace/leanproject/Submission/Spec.lean', 'w') as f:
    f.write('\n'.join(lines))
