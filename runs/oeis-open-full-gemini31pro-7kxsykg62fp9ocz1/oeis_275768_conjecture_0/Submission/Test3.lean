import Submission.Spec

#eval ((List.range 500).map (fun n => (n, a n))).filter (fun p => p.2 == 4)
