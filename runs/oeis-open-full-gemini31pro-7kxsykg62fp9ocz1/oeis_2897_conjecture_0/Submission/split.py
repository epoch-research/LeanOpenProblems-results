import os

with open("Submission/SpecMerged.lean") as f:
    text = f.read()

# We can split by known lemma names!
markers = [
    ("TestHugeSum3.lean", "lemma drop_filter_sum"),
    ("TestHugeSum2.lean", "lemma sum_ite_eq'"),
    ("TestHugeSum6.lean", "lemma inner_sum_eval"),
    ("TestHugeSum7.lean", "lemma sum_choose_square"),
    ("TestCommRing.lean", "lemma comm_ring_id"),
    ("TestIfEquiv.lean", "lemma if_cascade"),
    ("TestHugeSum14.lean", "lemma sum_ite_eq_drop"),
    ("TestHugeSum9.lean", "abbrev Vars_local"),
    ("TestHugeSum12.lean", "lemma sum_perm"),
    ("Proof.lean", "abbrev Vars_local"), # Wait, Proof is not needed, we have it
]

# Wait, `SpecMerged.lean` has the exact concatenation of the text.
# Let's read it and split manually.
