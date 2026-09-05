import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairSitesBase
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairSitesLeft
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairSitesRight

set_option warningAsError true

/-!
# H27 paired-round concrete site certificates

The public PairSites namespace is split into independent base, left-lane, and
right-lane modules. This facade preserves the original import path and API.
-/
