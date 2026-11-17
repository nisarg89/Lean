import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The forward rank-by-minor bound

Preservation of nonzero determinant minors is the algebraic bridge in the
FE few-ties argument. Mathlib gives the two components needed for one
direction: a nonzero square determinant has full rank, and taking a
submatrix cannot increase rank. The converse is supplied in the companion shared `RankMinorConverse`
module. Both manuscripts reuse this single algebraic certificate source.
-/

set_option autoImplicit false

namespace FairDivision.LinearAlgebra

/-- A nonzero `k × k` minor certifies that the ambient matrix over a field has
rank at least `k`. No injectivity assumption on the row/column selectors
is necessary: a nonzero determinant implies it automatically. -/
theorem rank_at_least_of_nonzero_minor
    {K : Type*} [Field K] {m n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
    (M : Matrix m n K) (rows : k → m) (cols : k → n)
    (hdet : (M.submatrix rows cols).det ≠ 0) :
    Fintype.card k ≤ M.rank := by
  calc
    Fintype.card k = (M.submatrix rows cols).rank :=
      (Matrix.rank_of_det_ne_zero hdet).symm
    _ ≤ M.rank := Matrix.rank_submatrix_le M rows cols

end FairDivision.LinearAlgebra
