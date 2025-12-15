import Mathlib

set_option maxHeartbeats 1000000

/--
Characteristic polynomial recurrence for path graph adjacency matrices.

For `n ≥ 2`, the characteristic polynomial of the `n × n` matrix representing the adjacency matrix
of a path graph on `n` vertices satisfies the recurrence relation:

charpoly(Pₙ) = X * charpoly(Pₙ₋₁) - charpoly(Pₙ₋₂)

The matrix is defined as:
- `A(i, j) = 1` if `|i - j| = 1` (adjacent vertices in the path)
- `A(i, j) = 0` otherwise

This recurrence is a classical result in algebraic graph theory and reflects the combinatorial
structure of path graphs.

## Parameters
- `n : ℕ` - The size of the matrix, must be at least 2
- `hn : 2 ≤ n` - Proof that `n ≥ 2`

## Notes
- The matrix represents the adjacency matrix of a path graph on `n` vertices
- The recurrence is analogous to the recurrence for Chebyshev polynomials
- The proof uses determinant expansion along the first row/column and properties of tridiagonal matrices

## References
* See any standard text on algebraic graph theory for path graph spectra
* Related to the characteristic polynomials of path graphs and their connection to Chebyshev polynomials
-/
theorem charpoly_recurrence (n : ℕ) (hn : 2 ≤ n) :
    Matrix.charpoly (Matrix.of (fun i j : Fin n ↦ if |(i : ℤ) - (j : ℤ)| = 1 then (1 : ℝ) else 0)) =
    Polynomial.X * Matrix.charpoly (Matrix.of (fun i j : Fin (n-1) ↦ if |(i : ℤ) - (j : ℤ)| = 1 then (1 : ℝ) else 0)) -
    Matrix.charpoly (Matrix.of (fun i j : Fin (n-2) ↦ if |(i : ℤ) - (j : ℤ)| = 1 then (1 : ℝ) else 0)) := by
  rcases n with ⟨ ⟩ <;> aesop (config := {warnOnNonterminal := false});
  -- Apply the recursive definition of the determinant to the current matrix.
  have h_det_apply : Matrix.det (Matrix.diagonal (fun _ => Polynomial.X) - Matrix.of (fun i j : Fin (Nat.succ n) => if |(i : ℤ) - j| = 1 then 1 else 0 : Fin (Nat.succ n) → Fin (Nat.succ n) → Polynomial ℝ)) = Polynomial.X * Matrix.det (Matrix.diagonal (fun _ => Polynomial.X) - Matrix.of (fun i j : Fin n => if |(i : ℤ) - j| = 1 then 1 else 0 : Fin n → Fin n → Polynomial ℝ)) - Matrix.det (Matrix.diagonal (fun _ => Polynomial.X) - Matrix.of (fun i j : Fin (n - 1) => if |(i : ℤ) - j| = 1 then 1 else 0 : Fin (n - 1) → Fin (n - 1) → Polynomial ℝ)) := by
    rcases n with ⟨ ⟩ <;> aesop (config := {warnOnNonterminal := false});
    rw [ Matrix.det_succ_column_zero ] ; aesop (config := {warnOnNonterminal := false});
    norm_num [ Fin.sum_univ_succ, Matrix.det_succ_row_zero ];
    simp +decide [ Fin.ext_iff, Matrix.submatrix, Matrix.diagonal ];
    norm_num [ Fin.succAbove, abs_of_nonpos, add_nonpos ] at *;
    norm_cast ; norm_num [ Finset.sum_ite ] ; ring!;
  -- By definition of the characteristic polynomial, we know that
  have h_char_def : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), Matrix.charpoly A = Matrix.det (Matrix.diagonal (fun _ => Polynomial.X) - Matrix.of (fun i j : Fin n => Polynomial.C (A i j))) := by
    simp +decide [ Matrix.charpoly, Matrix.det_apply' ];
    -- The two sums are identical, so the equality holds trivially.
    simp [Matrix.charmatrix];
  aesop (config := {warnOnNonterminal := false})
