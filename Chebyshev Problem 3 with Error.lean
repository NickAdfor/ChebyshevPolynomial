import Mathlib

set_option maxHeartbeats 1000000

variable (R : Type*) [CommRing R]

open Polynomial

open Chebyshev

open Real

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
lemma charpoly_recurrence (n : ℕ) (hn : 2 ≤ n) :
    Matrix.charpoly (Matrix.of (fun i j : Fin n ↦ if |(i : ℤ) - (j : ℤ)| = 1 then (1 : ℝ) else 0)) =
    Polynomial.X * Matrix.charpoly (Matrix.of (fun i j : Fin (n-1) ↦ if |(i : ℤ) - (j : ℤ)| = 1 then (1 : ℝ) else 0)) -
    Matrix.charpoly (Matrix.of (fun i j : Fin (n-2) ↦ if |(i : ℤ) - (j : ℤ)| = 1 then (1 : ℝ) else 0)) := by
  rcases n with ⟨ ⟩ <;> aesop (config := {warnOnNonterminal := false});
  -- Apply the recursive definition of the determinant to the current matrix.
  have h_det_apply : Matrix.det (Matrix.diagonal (fun _ => Polynomial.X) - Matrix.of (fun i j : Fin (Nat.succ n) => if |(i : ℤ) - j| = 1 then 1 else 0 : Fin (Nat.succ n) → Fin (Nat.succ n) → Polynomial ℝ)) = Polynomial.X * Matrix.det (Matrix.diagonal (fun _ => Polynomial.X) - Matrix.of (fun i j : Fin n => if |(i : ℤ) - j| = 1 then 1 else 0 : Fin n → Fin n → Polynomial ℝ)) - Matrix.det (Matrix.diagonal (fun _ => Polynomial.X) - Matrix.of (fun i j : Fin (n - 1) => if |(i : ℤ) - j| = 1 then 1 else 0 : Fin (n - 1) → Fin (n - 1) → Polynomial ℝ)) := by
    rcases n with ⟨ ⟩ <;> aesop (config := {warnOnNonterminal := false});
    rw [ Matrix.det_succ_column_zero ] ; aesop (config := {warnOnNonterminal := false});
    norm_num [ Fin.sum_univ_succ, Matrix.det_succ_row_zero ];
    simp +decide [ Fin.ext_iff, Fin.sum_univ_succ, Matrix.submatrix, Matrix.diagonal ];
    norm_num [ Fin.succAbove, abs_of_nonpos, add_nonpos ] at *;
    norm_cast ; norm_num [ Finset.sum_ite ] ; ring!;
  -- By definition of the characteristic polynomial, we know that
  have h_char_def : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), Matrix.charpoly A = Matrix.det (Matrix.diagonal (fun _ => Polynomial.X) - Matrix.of (fun i j : Fin n => Polynomial.C (A i j))) := by
    simp +decide [ Matrix.charpoly, Matrix.det_apply' ];
    -- The two sums are identical, so the equality holds trivially.
    simp [Matrix.charmatrix];
  aesop (config := {warnOnNonterminal := false})


/--
Eigenvalues of the Path Graph Adjacency Matrix

Let A(n) be an n × n real matrix defined by:
  A(n)ᵢⱼ = 1 if |i - j| = 1, 0 otherwise
This is the adjacency matrix of a path graph on n vertices.

Using:
1. The recurrence relation: charpoly(A(n)) = X * charpoly(A(n-1)) - charpoly(A(n-2)) for n ≥ 2
2. The connection with Chebyshev polynomials of the second kind: charpoly(A(n)) = Uₙ(X/2)

Prove that all eigenvalues of A(n) are real and distinct.
-/
theorem eigenvalues_real_and_distinct (n : ℕ):
    -- The characteristic polynomial has distinct real roots
    (Matrix.charpoly (Matrix.of (fun i j : Fin n ↦ if |(i : ℤ) - (j : ℤ)| = 1 then (1 : ℝ) else 0))).Splits (RingHom.id ℝ) ∧
    (Matrix.charpoly (Matrix.of (fun i j : Fin n ↦ if |(i : ℤ) - (j : ℤ)| = 1 then (1 : ℝ) else 0))).roots.toFinset.card = n := by
  -- The polynomial $U_n(x/2)$ has $n$ distinct roots in the interval $[-1, 1]$. These roots are all real and distinct.
  have h_U_distinct_roots : ∀ n : ℕ, (U ℝ n).roots.toFinset.card = n := by
    -- By definition of Chebyshev polynomials of the second kind, we know that $U_n(x)$ has $n$ distinct roots in the interval $[-1, 1]$.
    intro n
    -- Main goal: prove that for all n, the Chebyshev polynomial U_n has n distinct roots
    have h_distinct_roots : ∀ n : ℕ, (Polynomial.Chebyshev.U ℝ n).roots.toFinset.card = n := by
      intro n
      -- Auxiliary lemma: construct specific roots, proving that cos((k+1)π/(n+1)) is a root of U_n
      have h_distinct_roots_aux : ∀ k : ℕ, k < n → (Polynomial.Chebyshev.U ℝ n).eval (Real.cos ((k + 1) * Real.pi / (n + 1))) = 0 := by
        -- Utilize the known roots of the Chebyshev polynomial of the second kind.
        have h_roots : ∀ k : ℕ, k < n → Polynomial.eval (Real.cos ((k + 1) * Real.pi / (n + 1))) (Polynomial.Chebyshev.U ℝ n) = Real.sin ((n + 1) * ((k + 1) * Real.pi / (n + 1))) / Real.sin ((k + 1) * Real.pi / (n + 1)) := by
          -- Utilize the known identity for the Chebyshev polynomial of the second kind: $U_n(\cos \theta) = \frac{\sin((n+1)\theta)}{\sin \theta}$.
          have h_U_identity : ∀ θ : ℝ, Real.sin θ ≠ 0 → Polynomial.eval (Real.cos θ) (Polynomial.Chebyshev.U ℝ n) = Real.sin ((n + 1) * θ) / Real.sin θ := by
            simp_all +decide [ Polynomial.Chebyshev.U, add_mul, Real.sin_add, field_simps ];
          exact fun k hk => h_U_identity _ ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos, show ( k : ℝ ) + 1 ≤ n by norm_cast ] ) ) );
        intro k hk; rw [ h_roots k hk ] ; rw [ mul_div_cancel₀ _ ( by positivity ) ] ; norm_num;
        exact Or.inl ( Real.sin_eq_zero_iff.mpr ⟨ k + 1, by push_cast; ring ⟩ )
      -- Since these roots are distinct and lie within the interval $[-1, 1]$, we can conclude that the polynomial $U_n(x)$ has $n$ distinct roots.
      have h_distinct_roots_finset : Finset.image (fun k : ℕ => Real.cos ((k + 1) * Real.pi / (n + 1))) (Finset.range n) ⊆ (Polynomial.Chebyshev.U ℝ n).roots.toFinset := by
        intros x hx
        aesop (config := {warnOnNonterminal := false});
        replace a := congr_arg ( Polynomial.eval 1 ) a ; norm_num [ Polynomial.Chebyshev.U ] at a;
        linarith;
      refine le_antisymm ?_ ?_;
      · refine le_trans ( Multiset.toFinset_card_le _ ) <| le_trans ( Polynomial.card_roots' _ ) ?_;
        -- By definition of Chebyshev polynomials of the second kind, we know that their degree is $n$.
        have h_deg : ∀ n : ℕ, Polynomial.natDegree (Polynomial.Chebyshev.U ℝ n) ≤ n := by
          intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> simp_all +decide [ Polynomial.Chebyshev.U ];
          erw [ Polynomial.Chebyshev.U ];
          refine' le_trans ( Polynomial.natDegree_sub_le _ _ ) _ ; norm_num [ ih ];
          exact ⟨ le_trans ( Polynomial.natDegree_mul_le .. ) ( by norm_num; linarith! [ ih _ <| Nat.lt_succ_self _, ih _ <| Nat.lt_succ_of_lt <| Nat.lt_succ_self _ ] ), le_trans ( ih _ <| Nat.lt_succ_of_lt <| Nat.lt_succ_self _ ) <| by linarith ⟩;
        exact h_deg n;
      · refine le_trans ?_ ( Finset.card_mono h_distinct_roots_finset );
        rw [ Finset.card_image_of_injOn ];
        · norm_num;
        · intros k hk l hl hkl ; aesop (config := {warnOnNonterminal := false});
          exact_mod_cast ( by apply_fun Real.arccos at hkl; rw [ Real.arccos_cos, Real.arccos_cos ] at hkl <;> nlinarith [ Real.pi_pos, show ( k : ℝ ) + 1 ≤ n by norm_cast, show ( l : ℝ ) + 1 ≤ n by norm_cast, mul_div_cancel₀ ( ( k + 1 : ℝ ) * Real.pi ) ( by positivity : ( n : ℝ ) + 1 ≠ 0 ), mul_div_cancel₀ ( ( l + 1 : ℝ ) * Real.pi ) ( by positivity : ( n : ℝ ) + 1 ≠ 0 ) ] : ( k : ℝ ) = l );
    exact h_distinct_roots n;
  -- By the recurrence relation and the fact that $U_n(x/2)$ has $n$ distinct roots, the characteristic polynomial of $A(n)$ splits into linear factors over $\mathbb{R}$.
  have h_charpoly_splits : ∀ n : ℕ, Matrix.charpoly (Matrix.of (fun i j : Fin n ↦ if |(i : ℤ) - (j : ℤ)| = 1 then (1 : ℝ) else 0)) = (U ℝ n).comp (Polynomial.C (1 / 2 : ℝ) * Polynomial.X) := by
    -- We proceed by induction on $n$.
    intro n
    induction' n using Nat.strong_induction_on with n ih;
    rcases n with ( _ | _ | n );
    · norm_num [ Matrix.charpoly, Matrix.det_succ_row_zero ];
    · norm_num [ Matrix.charpoly, Matrix.det_succ_row_zero ] at * ; aesop (config := {warnOnNonterminal := false});
    · convert charpoly_recurrence _ _ using 1 <;> norm_num [ ih ] ; ring!; aesop (config := {warnOnNonterminal := false}); (
      -- Use the recurrence relation for Chebyshev polynomials: U_{n+2} = 2X·U_{n+1} - U_n
      norm_num [ add_comm, add_left_comm, add_assoc ] at * ; aesop (config := {warnOnNonterminal := false}););
  -- Since $U_n(x/2)$ has $n$ distinct roots in the interval $[-1, 1]$, and these roots are all real and distinct, the characteristic polynomial of $A(n)$ also splits into linear factors over $\mathbb{R}$.
  have h_charpoly_distinct_roots : ∀ n : ℕ, (Matrix.charpoly (Matrix.of (fun i j : Fin n ↦ if |(i : ℤ) - (j : ℤ)| = 1 then (1 : ℝ) else 0))).roots.toFinset.card = n := by
    -- Relationship between roots: roots of characteristic polynomial are scaled versions of Chebyshev roots
    have h_charpoly_distinct_roots : ∀ n : ℕ, (Matrix.charpoly (Matrix.of (fun i j : Fin n ↦ if |(i : ℤ) - (j : ℤ)| = 1 then (1 : ℝ) else 0))).roots.toFinset = Finset.image (fun x => 2 * x) (U ℝ n).roots.toFinset := by
      intro n; ext; aesop (config := {warnOnNonterminal := false});
      · exact ⟨ 2⁻¹ * a, ⟨ by aesop_cat, right ⟩, by ring ⟩;
      · rw [ Polynomial.comp_eq_zero_iff ] at a ; aesop (config := {warnOnNonterminal := false});
    intro n; rw [ h_charpoly_distinct_roots n, Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ two_ne_zero hxy ] ; aesop (config := {warnOnNonterminal := false});
  specialize h_charpoly_distinct_roots n;
  rw [ Polynomial.splits_iff_card_roots ];
  refine' ⟨ le_antisymm _ _, h_charpoly_distinct_roots ⟩;
  · exact Polynomial.card_roots' _;
  · rw [ Matrix.charpoly_natDegree_eq_dim ] ; aesop (config := {warnOnNonterminal := false});
    exact le_trans h_charpoly_distinct_roots.ge ( Multiset.toFinset_card_le _ )

#lint docBlameThm
