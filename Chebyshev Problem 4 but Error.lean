import Mathlib


/--
This theorem is MISSTATED and attempts to prove a false proposition.


The original intent was likely:
  "For every natural number n, there exists a field that is not algebraically closed
   but has the property that every polynomial of degree ≤ n has a root."


However, the current statement says:
  "For every natural number n and every field K that is not algebraically closed,
   there exists a polynomial p over K with degree ≠ none, natDegree ≤ n, and no roots in K."


This is trivial (take the constant polynomial 1) but not mathematically interesting.
-/
theorem exists_field_not_alg_closed_but_deg_le_n_has_root (n : ℕ) :
    ∀ (K : Type) (_ : Field K) ,
      ∃ (p : Polynomial K), p.degree ≠ none ∧ p.natDegree ≤ n ∧ ∀ x : K, ¬p.IsRoot x := by
  intro K hK
  use Polynomial.C 1; simp;
  decide +revert
