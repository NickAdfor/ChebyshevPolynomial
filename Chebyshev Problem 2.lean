import Mathlib

set_option maxHeartbeats 2000000

namespace Polynomial
namespace Chebyshev

variable (R : Type*) [CommRing R]

/-- The degree of the Chebyshev polynomial of the second kind at index -1 is ⊥ (undefined). -/
lemma degree_U_neg_one : (U R (-1)).degree = ⊥ := by
  simp [U_neg_one]

/-- The degree of the Chebyshev polynomial of the second kind at index 0 is 0 in a nontrivial ring. -/
lemma degree_U_zero [Nontrivial R] : (U R 0).degree = 0 := by
  simp [U_zero]

/-- The degree of the Chebyshev polynomial of the second kind at natural number index n is n,
    assuming the ring is a domain and its characteristic is not 2. -/
lemma degree_U_ofNat [IsDomain R] (h : ringChar R ≠ 2) : (n : ℕ) → (U R n).degree = n
  | 0 => degree_U_zero R
  | 1 => by
    simp [U_one]
    -- The degree of the constant polynomial 2 is 0 when 2 ≠ 0 in R
    have : degree (2 : R[X]) = 0 := by
      compute_degree
      exact Ring.two_ne_zero h
    simp [this]
  | n + 2 => by
    simp only [Nat.cast_add, Nat.cast_ofNat, U_add_two]
    -- Calculate the degree of 2 * X * U R (n + 1)
    have : degree (2 * X * U R (n + 1)) = n + 2 := by
      -- The degree of 2 * X is 1 when 2 ≠ 0 in R
      have h₂ : degree (2 * X : R[X]) = 1 := by
        compute_degree
        · exact Ring.two_ne_zero h
        · simp
      -- The degree of U R (n + 1) is n + 1 by induction
      have this : (U R (n + 1)).degree = n + 1 := degree_U_ofNat h (n + 1)
      rw [degree_mul, this, add_comm, h₂]
      rfl
    rwa [degree_sub_eq_left_of_degree_lt]
    -- Show that degree (U R n) < degree (2 * X * U R (n + 1))
    rw [this]
    rw [degree_U_ofNat h n]
    exact Order.lt_succ _ |>.trans <| Order.lt_succ _

open Real

/-- If a function f is injective on Fin n, then the multiset of its values over range n has no duplicates. -/
lemma range_n_nodup_of_fin_injective (n : ℕ) (f : ℕ → ℝ) (h : Function.Injective (fun (i : Fin n) => f i)) :
    (Multiset.map f (Multiset.range n)).Nodup := by
  -- The range multiset has no duplicates
  have h_range_nodup : (Multiset.range n).Nodup := by
    simp [Multiset.nodup_range]
  -- Map preserves nodup when the function is injective on the elements
  refine h_range_nodup.map_on fun x hx y hy hfxy => ?_
  rw [Multiset.mem_range] at hx hy
  let x' : Fin n := ⟨x, hx⟩
  let y' : Fin n := ⟨y, hy⟩
  rw [← propext Fin.mk_eq_mk]
  refine h hfxy
  · exact hx
  · exact hy

/-- The multiset of cosines cos((k+1)π/(n+1)) for k < n has no duplicates. -/
lemma nodups (n : ℕ) :
    (Multiset.map (fun k : ℕ ↦ cos ((k + 1) * π / (n + 1))) (.range n)).Nodup := by
  by_cases hn : n = 0
  · subst hn
    simp
  -- Define the function and show it's injective
  let g : Fin n → ℝ := fun i => cos ((i.val + 1 : ℝ) * π / (n + 1))
  -- Show it's injective
  have hg : Function.Injective g := by
    intro i j h
    let a := i.val
    let b := j.val
    by_cases hab : a = b
    · -- If indices are equal, then the Fin elements are equal
      have : i = j := by
        exact Fin.eq_of_val_eq hab
      exact this
    -- Otherwise, we have a < b or b < a
    have lt_or_gt : a < b ∨ b < a := by exact Nat.lt_or_gt_of_ne hab
    cases lt_or_gt with
    | inl a_lt_b =>
      let θa := (a + 1 : ℝ) * π / (n + 1)
      let θb := (b + 1 : ℝ) * π / (n + 1)
      -- Show θa < θb
      have θa_lt_θb : θa < θb := by
        calc
          θa = ((a + 1 : ℝ) / (n + 1)) * π := by ring
          _ < ((b + 1 : ℝ) / (n + 1)) * π := by
            apply mul_lt_mul_of_pos_right
            · apply div_lt_div_of_pos_right
              · exact_mod_cast Nat.succ_lt_succ a_lt_b
              · positivity
            · positivity
          _ = θb := by ring
      -- Show cos(θa) > cos(θb) using strict anti-monotonicity of cosine on (0,π)
      have hcos_gt : g i > g j := by
        -- Calculation
        have θa_pos : 0 < θa := by positivity
        -- Calculation
        have θb_lt_pi : θb < π := by
          -- Calculation
          have : (b + 1 : ℝ) / (n + 1) < 1 := by
            rw [div_lt_one_iff]
            aesop (config := {warnOnNonterminal := false})
            left
            exact Nat.cast_add_one_pos n
          -- Calculation
          have : (↑b + 1) / (↑n + 1) * π < π := by
            -- Calculation
            have hπ : 0 < π := by exact Real.pi_pos
            exact mul_lt_of_lt_one_left hπ this
          dsimp [θb]
          -- Calculation
          have h' : (↑b + 1) * π / (↑n + 1) < π := by
            rw [mul_div_right_comm]
            exact this
          exact h'
        -- Calculation
        have hanti := strictAntiOn_cos
        -- Calculation
        have : cos θa > cos θb := by
          apply hanti
          · constructor
            · linarith
            · linarith
          · constructor
            · linarith
            · linarith
          · linarith
        simpa [g] using this
      linarith
    | inr b_lt_a =>
      let θa := (a + 1 : ℝ) * π / (n + 1)
      let θb := (b + 1 : ℝ) * π / (n + 1)
      -- Show θb < θa
      have θb_lt_θa : θb < θa := by
        calc
          θb = ((b + 1 : ℝ) / (n + 1)) * π := by ring
          _ < ((a + 1 : ℝ) / (n + 1)) * π := by
            apply mul_lt_mul_of_pos_right
            · apply div_lt_div_of_pos_right
              · exact_mod_cast Nat.succ_lt_succ b_lt_a
              · positivity
            · positivity
          _ = θa := by ring
      -- Show cos(θb) > cos(θa) using strict anti-monotonicity of cosine on (0,π)
      have hcos_gt : g j > g i := by
        -- Calculation
        have θb_pos : 0 < θb := by positivity
        -- Calculation
        have θa_lt_pi : θa < π := by
          -- Calculation
          have : (a + 1 : ℝ) / (n + 1) < 1 := by
            rw [div_lt_one_iff]
            aesop (config := {warnOnNonterminal := false})
            left
            exact Nat.cast_add_one_pos n
          calc
            θa = ((a + 1 : ℝ) / (n + 1)) * π := by ring
            _ < 1 * π := by
              apply mul_lt_mul_of_pos_right ?_ (by exact Real.pi_pos)
              exact this
            _ = π := by ring
        -- Calculation
        have hanti := strictAntiOn_cos
        -- Calculation
        have : cos θb > cos θa := by
          apply hanti
          · constructor
            · linarith
            · linarith
          · constructor
            · linarith
            · linarith
          · linarith
        simpa [g] using this
      linarith
  exact range_n_nodup_of_fin_injective n (fun k => cos ((k + 1) * π / (n + 1))) hg

/-- sin((k+1)π) = 0 for any natural number k. -/
lemma sin_nat_add_one_mul_pi (k : ℕ) : sin ((k + 1) * π) = 0 := by
  rw [@sin_eq_zero_iff]
  simp
  -- There exists an integer n such that (k+1)π = nπ
  have h : ∃ n, ↑n = ↑k + 1 := by exact exists_apply_eq_apply (fun a => a) (k + 1)
  obtain ⟨n, hn⟩ := h
  use n
  subst hn
  simp_all only [Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_natCast, Int.cast_one]

/-- The roots of the Chebyshev polynomial of the second kind Uₙ are exactly the numbers cos((k+1)π/(n+1)) for k < n. -/
lemma roots_U (n : ℕ) :
    (U ℝ n).roots = Multiset.map (fun k : ℕ ↦ cos ((k + 1) * π / (n + 1))) (.range n) := by
  cases n with
  | zero => simp
  | succ n =>
    -- The number of roots is at most n+1
    have : (U ℝ (n + 1)).roots.card ≤ n + 1 := by
      convert card_roots' _
      exact Eq.symm <| natDegree_eq_of_degree_eq_some <| degree_U_ofNat ℝ (by simp) (n + 1)
    -- The two multisets are equal because they have the same elements and cardinality
    apply Eq.symm <| Multiset.eq_of_le_of_card_le ?_ (by simpa)
    rw [Multiset.le_iff_count]
    intro x
    simp only [count_roots]
    rw [Multiset.count_eq_of_nodup (nodups (n + 1))]
    split_ifs with h
    · -- If x is in the multiset, show it's a root with multiplicity 1
      change 0 < _
      simp
      refine ⟨ne_zero_of_degree_gt (n := 0) ?_, ?_⟩
      · calc
          (0 : WithBot ℕ) < n + 1 := by exact Nat.cast_add_one_pos n
          _ = (U ℝ (n + 1)).degree := degree_U_ofNat ℝ (by simp) (n + 1) |>.symm
      · -- Use the explicit formula for Uₙ(cos θ)
        simp only [Nat.cast_add, Nat.cast_one, Multiset.mem_map, Multiset.mem_range] at h
        obtain ⟨k, hk, rfl⟩ := h
        -- Calculation
        have : 0 < sin ((k + 1) * π / (n + 1 + 1)) := by
          apply sin_pos_of_mem_Ioo ⟨by positivity, ?_⟩
          calc
            _ < (n + 1 + 1 : ℝ) * π / (n + 1 + 1) := by gcongr; norm_cast
            _ = π := by field_simp
        rw [← mul_right_cancel_iff_of_pos this, zero_mul, U_real_cos]
        norm_cast
        field_simp
        exact sin_nat_mul_pi (k + 1)
    · simp

/-- The root multiplicity of cos((k+1)π/(n+1)) in Uₙ is exactly 1 when k < n. -/
lemma rootMultiplicity_U_real {n : ℕ} {k : ℕ} (hk : k < n) :
    (U ℝ n).rootMultiplicity (cos ((k + 1) * π / (n + 1))) = 1 := by
  rw [← count_roots, roots_U]
  refine Multiset.count_eq_one_of_mem (nodups n) ?_
  simpa using ⟨k, hk, rfl⟩

/-- All roots of the Chebyshev polynomial of the second kind Uₙ are simple. -/
lemma roots_U_simple (n : ℕ) : ∀ x ∈ (U ℝ n).roots, (U ℝ n).rootMultiplicity x = 1 := by
  intro x hx
  rw [roots_U] at hx
  rw [Multiset.mem_map] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  aesop (config := {warnOnNonterminal := false})
  exact rootMultiplicity_U_real hk

/-- All roots of the second kind Chebyshev polynomial Uₙ are real. -/
lemma roots_U_real (n : ℕ) : ∀ x ∈ (U ℝ n).roots, x ∈ (Set.univ : Set ℝ) := by
  rw [roots_U n]
  intro x hx
  obtain ⟨k, _, rfl⟩ := Multiset.mem_map.mp hx
  trivial

/-- All roots of the second kind Chebyshev polynomial Uₙ are real and simple. -/
theorem roots_U_real_and_simple (n : ℕ) :
    (∀ x ∈ (U ℝ n).roots, x ∈ (Set.univ : Set ℝ)) ∧
    (∀ x ∈ (U ℝ n).roots, (U ℝ n).rootMultiplicity x = 1) :=
  ⟨roots_U_real n, roots_U_simple n⟩

end Chebyshev
end Polynomial
