import Mathlib.Tactic
import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.BirkhoffSum.Average

/-!
# Birkhoff's ergodic theorem

This file defines Birkhoff sums, other related notions and proves Birkhoff's ergodic theorem.

## Implementation notes

...

## References

* ....

-/

section Ergodic_Theory

open BigOperators MeasureTheory

/-
- `T` is a measure preserving map of a probability space `(α, μ)`,
- `f g : α → ℝ` are integrable.
-/
variable {α : Type*} [MeasurableSpace α]
variable {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
variable (T : α → α) (hT : MeasurePreserving T μ)
variable (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)

open Filter

/-- The max of the `k`th Birkhoff sums for `k ≤ n`. -/
def maxOfSums (x : α) (n : ℕ) : ℝ :=
    Finset.sup' (Finset.range (n + 1)) (Finset.nonempty_range_succ) (fun k ↦ birkhoffSum T f k x)

/-- The `maxOfSums` is monotone increasing. -/
theorem maxOfSums_mono (x : α) (n : ℕ) : (maxOfSums T f x n) ≤ (maxOfSums T f x (n + 1)) := by
  exact Finset.sup'_mono (fun k ↦ birkhoffSum T f k x)
    (Finset.range_subset.mpr (Nat.le.step Nat.le.refl)) Finset.nonempty_range_succ

/-- The set of divergent points `{ x | sup_n ∑_{i=0}^{n} f(T^i x) = ∞}`. -/
def divSet := { x : α | Tendsto (fun n ↦ maxOfSums T f x n) atTop atTop }

theorem maxOfSums_succ_image (x : α) (n : ℕ) :
    maxOfSums T f (T x) n = maxOfSums T f x (n + 1) + f x := by

  sorry

/-- The set of divergent points is invariant. -/
theorem divSet_inv : T⁻¹' (divSet T f) = (divSet T f) := by
  ext x
  unfold divSet
  simp
  have h1 := maxOfSums_succ_image T f x
  --tendsto_map'_iff   ?

  sorry

/-- Convenient combination of terms. -/
theorem birkhoffSum_succ_image (n : ℕ) (x : α) :
      birkhoffSum T f n (T x) = birkhoffSum T f (n + 1) x - f x := by
    rw [birkhoffSum_add T f n 1 x]
    rw [eq_add_of_sub_eq' (birkhoffSum_apply_sub_birkhoffSum T f n x)]
    simp
    exact add_sub (birkhoffSum T f n x) (f (T^[n] x)) (f x)



/- Here follows surplus stuff that might or might not be useful. -/

/-- The max of the `k`th Birkhoff sums for `k ≤ n`. -/
noncomputable def maxOfSumsAlt (T : α → α) (f : α → ℝ) (x : α) (n : ℕ) : ℝ :=
  match n with
    | 0     => 0
    | m + 1 => max (birkhoffSum T f (m + 1) x) (maxOfSumsAlt T f x m)

/-- The `maxOfSums` is monotone increasing. -/
theorem maxOfSums_mono_alt (x : α) (n : ℕ) : (maxOfSumsAlt T f x n) ≤ (maxOfSumsAlt T f x (n + 1)) := by
  have h0 : (maxOfSumsAlt T f x (n + 1)) = max (birkhoffSum T f (n + 1) x) (maxOfSumsAlt T f x n) := by
    exact rfl
  rw [h0]
  exact le_max_right (birkhoffSum T f (n + 1) x) (maxOfSumsAlt T f x n)


theorem maxOfSums_succ_image_alt (n : ℕ) (x : α) :
    maxOfSumsAlt T f (T x) n = maxOfSumsAlt T f x (n + 1) + f x := by
  induction n
  unfold maxOfSumsAlt
  simp
  have h0 : maxOfSumsAlt T f x 0 = 0 := by
    exact rfl
  rw [h0]

  sorry

  sorry

-- Maybe problem relates to [https://github.com/leanprover/lean4/issues/1785]
noncomputable def maxOfSums' (n : ℕ) (T : α → α) (f : α → ℝ) (x : α) :=
    ((List.range (n + 1)).map (fun k ↦ birkhoffSum T f k x)).maximum

noncomputable def valsOfSums (T : α → α) (f : α → ℝ) (x : α) (n : ℕ) :=
    (Finset.range (n + 1)).image (fun k ↦ birkhoffSum T f k x)

theorem valsOfSums_Nonempty (n : ℕ) (T : α → α) (f : α → ℝ) (x : α) :
    Finset.Nonempty (valsOfSums T f x n) := by
  have h0 : (Finset.range (n + 1)).Nonempty := Finset.nonempty_range_succ
  exact Finset.Nonempty.image h0 fun k ↦ birkhoffSum T f k x


-- def maxOfSums'' (T : α → α) (f : α → ℝ) (x : α) (n : ℕ) : ℝ :=
--     Finset.sup' (Finset.range (n + 1)) (Finset.nonempty_range_succ) (fun k ↦ birkhoffSum T f k x)

-- noncomputable def maxOfSums'' (T : α → α) (f : α → ℝ) (x : α) (n : ℕ) : ℝ :=
--     Finset.sup' (valsOfSums T f x n) (valsOfSums_Nonempty n T f x)

/-- The set of divergent points `{ x | sup_n ∑_{i=0}^{n} f(T^i x) = ∞}`. -/
def divSet' := { x : α |  ∀ C : ℝ, ∃ n, C < birkhoffSum T f n x }

/-- The set of divergent points `{ x | sup_n ∑_{i=0}^{n} f(T^i x) = ∞}`. -/
def divSet'' := { x : α | Tendsto (fun n ↦ birkhoffSum T f n x) atTop atTop }

theorem divSet_inv_aux' (x : α) (hx : x ∈ divSet' T f) :
    ∀ C : ℝ, ∃ n, 1 ≤ n ∧ C < birkhoffSum T f n x := sorry

/-- The set of divergent points is invariant. -/
theorem divSet_inv' : T⁻¹' (divSet' T f) = (divSet' T f) := by
  unfold divSet'
  ext x
  have h1 (n : ℕ) (x : α) :
      birkhoffSum T f n (T x) = birkhoffSum T f (n + 1) x - f x := by
    rw [birkhoffSum_add T f n 1 x]
    rw [eq_add_of_sub_eq' (birkhoffSum_apply_sub_birkhoffSum T f n x)]
    simp
    exact add_sub (birkhoffSum T f n x) (f (T^[n] x)) (f x)
  constructor
  intro h0
  intro C
  have h2 := h0 (C - (f x))
  obtain ⟨n, h3⟩ := h2
  rw [h1 n x] at h3
  use (n + 1)
  simp at h3
  exact h3
  intro h4
  simp
  simp at h4
  intro C
  let C' := C
  have h5 := h4 (C + (f x))
  obtain ⟨n, h6⟩ := h5
  have h7 : 1 ≤ n := sorry
  use n - 1
  rw [h1]
  have h8 : n - 1 + 1 = n := Nat.sub_add_cancel h7
  rw [h8]
  exact lt_tsub_iff_right.mpr h6

-- idea: is it better to define a new type measureable sets in alpha and then restrict to that type?
-- def inv_sigma_algebra := { S : Set α | MeasurableSet S ∧ T⁻¹' S = S }
def inv_sigma_algebra := { S : Set α | MeasurableSet S ∧ IsInvariant (fun n x ↦ T^[n] x) S }
-- `IsInvariant` is defined as: a set s ⊆ α is invariant under ϕ : τ → α → α if ϕ t s ⊆ s for all t in τ.


/- define `Φ_n : max { ∑_{i=0}^{n} φ ∘ T^i }_{k ≤ n}` -/

/- ∀ `x ∈ A`, `Φ_{n+1}(x) - Φ_{n}(T(x)) = φ(x) - min(0,Φ_{n}(T(x))) ≥ φ(x)` decreases to `φ(x)`. -/

/- Using dominated convergence, `0 ≤ ∫_A (Φ_{n+1} - Φ_{n}) dμ = ∫_A (Φ_{n+1} - Φ_{n} ∘ T) dμ → ∫_A φ dμ`. -/

/- `(1/n) ∑_{k=0}^{n-1} φ ∘ T^k ≤ Φ_n / n`. -/

/- If `x ∉ A`, `limsup_n (1/n) ∑_{k=0}^{n-1} φ ∘ T^i ≤ 0`. -/

/- If conditional expection of `φ` is negative, i.e., `∫_C φ dμ = ∫_C φ|_inv_sigmal_algebra dμ < 0` for all `C` in `inv_sigma_algebra` with `μ(C) > 0`,
then `μ(A) = 0`. -/

/- Then (assumptions as prior step) `limsup_n (1/n) ∑_{k=0}^{n-1} φ ∘ T^i ≤ 0` a.e. -/

/- Let `φ = f - f|_I - ε`. -/

/- `f_I ∘ T = f|_I` and so `(1/n) ∑_{k=0}^{n-1} f ∘ T^k = (1/n) ∑_{k=0}^{n-1} f ∘ T^k - f_I - ε`. -/

/- `limsup_n (1/n) ∑_{k=0}^{n-1} f ∘ T^i ≤ f|_I + ε` a.e. -/

/- Replacing `f` with `-f`  we get the lower bound. -/

/- Birkhoff's theorem: Almost surely, `birkhoffAverage ℝ f g n x` converges to the conditional expectation of `f`. -/

-- #check birkhoffAverage ℝ T f n x

/- If `T` is ergodic, show that the invariant sigma-algebra is a.e. trivial. -/

/- Show that the conditional expectation with respect to an a.e. trivial subalgebra is a.e.
the integral. -/

/- Birkhoff theorem for ergodic maps. -/

end Ergodic_Theory
