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

open Finset in
/-- The max of the first `n + 1` Birkhoff sums. Indexed such that:
- `n = 0` corresponds to `max {birkhoffSum T f 1 x}`,
- `n = 1` corresponds to `max {birkhoffSum T f 1 x, birkhoffSum T f 2 x}`, etc.
(This indexing avoids the problem of the max of an empty set.) -/
def maxOfSums (x : α) (n : ℕ) :=
    sup' (range (n + 1)) (nonempty_range_succ) (fun k ↦ birkhoffSum T f (k + 1) x)

lemma maxOfSums_zero : maxOfSums T f x 0 = f x := by
  unfold maxOfSums
  simp only [zero_add, Finset.range_one, Finset.sup'_singleton, birkhoffSum_one']

/-- The `maxOfSums` is monotone. -/
theorem maxOfSums_succ_le (x : α) (n : ℕ) : (maxOfSums T f x n) ≤ (maxOfSums T f x (n + 1)) := by
  exact Finset.sup'_mono (fun k ↦ birkhoffSum T f (k + 1) x)
    (Finset.range_subset.mpr (Nat.le.step Nat.le.refl)) Finset.nonempty_range_succ

/-- The `maxOfSums` is monotone. -/
theorem maxOfSums_le_le (x : α) (m n : ℕ) (hmn : m ≤ n) :
    (maxOfSums T f x m) ≤ (maxOfSums T f x n) := by
  induction' n with n hi
  rw [Nat.le_zero.mp hmn]
  rcases Nat.of_le_succ hmn with hc | hc
  exact le_trans (hi hc) (maxOfSums_succ_le T f x n)
  rw [hc]

/-- The `maxOfSums` is monotone.
(Uncertain which is the best phrasing to keep of these options.) -/
theorem maxOfSums_le_le' (x : α) : Monotone (fun n ↦ maxOfSums T f x n) := by
  unfold Monotone
  intros n m hmn
  exact maxOfSums_le_le T f x n m hmn

open Filter in
/-- The set of divergent points `{ x | sup_n ∑_{i=0}^{n} f(T^i x) = ∞}`. -/
def divSet := { x : α | Tendsto (fun n ↦ maxOfSums T f x n) atTop atTop }

/-- Shift and image for `maxOfSums`. -/
theorem maxOfSums_succ_image (x : α) (n : ℕ) :
    maxOfSums T f (T x) n = maxOfSums T f x (n + 1) + f x := by
  unfold maxOfSums


  -- something wrong with this statement!



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

theorem um : birkhoffSum T f 1 x = f x := birkhoffSum_one T f x

open Finset in
/-- Isn't this available in a convenient way somewhere in mathlib. -/
lemma range_succ_union (n : ℕ) : range (Nat.succ n) = range n ∪ {n} := by
    ext k
    simp only [mem_range, mem_union, mem_singleton]
    exact Nat.lt_succ_iff_lt_or_eq

open Finset in
theorem claim1_aux (n : ℕ) (x : α) :
    maxOfSums T f x (n + 1) = max (f x) (maxOfSums T f (T x) n) := by
  unfold maxOfSums

  let s1 : Finset ℕ := {0}
  let s2 := filter (1 ≤ ·) (range (n + 1))
  have h0 : range (n + 1) = s1 ∪ s2 := by
    simp
    ext k
    simp
    constructor
    by_cases h2 : k = 0
    rw [h2]
    exact fun a ↦ Or.inl rfl
    have h4 : NeZero k := by exact { out := h2 }
    have h3 : 1 ≤ k := NeZero.one_le
    intro h5
    right
    exact ⟨h5, h3⟩
    intro h6
    aesop
    -- It's a proof but surely there is a simpler way to write this.

  have h1 : range (n + 1) = insert 0 s2 := h0

  -- have h2 : sup' (range (n + 1)) (nonempty_range_succ) (fun k ↦ birkhoffSum T f (k + 1) x)
  -- sup'_insert
  -- (insert b s).sup' (insert_nonempty _ _) f = f b ⊔ s.sup' H f


  sorry

open Finset in
/-- Claim 1 (Marco) -/
theorem claim1 (n : ℕ) (x : α) :
    maxOfSums T f x (n + 1) - maxOfSums T f (T x) n = f x - min 0 (maxOfSums T f (T x) n) := by
  -- `maxOfSums x (n + 1) = max { f, f + f ∘ T,..., f + f ∘ T + ... + f ∘ T^(n + 2) }`
  -- `maxOfSums (T x) n   = max {    f ∘ T,    ...,     f ∘ T + ... + f ∘ T^(n + 2) }`

  -- Consider `maxOfSums T f x (n + 1)` and find the location of the max term
  obtain ⟨k, h5, h6⟩ :=
    exists_max_image (range (n + 1)) (fun k ↦ birkhoffSum T f (k + 1) x) (nonempty_range_succ)
  -- Case when max is achieved by first element of the list
  by_cases h_cases :  k = 0 --
  have h15 : maxOfSums T f x (n + 1) = birkhoffSum T f 1 x := sorry
  rw [h_cases] at h6
  simp at h6

  have h8 (m : ℕ) : f x = birkhoffSum T f (m + 1) x - birkhoffSum T f m (T x) := by
    rw [birkhoffSum_succ_image T f m x]
    simp
  have h9 : ∀ m < n + 1,  birkhoffSum T f m (T x) ≤ 0 := by
    intros m h11
    have h12 := h6 m h11
    rw [h8 m] at h12
    simp at h12
    exact h12

  have h2 : maxOfSums T f (T x) n ≤ 0 := by sorry
  have h4 : min 0 (maxOfSums T f (T x) n) = maxOfSums T f (T x) n := min_eq_right h2
  rw [h4]
  simp
  simp at h15
  exact h15
  -- Other case when max is not achieved by the first element of the list
  have h3 : 0 ≤ maxOfSums T f (T x) n := by sorry


    -- ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x := by
    -- Finset.sup' (Finset.range (n + 1)) (Finset.nonempty_range_succ)
    --   (fun k ↦ birkhoffSum T f (k + 1) x)


  sorry


/- Here follows surplus stuff that might or might not be useful. -/

/-- The max of the `k`th Birkhoff sums for `k ≤ n`. -/
noncomputable def maxOfSumsAlt (T : α → α) (f : α → ℝ) (x : α) (n : ℕ) : ℝ :=
  match n with
    | 0     => 0
    | m + 1 => max (birkhoffSum T f (m + 1) x) (maxOfSumsAlt T f x m)

/-- The `maxOfSums` is monotone increasing. -/
theorem maxOfSums_succ_le_alt (x : α) (n : ℕ) : (maxOfSumsAlt T f x n) ≤ (maxOfSumsAlt T f x (n + 1)) := by
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
def divSet'' := { x : α | Filter.Tendsto (fun n ↦ birkhoffSum T f n x) Filter.atTop Filter.atTop }

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
