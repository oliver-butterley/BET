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

open MeasureTheory
/-
- `T` is a measure preserving map of a probability space `(α, μ)`,
- `f g : α → ℝ` are integrable.
-/
variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α} [IsProbabilityMeasure μ]
variable (T : α → α) (hT : MeasurePreserving T μ)
variable (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)

open Finset in
/-- The max of the first `n + 1` Birkhoff sums.
I.e., `maxOfSums T f x n` corresponds to `max {birkhoffSum T f 1 x,..., birkhoffSum T f (n + 1) x}`.
Indexing choice avoids max of empty set issue. -/
def maxOfSums (x : α) (n : ℕ) :=
    sup' (range (n + 1)) (nonempty_range_succ) (fun k ↦ birkhoffSum T f (k + 1) x)

lemma maxOfSums_zero : maxOfSums T f x 0 = f x := by
  unfold maxOfSums
  simp only [zero_add, Finset.range_one, Finset.sup'_singleton, birkhoffSum_one']

/-- `maxOfSums` is monotone (one step version). -/
theorem maxOfSums_succ_le (x : α) (n : ℕ) : (maxOfSums T f x n) ≤ (maxOfSums T f x (n + 1)) := by
  exact Finset.sup'_mono (fun k ↦ birkhoffSum T f (k + 1) x)
    (Finset.range_subset.mpr (Nat.le.step Nat.le.refl)) Finset.nonempty_range_succ

/-- `maxOfSums` is monotone (explict version). -/
theorem maxOfSums_le_le (x : α) (m n : ℕ) (hmn : m ≤ n) :
    (maxOfSums T f x m) ≤ (maxOfSums T f x n) := by
  induction' n with n hi
  rw [Nat.le_zero.mp hmn]
  rcases Nat.of_le_succ hmn with hc | hc
  exact le_trans (hi hc) (maxOfSums_succ_le T f x n)
  rw [hc]

/-- `maxOfSums` is monotone.
(Uncertain which is the best phrasing to keep of these options.) -/
theorem maxOfSums_le_le' (x : α) : Monotone (fun n ↦ maxOfSums T f x n) := by
  unfold Monotone
  intros n m hmn
  exact maxOfSums_le_le T f x n m hmn

open Filter in
/-- The set of divergent points `{ x | sup_n ∑_{i=0}^{n} f(T^i x) = ∞}`. -/
def divSet := { x : α | Tendsto (fun n ↦ maxOfSums T f x n) atTop atTop }

/-- Convenient combination of `birkhoffSum` terms. -/
theorem birkhoffSum_succ_image (n : ℕ) (x : α) :
      birkhoffSum T f n (T x) = birkhoffSum T f (n + 1) x - f x := by
    rw [birkhoffSum_add T f n 1 x]
    rw [eq_add_of_sub_eq' (birkhoffSum_apply_sub_birkhoffSum T f n x)]
    simp
    exact add_sub (birkhoffSum T f n x) (f (T^[n] x)) (f x)

-- TODO: clean the following, enquire if there is an easier way to extract it from mathlib.
/-- Would expect this to be in `Mathlib/Data/Finset/Lattice`. -/
theorem sup'_eq_iff_le {s : Finset β} [SemilatticeSup α] (H : s.Nonempty) (f : β → α) (hs : a ∈ s) :
    s.sup' H f = f a ↔ ∀ b ∈ s, f b ≤ f a := by
  constructor
  intros h0 b h2
  rw [← h0]
  exact Finset.le_sup' f h2
  intro h1
  have hle : s.sup' H f ≤ f a := by
    simp only [Finset.sup'_le_iff]
    exact h1
  exact (LE.le.ge_iff_eq hle).mp (Finset.le_sup' f hs)

open Finset in
/-- Divide a range into two parts. Maybe this exists in mathlib? Simpler way to write the proof?-/
theorem range_union (n m : ℕ) : range (n + m) = (range n) ∪ (filter (n ≤ ·) (range (n + m))) := by
  ext k
  constructor
  by_cases hc : k < n
  intro hkr
  exact mem_union.mpr (Or.inl (mem_range.mpr hc))
  push_neg at hc
  intro hkr
  exact mem_union_right (range n) (mem_filter.mpr { left := hkr, right := hc })
  intros hku
  simp
  simp at hku
  rcases hku with h1 | h2
  exact Nat.lt_add_right m h1
  exact h2.left

open Finset in
/-- Claim 1 (Marco) -/
theorem maxOfSums_succ_image (n : ℕ) (x : α) :
    maxOfSums T f x (n + 1) - maxOfSums T f (T x) n = f x - min 0 (maxOfSums T f (T x) n) := by
  -- Consider `maxOfSums T f x (n + 1) = max {birkhoffSum T f 1 x,..., birkhoffSum T f (n + 2) x}`
  by_cases hc : ∀ k ≤ n + 1, birkhoffSum T f (k + 1) x ≤ birkhoffSum T f 1 x
  -- Case when the max is achieved by first element.
  have h0 : maxOfSums T f x (n + 1) = birkhoffSum T f 1 x := by
    unfold maxOfSums
    rw [birkhoffSum_one']
    rw [birkhoffSum_one'] at hc
    have h12 : (range (n + 1 + 1)).Nonempty := nonempty_range_succ
    have h13 : 0 ∈ (range (n + 1 + 1)) := by
      refine mem_range.mpr (Nat.add_pos_right (n + 1) Nat.le.refl)
    have h11 := sup'_eq_iff_le h12 (fun k ↦ birkhoffSum T f (k + 1) x) h13
    simp only [zero_add, birkhoffSum_one', mem_range] at h11
    have h15 : ∀ b < n + 1 + 1, birkhoffSum T f (b + 1) x ≤ f x := by
      intros k h16
      have h17 : k ≤ n + 1 := Nat.lt_succ.mp h16
      exact hc k h17
    exact h11.mpr h15
  have h1 : birkhoffSum T f 1 x = f x := birkhoffSum_one T f x
  have h2 : ∀ k, birkhoffSum T f k (T x) = birkhoffSum T f (k + 1) x - f x := by
    intro k
    exact birkhoffSum_succ_image T f k x
  have h3 : ∀ k ≤ n + 1, birkhoffSum T f k (T x) ≤ 0 := by
    intros k hk
    rw [h2]
    rw [h1] at hc
    simp only [tsub_le_iff_right, zero_add]
    exact hc k hk
  have h4 : maxOfSums T f (T x) n ≤ 0 := by
    unfold maxOfSums
    simp only [sup'_le_iff, mem_range]
    intros k hk
    rw [Nat.lt_succ] at hk
    refine h3 (k + 1) (Nat.add_le_add hk Nat.le.refl)
  have h5 : min 0 (maxOfSums T f (T x) n) = maxOfSums T f (T x) n := min_eq_right h4
  linarith
  -- Case when max is not achieved by the first element
  push_neg at hc
  let bS := fun k ↦ birkhoffSum T f (k + 1) x
  let s1 := range 1
  let s2 := filter (1 ≤ ·) (range (n + 2))
  have h19 : range (n + 2) = s1 ∪ s2 := by
    have h20 := range_union 1 (n + 1)
    rw [Nat.one_add (n + 1)] at h20
    exact h20
  have h21 : s2.Nonempty := by
    simp
    use 1

    sorry
  have h17 : sup' (range (n + 2)) nonempty_range_succ bS = bS 0 ⊔ sup' s2 h21 bS := by
    -- Now use `sup'_union`, `range_union` to divide `maxOfSums T f x (n + 1)` into 2 pieces.

    sorry

  have h6 : maxOfSums T f x (n + 1) =
      sup' (range (n + 1)) (nonempty_range_succ) (fun k ↦ birkhoffSum T f (k + 2) x) := by
    unfold maxOfSums
    -- Since `hc`, the max is not achieved by the first element reduce to max over other terms.

    sorry
  have h7 : maxOfSums T f (T x) n =
      sup' (range (n + 1)) (nonempty_range_succ) (fun k ↦ birkhoffSum T f (k + 1) (T x)) := by
    exact rfl
  have h10 : maxOfSums T f x (n + 1) - maxOfSums T f (T x) n = f x := by
    rw [h6, h7]
    have h18 (k : ℕ) := birkhoffSum_succ_image T f (k + 1) x
    have h19 :
        (fun k ↦ birkhoffSum T f (k + 2) x) = (fun k ↦ birkhoffSum T f (k + 1) (T x) + f x) := by

      sorry
    rw [h19]

    -- Use `sup'_comm` to allow sup to commute with the function.
    sorry
  have h8 : 0 ≤ maxOfSums T f (T x) n := by
    unfold maxOfSums

    sorry
  have h9 : min 0 (maxOfSums T f (T x) n) = 0 := by
    exact min_eq_left h8
  rw [h9, h6, h7]

  sorry



open Filter in
/-- The set of divergent points is invariant. -/
theorem divSet_inv : T⁻¹' (divSet T f) = (divSet T f) := by

    unfold divSet
    simp
    ext x

    -- separate the ↔
    constructor
    · intro hx
      simp at hx
      simp

      -- we take advantage of claim 1
      have ha (n : ℕ) := maxOfSums_succ_image T f n x

      -- since `maxOfSums T f (T x) n` → ∞, eventually `min 0 (maxOfSums T f (T x) n) = 0`
      have h1 : ∀ᶠ n in atTop, min 0 (maxOfSums T f (T x) n) = 0 := by
        have h0 : ∀ᶠ n in atTop, 0 ≤ maxOfSums T f (T x) n := by
          exact Tendsto.eventually_ge_atTop hx 0
        simp at h0
        simp
        obtain ⟨k,hk⟩ := h0
        use k

      -- eventually we have a precise equality between the two maxOfSums
      have h2 : ∀ᶠ n in atTop, maxOfSums T f (T x) n = maxOfSums T f x (n + 1) - f x := by
        simp only [eventually_atTop, ge_iff_le] at h1
        obtain ⟨k,hk⟩ := h1
        simp only [eventually_atTop, ge_iff_le]
        use k
        intros m hm
        have h3 := ha m
        have h4 := hk m hm
        rw [h4] at h3
        rw [sub_zero] at h3
        linarith

      -- use the eventual equality
      have h5 : Tendsto (fun n ↦ maxOfSums T f x (n + 1) - f x) atTop atTop := by
        exact Tendsto.congr' h2 hx

      -- rearrange using properties of `Tendsto`
      have h6 : Tendsto (fun n ↦ maxOfSums T f x (n + 1)) atTop atTop := by
        have h7 := tendsto_atTop_add_const_right atTop (f x) h5
        simp at h7
        exact h7

      refine' (tendsto_add_atTop_iff_nat 1).mp _
      exact h6

    · intro hx
      simp at hx
      simp

      sorry

    /-
    On the other hand, again by Claim 1,
    `maxOfSums T f (T x) n = maxOfSums T f x (n + 1) - f x + min 0 (maxOfSums T f (T x) n)`
    If `maxOfSums T f x (n + 1)` → ∞ then, for large n, `min 0 (maxOfSums T f (T x) n) = 0` and
    `maxOfSums T f (T x) n = maxOfSums T f x (n + 1) - f x`.
    Consequently `maxOfSums T f (T x) n` → ∞.
    -/



-------------------------------------------------------------------
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

-- theorem divSet_inv_aux' (x : α) (hx : x ∈ divSet' T f) :
--     ∀ C : ℝ, ∃ n, 1 ≤ n ∧ C < birkhoffSum T f n x := sorry

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
