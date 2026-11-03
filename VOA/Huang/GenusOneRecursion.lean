import VOA.Huang.GenusOneTrace

/-!
# The formal compensating-mode recurrence for intertwiner traces

This is the algebraic input to the one-insertion Zhu/Miyamoto recursion: a vertex mode
paired with the opposite-weight intertwiner mode, its commutator, and the finite
geometric solution in both directions.  The zero-shift case gives bracket vanishing.
This is not yet the square-bracket/Eisenstein or Weierstrass recursion.

Sources: Miyamoto, arXiv:math/0010180, §3; Huang, arXiv:math/0303049, §2.
-/

namespace VOA.Huang.GenusOne

open VOA Module
open scoped BigOperators

universe u
variable {V M₁ M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V} {A : OrdVModule W M₁} {N : OrdVModule W M}

theorem compensating_support_finite (Y : IntertwiningOperator A N N) (a : V) (w : M₁)
    (i : ℤ) :
    (Function.support fun p : ℤ => cbz i p • zeroMode A Y.val (mode (A.YM a) p w)).Finite := by
  obtain ⟨K, hK⟩ := A.truncation a w
  refine (Set.finite_Ico (0 : ℤ) K).subset fun p hp => ?_
  simp only [Function.mem_support] at hp
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hp (by rw [cbz_apply_neg _ (lt_of_not_ge h), zero_smul])
  · by_contra h
    exact hp (by rw [hK p (le_of_not_gt h), map_zero, smul_zero])

/-- The full FHL commutator for the pair whose weight shifts cancel. -/
theorem compensating_commutator (Y : IntertwiningOperator A N N)
    {k : ℤ} {α : ℂ} {a : V} {w : M₁} (ha : a ∈ W.grading k) (hw : w ∈ A.weight α)
    (i : ℤ) :
    mode (N.YM a) i * Y.val ((k : ℂ) + α - i - 2) w
      - Y.val ((k : ℂ) + α - i - 2) w * mode (N.YM a) i
      = ∑ᶠ p : ℤ, cbz i p • zeroMode A Y.val (mode (A.YM a) p w) := by
  ext x
  change mode (N.YM a) i (Y.val ((k : ℂ) + α - i - 2) w x)
    - Y.val ((k : ℂ) + α - i - 2) w (mode (N.YM a) i x) = _
  rw [Y.property.commutator]
  rw [show (∑ᶠ p : ℤ, cbz i p • zeroMode A Y.val (mode (A.YM a) p w)) x
      = ∑ᶠ p : ℤ, cbz i p • zeroMode A Y.val (mode (A.YM a) p w) x from
    map_finsum (LinearMap.applyₗ x) (compensating_support_finite Y a w i)]
  apply finsum_congr
  intro p
  rw [zeroMode_of_mem _ _ (mode_mem_weight A ha hw p)]
  rw [show (i : ℂ) + ((k : ℂ) + α - i - 2) - p
    = (α + k - p - 1) - 1 by ring]

/-- Trace of the compensating commutator, expressed entirely by one-point traces. -/
theorem trace_compensating_commutator (Y : IntertwiningOperator A N N)
    {k : ℤ} {α : ℂ} {a : V} {w : M₁} (ha : a ∈ W.grading k) (hw : w ∈ A.weight α)
    (i : ℤ) (e : ℂ) :
    gradedTraceOp N (mode (N.YM a) i * Y.val ((k : ℂ) + α - i - 2) w
      - Y.val ((k : ℂ) + α - i - 2) w * mode (N.YM a) i) e
      = ∑ᶠ p : ℤ, cbz i p * trace Y (mode (A.YM a) p w) e := by
  rw [compensating_commutator Y ha hw i]
  have h := map_finsum (gradedTraceAt N e) (compensating_support_finite Y a w i)
  simpa only [gradedTraceAt_apply, map_smul, smul_eq_mul, trace] using h

theorem weightShift_partner (Y : IntertwiningOperator A N N) {α : ℂ} {w : M₁}
    (hw : w ∈ A.weight α) (k i : ℤ) :
    WeightShift N (Y.val ((k : ℂ) + α - i - 2) w) (-((k : ℂ) - i - 1)) := by
  have h := weightShift_mode Y hw ((k : ℂ) + α - i - 2)
  rwa [show α - ((k : ℂ) + α - i - 2) - 1 = -((k : ℂ) - i - 1) by ring] at h

/-- The exact coefficient recurrence before geometric inversion. -/
theorem trace_pair_step (Y : IntertwiningOperator A N N)
    {k : ℤ} {α : ℂ} {a : V} {w : M₁} (ha : a ∈ W.grading k) (hw : w ∈ A.weight α)
    (i : ℤ) (e : ℂ) :
    gradedTraceOp N (mode (N.YM a) i * Y.val ((k : ℂ) + α - i - 2) w)
        (e + ((k : ℂ) - i - 1))
      = gradedTraceOp N (mode (N.YM a) i * Y.val ((k : ℂ) + α - i - 2) w) e
        - ∑ᶠ p : ℤ, cbz i p * trace Y (mode (A.YM a) p w) e := by
  have h := gradedTraceOp_commutator_step N _ _ ((k : ℂ) - i - 1)
    (weightShift_partner Y hw k i) (VOA.weightShift_mode N ha i) e
  have hneg : Y.val ((k : ℂ) + α - i - 2) w * mode (N.YM a) i
      - mode (N.YM a) i * Y.val ((k : ℂ) + α - i - 2) w
      = (-1 : ℂ) • (mode (N.YM a) i * Y.val ((k : ℂ) + α - i - 2) w
        - Y.val ((k : ℂ) + α - i - 2) w * mode (N.YM a) i) := by
    simp only [neg_one_smul, neg_sub]
  rw [hneg, gradedTraceOp_smul, Pi.smul_apply, smul_eq_mul,
    trace_compensating_commutator Y ha hw i e] at h
  linear_combination h

/-- Positive weight shift: a finite downward geometric sum, with no vanishing input. -/
theorem trace_pair_geom_of_lt (Y : IntertwiningOperator A N N)
    {k : ℤ} {α : ℂ} {a : V} {w : M₁} (ha : a ∈ W.grading k) (hw : w ∈ A.weight α)
    {i : ℤ} (hi : i < k - 1) (e : ℂ) :
    ∃ n : ℕ,
      gradedTraceOp N (mode (N.YM a) i * Y.val ((k : ℂ) + α - i - 2) w) e
        = - ∑ j ∈ Finset.range n, ∑ᶠ p : ℤ,
          cbz i p * trace Y (mode (A.YM a) p w)
            (e - ((j : ℂ) + 1) * ((k : ℂ) - i - 1)) := by
  have hs : 0 < ((k : ℂ) - i - 1).re := by
    simp only [Complex.sub_re, Complex.intCast_re, Complex.one_re]
    exact_mod_cast (show 0 < k - i - 1 by omega)
  obtain ⟨n, hn⟩ := exists_gradedTraceOp_vanish N
    (mode (N.YM a) i * Y.val ((k : ℂ) + α - i - 2) w) hs e
  refine ⟨n, ?_⟩
  have h := gradedTrace_geomSolve _ (fun e =>
    -(∑ᶠ p : ℤ, cbz i p * trace Y (mode (A.YM a) p w) e)) _
    (fun e => by simpa only [sub_eq_add_neg] using trace_pair_step Y ha hw i e) e n hn
  simpa only [Finset.sum_neg_distrib] using h

/-- Negative weight shift: the mirror geometric sum starts at `j = 0`. -/
theorem trace_pair_geom_of_gt (Y : IntertwiningOperator A N N)
    {k : ℤ} {α : ℂ} {a : V} {w : M₁} (ha : a ∈ W.grading k) (hw : w ∈ A.weight α)
    {i : ℤ} (hi : k - 1 < i) (e : ℂ) :
    ∃ n : ℕ,
      gradedTraceOp N (mode (N.YM a) i * Y.val ((k : ℂ) + α - i - 2) w) e
        = ∑ j ∈ Finset.range n, ∑ᶠ p : ℤ,
          cbz i p * trace Y (mode (A.YM a) p w)
            (e + (j : ℂ) * ((k : ℂ) - i - 1)) := by
  have hs : ((k : ℂ) - i - 1).re < 0 := by
    simp only [Complex.sub_re, Complex.intCast_re, Complex.one_re]
    exact_mod_cast (show k - i - 1 < 0 by omega)
  obtain ⟨n, hn⟩ := exists_gradedTraceOp_vanish_up N
    (mode (N.YM a) i * Y.val ((k : ℂ) + α - i - 2) w) hs e
  refine ⟨n, ?_⟩
  have h := gradedTrace_geomSolve_up _ (fun e =>
    -(∑ᶠ p : ℤ, cbz i p * trace Y (mode (A.YM a) p w) e)) _
    (fun e => by simpa only [sub_eq_add_neg] using trace_pair_step Y ha hw i e) e n hn
  simpa only [Finset.sum_neg_distrib, neg_neg] using h

/-- The zero-shift relation, the uncollected `a[0]` vanishing identity. -/
theorem trace_zero_bracket (Y : IntertwiningOperator A N N)
    {k : ℤ} {α : ℂ} {a : V} {w : M₁} (ha : a ∈ W.grading k) (hw : w ∈ A.weight α)
    (e : ℂ) :
    (∑ᶠ p : ℤ, cbz (k - 1) p * trace Y (mode (A.YM a) p w) e) = 0 := by
  have h := trace_pair_step Y ha hw (k - 1) e
  have hs : (k : ℂ) - ((k - 1 : ℤ) : ℂ) - 1 = 0 := by push_cast; ring
  rw [hs, add_zero] at h
  linear_combination h

end VOA.Huang.GenusOne
