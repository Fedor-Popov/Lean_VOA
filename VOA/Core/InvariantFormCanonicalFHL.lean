/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.InvariantFormAdjoint

/-!
# Canonical-form FHL: the vacuum-symmetry lever, the native reduction to `CanDiagonal`, and the
# quasi-primarity obstruction

The full invariance of the constructed canonical form `canBilin` (`Core.InvariantFormCanonical`),
reduced *natively* (not through the circular `DiagonalFHL`) to a single matching-mode identity, with
the genuine Li lever proved and the precise hypothesis it needs identified.

* **`vacCoord_smul_symm`** — *the Li vacuum-symmetry lever*: applying the grade-0 functional
  `vacCoord` to the skew mode formula collapses the `L₋₁`-tower to its `j=0` term, giving
  `vacCoord(u₍ₙ₎v) = sgn(−n−1)·vacCoord(v₍ₙ₎u)`. (Used nowhere else; the construction-level tool.)
* **`canBilin_eq_vacCoord_adjMode`** — the Li characterization `canBilin a b = −vacCoord(Y*(a)₍₋₁₎b)`.
* **`canRHS`/`CanDiagonal`/`canBilin_fullyInvariant_of_diagonal`** — the native reduction: off-diagonal
  vanishing + bilinearity reduce the full adjunction to the single matching-mode `CanDiagonal`.
* **`canBilin_fullyInvariant_wt_le_zero`** — the `wt ≤ 0` slices, proved *unconditionally*.
* **`virSlice_vacuum`** — the rigorous witness that the unconditional statement is **false**: the `u=ω`,
  `a=𝟙` Virasoro slice holds iff `vacCoord(L₁b)=0`, i.e. iff `L₁𝒱₁ = 0` (Gannon's standing
  hypothesis 5.1.11b / quasi-primarity). So the canonical form is invariant *exactly* under `L₁𝒱₁=0`.

## Status
**The residual is discharged in `Core.InvariantFormFHL2`.**  The residual named below is discharged, under the
standing hypotheses `hne : 𝟙 ≠ 0` and `hqp : L₁𝒱₁ = 0`, by `canDiagonal_unconditional : CanDiagonal hne`
and `canVirasoroAdj_of_diagonal`; the resulting form is `canonicalInvariantForm`.  The text below
describes this file's own reduction, an intermediate step.
Axiom-free reduction; bottoms out at the residual `CanDiagonal` (→ Li 1994; discharged, see above).
Axiom-clean for the lever, the native reduction, the `wt ≤ 0` cases, and the obstruction witness.
The remaining content of this file, `CanDiagonal` (a hypothesis, not an axiom), is provable **under
`L₁𝒱₁=0`** (the correct Gannon 5.1.11b hypothesis) via `vacCoord_smul_symm` + `mode_iterate`; without
it `CanVirasoroAdj`/full invariance is genuinely false (`virSlice_vacuum`).

## References
* Gannon §5.1.3, eqs. (5.1.11)–(5.1.12); Frenkel–Huang–Lepowsky [199]; Li [380].
-/

namespace VOA
open VOA.VertexOperatorAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-! ## The vacuum-symmetry lemma (the Li lever)

`vacCoord` annihilates the image of `L₋₁` on homogeneous vectors (`vacCoord_Lneg1_homog`).
Applying it to the skew-symmetry mode formula `u₍ₙ₎v = ∑ⱼ (1/j!) sgn(-n-1-j) (L₋₁)ʲ(v₍-n-1-j₎u)`
kills every `j ≥ 1` term, leaving the single `j = 0` term:
`vacCoord(u₍ₙ₎v) = sgn(-n-1)·vacCoord(v₍-n-1₎u)`. -/

/-- **The vacuum symmetry** (Li's lever). For homogeneous `u ∈ V_p`, `v ∈ V_q`, applying the
grade-0 functional `vacCoord` to the skew mode formula collapses the `L₋₁`-tower to its `j = 0`
term: `vacCoord(u₍ₙ₎v) = sgn(-n-1)·vacCoord(v₍ₙ₎u)`. -/
theorem vacCoord_smul_symm (hne : W.vacuum ≠ 0) {p q : ℤ} {u v : V}
    (hu : u ∈ W.grading p) (hv : v ∈ W.grading q) (n : ℤ) :
    vacCoord W hne (W.smul u n v)
      = (sgn (-n - 1)) • vacCoord W hne (W.smul v n u) := by
  -- apply vacCoord (linear) to skew_mode
  have hskew := skew_mode W u v n
  apply_fun (fun x => vacCoord W hne x) at hskew
  rw [hskew]
  -- push vacCoord through the finsum (finiteness from skew_summand_finite W v u n)
  rw [map_finsum (vacCoord W hne) (skew_summand_finite W u v n)]
  -- now each summand: only j = 0 survives
  rw [finsum_eq_single _ 0 ?_]
  · -- j = 0 term
    rw [map_smul, map_smul]
    simp only [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one,
      one_smul, Nat.cast_zero, sub_zero]
    rw [Y_apply_eq_smul, show (-(-n - 1) - 1 : ℤ) = n by ring]
  · -- j ≠ 0 term vanishes
    intro j hj
    rw [map_smul, map_smul]
    have hvj : (W.Y v) (-n - 1 - j) u ∈ W.grading (q + p - (n + j) - 1) := by
      rw [Y_apply_eq_smul, show (-(-n - 1 - (j:ℤ)) - 1 : ℤ) = n + j by ring]
      have h := W.smul_mem_grading hv hu (n + (j:ℤ))
      rwa [show (q + p - (n + (j:ℤ)) - 1 : ℤ) = q + p - (n + j) - 1 by ring] at h
    -- Tʲ = (L₋₁)ʲ, j ≥ 1 ⟹ L₋₁ on homogeneous ⟹ vacCoord = 0
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [T_eq_Lneg1, pow_succ', Module.End.mul_apply]
    have hmem := L_neg_one_pow_raise W hvj k
    rw [vacCoord_Lneg1_homog hne hmem, smul_zero, smul_zero]

/-! ## Li's characterization: `canBilin a b = −vacCoord(Y*(a)₍₋₁₎ b)`

For homogeneous `a ∈ V_p`, the canonical form is (minus) the vacuum coefficient of the FHL adjoint
field `Y*(a) = Y(e^{zL₁}(−z⁻²)^{L₀}a, z⁻¹)` at the creation mode `n = −1`: `adjMode a p (−1)`.
This is exactly how the construction is defined (`adjPair = vacCoord ∘ adjMode … (−1)`). -/

/-- **The Li characterization** of `canBilin`: for `a ∈ V_p`,
`canBilin a b = −vacCoord(adjMode a p (−1) b)`. -/
theorem canBilin_eq_vacCoord_adjMode (hne : W.vacuum ≠ 0) {p : ℤ} {a : V}
    (ha : a ∈ W.grading p) (b : V) :
    canBilin W hne a b = - vacCoord W hne (adjMode W a p (-1) b) := by
  rw [canBilin_homog W hne ha, adjPair, adjMode_def, map_smul, map_sum]
  congr 2
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_smul, show (2 * p - -1 - 2 - (j:ℤ)) = 2 * p - 1 - (j:ℤ) by ring]

/-! ## The target predicate and its structural reductions

`canRHS u a b wt n` is the FHL `e^{zL₁}(−z⁻²)^{L₀}` adjoint sum that the full adjunction equates
`canBilin (u₍ₙ₎a) b` to.  We prove the structural facts (bilinearity, base cases, off-diagonal
vanishing) for `canBilin` directly. -/

/-- The FHL right-hand side for `canBilin`. -/
noncomputable def canRHS (hne : W.vacuum ≠ 0) (u a b : V) (wt n : ℤ) : ℂ :=
  (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
    canBilin W hne a (W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b)

/-- The full-invariance body at a fixed weight, for `canBilin`. -/
def CanFullyInvariantAt (hne : W.vacuum ≠ 0) (wt : ℤ) : Prop :=
  ∀ (u : V), u ∈ W.grading wt → ∀ (n : ℤ) (a b : V),
    canBilin W hne (W.smul u n a) b = canRHS hne u a b wt n

/-! ### Base cases -/

/-- **Below grade 0:** `𝒱_{wt} = 0`, both sides vanish. -/
theorem canFullyInvariantAt_neg (hne : W.vacuum ≠ 0) {wt : ℤ} (hwt : wt < 0) :
    CanFullyInvariantAt hne wt := by
  intro u hu n a b
  have hu0 : u = 0 := eq_zero_of_mem_neg_grading W hwt hu
  subst hu0
  rw [PreVertexAlgebra.smul_zero_left, map_zero, LinearMap.zero_apply, canRHS,
    show wt.toNat = 0 by omega]
  simp

/-- **At grade 0** (`u ∈ ℂ𝟙`): both sides reduce to `c·δ_{n,-1}·canBilin a b`. -/
theorem canFullyInvariantAt_zero (hne : W.vacuum ≠ 0) : CanFullyInvariantAt hne 0 := by
  intro u hu n a b
  rw [W.vacuum_grade, Submodule.mem_span_singleton] at hu
  obtain ⟨c, hc⟩ := hu
  subst hc
  rw [PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_vacuum_left, map_smul,
    LinearMap.smul_apply, smul_eq_mul, canRHS, show ((0:ℤ).toNat + 1) = 1 from rfl,
    Finset.sum_range_one, pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one,
    inv_one, one_smul, zpow_zero, one_smul, Nat.cast_zero,
    show (2 * (0 : ℤ) - n - 2 - 0) = -n - 2 by ring,
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_vacuum_left, map_smul, smul_eq_mul]
  by_cases hn : n = -1
  · subst hn; norm_num
  · rw [if_neg hn, if_neg (by omega : ¬ (-n - 2 = -1))]; simp

/-! ### Bilinearity of `canRHS` -/

theorem canRHS_add_right (hne : W.vacuum ≠ 0) (u a b₁ b₂ : V) (wt n : ℤ) :
    canRHS hne u a (b₁ + b₂) wt n = canRHS hne u a b₁ wt n + canRHS hne u a b₂ wt n := by
  rw [canRHS, canRHS, canRHS, ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [PreVertexAlgebra.smul_add_right, map_add, ← smul_add]

theorem canRHS_zero_right (hne : W.vacuum ≠ 0) (u a : V) (wt n : ℤ) :
    canRHS hne u a 0 wt n = 0 := by
  rw [canRHS, Finset.sum_eq_zero (fun j _ => ?_), smul_zero]
  rw [PreVertexAlgebra.smul_def, map_zero, map_zero, smul_zero]

theorem canRHS_add_left (hne : W.vacuum ≠ 0) (u a₁ a₂ b : V) (wt n : ℤ) :
    canRHS hne u (a₁ + a₂) b wt n = canRHS hne u a₁ b wt n + canRHS hne u a₂ b wt n := by
  rw [canRHS, canRHS, canRHS, ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_add, LinearMap.add_apply, ← smul_add]

theorem canRHS_zero_left (hne : W.vacuum ≠ 0) (u b : V) (wt n : ℤ) :
    canRHS hne u 0 b wt n = 0 := by
  rw [canRHS, Finset.sum_eq_zero (fun j _ => by rw [map_zero, LinearMap.zero_apply, smul_zero]),
    smul_zero]

/-! ### Off-diagonal vanishing (grading) -/

/-- `canRHS` vanishes off the matching mode for homogeneous `a, b`. -/
theorem canRHS_offdiag (hne : W.vacuum ≠ 0) {wt p q : ℤ} {u a b : V}
    (hu : u ∈ W.grading wt) (ha : a ∈ W.grading p) (hb : b ∈ W.grading q)
    (n : ℤ) (hn : n ≠ p + wt - q - 1) :
    canRHS hne u a b wt n = 0 := by
  rw [canRHS, Finset.sum_eq_zero, smul_zero]
  intro j _
  have hvj : ((W.L 1) ^ j) u ∈ W.grading (wt - (j : ℤ)) := L_one_pow_mem W hu j
  have hmem : W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b
      ∈ W.grading (n + q + 1 - wt) := by
    have h := W.smul_mem_grading hvj hb (2 * wt - n - 2 - (j : ℤ))
    rwa [show (wt - (j : ℤ) + q - (2 * wt - n - 2 - (j : ℤ)) - 1 : ℤ) = n + q + 1 - wt by ring] at h
  rw [canBilin_offdiag hne ha hmem (by omega : p ≠ n + q + 1 - wt), smul_zero]

/-- The true value `canBilin(u₍ₙ₎a) b` vanishes off the matching mode for homogeneous `a, b`. -/
theorem canLHS_offdiag (hne : W.vacuum ≠ 0) {wt p q : ℤ} {u a b : V}
    (hu : u ∈ W.grading wt) (ha : a ∈ W.grading p) (hb : b ∈ W.grading q)
    (n : ℤ) (hn : n ≠ p + wt - q - 1) :
    canBilin W hne (W.smul u n a) b = 0 := by
  have hmem : W.smul u n a ∈ W.grading (wt + p - n - 1) := by
    have h := W.smul_mem_grading hu ha n
    rwa [show (wt + p - n - 1 : ℤ) = wt + p - n - 1 by ring] at h
  exact canBilin_offdiag hne hmem hb (by omega : wt + p - n - 1 ≠ q)

/-! ### Reduction to the matching-mode diagonal -/

/-- The **matching-mode diagonal identity** for `canBilin`: for homogeneous `a ∈ V_p`, `b ∈ V_q`,
`u ∈ V_wt`, the full adjunction at the unique non-orthogonal mode `n = p + wt − q − 1`. -/
def CanDiagonal (hne : W.vacuum ≠ 0) : Prop :=
  ∀ (wt p q : ℤ) (u a b : V), u ∈ W.grading wt → a ∈ W.grading p → b ∈ W.grading q →
    canBilin W hne (W.smul u (p + wt - q - 1) a) b = canRHS hne u a b wt (p + wt - q - 1)

/-- **`CanFullyInvariantAt wt` for all `wt` from the matching-mode diagonal.**  Off-diagonal
vanishing (`canLHS_offdiag`/`canRHS_offdiag`) plus bilinearity reduces every mode to the matching
one. -/
theorem canFullyInvariantAt_of_diagonal (hne : W.vacuum ≠ 0) (hdiag : CanDiagonal hne)
    (wt : ℤ) : CanFullyInvariantAt hne wt := by
  intro u hu n a b
  have hatop : a ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun a =>
      ∀ b : V, canBilin W hne (W.smul u n a) b = canRHS hne u a b wt n) hatop ?_ ?_ ?_ b
  · intro p a ha b
    have hbtop : b ∈ ⨆ i, W.grading i := by
      rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction W.grading (motive := fun b =>
        canBilin W hne (W.smul u n a) b = canRHS hne u a b wt n) hbtop ?_ ?_ ?_
    · intro q b hb
      by_cases hn : n = p + wt - q - 1
      · subst hn; exact hdiag wt p q u a b hu ha hb
      · rw [canLHS_offdiag hne hu ha hb n hn, canRHS_offdiag hne hu ha hb n hn]
    · show canBilin W hne (W.smul u n a) 0 = canRHS hne u a 0 wt n
      rw [map_zero, canRHS_zero_right]
    · intro b₁ b₂ hb₁ hb₂
      show canBilin W hne (W.smul u n a) (b₁ + b₂) = canRHS hne u a (b₁ + b₂) wt n
      rw [map_add, hb₁, hb₂, canRHS_add_right]
  · intro b
    show canBilin W hne (W.smul u n 0) b = canRHS hne u 0 b wt n
    rw [PreVertexAlgebra.smul_def, map_zero, map_zero, LinearMap.zero_apply, canRHS_zero_left]
  · intro a₁ a₂ ha₁ ha₂ b
    show canBilin W hne (W.smul u n (a₁ + a₂)) b = canRHS hne u (a₁ + a₂) b wt n
    rw [W.smul_add_right, map_add, LinearMap.add_apply, ha₁ b, ha₂ b, canRHS_add_left]

/-! ### The main theorem, from the diagonal -/

/-- **Full adjunction for `canBilin` from the matching-mode diagonal.** -/
theorem canBilin_fullyInvariant_of_diagonal (hne : W.vacuum ≠ 0) (hdiag : CanDiagonal hne)
    (wt : ℤ) (u : V) (hu : u ∈ W.grading wt) (n : ℤ) (a b : V) :
    canBilin W hne (W.smul u n a) b
      = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
          canBilin W hne a (W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b) :=
  canFullyInvariantAt_of_diagonal hne hdiag wt u hu n a b

/-! ## A genuine obstruction: the unconditional target is FALSE without `L₁𝒱₁ = 0`

The full adjunction `canBilin_fullyInvariant` (with `u = ω`) implies the Virasoro-adjointness
`canBilin(L₋₁a) b = canBilin a (L₁b)`.  But for `a = 𝟙`: the left side is
`canBilin(L₋₁𝟙) b = canBilin 0 b = 0` (since `L₋₁𝟙 = 0`), while the right side is
`canBilin 𝟙 (L₁b) = −vacCoord(L₁b)` (since `canBilin 𝟙 X = −vacCoord X`).  These agree **iff**
`vacCoord(L₁b) = 0`, i.e. (taking `b ∈ 𝒱₁`, so `L₁b ∈ 𝒱₀ = ℂ𝟙`) **iff `L₁𝒱₁ = 0`**.

So the canonical form is invariant exactly under Gannon's standing hypothesis `L₁𝒱₁ = 0`
(5.1.11b / quasi-primarity).  Without it the construction is genuinely NOT Virasoro-adjoint, and
the unconditional `canBilin_fullyInvariant` is **not a theorem** — matching
the `Core.InvariantFormFHLClosure` finding that the residuals are FHL-strength.  This is recorded
honestly, not papered over. -/

/-- **The `n = −1` Virasoro slice, on `a = 𝟙`, reduces to a clean `vacCoord(L₁b)` condition.**
`canBilin(L₋₁𝟙) b = 0` always, whereas `canBilin 𝟙 (L₁b) = −vacCoord(L₁b)`.  Hence the
adjointness `canBilin(L₋₁𝟙) b = canBilin 𝟙 (L₁b)` holds iff `vacCoord(L₁b) = 0`. -/
theorem virSlice_vacuum (hne : W.vacuum ≠ 0) (b : V) :
    canBilin W hne (W.L (-1) W.vacuum) b = 0
      ∧ canBilin W hne W.vacuum (W.L 1 b) = - vacCoord W hne (W.L 1 b) := by
  refine ⟨by rw [L_neg_one_vacuum, map_zero, LinearMap.zero_apply], ?_⟩
  rw [canBilin_homog W hne W.vacuum_mem, adjPair, show ((0:ℤ).toNat + 1) = 1 from rfl,
    Finset.sum_range_one, pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one,
    inv_one, one_smul, Nat.cast_zero, zpow_zero, show (2 * (0:ℤ) - 1 - 0) = -1 by ring,
    PreVertexAlgebra.smul_vacuum_left, if_pos rfl, one_smul]

/-! ## Unconditional special cases (weights `≤ 0`) -/

/-- **Weight ≤ 0, unconditionally.**  For `u ∈ V_wt` with `wt ≤ 0` (so `u ∈ ℂ𝟙` if `wt = 0`,
else `u = 0`), the full adjunction holds with no hypothesis. -/
theorem canBilin_fullyInvariant_wt_le_zero (hne : W.vacuum ≠ 0) {wt : ℤ} (hwt : wt ≤ 0)
    (u : V) (hu : u ∈ W.grading wt) (n : ℤ) (a b : V) :
    canBilin W hne (W.smul u n a) b
      = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
          canBilin W hne a (W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b) := by
  rcases lt_or_eq_of_le hwt with h | h
  · exact canFullyInvariantAt_neg hne h u hu n a b
  · subst h; exact canFullyInvariantAt_zero hne u hu n a b

end VOA
