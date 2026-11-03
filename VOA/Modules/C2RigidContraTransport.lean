/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.C2RigidContraJacobi

/-!
# Port of `Modules/ContragredientTransport.lean` from `OrdVModule` to `GWModule`

Input to the McRae rigidity argument.  Statements and proofs are those of the original file, with the
structure `OrdVModule` replaced by `C2Rigid.GWModule` (graded weak modules, `L₀` possibly
non-semisimple) and the namespace `VOA` replaced by `VOA.C2Rigid`.  See
`Modules/C2RigidGraded.lean` for why this is the only change needed.
-/



namespace VOA.C2Rigid
open VertexOperatorAlgebra
open Module (End Dual)
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The matching input weight slot for output `α`: `γ = α + k + 1 − wt`, the inverse of
`dualOutIdx wt k γ = γ + wt − k − 1`. -/
def matchIdx (wt k : ℤ) (α : ℂ) : ℂ := α + (k : ℂ) + 1 - (wt : ℂ)

theorem dualOutIdx_matchIdx (wt k : ℤ) (α : ℂ) :
    dualOutIdx wt k (matchIdx wt k α) = α := by
  simp only [dualOutIdx, matchIdx]; ring

theorem matchIdx_of_dualOutIdx (wt k : ℤ) (γ : ℂ) :
    matchIdx wt k (dualOutIdx wt k γ) = γ := by
  simp only [dualOutIdx, matchIdx]; ring

/-- **The transpose-pairing bridge on a single graded generator** (no extra hypothesis): for
homogeneous `u ∈ 𝒱_wt` and `xα ∈ M_α`, the pairing of `(YMdual N u)₍ₖ₎ (lof γ g)` against `xα`
is the `Y_M`-side functional when `γ` is the matching slot, else `0`. -/
theorem dualPairing_mode_lof (N : GWModule W M) {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt)
    (k : ℤ) (γ : ℂ) (g : Module.Dual ℂ (N.weight γ)) {α : ℂ} {xα : M}
    (hxα : xα ∈ N.weight α) :
    dualPairing N xα (mode (YMdual N u) k
        (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) γ g))
      = (if α = dualOutIdx wt k γ then dualCompMap N wt u k γ g xα else 0) := by
  by_cases h : α = dualOutIdx wt k γ
  · rw [if_pos h, dualPairing_mode_lof_matched N hu k γ g hxα h]
  · rw [if_neg h, dualPairing_mode_lof_mismatched N hu k γ g hxα h]

/-- The `Y_M`-side **adjoint vector** in `M_{matchIdx wt k α}` (the transpose target of the
contragredient mode): `(−1)^wt ∑_{j≤wt} (1/j!) proj_{matchIdx} ((L₁ʲu)₍2wt−k−2−j₎ xα)`. -/
noncomputable def adjVec (N : GWModule W M) (wt : ℤ) (u : 𝒱) (k : ℤ) (α : ℂ) (xα : M) :
    N.weight (matchIdx wt k α) :=
  (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
    internalProjTo N.isInternal (matchIdx wt k α)
      (mode (N.YM ((W.L 1 ^ j) u)) (2 * wt - k - 2 - (j : ℤ)) xα)

/-- `dualCompMap` on the matched slot is `g` applied to `adjVec`. -/
theorem dualCompMap_matched_eq_adjVec (N : GWModule W M) (wt : ℤ) (u : 𝒱) (k : ℤ) (α : ℂ)
    (g : Module.Dual ℂ (N.weight (matchIdx wt k α))) {xα : M} :
    dualCompMap N wt u k (matchIdx wt k α) g xα = g (adjVec N wt u k α xα) := by
  rw [dualCompMap_apply, adjVec]
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_smul]

/-- **The module adjoint of `Y_M`** (no extra hypothesis), generator form: the pairing
`⟨xα, (YMdual N u)₍ₖ₎ f⟩` reads off `f`'s `matchIdx`-component applied to the `Y_M`-side adjoint
vector `adjVec`. The module analogue of the `𝒱`-level skew adjoint `form_smul_skew`. -/
theorem dualPairing_mode_homog (N : GWModule W M) {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt)
    (k : ℤ) (f : RestrictedDual N) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    dualPairing N xα (mode (YMdual N u) k f)
      = (DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) (matchIdx wt k α) f)
          (adjVec N wt u k α xα) := by
  classical
  set Lhs : RestrictedDual N →ₗ[ℂ] ℂ :=
    (dualPairing N xα).comp (mode (YMdual N u) k) with hLhs
  set Rhs : RestrictedDual N →ₗ[ℂ] ℂ :=
    (LinearMap.flip (LinearMap.id (R := ℂ)
        (M := Module.Dual ℂ (N.weight (matchIdx wt k α)))) (adjVec N wt u k α xα)).comp
      (DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) (matchIdx wt k α)) with hRhs
  have hgen : Lhs = Rhs := by
    refine DirectSum.linearMap_ext ℂ (fun γ => ?_)
    refine LinearMap.ext (fun g => ?_)
    show dualPairing N xα (mode (YMdual N u) k
        (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) γ g))
      = (DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) (matchIdx wt k α)
          (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) γ g)) (adjVec N wt u k α xα)
    rw [dualPairing_mode_lof N hu k γ g hxα]
    by_cases h : γ = matchIdx wt k α
    · subst h
      have hαout : α = dualOutIdx wt k (matchIdx wt k α) := (dualOutIdx_matchIdx wt k α).symm
      rw [if_pos hαout, DirectSum.component.lof_self,
        dualCompMap_matched_eq_adjVec N wt u k α g]
    · have hαout : α ≠ dualOutIdx wt k γ := by
        intro hc; exact h (by rw [hc, matchIdx_of_dualOutIdx])
      rw [if_neg hαout, DirectSum.component.of, dif_neg h, LinearMap.zero_apply]
  exact DFunLike.congr_fun hgen f

/-- The `M`-vector transpose of one contragredient mode `(YMdual N u)₍ₖ₎`, for homogeneous
`u ∈ 𝒱_wt`, on a weight vector `xα ∈ M_α`: `↑(adjVec N wt u k α xα) ∈ M`. -/
noncomputable def dualAdj (N : GWModule W M) (wt : ℤ) (u : 𝒱) (k : ℤ) (α : ℂ) (xα : M) : M :=
  ((adjVec N wt u k α xα : N.weight (matchIdx wt k α)) : M)

/-- `dualAdj N wt u k α xα` lands in the weight space `M_{matchIdx wt k α}`. -/
theorem dualAdj_mem (N : GWModule W M) (wt : ℤ) (u : 𝒱) (k : ℤ) (α : ℂ) (xα : M) :
    dualAdj N wt u k α xα ∈ N.weight (matchIdx wt k α) :=
  (adjVec N wt u k α xα).2

/-- **The operator-level module adjoint of `Y_M`** (no extra hypothesis): the pairing
`⟨xα, (YMdual N u)₍ₖ₎ f⟩` equals `⟨dualAdj…, f⟩` — the contragredient mode is the genuine transpose
of the `Y_M`-built vector `dualAdj`. -/
theorem dualPairing_mode_adj (N : GWModule W M) {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt)
    (k : ℤ) (f : RestrictedDual N) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    dualPairing N xα (mode (YMdual N u) k f)
      = dualPairing N ((adjVec N wt u k α xα : N.weight (matchIdx wt k α)) : M) f := by
  rw [dualPairing_mode_homog N hu k f hxα]
  rw [dualPairing_component N f
        (show ((adjVec N wt u k α xα : N.weight (matchIdx wt k α)) : M)
            ∈ N.weight (matchIdx wt k α) from (adjVec N wt u k α xα).2)]

/-- Restating `dualPairing_mode_adj` with `dualAdj`. -/
theorem dualPairing_mode_dualAdj (N : GWModule W M) {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt)
    (k : ℤ) (f : RestrictedDual N) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    dualPairing N xα (mode (YMdual N u) k f)
      = dualPairing N (dualAdj N wt u k α xα) f :=
  dualPairing_mode_adj N hu k f hxα

/-- **Double-mode transport** (no extra hypothesis): a nested contragredient pairing transports to
a `dualPairing` against the `Y_M`-side double transpose `dualAdj ∘ dualAdj`. -/
theorem dualPairing_mode2 (N : GWModule W M) {wtu : ℤ} {u : 𝒱} (hu : u ∈ W.grading wtu)
    {wtv : ℤ} {v : 𝒱} (hv : v ∈ W.grading wtv) (p q : ℤ) (f : RestrictedDual N) {α : ℂ}
    {xα : M} (hxα : xα ∈ N.weight α) :
    dualPairing N xα (mode (YMdual N u) p (mode (YMdual N v) q f))
      = dualPairing N
          (dualAdj N wtv v q (matchIdx wtu p α) (dualAdj N wtu u p α xα))
          f := by
  rw [dualPairing_mode_dualAdj N hu p (mode (YMdual N v) q f) hxα]
  rw [dualPairing_mode_dualAdj N hv q f (dualAdj_mem N wtu u p α xα)]

/-- The residual identity at one homogeneous datum: the `Y_M`-side nested-transpose Borcherds
identity. -/
def DualAdjResidualAt (N : GWModule W M) (wtu : ℤ) (u : 𝒱) (wtv : ℤ) (v : 𝒱)
    (f : RestrictedDual N) (ℓ m n : ℤ) (α : ℂ) (xα : M) : Prop :=
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (dualPairing N
            (dualAdj N wtv v (n + i) (matchIdx wtu (ℓ + m - i) α)
              (dualAdj N wtu u (ℓ + m - i) α xα)) f
          - negOnePow ℓ • dualPairing N
              (dualAdj N wtu u (m + i) (matchIdx wtv (ℓ + n - i) α)
                (dualAdj N wtv v (ℓ + n - i) α xα)) f))
      = ∑ᶠ i : ℤ, cbz m i •
          dualPairing N xα (mode (YMdual N (W.smul u (ℓ + i) v)) (m + n - i) f)

/-- **Homogeneous reduction.** For homogeneous `u, v`, the paired contragredient-Jacobi instance is
*literally* its transported residual `DualAdjResidualAt` (transport each LHS double-mode summand via
`dualPairing_mode2`). -/
theorem contraJacobiPaired_at_iff_residual (N : GWModule W M)
    {wtu : ℤ} {u : 𝒱} (hu : u ∈ W.grading wtu) {wtv : ℤ} {v : 𝒱} (hv : v ∈ W.grading wtv)
    (f : RestrictedDual N) (ℓ m n : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    ((∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (dualPairing N xα (mode (YMdual N u) (ℓ + m - i) (mode (YMdual N v) (n + i) f))
          - negOnePow ℓ • dualPairing N xα
              (mode (YMdual N v) (ℓ + n - i) (mode (YMdual N u) (m + i) f))))
      = ∑ᶠ i : ℤ, cbz m i •
          dualPairing N xα (mode (YMdual N (W.smul u (ℓ + i) v)) (m + n - i) f))
    ↔ DualAdjResidualAt N wtu u wtv v f ℓ m n α xα := by
  unfold DualAdjResidualAt
  constructor
  · intro h
    rw [← h]
    refine finsum_congr (fun i => ?_)
    congr 2
    · rw [dualPairing_mode2 N hu hv (ℓ + m - i) (n + i) f hxα]
    · congr 1
      rw [dualPairing_mode2 N hv hu (ℓ + n - i) (m + i) f hxα]
  · intro h
    rw [← h]
    refine finsum_congr (fun i => ?_)
    congr 2
    · rw [dualPairing_mode2 N hu hv (ℓ + m - i) (n + i) f hxα]
    · congr 1
      rw [dualPairing_mode2 N hv hu (ℓ + n - i) (m + i) f hxα]

/-- **The clean module-level residual hypothesis** (the module analogue of
`Core.InvariantFormDiagonal.DiagonalFHL` / `ResidualFHL`): the `Y_M`-side nested-transpose Borcherds
identity for every homogeneous datum. -/
def DualAdjResidual (N : GWModule W M) : Prop :=
  ∀ (wtu : ℤ) (u : 𝒱), u ∈ W.grading wtu → ∀ (wtv : ℤ) (v : 𝒱), v ∈ W.grading wtv →
    ∀ (f : RestrictedDual N) (ℓ m n : ℤ) (α : ℂ) (xα : M), xα ∈ N.weight α →
      DualAdjResidualAt N wtu u wtv v f ℓ m n α xα

/-- **Main theorem (homogeneous slice).** From `DualAdjResidual N`, the paired contragredient-Jacobi
identity holds for every *homogeneous* `u, v` (and all `f, ℓ, m, n, α, xα`). -/
theorem contraJacobiPaired_homog_of_residual (N : GWModule W M) (hres : DualAdjResidual N)
    {wtu : ℤ} {u : 𝒱} (hu : u ∈ W.grading wtu) {wtv : ℤ} {v : 𝒱} (hv : v ∈ W.grading wtv)
    (f : RestrictedDual N) (ℓ m n : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (dualPairing N xα (mode (YMdual N u) (ℓ + m - i) (mode (YMdual N v) (n + i) f))
          - negOnePow ℓ • dualPairing N xα
              (mode (YMdual N v) (ℓ + n - i) (mode (YMdual N u) (m + i) f))))
      = ∑ᶠ i : ℤ, cbz m i •
          dualPairing N xα (mode (YMdual N (W.smul u (ℓ + i) v)) (m + n - i) f) :=
  (contraJacobiPaired_at_iff_residual N hu hv f ℓ m n hxα).mpr
    (hres wtu u hu wtv v hv f ℓ m n α xα hxα)


/-! ## (VII) The projection-eliminated `M`-vector reformulation of the residual.

The reduction of §VI lands the paired residual `DualAdjResidualAt` (with the abstract contragredient
mode `mode (YMdual N ·)` and the free `f`). Here we strip both: using `dualPairing_mode_dualAdj`
once more on the RHS and the linearity of `dualPairing N` in the `M`-slot, the residual is reduced
to a concrete, `f`-free, projection-free identity in `M` — `DualAdjResidualMvec` — the genuine
module FHL **Borcherds identity for the `dualAdj` operators**: that the `Y_M`-side adjoint operators
`dualAdj` satisfy the same commutator/Jacobi identity as `Y_M` itself. This is proved
unconditionally (axiom-clean — `Modules/ContragredientClose.lean`, `dualAdjResidualMvec_holds`),
via the module Jacobi `N.jacobi` plus the sl₂/skew state-recombination. -/

/-- `↑(proj_β y) = y` for `y ∈ N.weight β`. -/
theorem internalProjTo_coe_mem (N : GWModule W M) {β : ℂ} {y : M} (hy : y ∈ N.weight β) :
    ((internalProjTo N.isInternal β y : N.weight β) : M) = y :=
  congrArg Subtype.val (internalProjTo_coe N.isInternal β ⟨y, hy⟩)

/-- **Clean `Y_M` form of `dualAdj`** (projection elimination): for homogeneous `u ∈ 𝒱_wt`,
`xα ∈ M_α`, the projector in `adjVec` is the identity. -/
theorem dualAdj_clean (N : GWModule W M) {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt)
    (k : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    dualAdj N wt u k α xα
      = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
          mode (N.YM ((W.L 1 ^ j) u)) (2 * wt - k - 2 - (j : ℤ)) xα := by
  unfold dualAdj adjVec
  rw [SetLike.val_smul]
  congr 1
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [SetLike.val_smul]
  congr 1
  apply internalProjTo_coe_mem
  have h := twistMode_mem_weight N hu hxα k j
  rwa [show (α + (k : ℂ) + 1 - (wt : ℂ)) = matchIdx wt k α from by rw [matchIdx]] at h

/-- `dualAdj` of the zero state vanishes. -/
theorem dualAdj_zero_state (N : GWModule W M) (wt : ℤ) (k : ℤ) {α : ℂ} {xα : M}
    (hxα : xα ∈ N.weight α) : dualAdj N wt (0 : 𝒱) k α xα = 0 := by
  rw [dualAdj_clean N (Submodule.zero_mem _) k hxα]
  refine smul_eq_zero_of_right _ (Finset.sum_eq_zero (fun j _ => ?_))
  rw [map_zero, map_zero]
  exact smul_eq_zero_of_right _ rfl

/-- `dualAdj` of the zero M-vector vanishes. -/
theorem dualAdj_zero_vec (N : GWModule W M) {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt) (k : ℤ)
    (α : ℂ) : dualAdj N wt u k α (0 : M) = 0 := by
  rw [dualAdj_clean N hu k (Submodule.zero_mem (N.weight α))]
  rw [Finset.sum_eq_zero (fun j _ => ?_), smul_zero]
  rw [map_zero, smul_zero]

/-- **Mode-index truncation of `dualAdj`**: for homogeneous `u, xα`, `dualAdj N wt u k α xα = 0`
once `k` is small enough (the twisted `Y_M` modes truncate). -/
theorem dualAdj_eventually_zero_below (N : GWModule W M) {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt)
    {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    ∃ K : ℤ, ∀ k : ℤ, k ≤ K → dualAdj N wt u k α xα = 0 := by
  classical
  -- For each j, choose a truncation threshold for the mode N.YM (L₁ʲu) on xα.
  have hthr : ∀ j : ℕ, ∃ Nthr : ℤ,
      ∀ s : ℤ, Nthr ≤ s → mode (N.YM ((W.L 1 ^ j) u)) s xα = 0 :=
    fun j => N.truncation ((W.L 1 ^ j) u) xα
  choose Nf hNf using hthr
  obtain ⟨S, hSbound⟩ : ∃ S : ℤ, ∀ j ∈ Finset.range (wt.toNat + 1), (j : ℤ) + Nf j ≤ S :=
    ⟨(Finset.range (wt.toNat + 1)).sup' (by simp) (fun (j : ℕ) => (j : ℤ) + Nf j),
      fun j hj => Finset.le_sup' (fun (j : ℕ) => (j : ℤ) + Nf j) hj⟩
  refine ⟨2 * wt - 2 - S, fun k hk => ?_⟩
  rw [dualAdj_clean N hu k hxα, Finset.sum_eq_zero (fun j hj => ?_), smul_zero]
  rw [hNf j (2 * wt - k - 2 - (j : ℤ)) ?_, smul_zero]
  have hSj := hSbound j hj
  omega

/-! ## The dual pairing is linear in the `M`-slot. -/

theorem dualPairing_add_left (N : GWModule W M) (x y : M) (f : RestrictedDual N) :
    dualPairing N (x + y) f = dualPairing N x f + dualPairing N y f := by
  refine DirectSum.induction_on f ?_ (fun γ g => ?_) (fun a b ha hb => ?_)
  · change dualPairing N (x + y) (0 : RestrictedDual N)
        = dualPairing N x (0 : RestrictedDual N) + dualPairing N y (0 : RestrictedDual N)
    rw [map_zero, map_zero, map_zero, add_zero]
  · have hof : (DirectSum.of (fun β => Module.Dual ℂ (N.weight β)) γ g)
        = DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) γ g := rfl
    rw [hof, dualPairing_lof, dualPairing_lof, dualPairing_lof]
    simp only [map_add]
  · have e1 : dualPairing N (x + y) (a + b) = dualPairing N (x + y) a + dualPairing N (x + y) b :=
      map_add _ _ _
    have e2 : dualPairing N x (a + b) = dualPairing N x a + dualPairing N x b := map_add _ _ _
    have e3 : dualPairing N y (a + b) = dualPairing N y a + dualPairing N y b := map_add _ _ _
    linear_combination e1 - e2 - e3 + ha + hb

theorem dualPairing_smul_left (N : GWModule W M) (c : ℂ) (x : M) (f : RestrictedDual N) :
    dualPairing N (c • x) f = c • dualPairing N x f := by
  refine DirectSum.induction_on f ?_ (fun γ g => ?_) (fun a b ha hb => ?_)
  · change dualPairing N (c • x) (0 : RestrictedDual N) = c • dualPairing N x (0 : RestrictedDual N)
    rw [map_zero, map_zero, smul_zero]
  · have hof : (DirectSum.of (fun β => Module.Dual ℂ (N.weight β)) γ g)
        = DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) γ g := rfl
    rw [hof, dualPairing_lof, dualPairing_lof]
    simp only [map_smul, smul_eq_mul]
  · have e1 : dualPairing N (c • x) (a + b) = dualPairing N (c • x) a + dualPairing N (c • x) b :=
      map_add _ _ _
    have e2 : dualPairing N x (a + b) = dualPairing N x a + dualPairing N x b := map_add _ _ _
    have ha' : dualPairing N (c • x) a = c * dualPairing N x a := by rw [ha, smul_eq_mul]
    have hb' : dualPairing N (c • x) b = c * dualPairing N x b := by rw [hb, smul_eq_mul]
    rw [smul_eq_mul]; linear_combination e1 + ha' + hb' - c * e2

/-- The dual pairing as a `ℂ`-linear functional in the **`M`-slot** (fixed `f`). -/
noncomputable def dualPairingFlip (N : GWModule W M) (f : RestrictedDual N) : M →ₗ[ℂ] ℂ where
  toFun x := dualPairing N x f
  map_add' := fun x y => dualPairing_add_left N x y f
  map_smul' := fun c x => dualPairing_smul_left N c x f

@[simp] theorem dualPairingFlip_apply (N : GWModule W M) (f : RestrictedDual N) (x : M) :
    dualPairingFlip N f x = dualPairing N x f := rfl

/-! ## The `M`-vector residual (the crux, projection-eliminated). -/

/-- **The `M`-vector Borcherds identity for the `dualAdj` operators** — the projection-eliminated,
`f`-free crux equivalent to `DualAdjResidualAt`. This is the genuine FHL content: the adjoint
operators `dualAdj` satisfy the same Borcherds/Jacobi commutator identity as `Y_M`. -/
def DualAdjResidualMvecAt (N : GWModule W M) (wtu : ℤ) (u : 𝒱) (wtv : ℤ) (v : 𝒱)
    (ℓ m n : ℤ) (α : ℂ) (xα : M) : Prop :=
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (dualAdj N wtv v (n + i) (matchIdx wtu (ℓ + m - i) α)
            (dualAdj N wtu u (ℓ + m - i) α xα)
          - negOnePow ℓ • dualAdj N wtu u (m + i) (matchIdx wtv (ℓ + n - i) α)
              (dualAdj N wtv v (ℓ + n - i) α xα)))
      = ∑ᶠ i : ℤ, cbz m i •
          dualAdj N (wtu + wtv - (ℓ + i) - 1) (W.smul u (ℓ + i) v) (m + n - i) α xα

/-- Finiteness of the `M`-vector RHS summand. -/
theorem starRHS_Mvec_fin (N : GWModule W M) {wtu : ℤ} {u : 𝒱} (_hu : u ∈ W.grading wtu)
    {wtv : ℤ} {v : 𝒱} (_hv : v ∈ W.grading wtv) (ℓ m n : ℤ) {α : ℂ} {xα : M}
    (hxα : xα ∈ N.weight α) :
    (Function.support fun i : ℤ => cbz m i •
      dualAdj N (wtu + wtv - (ℓ + i) - 1) (W.smul u (ℓ + i) v) (m + n - i) α xα).Finite := by
  obtain ⟨Ns, hNs⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
  apply Set.Finite.subset (Set.finite_Icc 0 (Ns - ℓ))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg m h, zero_smul]
  · rw [show W.smul u (ℓ + i) v = 0 from hNs (ℓ + i) (by omega), dualAdj_zero_state N _ _ hxα,
      smul_zero]

/-- Finiteness of the `M`-vector LHS summand. -/
theorem starLHS_Mvec_fin (N : GWModule W M) {wtu : ℤ} {u : 𝒱} (hu : u ∈ W.grading wtu)
    {wtv : ℤ} {v : 𝒱} (hv : v ∈ W.grading wtv) (ℓ m n : ℤ) {α : ℂ} {xα : M}
    (hxα : xα ∈ N.weight α) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ℓ i) •
        (dualAdj N wtv v (n + i) (matchIdx wtu (ℓ + m - i) α)
            (dualAdj N wtu u (ℓ + m - i) α xα)
          - negOnePow ℓ • dualAdj N wtu u (m + i) (matchIdx wtv (ℓ + n - i) α)
              (dualAdj N wtv v (ℓ + n - i) α xα))).Finite := by
  obtain ⟨Ku, hKu⟩ := dualAdj_eventually_zero_below N hu hxα
  obtain ⟨Kv, hKv⟩ := dualAdj_eventually_zero_below N hv hxα
  apply Set.Finite.subset (Set.finite_Icc 0 (max (ℓ + m - Ku) (ℓ + n - Kv)))
  intro i hi
  rw [Function.mem_support] at hi; rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · -- i > max(...) : both inner dualAdj vanish, so the bracket is 0
    have hAu : dualAdj N wtu u (ℓ + m - i) α xα = 0 := hKu _ (by omega)
    have hBv : dualAdj N wtv v (ℓ + n - i) α xα = 0 := hKv _ (by omega)
    rw [hAu, dualAdj_zero_vec N hv _ _, hBv, dualAdj_zero_vec N hu _ _, smul_zero, sub_zero,
      smul_zero]

/-- **The reduction.** The projection-eliminated `M`-vector Borcherds identity
`DualAdjResidualMvecAt` implies the paired residual `DualAdjResidualAt` (for every `f`). The
crux is an `f`-free identity in `M`. -/
theorem dualAdjResidualAt_of_mvec (N : GWModule W M)
    {wtu : ℤ} {u : 𝒱} (hu : u ∈ W.grading wtu) {wtv : ℤ} {v : 𝒱} (hv : v ∈ W.grading wtv)
    (f : RestrictedDual N) (ℓ m n : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α)
    (hmv : DualAdjResidualMvecAt N wtu u wtv v ℓ m n α xα) :
    DualAdjResidualAt N wtu u wtv v f ℓ m n α xα := by
  unfold DualAdjResidualAt
  unfold DualAdjResidualMvecAt at hmv
  -- transpose RHS termwise via the single-mode adjoint
  have hrhs : (∑ᶠ i : ℤ, cbz m i •
        dualPairing N xα (mode (YMdual N (W.smul u (ℓ + i) v)) (m + n - i) f))
      = ∑ᶠ i : ℤ, cbz m i • dualPairing N
          (dualAdj N (wtu + wtv - (ℓ + i) - 1) (W.smul u (ℓ + i) v) (m + n - i) α xα) f :=
    finsum_congr (fun i => by
      rw [dualPairing_mode_dualAdj N (W.smul_mem_grading hu hv (ℓ + i)) (m + n - i) f hxα])
  rw [hrhs]
  -- push `dualPairing N · f` (as `dualPairingFlip`) through both M-vector finsums
  have hL : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (dualPairing N (dualAdj N wtv v (n + i) (matchIdx wtu (ℓ + m - i) α)
            (dualAdj N wtu u (ℓ + m - i) α xα)) f
          - negOnePow ℓ • dualPairing N (dualAdj N wtu u (m + i) (matchIdx wtv (ℓ + n - i) α)
              (dualAdj N wtv v (ℓ + n - i) α xα)) f))
      = dualPairingFlip N f (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (dualAdj N wtv v (n + i) (matchIdx wtu (ℓ + m - i) α)
              (dualAdj N wtu u (ℓ + m - i) α xα)
            - negOnePow ℓ • dualAdj N wtu u (m + i) (matchIdx wtv (ℓ + n - i) α)
                (dualAdj N wtv v (ℓ + n - i) α xα))) := by
    rw [map_finsum (dualPairingFlip N f) (starLHS_Mvec_fin N hu hv ℓ m n hxα)]
    exact finsum_congr (fun i => by simp only [map_smul, map_sub, dualPairingFlip_apply])
  have hR : (∑ᶠ i : ℤ, cbz m i • dualPairing N
          (dualAdj N (wtu + wtv - (ℓ + i) - 1) (W.smul u (ℓ + i) v) (m + n - i) α xα) f)
      = dualPairingFlip N f (∑ᶠ i : ℤ, cbz m i •
          dualAdj N (wtu + wtv - (ℓ + i) - 1) (W.smul u (ℓ + i) v) (m + n - i) α xα) := by
    rw [map_finsum (dualPairingFlip N f) (starRHS_Mvec_fin N hu hv ℓ m n hxα)]
    exact finsum_congr (fun i => by simp only [map_smul, dualPairingFlip_apply])
  rw [hL, hR, hmv]

/-- **The clean `M`-vector crux** (the module FHL Borcherds identity): the `dualAdj` operators
satisfy the Borcherds/Jacobi commutator identity of `Y_M`, for every homogeneous datum. The
projection-eliminated, `f`-free reformulation of `DualAdjResidual`. -/
def DualAdjResidualMvec (N : GWModule W M) : Prop :=
  ∀ (wtu : ℤ) (u : 𝒱), u ∈ W.grading wtu → ∀ (wtv : ℤ) (v : 𝒱), v ∈ W.grading wtv →
    ∀ (ℓ m n : ℤ) (α : ℂ) (xα : M), xα ∈ N.weight α →
      DualAdjResidualMvecAt N wtu u wtv v ℓ m n α xα

/-- **The reduction of `DualAdjResidual` to the clean `M`-vector crux.** -/
theorem dualAdjResidual_of_mvec (N : GWModule W M) (h : DualAdjResidualMvec N) :
    DualAdjResidual N :=
  fun wtu u hu wtv v hv f ℓ m n α xα hxα =>
    dualAdjResidualAt_of_mvec N hu hv f ℓ m n hxα (h wtu u hu wtv v hv ℓ m n α xα hxα)


end VOA.C2Rigid