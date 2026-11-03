/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.C2RigidContraTransport
import VOA.Core.InvariantFormDiagonal

/-!
# Port of `Modules/ContragredientFHL.lean` from `OrdVModule` to `GWModule`

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

/-- **Iterated module translation covariance**: `(L₋₁ʲ w)₍s₎ᴹ x = (−1)ʲ (∏_{l<j}(s−l)) • w₍s−j₎ᴹ x`.
By induction on `j` off `act_T_covariance`. Hqp-free. -/
theorem mode_Lneg1_pow (N : GWModule W M) (w : 𝒱) (j : ℕ) (s : ℤ) (x : M) :
    mode (N.YM (((W.L (-1)) ^ j) w)) s x
      = (-1 : ℂ) ^ j • (∏ l ∈ Finset.range j, ((s - (l : ℤ) : ℤ) : ℂ)) •
          mode (N.YM w) (s - (j : ℤ)) x := by
  induction j generalizing s with
  | zero => simp
  | succ k ih =>
      have hpow : ((W.L (-1)) ^ (k + 1)) w = W.L (-1) (((W.L (-1)) ^ k) w) := by
        rw [pow_succ']; rfl
      have hcov := act_T_covariance N.toWeakModule (((W.L (-1)) ^ k) w) s x
      rw [WeakModule.act_def, WeakModule.act_def] at hcov
      rw [hpow, hcov, ih (s - 1)]
      rw [show (s - 1) - (k : ℤ) = s - ((k + 1 : ℕ) : ℤ) from by push_cast; ring]
      have hprod : (∏ l ∈ Finset.range (k + 1), ((s - (l : ℤ) : ℤ) : ℂ))
          = (s : ℂ) * ∏ l ∈ Finset.range k, (((s - 1) - (l : ℤ) : ℤ) : ℂ) := by
        rw [Finset.prod_range_succ' (fun l => ((s - (l : ℤ) : ℤ) : ℂ)) k]
        rw [Finset.prod_congr rfl
          (fun l _ => show ((s - ((l + 1 : ℕ) : ℤ) : ℤ) : ℂ) = (((s - 1) - (l : ℤ) : ℤ) : ℂ) from by
            push_cast; ring)]
        push_cast; ring
      simp only [smul_smul]
      rw [hprod]
      congr 1
      ring

/-- `Φ g := mode (N.YM g) k x`, the linear map `𝒱 →ₗ M` reading off a fixed module mode. -/
noncomputable def modeAtState (N : GWModule W M) (k : ℤ) (x : M) : 𝒱 →ₗ[ℂ] M where
  toFun g := mode (N.YM g) k x
  map_add' a b := by simp only [map_add, mode_add, LinearMap.add_apply]
  map_smul' c a := by simp only [map_smul, mode_smul, LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem modeAtState_apply (N : GWModule W M) (k : ℤ) (x : M) (g : 𝒱) :
    modeAtState N k x g = mode (N.YM g) k x := rfl

/-- **Skew-symmetry transported to module modes.** `Y_M(v₍s₎u)₍k₎ x` re-expands as a tower in
`Y_M(u₍s+j₎v)₍k−j₎ x` (`skew_mode` + iterated translation covariance). Hqp-free. -/
theorem mode_skew_reduction (N : GWModule W M) (u v : 𝒱) (s k : ℤ) (x : M) :
    mode (N.YM (W.smul v s u)) k x
      = ∑ᶠ j : ℕ, ((j.factorial : ℂ)⁻¹) • (sgn (-s - 1 - (j : ℤ))) •
          ((-1 : ℂ) ^ j • (∏ l ∈ Finset.range j, ((k - (l : ℤ) : ℤ) : ℂ)) •
            mode (N.YM (W.smul u (s + (j : ℤ)) v)) (k - (j : ℤ)) x) := by
  change modeAtState N k x (W.smul v s u) = _
  rw [skew_mode W v u s, map_finsum (modeAtState N k x) (skew_support_finite W v u (-s - 1))]
  refine finsum_congr (fun j => ?_)
  rw [map_smul, map_smul, modeAtState_apply, T_eq_Lneg1]
  have hidx : (W.Y u) (-s - 1 - (j : ℤ)) v = W.smul u (s + (j : ℤ)) v := by
    rw [PreVertexAlgebra.smul_def, mode_apply,
      show -(s + (j : ℤ)) - 1 = -s - 1 - (j : ℤ) from by ring]
  rw [hidx, mode_Lneg1_pow N (W.smul u (s + (j : ℤ)) v) j k x]

/-- **Quasi-primary `L₁`-collapse** (general weight, hqp-free): for `u ∈ 𝒱_wtu` with `L₁u=0` and
`L₁v=0`, `L₁ʲ(u₍s₎v) = (∏_{l<j}(2wtu−s−2−l)) • u₍s+j₎v`. (Generalizes the weight-1, hqp-bearing
`Core.InvariantFormCanonicalPStep.L1pow_smul_qp` to all weights without `hqp`.) -/
theorem L1pow_smul_qp_gen (W : VertexOperatorAlgebra 𝒱) {wtu : ℤ} {u : 𝒱} (hu : u ∈ W.grading wtu)
    (hqpu : W.L 1 u = 0) {v : 𝒱} (hqpv : W.L 1 v = 0) (s : ℤ) (j : ℕ) :
    ((W.L 1) ^ j) (W.smul u s v)
      = (∏ l ∈ Finset.range j, ((2 * wtu - s - 2 - (l : ℤ) : ℤ) : ℂ)) •
          W.smul u (s + (j : ℤ)) v := by
  induction j generalizing s with
  | zero => simp
  | succ k ih =>
      have hstep : W.L 1 (W.smul u s v) = ((2 * wtu - s - 2 : ℤ) : ℂ) • W.smul u (s + 1) v := by
        have hbr := L1_bracket_smul W hu s v
        rw [hqpv, PreVertexAlgebra.smul_zero_right, sub_zero, hqpu,
          PreVertexAlgebra.smul_zero_left, add_zero] at hbr
        rw [hbr]; push_cast; ring_nf
      have hpow : ((W.L 1) ^ (k + 1)) (W.smul u s v)
          = ((W.L 1) ^ k) (W.L 1 (W.smul u s v)) := by rw [pow_succ, Module.End.mul_apply]
      rw [hpow, hstep, map_smul, ih (s + 1)]
      rw [show (s + 1) + (k : ℤ) = s + ((k + 1 : ℕ) : ℤ) from by push_cast; ring]
      have hprod : (∏ l ∈ Finset.range (k + 1), ((2 * wtu - s - 2 - (l : ℤ) : ℤ) : ℂ))
          = ((2 * wtu - s - 2 : ℤ) : ℂ) *
              ∏ l ∈ Finset.range k, ((2 * wtu - (s + 1) - 2 - (l : ℤ) : ℤ) : ℂ) := by
        rw [Finset.prod_range_succ' (fun l => ((2 * wtu - s - 2 - (l : ℤ) : ℤ) : ℂ)) k]
        rw [Finset.prod_congr rfl
          (fun l _ => show ((2 * wtu - s - 2 - ((l + 1 : ℕ) : ℤ) : ℤ) : ℂ)
              = ((2 * wtu - (s + 1) - 2 - (l : ℤ) : ℤ) : ℂ) from by push_cast; ring)]
        push_cast; ring
      rw [smul_smul, hprod]

/-- **Quasi-primary `dualAdj` collapse**: for `L₁u=0`, the `dualAdj` tower collapses to its single
`j=0` term, `dualAdj N wt u k α xα = (−1)^wt • Y_M(u)₍2wt−k−2₎ xα`. (The quasi-primary slice where
the `e^{zL₁}` twist is trivial — the tractable base case of the module FHL recombination.) -/
theorem dualAdj_qp (N : GWModule W M) {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt)
    (hqpu : W.L 1 u = 0) (k : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    dualAdj N wt u k α xα = (-1 : ℂ) ^ wt • mode (N.YM u) (2 * wt - k - 2) xα := by
  rw [dualAdj_clean N hu k hxα]
  congr 1
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj0
    have hz : ((W.L 1) ^ j) u = 0 := by
      obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
      rw [pow_succ, Module.End.mul_apply, hqpu, map_zero]
    rw [hz, map_zero]
    show ((j.factorial : ℂ)⁻¹) • mode (0 : (End ℂ M)⟦z^±⟧) (2 * wt - k - 2 - (j : ℤ)) xα = 0
    rw [show mode (0 : (End ℂ M)⟦z^±⟧) (2 * wt - k - 2 - (j : ℤ)) = 0 from rfl]
    simp
  · intro hcontra
    exact absurd (Finset.mem_range.mpr (by omega : 0 < wt.toNat + 1)) hcontra


/-! ## The quasi-primary base case of `DualAdjResidualMvec` (the recombination machinery in action). -/

/-- **Nested quasi-primary collapse**: for `L₁u=L₁v=0`, the nested `dualAdj` collapses to a pure
double `Y_M` mode product. -/
theorem nested_dualAdj_qp (N : GWModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    (hqpu : W.L 1 u = 0) {q : ℤ} {v : 𝒱} (hv : v ∈ W.grading q) (hqpv : W.L 1 v = 0)
    (k₁ k₂ : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    dualAdj N q v k₂ (matchIdx p k₁ α) (dualAdj N p u k₁ α xα)
      = (-1 : ℂ) ^ (p + q) •
          mode (N.YM v) (2 * q - k₂ - 2) (mode (N.YM u) (2 * p - k₁ - 2) xα) := by
  rw [dualAdj_qp N hv hqpv k₂ (dualAdj_mem N p u k₁ α xα),
      dualAdj_qp N hu hqpu k₁ hxα, map_smul, smul_smul]
  rw [show (-1 : ℂ) ^ q * (-1 : ℂ) ^ p = (-1 : ℂ) ^ (p + q) from by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), add_comm q p]]

/-- **LHS reduction (qp).** For quasi-primary `u,v`, the `DualAdjResidualMvecAt` LHS collapses (via
`nested_dualAdj_qp` + the module Jacobi `N.jacobi`) to `(−1)^{p+q} • ∑ᶠ i, cbz(2q−ℓ−n−2) i • (v₍ℓ+i₎ u)₍C−i₎ xα`. -/
theorem lhs_qp_eq (N : GWModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    (hqpu : W.L 1 u = 0) {q : ℤ} {v : 𝒱} (hv : v ∈ W.grading q) (hqpv : W.L 1 v = 0)
    (ℓ m n : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (dualAdj N q v (n + i) (matchIdx p (ℓ + m - i) α) (dualAdj N p u (ℓ + m - i) α xα)
          - negOnePow ℓ • dualAdj N p u (m + i) (matchIdx q (ℓ + n - i) α)
              (dualAdj N q v (ℓ + n - i) α xα)))
      = (-1 : ℂ) ^ (p + q) • ∑ᶠ i : ℤ, cbz (2 * q - ℓ - n - 2) i •
          mode (N.YM (W.smul v (ℓ + i) u)) ((2 * q - ℓ - n - 2) + (2 * p - ℓ - m - 2) - i) xα := by
  have hjac := N.jacobi v u xα ℓ (2 * q - ℓ - n - 2) (2 * p - ℓ - m - 2)
  rw [← hjac, smul_finsum]
  refine finsum_congr (fun i => ?_)
  rw [nested_dualAdj_qp N hu hqpu hv hqpv (ℓ + m - i) (n + i) hxα,
      nested_dualAdj_qp N hv hqpv hu hqpu (ℓ + n - i) (m + i) hxα]
  rw [show (2 * q - (n + i) - 2 : ℤ) = ℓ + (2 * q - ℓ - n - 2) - i from by ring,
      show (2 * p - (ℓ + m - i) - 2 : ℤ) = (2 * p - ℓ - m - 2) + i from by ring,
      show (2 * p - (m + i) - 2 : ℤ) = ℓ + (2 * p - ℓ - m - 2) - i from by ring,
      show (2 * q - (ℓ + n - i) - 2 : ℤ) = (2 * q - ℓ - n - 2) + i from by ring,
      show (-1 : ℂ) ^ (q + p) = (-1 : ℂ) ^ (p + q) from by rw [add_comm]]
  module

/-- The antidiagonal bijection `(i,j) ↦ (i+j, j)` on `ℤ × ℕ`. -/
def shiftEquiv : ℤ × ℕ ≃ ℤ × ℕ where
  toFun p := (p.1 + (p.2 : ℤ), p.2)
  invFun p := (p.1 - (p.2 : ℤ), p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- **Antidiagonal reindex.** `∑ᶠ i ∑ᶠ j g(i,j) • V(i+j) = ∑ᶠ r (∑ᶠ j g(r−j,j)) • V(r)`. -/
theorem antidiag_reindex (g : ℤ → ℕ → ℂ) (V : ℤ → M)
    (hfin : (Function.support (fun p : ℤ × ℕ => g p.1 p.2 • V (p.1 + (p.2 : ℤ)))).Finite)
    (hfin2 : (Function.support (fun p : ℤ × ℕ => g (p.1 - (p.2 : ℤ)) p.2 • V p.1)).Finite)
    (hfinr : ∀ r : ℤ, (Function.support (fun j : ℕ => g (r - (j : ℤ)) j)).Finite) :
    ∑ᶠ (i : ℤ), ∑ᶠ (j : ℕ), g i j • V (i + (j : ℤ))
      = ∑ᶠ (r : ℤ), (∑ᶠ (j : ℕ), g (r - (j : ℤ)) j) • V r := by
  rw [← finsum_curry (fun p : ℤ × ℕ => g p.1 p.2 • V (p.1 + (p.2 : ℤ))) hfin]
  have hstep : (∑ᶠ p : ℤ × ℕ, g p.1 p.2 • V (p.1 + (p.2 : ℤ)))
      = ∑ᶠ p : ℤ × ℕ, g (p.1 - (p.2 : ℤ)) p.2 • V p.1 := by
    rw [← finsum_comp_equiv shiftEquiv
      (f := fun p : ℤ × ℕ => g (p.1 - (p.2 : ℤ)) p.2 • V p.1)]
    refine finsum_congr (fun p => ?_)
    show g p.1 p.2 • V (p.1 + (p.2 : ℤ))
      = g ((p.1 + (p.2 : ℤ)) - (p.2 : ℤ)) p.2 • V (p.1 + (p.2 : ℤ))
    rw [add_sub_cancel_right]
  rw [hstep, finsum_curry (fun p : ℤ × ℕ => g (p.1 - (p.2 : ℤ)) p.2 • V p.1) hfin2]
  refine finsum_congr (fun r => ?_)
  rw [finsum_smul' (hfinr r)]


end VOA.C2Rigid