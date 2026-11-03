/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.LogarithmicQSeries
import VOA.Modules.LogVModule
import VOA.Modules.Character
import Mathlib.RingTheory.Finiteness.Nilpotent
import Mathlib.Algebra.Polynomial.Coeff

/-!
# A VOA-facing realization interface for logarithmic pseudo-traces

`LogarithmicQSeries` constructs the Hattori--Stallings exponential polynomial from projective
pieces, but deliberately has no vertex-operator input.  This file supplies the next honest rung.

`LogPseudoTraceCommutantData N A` consists of a finite-dimensional auxiliary algebra `A`, an
`A`-module structure on every generalized `L₀`-weight piece of a logarithmic module `N`, finite
projectivity of those pieces, a symmetric functional on `A`, and compatibility with the actual
vertex-operator modes.  In particular, its `zeroModeA` field is an `A`-linear lift of the genuine
VOA zero mode on each generalized weight piece.

From this data the file constructs `logPseudoTraceOnePoint`, a polynomial-valued formal
one-point pseudo-trace family.  The nilpotent operator and a uniform cutoff on each piece are not
extra assumptions: they are derived from the conformal-vector zero mode and the generalized
weight-space finiteness already carried by `LogVModule`.

The missing existence theorem is substantial.  Nothing here constructs
`LogPseudoTraceCommutantData` from `C₂`-cofiniteness or strong finiteness.  That requires the
Huang--Miyamoto generalized-Verma/projective-commutant theorem producing one auxiliary algebra
whose action commutes with all vertex modes and whose generalized weight pieces are finite
projective.  This file also proves no convergence, genus-one recursion, spanning, or modularity.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u v w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱}
variable {M : Type v} [AddCommGroup M] [Module ℂ M]

/-! ## The zero mode of a logarithmic module -/

/-- The weight-`k` zero-mode slice for a logarithmic module.  This construction only uses the
underlying weak module; semisimplicity of `L₀` is irrelevant. -/
noncomputable def logOModFamily (N : LogVModule W M) (k : ℤ) :
    (W.grading k) →ₗ[ℂ] End ℂ M :=
  (modeLinear (k - 1)).comp (N.YM.comp (W.grading k).subtype)

/-- The genuine VOA zero mode on a logarithmic module, assembled over the finite conformal-weight
decomposition of the inserted state. -/
noncomputable def logOMod (N : LogVModule W M) : 𝒱 →ₗ[ℂ] End ℂ M :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (logOModFamily N)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

/-- On a homogeneous state, `logOMod` is the expected conformal zero mode. -/
theorem logOMod_homogeneous (N : LogVModule W M) {k : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) :
    logOMod N a = mode (N.YM a) (k - 1) := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : logOMod N a = logOModFamily N k ⟨a, ha⟩ := by
    change (DFinsupp.lsum ℂ (logOModFamily N)) (DirectSum.decompose W.grading a) = _
    rw [DirectSum.decompose_of_mem W.grading ha]
    exact DFinsupp.lsum_single ℂ (logOModFamily N) k ⟨a, ha⟩
  rw [hcollapse]
  rfl

/-- The vacuum zero mode is the identity also on a logarithmic module. -/
theorem logOMod_vacuum (N : LogVModule W M) :
    logOMod N W.vacuum = LinearMap.id := by
  rw [logOMod_homogeneous N W.vacuum_mem_grading_zero]
  change mode (N.YM W.vacuum) (-1) = LinearMap.id
  rw [N.vacuum_YM, mode_one, if_pos rfl, Module.End.one_eq_id]

/-- The conformal-vector zero mode is the logarithmic module's actual `L₀`. -/
theorem logOMod_conformalVector (N : LogVModule W M) :
    logOMod N W.conformalVector = N.L0op := by
  rw [logOMod_homogeneous N W.conformalVector_mem_grading_two]
  rfl

/-! ## Auxiliary commutant data -/

variable (N : LogVModule W M)
variable (A : Type w) [Ring A] [Algebra ℂ A]
variable [∀ α : ℂ, Module A (N.weight α)]
variable [∀ α : ℂ, IsScalarTower ℂ A (N.weight α)]

/-- Operational data realizing logarithmic pseudo-traces on a fixed logarithmic module.

The `mode_commutes` field is stated piecewise because the repository does not put one global
`A`-module structure on `M`: whenever a vertex mode carries a vector from one generalized weight
piece into another, it intertwines the two supplied `A`-actions.  The separately bundled
`zeroModeA` is the endomorphism-valued linear map actually consumed by the one-point function. -/
structure LogPseudoTraceCommutantData where
  /-- The auxiliary algebra is finite-dimensional over `ℂ`. -/
  finite_algebra : FiniteDimensional ℂ A
  /-- Every generalized weight piece is finitely generated over the auxiliary algebra. -/
  finite_piece : ∀ α : ℂ, Module.Finite A (N.weight α)
  /-- Every generalized weight piece is projective over the auxiliary algebra. -/
  projective_piece : ∀ α : ℂ, Module.Projective A (N.weight α)
  /-- The symmetric functional used by the Hattori--Stallings pseudo-trace. -/
  phi : symmetricFunctionals ℂ A
  /-- The auxiliary action commutes with every actual vertex-operator mode between generalized
  weight pieces. -/
  mode_commutes : ∀ (a : A) (α β : ℂ) (v : 𝒱) (n : ℤ) (x : N.weight α)
    (hx : mode (N.YM v) n (x : M) ∈ N.weight β),
    mode (N.YM v) n ((a • x : N.weight α) : M) =
      ((a • (⟨mode (N.YM v) n (x : M), hx⟩ : N.weight β) : N.weight β) : M)
  /-- The genuine VOA zero mode, lifted to an `A`-linear endomorphism of every generalized
  weight piece and linear in the inserted state. -/
  zeroModeA : ∀ α : ℂ, 𝒱 →ₗ[ℂ] Module.End A (N.weight α)
  /-- The lift has the actual VOA zero mode as its underlying map. -/
  zeroModeA_coe : ∀ (α : ℂ) (v : 𝒱) (x : N.weight α),
    ((zeroModeA α v x : N.weight α) : M) = logOMod N v (x : M)

namespace LogPseudoTraceCommutantData

variable {N A}

/-- The auxiliary-algebra endomorphism induced by the nilpotent part of `L₀` on one generalized
weight piece.  It is derived from the conformal-vector zero mode, not supplied independently. -/
noncomputable def nilpotentPiece (D : LogPseudoTraceCommutantData N A) (α : ℂ) :
    Module.End A (N.weight α) :=
  D.zeroModeA α W.conformalVector - α • (1 : Module.End A (N.weight α))

/-- The derived auxiliary endomorphism is the actual nilpotent part of `L₀`. -/
theorem nilpotentPiece_coe (D : LogPseudoTraceCommutantData N A) (α : ℂ)
    (x : N.weight α) :
    ((D.nilpotentPiece α x : N.weight α) : M) = N.L0nil (x : M) := by
  change ((D.zeroModeA α W.conformalVector x : N.weight α) : M) - α • (x : M) = _
  rw [D.zeroModeA_coe, logOMod_conformalVector]
  exact N.L0nil_apply_of_mem x.2 |>.symm

/-- Powers of the derived auxiliary endomorphism agree with powers of the actual `L₀` nilpotent
part on the ambient logarithmic module. -/
theorem nilpotentPiece_pow_coe (D : LogPseudoTraceCommutantData N A) (α : ℂ)
    (k : ℕ) (x : N.weight α) :
    ((((D.nilpotentPiece α) ^ k) x : N.weight α) : M) = (N.L0nil ^ k) (x : M) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      calc
        ((((D.nilpotentPiece α) ^ (k + 1)) x : N.weight α) : M)
            = ((((D.nilpotentPiece α) ^ k) (D.nilpotentPiece α x) : N.weight α) : M) := by
                rw [pow_succ, Module.End.mul_apply]
        _ = (N.L0nil ^ k) ((D.nilpotentPiece α x : N.weight α) : M) :=
              ih (D.nilpotentPiece α x)
        _ = (N.L0nil ^ k) (N.L0nil (x : M)) := by rw [D.nilpotentPiece_coe]
        _ = (N.L0nil ^ (k + 1)) (x : M) := by rw [pow_succ, Module.End.mul_apply]

/-- The derived nilpotent operator is locally nilpotent on the auxiliary module. -/
theorem nilpotentPiece_locallyNilpotent (D : LogPseudoTraceCommutantData N A) (α : ℂ)
    (x : N.weight α) :
    ∃ k : ℕ, ((D.nilpotentPiece α) ^ k) x = 0 := by
  obtain ⟨k, hk⟩ := N.L0nil_locNilpotent x.2
  refine ⟨k, Subtype.ext ?_⟩
  rw [ZeroMemClass.coe_zero, D.nilpotentPiece_pow_coe, hk]

/-- Restrict the derived auxiliary endomorphism to the underlying complex vector space. -/
noncomputable def nilpotentPieceC (D : LogPseudoTraceCommutantData N A) (α : ℂ) :
    Module.End ℂ (N.weight α) :=
  (D.nilpotentPiece α).restrictScalars ℂ

@[simp] theorem nilpotentPieceC_apply (D : LogPseudoTraceCommutantData N A) (α : ℂ)
    (x : N.weight α) : D.nilpotentPieceC α x = D.nilpotentPiece α x := rfl

/-- Restriction of scalars commutes with powers of the derived endomorphism. -/
theorem nilpotentPieceC_pow_apply (D : LogPseudoTraceCommutantData N A) (α : ℂ)
    (k : ℕ) (x : N.weight α) :
    ((D.nilpotentPieceC α) ^ k) x = ((D.nilpotentPiece α) ^ k) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply,
        ih, nilpotentPieceC_apply]

/-- Finite-dimensionality of the generalized weight piece upgrades local nilpotence to one
uniform exponent. -/
theorem nilpotent_nilpotentPiece (D : LogPseudoTraceCommutantData N A) (α : ℂ) :
    IsNilpotent (D.nilpotentPiece α) := by
  letI : FiniteDimensional ℂ (N.weight α) := N.finrank α
  have hC : IsNilpotent (D.nilpotentPieceC α) :=
    Module.End.isNilpotent_iff_of_finite.mpr fun x => by
      obtain ⟨k, hk⟩ := D.nilpotentPiece_locallyNilpotent α x
      exact ⟨k, by rwa [D.nilpotentPieceC_pow_apply]⟩
  obtain ⟨k, hk⟩ := hC
  refine ⟨k, LinearMap.ext fun x => ?_⟩
  have hx := LinearMap.congr_fun hk x
  rw [D.nilpotentPieceC_pow_apply] at hx
  exact hx

/-- A canonical uniform cutoff for the nilpotent exponential on one generalized weight piece. -/
noncomputable def nilpotentCutoff (D : LogPseudoTraceCommutantData N A) (α : ℂ) : ℕ :=
  (D.nilpotent_nilpotentPiece α).choose

/-- The canonical cutoff kills the nilpotent operator. -/
theorem nilpotentPiece_pow_cutoff (D : LogPseudoTraceCommutantData N A) (α : ℂ) :
    (D.nilpotentPiece α) ^ D.nilpotentCutoff α = 0 :=
  (D.nilpotent_nilpotentPiece α).choose_spec

/-- The lifted zero mode is genuinely `A`-linear. -/
theorem zeroModeA_map_smul (D : LogPseudoTraceCommutantData N A) (α : ℂ)
    (v : 𝒱) (a : A) (x : N.weight α) :
    D.zeroModeA α v (a • x) = a • D.zeroModeA α v x :=
  (D.zeroModeA α v).map_smul a x

/-- The vacuum lift is the identity auxiliary endomorphism. -/
theorem zeroModeA_vacuum (D : LogPseudoTraceCommutantData N A) (α : ℂ) :
    D.zeroModeA α W.vacuum = 1 := by
  ext x
  rw [D.zeroModeA_coe, logOMod_vacuum]
  rfl

/-! ## The realized polynomial-valued one-point family -/

/-- The polynomial-valued formal logarithmic one-point pseudo-trace attached to operational
commutant data.  Its exponent `e` uses the generalized weight `e + c/24`, matching the ordinary
one-point convention elsewhere in the repository. -/
noncomputable def logPseudoTraceOnePoint (D : LogPseudoTraceCommutantData N A) (v : 𝒱) :
    LogFormalQSeries :=
  fun e =>
    let α := e + W.centralCharge / 24
    letI : Module.Finite A (N.weight α) := D.finite_piece α
    letI : Module.Projective A (N.weight α) := D.projective_piece α
    pseudoTraceExpPolynomial (N.weight α) D.phi (D.zeroModeA α v)
      (D.nilpotentPiece α) (D.nilpotentCutoff α)

/-- The coefficient of `τ^k` is the Hattori--Stallings pseudo-trace of the actual VOA zero mode
times the `k`-th power of the `L₀` nilpotent part. -/
theorem logPseudoTraceOnePoint_coeff (D : LogPseudoTraceCommutantData N A) (v : 𝒱)
    (e : ℂ) (k : ℕ) :
    let α := e + W.centralCharge / 24
    letI : Module.Finite A (N.weight α) := D.finite_piece α
    letI : Module.Projective A (N.weight α) := D.projective_piece α
    (D.logPseudoTraceOnePoint v e).coeff k =
      if k < D.nilpotentCutoff α then
        logExpCoeff k * pseudoTrace (N.weight α) D.phi
          (D.zeroModeA α v * (D.nilpotentPiece α) ^ k)
      else 0 := by
  let α := e + W.centralCharge / 24
  letI : Module.Finite A (N.weight α) := D.finite_piece α
  letI : Module.Projective A (N.weight α) := D.projective_piece α
  exact pseudoTraceExpPolynomial_coeff (N.weight α) D.phi (D.zeroModeA α v)
    (D.nilpotentPiece α) (D.nilpotentCutoff α) k

/-- Evaluation of the coefficient polynomial is the expected finite nilpotent exponential. -/
theorem logPseudoTraceOnePoint_eval (D : LogPseudoTraceCommutantData N A) (v : 𝒱)
    (e tau : ℂ) :
    let α := e + W.centralCharge / 24
    letI : Module.Finite A (N.weight α) := D.finite_piece α
    letI : Module.Projective A (N.weight α) := D.projective_piece α
    (D.logPseudoTraceOnePoint v e).eval tau =
      ∑ k ∈ Finset.range (D.nilpotentCutoff α),
        logExpCoeff k * pseudoTrace (N.weight α) D.phi
          (D.zeroModeA α v * (D.nilpotentPiece α) ^ k) * tau ^ k := by
  let α := e + W.centralCharge / 24
  letI : Module.Finite A (N.weight α) := D.finite_piece α
  letI : Module.Projective A (N.weight α) := D.projective_piece α
  exact pseudoTraceExpPolynomial_eval (N.weight α) D.phi (D.zeroModeA α v)
    (D.nilpotentPiece α) (D.nilpotentCutoff α) tau

/-- The realized one-point family is additive in its VOA insertion. -/
theorem logPseudoTraceOnePoint_add (D : LogPseudoTraceCommutantData N A) (v w : 𝒱) :
    D.logPseudoTraceOnePoint (v + w) =
      D.logPseudoTraceOnePoint v + D.logPseudoTraceOnePoint w := by
  funext e
  let α := e + W.centralCharge / 24
  letI : Module.Finite A (N.weight α) := D.finite_piece α
  letI : Module.Projective A (N.weight α) := D.projective_piece α
  apply Polynomial.ext
  intro k
  simp only [Pi.add_apply, Polynomial.coeff_add]
  rw [D.logPseudoTraceOnePoint_coeff, D.logPseudoTraceOnePoint_coeff,
    D.logPseudoTraceOnePoint_coeff]
  by_cases hk : k < D.nilpotentCutoff α
  · rw [if_pos hk, if_pos hk, if_pos hk, map_add, add_mul, map_add, mul_add]
  · rw [if_neg hk, if_neg hk, if_neg hk, add_zero]

/-- The realized one-point family is complex-homogeneous in its VOA insertion. -/
theorem logPseudoTraceOnePoint_smul (D : LogPseudoTraceCommutantData N A) (c : ℂ) (v : 𝒱) :
    D.logPseudoTraceOnePoint (c • v) = c • D.logPseudoTraceOnePoint v := by
  funext e
  let α := e + W.centralCharge / 24
  letI : Module.Finite A (N.weight α) := D.finite_piece α
  letI : Module.Projective A (N.weight α) := D.projective_piece α
  apply Polynomial.ext
  intro k
  simp only [Pi.smul_apply, Polynomial.coeff_smul]
  rw [D.logPseudoTraceOnePoint_coeff, D.logPseudoTraceOnePoint_coeff]
  by_cases hk : k < D.nilpotentCutoff α
  · rw [if_pos hk, if_pos hk, map_smul, smul_mul_assoc, map_smul]
    simp [smul_eq_mul, mul_left_comm]
  · rw [if_neg hk, if_neg hk]
    simp

/-- The logarithmic pseudo-character supplied by the same commutant data. -/
noncomputable def logPseudoCharacter (D : LogPseudoTraceCommutantData N A) :
    LogFormalQSeries :=
  D.logPseudoTraceOnePoint W.vacuum

/-- The vacuum one-point pseudo-trace is the logarithmic pseudo-character by construction. -/
theorem logPseudoTraceOnePoint_vacuum (D : LogPseudoTraceCommutantData N A) :
    D.logPseudoTraceOnePoint W.vacuum = D.logPseudoCharacter := rfl

/-- Increasing the cutoff beyond the canonical nilpotence exponent does not change one
coefficient polynomial. -/
theorem logPseudoTraceOnePoint_cutoff_stable (D : LogPseudoTraceCommutantData N A)
    (v : 𝒱) (e : ℂ) {r : ℕ}
    (hr : D.nilpotentCutoff (e + W.centralCharge / 24) ≤ r) :
    let α := e + W.centralCharge / 24
    letI : Module.Finite A (N.weight α) := D.finite_piece α
    letI : Module.Projective A (N.weight α) := D.projective_piece α
    pseudoTraceExpPolynomial (N.weight α) D.phi (D.zeroModeA α v)
      (D.nilpotentPiece α) r = D.logPseudoTraceOnePoint v e := by
  let α := e + W.centralCharge / 24
  letI : Module.Finite A (N.weight α) := D.finite_piece α
  letI : Module.Projective A (N.weight α) := D.projective_piece α
  dsimp only [logPseudoTraceOnePoint]
  apply pseudoTraceExpPolynomial_stable
  · exact hr
  · exact D.nilpotentPiece_pow_cutoff (e + W.centralCharge / 24)

end LogPseudoTraceCommutantData

end VOA
