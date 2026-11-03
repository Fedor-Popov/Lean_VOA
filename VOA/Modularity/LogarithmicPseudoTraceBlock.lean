/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.LogarithmicPseudoTraceRealization
import VOA.Modularity.ZhuBlockConditions

/-!
# The cyclic genus-one layer for logarithmic pseudo-traces

`LogarithmicPseudoTraceRealization` constructs polynomial-valued one-point pseudo-traces from
explicit commutant data.  This file proves the part of the genus-one block calculation which
follows from that data without a Huang--Miyamoto existence theorem or a new recursion axiom:

* the one-point family is bundled as a linear map;
* its vacuum value is the logarithmic pseudo-character;
* square-bracket translation `L[-1]` vanishes;
* the nilpotent exponential does not spoil pseudo-trace cyclicity;
* consequently the Zhu zero-mode relation `S(a[0]v)=0` holds.

The target is deliberately still `LogFormalQSeries = ℂ → ℂ[X]`.  Evaluating the
coefficient polynomial at a fixed `τ` does not turn it into an ordinary `IsFormalBlock`: the
`q`-derivative also differentiates the polynomial in `τ`.  The logarithmic `[-2]` and `ω`
recursions therefore remain outside the partial block predicate below.  Proving them requires the
cross-weight pseudo-trace recursion for complementary nonzero modes.  No construction from strong
finiteness, convergence, spanning, or modularity is asserted here.
-/

namespace VOA

open Module (End)
open scoped BigOperators

set_option autoImplicit false

universe u v w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱}
variable {M : Type v} [AddCommGroup M] [Module ℂ M]
variable {A : Type w} [Ring A] [Algebra ℂ A]
variable {N : LogVModule W M}
variable [∀ α : ℂ, Module A (N.weight α)]
variable [∀ α : ℂ, IsScalarTower ℂ A (N.weight α)]

/-! ## Logarithmic zero-mode identities -/

/-- The boundary module-Jacobi identity giving the raw `L₀` commutator, stated with independent
universes for the VOA and module carriers. -/
theorem logL0_commutator_raw (B : WeakModule W M) (a : 𝒱) (x : M) (n : ℤ) :
    mode (B.YM W.conformalVector) 1 (mode (B.YM a) n x)
      - mode (B.YM a) n (mode (B.YM W.conformalVector) 1 x)
      = mode (B.YM (W.smul W.conformalVector 0 a)) (1 + n) x
        + mode (B.YM (W.smul W.conformalVector 1 a)) n x := by
  have hjac := B.jacobi W.conformalVector a x 0 1 n
  have hlhs : (∑ᶠ i : ℤ, (negOnePow i * cbz 0 i) •
        (mode (B.YM W.conformalVector) (0 + 1 - i) (mode (B.YM a) (n + i) x)
          - negOnePow 0 • mode (B.YM a) (0 + n - i)
              (mode (B.YM W.conformalVector) (1 + i) x)))
      = mode (B.YM W.conformalVector) 1 (mode (B.YM a) n x)
        - mode (B.YM a) n (mode (B.YM W.conformalVector) 1 x) := by
    rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by
      rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])]
    simp only [cbz_zero_left, mul_one, add_zero, zero_add, sub_zero,
      negOnePow, Even.zero, if_true, one_smul]
  have hvanish : ∀ i : ℤ, i ≠ 0 → i ≠ 1 →
      cbz 1 i • mode (B.YM (W.smul W.conformalVector (0 + i) a)) (1 + n - i) x = 0 := by
    intro i hi0 hi1
    rcases lt_trichotomy i 0 with hi | hi | hi
    · rw [cbz_apply_neg 1 hi, zero_smul]
    · exact absurd hi hi0
    · rw [cbz_lt (by norm_num) (by omega : (1 : ℤ) < i), zero_smul]
  have hrhs : (∑ᶠ i : ℤ,
        cbz 1 i • mode (B.YM (W.smul W.conformalVector (0 + i) a)) (1 + n - i) x)
      = mode (B.YM (W.smul W.conformalVector 0 a)) (1 + n) x
        + mode (B.YM (W.smul W.conformalVector 1 a)) n x := by
    rw [finsum_eq_sum_of_support_subset _ (s := ({0, 1} : Finset ℤ)) (by
      intro i hi
      simp only [Function.mem_support] at hi
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      by_contra hc
      push Not at hc
      exact hi (hvanish i hc.1 hc.2))]
    rw [Finset.sum_insert (by norm_num), Finset.sum_singleton]
    have hc10 : cbz (1 : ℤ) 0 = 1 := cbz_zero 1
    have hc11 : cbz (1 : ℤ) 1 = 1 := by
      rw [cbz_pascal 1 1, show (1 : ℤ) - 1 = 0 by ring, cbz_zero,
        cbz_lt (le_refl 0) (by norm_num)]
      ring
    rw [hc10, hc11, one_smul, one_smul,
      show (0 + (0 : ℤ)) = 0 by ring, show (0 + (1 : ℤ)) = 1 by ring,
      show (1 + n - (0 : ℤ)) = 1 + n by ring,
      show (1 + n - (1 : ℤ)) = n by ring]
  rw [← hlhs, hjac]
  exact hrhs

/-- For a homogeneous state, the usual `L₀` commutator formula holds on a logarithmic module.
The proof uses only the weak-module Jacobi identity and conformal covariance. -/
theorem logL0_commutator (N : LogVModule W M) {k : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) (x : M) (n : ℤ) :
    N.L0op (mode (N.YM a) n x)
      = ((k : ℂ) - n - 1) • mode (N.YM a) n x
        + mode (N.YM a) n (N.L0op x) := by
  have hraw := logL0_commutator_raw N.toWeakModule a x n
  have hzero : W.smul W.conformalVector 0 a = W.L (-1) a := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def,
      show ((-1 : ℤ) + 1) = 0 from by ring]
  have hone : W.smul W.conformalVector 1 a = W.L 0 a := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def,
      show ((0 : ℤ) + 1) = 1 from by ring]
  rw [hzero, hone, W.L_zero_grading a ha] at hraw
  have hcov := act_T_covariance N.toWeakModule a (1 + n) x
  simp only [WeakModule.act_def, show (1 + n - 1 : ℤ) = n from by ring] at hcov
  have hlin : mode (N.YM ((k : ℂ) • a)) n x =
      (k : ℂ) • mode (N.YM a) n x := by
    rw [map_smul, mode_smul]
    rfl
  rw [hcov, hlin] at hraw
  rw [sub_eq_iff_eq_add] at hraw
  change mode (N.YM W.conformalVector) 1 (mode (N.YM a) n x)
      = ((k : ℂ) - n - 1) • mode (N.YM a) n x
        + mode (N.YM a) n (mode (N.YM W.conformalVector) 1 x)
  rw [hraw]
  have hscalar : (-((1 + n : ℤ) : ℂ)) • mode (N.YM a) n x
        + (k : ℂ) • mode (N.YM a) n x
      = ((k : ℂ) - n - 1) • mode (N.YM a) n x := by
    rw [← add_smul]
    congr 1
    push_cast
    ring
  rw [hscalar]

/-- The zero mode of `L₋₁u` is `-k` times the zero mode of a weight-`k` state.  This only
uses weak-module translation covariance, so semisimplicity of `L₀` is irrelevant. -/
theorem logOMod_L_neg_one (N : LogVModule W M) {k : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) :
    logOMod N (W.L (-1) a) = (-(k : ℂ)) • logOMod N a := by
  have heq : W.L (-1) a = W.smul W.conformalVector 0 a := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def,
      show ((-1 : ℤ) + 1) = 0 from by ring]
  have hmem : W.L (-1) a ∈ W.grading (k + 1) := by
    have h := W.smul_mem_grading W.conformalVector_mem_grading_two ha 0
    rw [show (2 + k - 0 - 1 : ℤ) = k + 1 from by ring] at h
    rwa [← heq] at h
  rw [logOMod_homogeneous N hmem, logOMod_homogeneous N ha,
    show (k + 1 - 1 : ℤ) = k from by ring]
  ext x
  simp only [LinearMap.smul_apply]
  have hcov := act_T_covariance N.toWeakModule a k x
  simp only [WeakModule.act_def] at hcov
  exact hcov

/-- The logarithmic zero mode kills Zhu translation on a homogeneous state. -/
theorem logOMod_L_translation (N : LogVModule W M) {k : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) :
    logOMod N (W.L (-1) a + W.L 0 a) = 0 := by
  rw [map_add, logOMod_L_neg_one N ha, W.L_zero_grading a ha, map_smul, ← add_smul,
    neg_add_cancel, zero_smul]

/-- Zhu translation is killed for an arbitrary, not necessarily homogeneous, state. -/
theorem logOMod_L_translation_all (N : LogVModule W M) (a : 𝒱) :
    logOMod N (W.L (-1) a + W.L 0 a) = 0 := by
  have hatop : a ∈ ⨆ k, W.grading k := by
    rw [W.isInternal.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun a => logOMod N (W.L (-1) a + W.L 0 a) = 0) hatop ?_ ?_ ?_
  · intro k x hx
    exact logOMod_L_translation N hx
  · simp only [map_zero, add_zero]
  · intro x y hx hy
    rw [show W.L (-1) (x + y) + W.L 0 (x + y)
        = (W.L (-1) x + W.L 0 x) + (W.L (-1) y + W.L 0 y) from by
      simp only [map_add]
      abel, map_add, hx, hy, add_zero]

/-- The logarithmic zero mode satisfies the same homogeneous zero-mode commutator formula as an
ordinary module. -/
theorem logOMod_commutator (N : LogVModule W M) {k l : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading k) (hb : b ∈ W.grading l) (x : M) :
    logOMod N a (logOMod N b x) - logOMod N b (logOMod N a x)
      = ∑ᶠ i : ℤ, cbz (k - 1) i • logOMod N (W.smul a i b) x := by
  rw [logOMod_homogeneous N ha, logOMod_homogeneous N hb,
    mode_commutator N.toWeakModule a b x (k - 1) (l - 1)]
  refine finsum_congr (fun i => ?_)
  congr 1
  rw [logOMod_homogeneous N (W.smul_mem_grading ha hb i)]
  rw [show k - 1 + (l - 1) - i = k + l - i - 1 - 1 from by ring]

/-- The structural square-bracket identity `o(a[0]b)=[o(a),o(b)]` also holds on a logarithmic
module. -/
theorem logOMod_vSqZ_zero (N : LogVModule W M) {k : ℕ} {l : ℤ} {a b : 𝒱}
    (hk : 1 ≤ k) (ha : a ∈ W.grading (k : ℤ)) (hb : b ∈ W.grading l) (x : M) :
    logOMod N (vSqZ W a k 0 b) x
      = logOMod N a (logOMod N b x) - logOMod N b (logOMod N a x) := by
  rw [logOMod_commutator N ha hb x]
  have happ : ∀ z : 𝒱,
      ((LinearMap.applyₗ x).comp (logOMod N) : 𝒱 →ₗ[ℂ] M) z = logOMod N z x :=
    fun _ => rfl
  rw [← happ, vSqZ_apply,
    map_finsum ((LinearMap.applyₗ x).comp (logOMod N) : 𝒱 →ₗ[ℂ] M)
      (sqModeZ_support_finite W a k 0 b)]
  refine finsum_congr (fun i => ?_)
  rw [map_smul, happ, cbz_eq_sqBracketCoeffZ_zero k hk i, PreVertexAlgebra.smul_def]

/-! ## Cyclicity with the nilpotent exponential -/

/-- A pseudo-trace kills a commutator after multiplication by a power of an endomorphism which
commutes with the factor moved through the cyclic trace. -/
theorem pseudoTrace_commutator_mul_pow_eq_zero
    {P : Type*} [AddCommGroup P] [Module A P] [Module ℂ P] [IsScalarTower ℂ A P]
    [Module.Finite A P] [Module.Projective A P]
    (phi : symmetricFunctionals ℂ A) (S T R : Module.End A P)
    (hSR : S * R = R * S) (j : ℕ) :
    pseudoTrace P phi ((S * T - T * S) * R ^ j) = 0 := by
  have hcomm : Commute S R := hSR
  have hSRj : S * R ^ j = R ^ j * S := hcomm.pow_right j
  have hcyc := pseudoTrace_mem_symmetricFunctionals (W := P) phi
  rw [sub_mul, map_sub]
  suffices pseudoTrace P phi ((S * T) * R ^ j) =
      pseudoTrace P phi ((T * S) * R ^ j) by
    rw [this, sub_self]
  calc
    pseudoTrace P phi ((S * T) * R ^ j)
        = pseudoTrace P phi (S * (T * R ^ j)) := by rw [mul_assoc]
    _ = pseudoTrace P phi ((T * R ^ j) * S) := hcyc S (T * R ^ j)
    _ = pseudoTrace P phi ((T * S) * R ^ j) := by
      rw [mul_assoc, ← hSRj, ← mul_assoc]

namespace LogPseudoTraceCommutantData

/-- The polynomial-valued logarithmic one-point family, bundled as a linear map in its insertion. -/
noncomputable def logPseudoTraceOnePointHom (D : LogPseudoTraceCommutantData N A) :
    𝒱 →ₗ[ℂ] LogFormalQSeries where
  toFun := D.logPseudoTraceOnePoint
  map_add' := D.logPseudoTraceOnePoint_add
  map_smul' := D.logPseudoTraceOnePoint_smul

@[simp] theorem logPseudoTraceOnePointHom_apply
    (D : LogPseudoTraceCommutantData N A) (a : 𝒱) :
    D.logPseudoTraceOnePointHom a = D.logPseudoTraceOnePoint a := rfl

/-- The lifted zero mode kills Zhu translation on every generalized weight piece. -/
theorem zeroModeA_L_translation_all (D : LogPseudoTraceCommutantData N A)
    (α : ℂ) (a : 𝒱) :
    D.zeroModeA α (W.L (-1) a + W.L 0 a) = 0 := by
  ext x
  rw [D.zeroModeA_coe, logOMod_L_translation_all]
  exact rfl

/-- If all lifted zero modes of an insertion vanish, so does its logarithmic one-point
pseudo-trace. -/
theorem logPseudoTraceOnePoint_eq_zero_of_zeroModeA
    (D : LogPseudoTraceCommutantData N A) {a : 𝒱}
    (ha : ∀ α : ℂ, D.zeroModeA α a = 0) :
    D.logPseudoTraceOnePoint a = 0 := by
  funext e
  apply Polynomial.ext
  intro j
  let α := e + W.centralCharge / 24
  letI : Module.Finite A (N.weight α) := D.finite_piece α
  letI : Module.Projective A (N.weight α) := D.projective_piece α
  rw [D.logPseudoTraceOnePoint_coeff]
  by_cases hj : j < D.nilpotentCutoff α
  · rw [if_pos hj, ha α, zero_mul, map_zero, mul_zero]
    rfl
  · rw [if_neg hj]
    rfl

/-- Square-bracket translation vanishes in the logarithmic one-point pseudo-trace. -/
theorem logPseudoTraceOnePoint_Lsq_neg_one
    (D : LogPseudoTraceCommutantData N A) (a : 𝒱) :
    D.logPseudoTraceOnePoint (Lsq W (-1) a) = 0 := by
  apply D.logPseudoTraceOnePoint_eq_zero_of_zeroModeA
  intro α
  rw [Lsq_neg_one]
  exact D.zeroModeA_L_translation_all α a

/-- On a homogeneous state, its lifted zero mode commutes with the lifted nilpotent part of
`L₀`. -/
theorem zeroModeA_comm_nilpotentPiece (D : LogPseudoTraceCommutantData N A)
    (α : ℂ) {k : ℤ} {a : 𝒱} (ha : a ∈ W.grading k) :
    D.zeroModeA α a * D.nilpotentPiece α =
      D.nilpotentPiece α * D.zeroModeA α a := by
  have hcommL0 : D.zeroModeA α a * D.zeroModeA α W.conformalVector =
      D.zeroModeA α W.conformalVector * D.zeroModeA α a := by
    ext x
    simp only [Module.End.mul_apply]
    rw [D.zeroModeA_coe, D.zeroModeA_coe, D.zeroModeA_coe, D.zeroModeA_coe,
      logOMod_conformalVector]
    rw [logOMod_homogeneous N ha]
    have hraw := logL0_commutator N ha (x : M) (k - 1)
    have hzero : (k : ℂ) - ((k - 1 : ℤ) : ℂ) - 1 = 0 := by
      push_cast
      ring
    rw [hzero, zero_smul, zero_add] at hraw
    exact hraw.symm
  rw [nilpotentPiece, mul_sub, sub_mul, hcommL0]
  simp

/-- The lifted zero mode of `a[0]b` is the commutator of the two lifted zero modes. -/
theorem zeroModeA_vSqZ_zero (D : LogPseudoTraceCommutantData N A)
    (α : ℂ) {k : ℕ} {l : ℤ} {a b : 𝒱}
    (hk : 1 ≤ k) (ha : a ∈ W.grading (k : ℤ)) (hb : b ∈ W.grading l) :
    D.zeroModeA α (vSqZ W a k 0 b)
      = D.zeroModeA α a * D.zeroModeA α b
        - D.zeroModeA α b * D.zeroModeA α a := by
  ext x
  simp only [LinearMap.sub_apply, Module.End.mul_apply]
  change ((D.zeroModeA α (vSqZ W a k 0 b) x : N.weight α) : M)
      = ((D.zeroModeA α a (D.zeroModeA α b x) : N.weight α) : M)
        - ((D.zeroModeA α b (D.zeroModeA α a x) : N.weight α) : M)
  simp only [D.zeroModeA_coe]
  exact logOMod_vSqZ_zero N hk ha hb x

/-- The logarithmic pseudo-trace kills the Zhu zero-mode relation for a homogeneous right input. -/
theorem logPseudoTraceOnePoint_vSqZ_zero_homogeneous
    (D : LogPseudoTraceCommutantData N A)
    {k : ℕ} {l : ℤ} {a b : 𝒱}
    (hk : 1 ≤ k) (ha : a ∈ W.grading (k : ℤ)) (hb : b ∈ W.grading l) :
    D.logPseudoTraceOnePoint (vSqZ W a k 0 b) = 0 := by
  funext e
  apply Polynomial.ext
  intro j
  let α := e + W.centralCharge / 24
  letI : Module.Finite A (N.weight α) := D.finite_piece α
  letI : Module.Projective A (N.weight α) := D.projective_piece α
  rw [D.logPseudoTraceOnePoint_coeff]
  by_cases hj : j < D.nilpotentCutoff α
  · rw [if_pos hj, D.zeroModeA_vSqZ_zero α hk ha hb,
      pseudoTrace_commutator_mul_pow_eq_zero D.phi
        (D.zeroModeA α a) (D.zeroModeA α b) (D.nilpotentPiece α)
        (D.zeroModeA_comm_nilpotentPiece α ha), mul_zero]
    rfl
  · rw [if_neg hj]
    rfl

/-- The Zhu zero-mode relation holds for every right input, by the internal conformal-weight
decomposition and linearity. -/
theorem logPseudoTraceOnePoint_vSqZ_zero_eq_zero
    (D : LogPseudoTraceCommutantData N A)
    {k : ℕ} (hk : 1 ≤ k) {a : 𝒱} (ha : a ∈ W.grading (k : ℤ)) (b : 𝒱) :
    D.logPseudoTraceOnePointHom (vSqZ W a k 0 b) = 0 := by
  have hbtop : b ∈ ⨆ l : ℤ, W.grading l := by
    rw [W.isInternal.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun b => D.logPseudoTraceOnePointHom (vSqZ W a k 0 b) = 0)
    hbtop ?_ ?_ ?_
  · intro l x hx
    exact D.logPseudoTraceOnePoint_vSqZ_zero_homogeneous hk ha hx
  · change D.logPseudoTraceOnePointHom (vSqZ W a k 0 0) = 0
    rw [map_zero, map_zero]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy, add_zero]

/-! ## The honest partial genus-one predicate -/

/-- The genus-one identities established from commutant data alone.  This is intentionally not a
full logarithmic formal block: it omits the `[-2]` Eisenstein recursion and the `ω`/logarithmic
`q`-derivative identity. -/
structure IsLogPseudoTraceCyclicBlock
    (S : 𝒱 →ₗ[ℂ] LogFormalQSeries) (character : LogFormalQSeries) : Prop where
  vacuum : S W.vacuum = character
  translation : ∀ a : 𝒱, S (Lsq W (-1) a) = 0
  zhuZero : ∀ (k : ℕ), 1 ≤ k → ∀ a ∈ W.grading (k : ℤ), ∀ b : 𝒱,
    S (vSqZ W a k 0 b) = 0

/-- Operational commutant data produces the cyclic, translation, and zero-mode part of a
logarithmic genus-one block. -/
theorem isLogPseudoTraceCyclicBlock (D : LogPseudoTraceCommutantData N A) :
    IsLogPseudoTraceCyclicBlock (W := W)
      D.logPseudoTraceOnePointHom D.logPseudoCharacter where
  vacuum := D.logPseudoTraceOnePoint_vacuum
  translation := D.logPseudoTraceOnePoint_Lsq_neg_one
  zhuZero := fun _ hk _ ha b => D.logPseudoTraceOnePoint_vSqZ_zero_eq_zero hk ha b

end LogPseudoTraceCommutantData

end VOA
