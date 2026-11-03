/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli and Fedor K. Popov
-/
import VOA.Modularity.SuperTorusOnePoint
import VOA.Modularity.SuperCuspFunctionalCount
import VOA.Modules.SuperTwistedModule

/-!
# Signed iterate and geometric inversion for super Zhu recursion

This file proves the module supercommutator formula directly from the `ell = 0` slice of the
super-module Jacobi identity, identifies the square-bracket zero mode with the supercommutator of
global zero modes, and applies finite-block Koszul cyclicity.  It also proves cross-weight Koszul
cyclicity, the signed first-order step equation, its finite geometric telescope, and termination
from the ordinary module's bounded-below grading.  Thus the torus one-point supertrace annihilates
the actual square-bracket-zero relation and the displaced pair-trace engine is available.

This is the sign-sensitive gate of the super recursion.  The two signs occur in different places:

* super Jacobi gives `o(a)o(b) - epsilon(a,b)o(b)o(a)`;
* supertrace cyclicity gives `str(o(a)o(b)) = epsilon(a,b)str(o(b)o(a))`.

They therefore cancel.  In particular the odd--odd case is retained rather than discarded: both
products are even and can have nonzero supertrace.
-/

namespace VOA

open Module (End)
open scoped BigOperators

set_option autoImplicit false

universe u v

variable {VType : Type u} [AddCommGroup VType] [Module ℂ VType]
variable {M : Type v} [AddCommGroup M] [Module ℂ M]

/-! ## Cross-space Koszul cyclicity

The two factors in the displaced trace act between *different* conformal-weight spaces.  The
same-space theorem `supertrace_mul_comm` is therefore not enough: the parity involutions on the
source and target blocks must be intertwined before applying `LinearMap.trace_comp_comm'`.
-/

/-- A homogeneous linear map between two (possibly different) parity-graded spaces. -/
def IsParityHomogeneousMap {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (P : ParityGrading X) (Q : ParityGrading Y)
    (p : ZMod 2) (f : X →ₗ[ℂ] Y) : Prop :=
  ∀ (q : ZMod 2) ⦃x : X⦄, x ∈ P.parity q → f x ∈ Q.parity (p + q)

/-- Homogeneous degrees add under cross-space composition. -/
theorem IsParityHomogeneousMap.comp {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {P : ParityGrading X} {Q : ParityGrading Y} {R : ParityGrading Z}
    {p q : ZMod 2} {f : Y →ₗ[ℂ] Z} {g : X →ₗ[ℂ] Y}
    (hf : IsParityHomogeneousMap Q R p f)
    (hg : IsParityHomogeneousMap P Q q g) :
    IsParityHomogeneousMap P R (p + q) (f.comp g) := by
  intro r x hx
  change f (g x) ∈ R.parity ((p + q) + r)
  simpa only [add_assoc] using hf (q + r) (hg r hx)

/-- Moving a homogeneous map past the parity involution, from source to target. -/
theorem parityInvol_comp_of_isParityHomogeneousMap
    {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (P : ParityGrading X) (Q : ParityGrading Y) {p : ZMod 2}
    {f : X →ₗ[ℂ] Y} (hf : IsParityHomogeneousMap P Q p f) :
    Q.parityInvol.comp f = parSign p • (f.comp P.parityInvol) := by
  apply LinearMap.ext
  intro x
  obtain ⟨x0, hx0, x1, hx1, hsum⟩ := P.exists_parity_decomp x
  rw [← hsum, map_add, map_add]
  simp only [LinearMap.comp_apply, LinearMap.smul_apply]
  congr 1
  · change Q.parityInvol (f x0) = parSign p • f (P.parityInvol x0)
    rw [Q.parityInvol_homog (hf 0 hx0), P.parityInvol_homog hx0, map_smul,
      parSign_add, smul_smul]
  · change Q.parityInvol (f x1) = parSign p • f (P.parityInvol x1)
    rw [Q.parityInvol_homog (hf 1 hx1), P.parityInvol_homog hx1, map_smul,
      parSign_add, smul_smul]

/-- The reverse parity-involution interchange. -/
theorem comp_parityInvol_of_isParityHomogeneousMap
    {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (P : ParityGrading X) (Q : ParityGrading Y) {p : ZMod 2}
    {f : X →ₗ[ℂ] Y} (hf : IsParityHomogeneousMap P Q p f) :
    f.comp P.parityInvol = parSign p • (Q.parityInvol.comp f) := by
  apply LinearMap.ext
  intro x
  obtain ⟨x0, hx0, x1, hx1, hsum⟩ := P.exists_parity_decomp x
  rw [← hsum, map_add, map_add]
  simp only [LinearMap.comp_apply, LinearMap.smul_apply]
  congr 1
  · change f (P.parityInvol x0) = parSign p • Q.parityInvol (f x0)
    rw [P.parityInvol_homog hx0, map_smul, Q.parityInvol_homog (hf 0 hx0),
      parSign_add, smul_smul]
    rw [← mul_assoc, parSign_mul_self, one_mul]
  · change f (P.parityInvol x1) = parSign p • Q.parityInvol (f x1)
    rw [P.parityInvol_homog hx1, map_smul, Q.parityInvol_homog (hf 1 hx1),
      parSign_add, smul_smul]
    rw [← mul_assoc, parSign_mul_self, one_mul]

/-- Cross-space supertrace cyclicity before the two-parity refinement.  Moving the right factor
around the trace contributes its parity sign. -/
theorem supertrace_comp_comm_shift_right_degree
    {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]
    (P : ParityGrading X) (Q : ParityGrading Y) {q : ZMod 2}
    (A : Y →ₗ[ℂ] X) {B : X →ₗ[ℂ] Y}
    (hB : IsParityHomogeneousMap P Q q B) :
    supertrace P (A.comp B) = parSign q * supertrace Q (B.comp A) := by
  rw [supertrace, supertrace]
  change LinearMap.trace ℂ X (P.parityInvol.comp (A.comp B)) = _
  rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm', ← LinearMap.comp_assoc,
    comp_parityInvol_of_isParityHomogeneousMap P Q hB,
    LinearMap.smul_comp, map_smul]
  rfl

/-- Cross-space **Koszul** cyclicity.  In the mixed-parity cases both composites are odd, so
their supertraces vanish; in the even-even and odd-odd cases the preceding right-degree sign is
already exactly the Koszul sign. -/
theorem supertrace_comp_comm_shift
    {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]
    (P : ParityGrading X) (Q : ParityGrading Y) {p q : ZMod 2}
    {A : Y →ₗ[ℂ] X} {B : X →ₗ[ℂ] Y}
    (hA : IsParityHomogeneousMap Q P p A)
    (hB : IsParityHomogeneousMap P Q q B) :
    supertrace P (A.comp B) = koszul p q * supertrace Q (B.comp A) := by
  rcases zmod2_cases p with hp | hp <;> rcases zmod2_cases q with hq | hq <;>
    subst hp <;> subst hq
  · simpa using supertrace_comp_comm_shift_right_degree P Q A hB
  · have hAB : IsParityHomogeneousEnd P 1 (A.comp B) := by
      simpa using hA.comp hB
    have hBA : IsParityHomogeneousEnd Q 1 (B.comp A) := by
      simpa using hB.comp hA
    rw [supertrace_eq_zero_of_odd P hAB, supertrace_eq_zero_of_odd Q hBA]
    simp
  · simpa using supertrace_comp_comm_shift_right_degree P Q A hB
  · simpa using supertrace_comp_comm_shift_right_degree P Q A hB

namespace SuperWeakModule

variable {V : SuperVertexAlgebra VType}

/-- The `ell=0` super-module Jacobi identity is the Borcherds supercommutator formula. -/
theorem mode_supercommutator (A : SuperWeakModule V M) {p q : ZMod 2}
    {a b : VType} (ha : a ∈ V.parity p) (hb : b ∈ V.parity q)
    (x : M) (m n : ℤ) :
    mode (A.YM a) m (mode (A.YM b) n x) -
        koszul p q • mode (A.YM b) n (mode (A.YM a) m x) =
      ∑ᶠ i : ℤ, cbz m i • mode (A.YM (V.smul a i b)) (m + n - i) x := by
  have hjac := A.jacobi a ha b hb x 0 m n
  have hlhs : (∑ᶠ i : ℤ, (negOnePow i * cbz 0 i) •
        (mode (A.YM a) (0 + m - i) (mode (A.YM b) (n + i) x) -
          (koszul p q * negOnePow 0) •
            mode (A.YM b) (0 + n - i) (mode (A.YM a) (m + i) x))) =
      mode (A.YM a) m (mode (A.YM b) n x) -
        koszul p q • mode (A.YM b) n (mode (A.YM a) m x) := by
    rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by
      rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])]
    simp only [cbz_zero_left, mul_one, add_zero, zero_add, sub_zero,
      negOnePow, Even.zero, if_true, one_smul]
  rw [← hlhs, hjac]
  exact finsum_congr (fun i => by rw [zero_add])

end SuperWeakModule

namespace SuperOrdVModule

variable {W : SuperVertexOperatorAlgebra VType}

/-! ## Displaced graded supertraces -/

/-- The diagonal weight block of an arbitrary module endomorphism. -/
noncomputable def superWeightBlock (N : SuperOrdVModule W M) (A : End ℂ M) (α : ℂ) :
    End ℂ (N.weight α) :=
  (internalProjTo N.weight_isInternal α).comp (A.comp (N.weight α).subtype)

@[simp] theorem superWeightBlock_add (N : SuperOrdVModule W M)
    (A B : End ℂ M) (α : ℂ) :
    N.superWeightBlock (A + B) α = N.superWeightBlock A α + N.superWeightBlock B α := by
  simp only [superWeightBlock, LinearMap.add_comp, LinearMap.comp_add]

@[simp] theorem superWeightBlock_smul (N : SuperOrdVModule W M)
    (c : ℂ) (A : End ℂ M) (α : ℂ) :
    N.superWeightBlock (c • A) α = c • N.superWeightBlock A α := by
  simp only [superWeightBlock, LinearMap.smul_comp, LinearMap.comp_smul]

/-- The graded supertrace of an arbitrary module endomorphism. -/
noncomputable def superGradedTraceOp (N : SuperOrdVModule W M) (A : End ℂ M) :
    FormalQSeries := fun e =>
  let α := e + W.centralCharge / 24
  haveI := N.weight_finite α
  supertrace (N.weightParityGrading α) (N.superWeightBlock A α)

@[simp] theorem superGradedTraceOp_add (N : SuperOrdVModule W M) (A B : End ℂ M) :
    N.superGradedTraceOp (A + B) = N.superGradedTraceOp A + N.superGradedTraceOp B := by
  funext e
  let α := e + W.centralCharge / 24
  haveI := N.weight_finite α
  change supertrace (N.weightParityGrading α) (N.superWeightBlock (A + B) α) = _
  rw [N.superWeightBlock_add, supertrace_add]
  rfl

@[simp] theorem superGradedTraceOp_smul (N : SuperOrdVModule W M)
    (c : ℂ) (A : End ℂ M) :
    N.superGradedTraceOp (c • A) = c • N.superGradedTraceOp A := by
  funext e
  let α := e + W.centralCharge / 24
  haveI := N.weight_finite α
  change supertrace (N.weightParityGrading α) (N.superWeightBlock (c • A) α) = _
  rw [N.superWeightBlock_smul, supertrace_smul]
  rfl

theorem superGradedTraceOp_sub (N : SuperOrdVModule W M) (A B : End ℂ M) :
    N.superGradedTraceOp (A - B) = N.superGradedTraceOp A - N.superGradedTraceOp B := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ B, N.superGradedTraceOp_add,
    N.superGradedTraceOp_smul]
  funext e
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- An operator shifts every conformal-weight space by `s`. -/
def SuperWeightShift (N : SuperOrdVModule W M) (A : End ℂ M) (s : ℂ) : Prop :=
  ∀ α : ℂ, ∀ x ∈ N.weight α, A x ∈ N.weight (α + s)

/-- An operator has a fixed degree for the module parity decomposition. -/
def SuperParityDegree (N : SuperOrdVModule W M) (p : ZMod 2) (A : End ℂ M) : Prop :=
  ∀ (q : ZMod 2) ⦃x : M⦄, x ∈ N.parity q → A x ∈ N.parity (p + q)

/-- The ordinary mode of a weight-homogeneous state has the expected conformal-weight shift. -/
theorem superWeightShift_mode (N : SuperOrdVModule W M) {k : ℤ} {a : VType}
    (ha : a ∈ W.toSuperNearVOA.gradingZ k) (i : ℤ) :
    N.SuperWeightShift (mode (N.YM a) i) ((k : ℂ) - i - 1) := by
  intro α x hx
  have h := N.act_weight ha hx i
  simpa only [SuperOrdVModule.act_def,
    show α + (k : ℂ) - (i : ℂ) - 1 = α + ((k : ℂ) - i - 1) by ring] using h

/-- The ordinary mode of a parity-homogeneous state has that parity degree. -/
theorem superParityDegree_mode (N : SuperOrdVModule W M) {p : ZMod 2} {a : VType}
    (ha : a ∈ W.parity p) (i : ℤ) :
    N.SuperParityDegree p (mode (N.YM a) i) := by
  intro q x hx
  exact N.toSuperWeakModule.parity_mode a ha x hx i

/-- Across a weight shift, the diagonal block of a product is the composite of the two
restricted maps between the corresponding weight spaces. -/
theorem superWeightBlock_mul_shift (N : SuperOrdVModule W M) (A B : End ℂ M)
    (α β : ℂ) (hA : ∀ x ∈ N.weight β, A x ∈ N.weight α)
    (hB : ∀ x ∈ N.weight α, B x ∈ N.weight β) :
    N.superWeightBlock (A * B) α =
      (LinearMap.restrict A hA).comp (LinearMap.restrict B hB) := by
  refine LinearMap.ext (fun y => Subtype.ext ?_)
  have hmem : A (B (y : M)) ∈ N.weight α := hA _ (hB _ y.2)
  change ((internalProjTo N.weight_isInternal α) (A (B (y : M))) : M) = _
  rw [show ((internalProjTo N.weight_isInternal α) (A (B (y : M))) : M) =
      A (B (y : M)) from congrArg Subtype.val
        (internalProjTo_coe N.weight_isInternal α ⟨A (B (y : M)), hmem⟩)]
  rfl

/-- Restricting a globally parity-homogeneous operator between two weight spaces preserves its
parity degree for the induced block gradings. -/
theorem restrict_isParityHomogeneousMap (N : SuperOrdVModule W M)
    {p : ZMod 2} {A : End ℂ M} (hP : N.SuperParityDegree p A)
    {α β : ℂ} (hA : ∀ x ∈ N.weight α, A x ∈ N.weight β) :
    IsParityHomogeneousMap (N.weightParityGrading α) (N.weightParityGrading β) p
      (LinearMap.restrict A hA) := by
  intro q x hx
  change A (x : M) ∈ N.parity (p + q)
  exact hP q hx

/-- Displaced `q`-graded Koszul cyclicity.  The two supertraces are the same cross-space trace,
but occur in conformal degrees separated by `s`. -/
theorem superGradedTraceOp_comm_shift (N : SuperOrdVModule W M)
    {p q : ZMod 2} (A B : End ℂ M) (s : ℂ)
    (hAw : N.SuperWeightShift A (-s)) (hBw : N.SuperWeightShift B s)
    (hAp : N.SuperParityDegree p A) (hBp : N.SuperParityDegree q B) (e : ℂ) :
    N.superGradedTraceOp (A * B) e =
      koszul p q * N.superGradedTraceOp (B * A) (e + s) := by
  let α := e + W.centralCharge / 24
  let β := e + s + W.centralCharge / 24
  have hBα : ∀ x ∈ N.weight α, B x ∈ N.weight β := by
    intro x hx
    have h := hBw α x hx
    rwa [show α + s = β by simp only [α, β]; ring] at h
  have hAβ : ∀ x ∈ N.weight β, A x ∈ N.weight α := by
    intro x hx
    have h := hAw β x hx
    rwa [show β + -s = α by simp only [α, β]; ring] at h
  haveI := N.weight_finite α
  haveI := N.weight_finite β
  change supertrace (N.weightParityGrading α) (N.superWeightBlock (A * B) α) =
    koszul p q * supertrace (N.weightParityGrading β) (N.superWeightBlock (B * A) β)
  rw [N.superWeightBlock_mul_shift A B α β hAβ hBα,
    N.superWeightBlock_mul_shift B A β α hBα hAβ]
  exact supertrace_comp_comm_shift _ _
    (N.restrict_isParityHomogeneousMap hAp hAβ)
    (N.restrict_isParityHomogeneousMap hBp hBα)

/-- The signed first-order step equation.  For odd--odd inputs the Koszul scalar is `-1`, so the
supercommutator is an anticommutator and the inhomogeneous term enters with a minus sign. -/
theorem superGradedTraceOp_supercommutator_step (N : SuperOrdVModule W M)
    {p q : ZMod 2} (A B : End ℂ M) (s : ℂ)
    (hAw : N.SuperWeightShift A (-s)) (hBw : N.SuperWeightShift B s)
    (hAp : N.SuperParityDegree p A) (hBp : N.SuperParityDegree q B) (e : ℂ) :
    N.superGradedTraceOp (B * A) (e + s) =
      N.superGradedTraceOp (B * A) e + koszul p q *
        N.superGradedTraceOp (A * B - koszul p q • (B * A)) e := by
  rw [N.superGradedTraceOp_sub, N.superGradedTraceOp_smul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  have hcyc := N.superGradedTraceOp_comm_shift A B s hAw hBw hAp hBp e
  have hsign : koszul p q * koszul p q = 1 := koszul_mul_self p q
  have hrev : N.superGradedTraceOp (B * A) (e + s) =
      koszul p q * N.superGradedTraceOp (A * B) e := by
    calc
      N.superGradedTraceOp (B * A) (e + s) =
          1 * N.superGradedTraceOp (B * A) (e + s) := by rw [one_mul]
      _ = (koszul p q * koszul p q) *
          N.superGradedTraceOp (B * A) (e + s) := by rw [hsign]
      _ = koszul p q * (koszul p q *
          N.superGradedTraceOp (B * A) (e + s)) := by ring
      _ = koszul p q * N.superGradedTraceOp (A * B) e := by rw [← hcyc]
  rw [hrev]
  linear_combination hsign * N.superGradedTraceOp (B * A) e

/-- Finite geometric inversion of the signed step equation.  This is the parity-sensitive layer;
the telescope itself is the repository's parity-blind `gradedTrace_geomSolve`. -/
theorem superGradedTraceOp_geomSolve (N : SuperOrdVModule W M)
    {p q : ZMod 2} (A B : End ℂ M) (s : ℂ)
    (hAw : N.SuperWeightShift A (-s)) (hBw : N.SuperWeightShift B s)
    (hAp : N.SuperParityDegree p A) (hBp : N.SuperParityDegree q B)
    (e : ℂ) (n : ℕ)
    (hvanish : N.superGradedTraceOp (B * A) (e - (n : ℂ) * s) = 0) :
    N.superGradedTraceOp (B * A) e =
      ∑ j ∈ Finset.range n, koszul p q *
        N.superGradedTraceOp (A * B - koszul p q • (B * A))
          (e - ((j : ℂ) + 1) * s) := by
  exact gradedTrace_geomSolve
    (N.superGradedTraceOp (B * A))
    (fun z => koszul p q *
      N.superGradedTraceOp (A * B - koszul p q • (B * A)) z)
    s (N.superGradedTraceOp_supercommutator_step A B s hAw hBw hAp hBp)
    e n hvanish

/-- A super graded trace vanishes when its conformal-weight block is zero. -/
theorem superGradedTraceOp_eq_zero_of_weight_bot (N : SuperOrdVModule W M)
    (A : End ℂ M) (e : ℂ)
    (h : N.weight (e + W.centralCharge / 24) = ⊥) :
    N.superGradedTraceOp A e = 0 := by
  haveI := N.weight_finite (e + W.centralCharge / 24)
  haveI : Subsingleton (N.weight (e + W.centralCharge / 24)) := by
    rw [h]
    infer_instance
  change supertrace (N.weightParityGrading (e + W.centralCharge / 24))
      (N.superWeightBlock A (e + W.centralCharge / 24)) = 0
  rw [Subsingleton.elim (N.superWeightBlock A (e + W.centralCharge / 24)) 0]
  unfold supertrace
  rw [mul_zero, map_zero]

/-- Bounded-below module weights bound the support of every graded supertrace. -/
theorem superGradedTraceOp_eq_zero_of_re_lt (N : SuperOrdVModule W M) (A : End ℂ M) :
    ∃ B : ℝ, ∀ e : ℂ, (e + W.centralCharge / 24).re < B →
      N.superGradedTraceOp A e = 0 := by
  obtain ⟨B, hB⟩ := N.boundedBelow
  refine ⟨B, fun e he => N.superGradedTraceOp_eq_zero_of_weight_bot A e ?_⟩
  by_contra hne
  exact absurd (hB _ hne) (not_le.mpr he)

/-- Stepping down by a shift of positive real part eventually leaves the module support. -/
theorem exists_superGradedTraceOp_vanish (N : SuperOrdVModule W M) (A : End ℂ M)
    {s : ℂ} (hs : 0 < s.re) (e : ℂ) :
    ∃ n : ℕ, N.superGradedTraceOp A (e - (n : ℂ) * s) = 0 := by
  obtain ⟨Bd, hBd⟩ := N.superGradedTraceOp_eq_zero_of_re_lt A
  obtain ⟨n, hn⟩ := exists_nat_gt ((e.re + (W.centralCharge / 24).re - Bd) / s.re)
  refine ⟨n, hBd _ ?_⟩
  have hlt : (e.re + (W.centralCharge / 24).re - Bd) < (n : ℝ) * s.re :=
    (div_lt_iff₀ hs).mp hn
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero]
  linarith

/-- The signed geometric solution with the vanishing endpoint discharged from boundedness. -/
theorem superGradedTraceOp_geomSolve_of_re_pos (N : SuperOrdVModule W M)
    {p q : ZMod 2} (A B : End ℂ M) {s : ℂ} (hs : 0 < s.re)
    (hAw : N.SuperWeightShift A (-s)) (hBw : N.SuperWeightShift B s)
    (hAp : N.SuperParityDegree p A) (hBp : N.SuperParityDegree q B) (e : ℂ) :
    ∃ n : ℕ, N.superGradedTraceOp (B * A) e =
      ∑ j ∈ Finset.range n, koszul p q *
        N.superGradedTraceOp (A * B - koszul p q • (B * A))
          (e - ((j : ℂ) + 1) * s) := by
  obtain ⟨n, hn⟩ := N.exists_superGradedTraceOp_vanish (B * A) hs e
  exact ⟨n, N.superGradedTraceOp_geomSolve A B s hAw hBw hAp hBp e n hn⟩

/-- The supercommutator of homogeneous global zero modes is the zero mode of the corresponding
ordinary products, term by term. -/
theorem superOMod_supercommutator (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) {p q : ZMod 2} {k l : ℤ}
    {a b : VType} (hak : a ∈ W.toSuperNearVOA.gradingZ k)
    (hbl : b ∈ W.toSuperNearVOA.gradingZ l)
    (hap : a ∈ W.parity p) (hbq : b ∈ W.parity q) (x : M) :
    N.superOMod hW a (N.superOMod hW b x) -
        koszul p q • N.superOMod hW b (N.superOMod hW a x) =
      ∑ᶠ i : ℤ, cbz (k - 1) i • N.superOMod hW (W.toSuperNearVOA.smul a i b) x := by
  rw [N.superOMod_of_mem_gradingZ hW hak, N.superOMod_of_mem_gradingZ hW hbl,
    N.toSuperWeakModule.mode_supercommutator hap hbq x (k - 1) (l - 1)]
  refine finsum_congr (fun i => ?_)
  rw [show W.smul a i b = W.toSuperNearVOA.smul a i b from rfl]
  congr 1
  rw [N.superOMod_of_mem_gradingZ hW
    (W.toSuperNearVOA.smul_mem_gradingZ hak hbl i)]
  congr 1
  ring

/-- The zero mode of an ordinary product `a_(i)v` as a signed sum of compensated mode pairs.
The exchanged family carries the unique super correction `koszul p q`; the remaining
`negOnePow` and binomial factors are exactly those of the bosonic iterate formula. -/
theorem superOMod_smul_eq_iterate (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) {p q : ZMod 2} {ka l : ℤ}
    {a v : VType} (ha : a ∈ W.toSuperNearVOA.gradingZ ka)
    (hv : v ∈ W.toSuperNearVOA.gradingZ l)
    (hap : a ∈ W.parity p) (hvq : v ∈ W.parity q) (i : ℤ) (x : M) :
    N.superOMod hW (W.toSuperNearVOA.smul a i v) x =
      ∑ᶠ j : ℤ, (negOnePow j * cbz i j) •
        (mode (N.YM a) (i - j)
            (mode (N.YM v) (ka + l - (i - j) - 2) x)
          - (koszul p q * negOnePow i) •
            mode (N.YM v) (ka + l - j - 2) (mode (N.YM a) j x)) := by
  rw [N.superOMod_of_mem_gradingZ hW
    (W.toSuperNearVOA.smul_mem_gradingZ ha hv i)]
  rw [show ka + l - i - 1 - 1 = ka + l - i - 2 by ring]
  change mode (N.YM (W.smul a i v)) (ka + l - i - 2) x = _
  have hiter := N.toSuperWeakModule.module_iterate_zero
    a hap v hvq x i (ka + l - i - 2)
  rw [hiter]
  refine finsum_congr (fun j => ?_)
  rw [show ka + l - i - 2 + j = ka + l - (i - j) - 2 by ring,
    show i + (ka + l - i - 2) - j = ka + l - j - 2 by ring]

/-- `o(a[0]b)` is the supercommutator of `o(a)` and `o(b)`. -/
theorem superOMod_superVSqZ_zero (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) {p q : ZMod 2} {k : ℕ} {l : ℤ}
    {a b : VType} (hk : 1 ≤ k)
    (hak : a ∈ W.toSuperNearVOA.gradingZ (k : ℤ))
    (hbl : b ∈ W.toSuperNearVOA.gradingZ l)
    (hap : a ∈ W.parity p) (hbq : b ∈ W.parity q) (x : M) :
    N.superOMod hW (W.toSuperNearVOA.superVSqZ a k 0 b) x =
      N.superOMod hW a (N.superOMod hW b x) -
        koszul p q • N.superOMod hW b (N.superOMod hW a x) := by
  rw [N.superOMod_supercommutator hW hak hbl hap hbq x]
  have happ : ∀ y : VType,
      ((LinearMap.applyₗ x).comp (N.superOMod hW) : VType →ₗ[ℂ] M) y =
        N.superOMod hW y x := fun _ => rfl
  rw [← happ, W.toSuperNearVOA.superVSqZ_apply,
    map_finsum ((LinearMap.applyₗ x).comp (N.superOMod hW) : VType →ₗ[ℂ] M)
      (W.toSuperNearVOA.superSqModeZ_support_finite a k 0 b)]
  refine finsum_congr (fun i => ?_)
  rw [map_smul, happ, cbz_eq_sqBracketCoeffZ_zero k hk i]

/-- A homogeneous global zero mode preserves every module weight space. -/
theorem superOMod_mem_weight (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) {k : ℤ} {a : VType}
    (ha : a ∈ W.toSuperNearVOA.gradingZ k) {α : ℂ} {x : M}
    (hx : x ∈ N.weight α) : N.superOMod hW a x ∈ N.weight α := by
  rw [N.superOMod_of_mem_gradingZ hW ha]
  have hw := N.act_weight (mem_zeroModeWeight_of_mem_gradingZ ha) hx (k - 1)
  simpa only [SuperOrdVModule.act_def, Int.cast_sub, Int.cast_one,
    show α + (((k : ℂ) - 1) + 1) - ((k : ℂ) - 1) - 1 = α by ring] using hw

/-- The diagonal block of a product splits when the right factor preserves the weight space. -/
theorem superOModWeightBlock_mul (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) {a b : VType} {α : ℂ}
    (hb : ∀ x ∈ N.weight α, N.superOMod hW b x ∈ N.weight α) :
    (internalProjTo N.weight_isInternal α).comp
        (((N.superOMod hW a) * (N.superOMod hW b)).comp (N.weight α).subtype) =
      N.superOModWeightBlock hW a α * N.superOModWeightBlock hW b α := by
  apply LinearMap.ext
  intro x
  have hbx : ((N.superOModWeightBlock hW b α x : N.weight α) : M) =
      N.superOMod hW b (x : M) :=
    congrArg Subtype.val
      (internalProjTo_coe N.weight_isInternal α
        ⟨N.superOMod hW b (x : M), hb _ x.2⟩)
  apply Subtype.ext
  change ((internalProjTo N.weight_isInternal α)
      (N.superOMod hW a (N.superOMod hW b (x : M))) : M) = _
  rw [← hbx]
  rfl

/-- The actual square-bracket-zero genus-one relation for homogeneous weight/parity inputs. -/
theorem superTorusOnePoint_superVSqZ_zero_eq_zero_bihomogeneous
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    {p q : ZMod 2} {k : ℕ} {l : ℤ} {a b : VType} (hk : 1 ≤ k)
    (hak : a ∈ W.toSuperNearVOA.gradingZ (k : ℤ))
    (hbl : b ∈ W.toSuperNearVOA.gradingZ l)
    (hap : a ∈ W.parity p) (hbq : b ∈ W.parity q) :
    N.superTorusOnePoint hW (W.toSuperNearVOA.superVSqZ a k 0 b) = 0 := by
  funext e
  let α := e + W.centralCharge / 24
  haveI := N.weight_finite α
  have hop : N.superOMod hW (W.toSuperNearVOA.superVSqZ a k 0 b) =
      N.superOMod hW a * N.superOMod hW b -
        koszul p q • (N.superOMod hW b * N.superOMod hW a) := by
    apply LinearMap.ext
    intro x
    exact N.superOMod_superVSqZ_zero hW hk hak hbl hap hbq x
  have haW : ∀ x ∈ N.weight α, N.superOMod hW a x ∈ N.weight α :=
    fun _ hx => N.superOMod_mem_weight hW hak hx
  have hbW : ∀ x ∈ N.weight α, N.superOMod hW b x ∈ N.weight α :=
    fun _ hx => N.superOMod_mem_weight hW hbl hx
  have haP := N.zeroModeBlock_isParityHomogeneous hap (k - 1)
    (mem_zeroModeWeight_of_mem_gradingZ hak) α
  have hbP := N.zeroModeBlock_isParityHomogeneous hbq (l - 1)
    (mem_zeroModeWeight_of_mem_gradingZ hbl) α
  change supertrace (N.weightParityGrading α)
      (N.superOModWeightBlock hW (W.toSuperNearVOA.superVSqZ a k 0 b) α) = 0
  unfold superOModWeightBlock
  rw [hop]
  change supertrace (N.weightParityGrading α)
    ((internalProjTo N.weight_isInternal α).comp
      (((N.superOMod hW a * N.superOMod hW b) -
        koszul p q • (N.superOMod hW b * N.superOMod hW a)).comp
          (N.weight α).subtype)) = 0
  have hlin : (internalProjTo N.weight_isInternal α).comp
      (((N.superOMod hW a * N.superOMod hW b) -
        koszul p q • (N.superOMod hW b * N.superOMod hW a)).comp
          (N.weight α).subtype) =
      (N.superOModWeightBlock hW a α * N.superOModWeightBlock hW b α) -
        koszul p q •
          (N.superOModWeightBlock hW b α * N.superOModWeightBlock hW a α) := by
    apply LinearMap.ext
    intro x
    change (internalProjTo N.weight_isInternal α)
        (((N.superOMod hW a * N.superOMod hW b) x) -
          koszul p q • ((N.superOMod hW b * N.superOMod hW a) x)) =
      (N.superOModWeightBlock hW a α * N.superOModWeightBlock hW b α) x -
        koszul p q •
          (N.superOModWeightBlock hW b α * N.superOModWeightBlock hW a α) x
    rw [map_sub, map_smul]
    have hab := congrArg (fun f : End ℂ (N.weight α) => f x)
      (N.superOModWeightBlock_mul hW (a := a) (b := b) hbW)
    have hba := congrArg (fun f : End ℂ (N.weight α) => f x)
      (N.superOModWeightBlock_mul hW (a := b) (b := a) haW)
    exact congrArg₂ (fun y z => y - koszul p q • z) hab hba
  rw [hlin]
  rw [show (N.superOModWeightBlock hW a α) =
      N.zeroModeBlock a (k - 1) (mem_zeroModeWeight_of_mem_gradingZ hak) α from
        N.superOModWeightBlock_of_mem_gradingZ hW hak α,
    show (N.superOModWeightBlock hW b α) =
      N.zeroModeBlock b (l - 1) (mem_zeroModeWeight_of_mem_gradingZ hbl) α from
        N.superOModWeightBlock_of_mem_gradingZ hW hbl α]
  change supertraceLinear (N.weightParityGrading α)
      (_ * _ - koszul p q • (_ * _)) = 0
  rw [map_sub, map_smul, supertraceLinear_apply, supertraceLinear_apply,
    supertrace_mul_comm (N.weightParityGrading α) haP hbP]
  rw [smul_eq_mul, sub_self]

/-- The square-bracket-zero relation for the actual formal torus one-point map, with only the
weight homogeneity required by the formal-block interface.  The left state is first split by
parity; the right state is then split simultaneously by weight and parity. -/
theorem superTorusOnePoint_superVSqZ_zero_eq_zero
    (N : SuperOrdVModule W M) (hW : W.toSuperNearVOA.IntegralWeights)
    (k : ℕ) (hk : 1 ≤ k) {a : VType}
    (ha : a ∈ W.toSuperNearVOA.gradingZ (k : ℤ)) (b : VType) :
    N.superTorusOnePoint hW (W.toSuperNearVOA.superVSqZ a k 0 b) = 0 := by
  classical
  let V := W.toSuperNearVOA
  obtain ⟨s, hs, _⟩ := V.exists_sum_parProj a
  rw [← hs, V.superVSqZ_sum_left, map_sum]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  have hap : V.parProj p a ∈ V.parity p := V.parProj_mem p a
  have hak : V.parProj p a ∈ V.gradingZ (k : ℤ) := V.parProj_mem_grading p ha
  refine V.reduce_bihomogeneous hW
    (P := fun v => N.superTorusOnePoint hW (V.superVSqZ (V.parProj p a) k 0 v) = 0)
    ?_ ?_ ?_ b
  · intro l q v hv
    exact N.superTorusOnePoint_superVSqZ_zero_eq_zero_bihomogeneous hW hk
      hak hv.1 hap hv.2
  · change N.superTorusOnePoint hW
      (V.superVSqZ (V.parProj p a) k 0 (0 : VType)) = 0
    rw [map_zero, map_zero]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy, add_zero]

end SuperOrdVModule

end VOA
