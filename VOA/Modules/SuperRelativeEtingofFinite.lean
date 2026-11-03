/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperPoissonTrace
import VOA.Modules.SuperTwistedModule
import VOA.Modules.SuperAdjointModule
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Relative super Etingof finiteness

For a fixed spatial automorphism `g`, the relative Poisson-homology carrier is

`R_M / {(R_V)^g, R_M}`.

This file keeps that formula literal.  The state-side fixed subspace is the fixed subspace of
the **C2 quotient** `R_V = V / C2(V)` under `g`; it is not the fixed subspace for `parity * g`.
The module-side carrier is `R_M = M / C2(M)`.  A descended bilinear zero-mode/bracket operation
`(R_V)^g -> R_M -> R_M` is actual data, and the relative relation subspace is the span of its
actual image.  Thus `SuperRelativePoissonData.HP₀` is an honest quotient, not a proposition standing in
for a quotient.  `SuperRelativePoissonData` bundles only this bilinear operation needed to form the
displayed quotient; it does not bundle or prove Poisson-module Jacobi or derivation laws and must
not be read as a full Poisson-module structure.

The existing twisted-supermodule API supplies the fractional modes needed to define the canonical
candidate `C2(M)` span, but it does not yet prove that zero modes descend through the two C2
quotients.  `SuperTwistedZeroModeDescent` isolates the two exact representative-independence
obligations, and `SuperTwistedRelativePoissonData.ofZeroModeDescent` constructs the descended
action from them.  The current twisted-module axioms do not prove those obligations: their
eigenspace support and Jacobi laws apply only after an actual eigenspace representative has been
provided, whereas a fixed class in the C2 quotient need not have a fixed representative.  No
existence of the descent obligations is asserted.  The identity-twist and adjoint lemmas at the
end identify all C2 carriers which can already be identified without that descent theorem.

The distinct Dong--Zhao convention involving `parity * g` belongs only to the separately named
twisted-Zhu comparison file; it never enters the relative quotient below.
-/

namespace VOA

open Module (End)
open GammaThetaStmt

set_option autoImplicit false

universe u v

variable {VType : Type u} [AddCommGroup VType] [Module ℂ VType]
variable {M : Type v} [AddCommGroup M] [Module ℂ M]
variable {W : SuperVertexOperatorAlgebra VType}

/-! ## The state C2 quotient and its fixed subspace -/

/-- The super C2 symbol space `R_V = V / C2(V)`. -/
noncomputable abbrev SuperC2Symbol (W : SuperVertexOperatorAlgebra VType) : Type u :=
  VType ⧸ superO₂ W

/-- The projection to the super C2 symbol space. -/
noncomputable def superC2Mk (W : SuperVertexOperatorAlgebra VType) :
    VType →ₗ[ℂ] SuperC2Symbol W :=
  (superO₂ W).mkQ

/-- A super-VOA automorphism preserves the C2 relation subspace. -/
theorem SuperAut.map_mem_superO₂ (g : SuperAut W) {x : VType} (hx : x ∈ superO₂ W) :
    g x ∈ superO₂ W := by
  refine Submodule.span_induction (p := fun y _ => g y ∈ superO₂ W) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨a, b, rfl⟩
    rw [g.map_smul]
    exact Submodule.subset_span ⟨g a, g b, rfl⟩
  · change g (0 : VType) ∈ superO₂ W
    simp
  · intro a b _ _ ha hb
    rw [g.toLinearEquiv.map_add]
    exact (superO₂ W).add_mem ha hb
  · intro c a _ ha
    rw [g.toLinearEquiv.map_smul]
    exact (superO₂ W).smul_mem c ha

/-- The endomorphism induced by `g` on `R_V`. -/
noncomputable def SuperAut.superC2Map (g : SuperAut W) :
    End ℂ (SuperC2Symbol W) :=
  (superO₂ W).liftQ ((superO₂ W).mkQ.comp g.toLinearEquiv.toLinearMap) (by
    intro x hx
    change (superO₂ W).mkQ (g x) = 0
    exact (Submodule.Quotient.mk_eq_zero (superO₂ W)).2 (g.map_mem_superO₂ hx))

@[simp] theorem SuperAut.superC2Map_mk (g : SuperAut W) (x : VType) :
    g.superC2Map (superC2Mk W x) = superC2Mk W (g x) := rfl

@[simp] theorem SuperAut.superC2Map_one_apply (x : SuperC2Symbol W) :
    (1 : SuperAut W).superC2Map x = x := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (superO₂ W) x
  rfl

/-- The action on the C2 quotient respects the automorphism multiplication order. -/
@[simp] theorem SuperAut.superC2Map_mul_apply (g h : SuperAut W)
    (x : SuperC2Symbol W) :
    (g * h).superC2Map x = g.superC2Map (h.superC2Map x) := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (superO₂ W) x
  rfl

/-- The literal invariant subspace `(R_V)^g` of the state C2 quotient. -/
noncomputable def SuperAut.superC2Fixed (g : SuperAut W) :
    Submodule ℂ (SuperC2Symbol W) :=
  LinearMap.ker (g.superC2Map - LinearMap.id)

theorem SuperAut.mem_superC2Fixed_iff (g : SuperAut W) (x : SuperC2Symbol W) :
    x ∈ g.superC2Fixed ↔ g.superC2Map x = x := by
  rw [SuperAut.superC2Fixed, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

@[simp] theorem SuperAut.superC2Fixed_one :
    (1 : SuperAut W).superC2Fixed = ⊤ := by
  ext x
  rw [SuperAut.mem_superC2Fixed_iff]
  simp

/-! ## Canonical module C2 carriers -/

/-- The ordinary module `C2(M)` span for a super weak module. -/
def SuperWeakModule.superC2Span
    (A : SuperWeakModule W.toSuperVertexAlgebra M) : Submodule ℂ M :=
  Submodule.span ℂ {y : M | ∃ a : VType, ∃ x : M, y = A.act a (-2) x}

/-- The ordinary module symbol carrier `R_M = M / C2(M)`. -/
noncomputable abbrev SuperWeakModule.SuperC2Symbol
    (A : SuperWeakModule W.toSuperVertexAlgebra M) : Type v :=
  M ⧸ A.superC2Span

/-- For a `1/N`-labelled twisted module, mode `-2` has integer label `-2N`. -/
def SuperTwistedModule.superC2Span {g : SuperAut W} {N : ℕ}
    (T : SuperTwistedModule W g N M) : Submodule ℂ M :=
  Submodule.span ℂ
    {y : M | ∃ a : VType, ∃ x : M, y = T.act a (-2 * (N : ℤ)) x}

/-- The canonical candidate `R_M` carrier of a twisted module. -/
noncomputable abbrev SuperTwistedModule.SuperC2Symbol {g : SuperAut W} {N : ℕ}
    (T : SuperTwistedModule W g N M) : Type v :=
  M ⧸ T.superC2Span

/-- Projection to the twisted-module C2 carrier. -/
noncomputable def SuperTwistedModule.superC2Mk {g : SuperAut W} {N : ℕ}
    (T : SuperTwistedModule W g N M) : M →ₗ[ℂ] T.SuperC2Symbol :=
  T.superC2Span.mkQ

/-! ## The exact relative quotient from a descended bilinear zero-mode operation -/

/-- A bilinear descended zero-mode/bracket operation of `(R_V)^g` on a proposed module symbol
carrier `R_M`.

The type already contains the two quotients/fixed locus; this is data, not a proposition asserting
that an unspecified operation exists.  It is exactly the data needed to form the bracket-image
quotient below; no Poisson-module Jacobi or derivation law is included. -/
structure SuperRelativePoissonData (W : SuperVertexOperatorAlgebra VType)
    (g : SuperAut W) (RM : Type v) [AddCommGroup RM] [Module ℂ RM] where
  /-- The descended bilinear zero-mode/bracket operation. -/
  bracketAction : g.superC2Fixed →ₗ[ℂ] RM →ₗ[ℂ] RM

namespace SuperRelativePoissonData

variable {RM : Type v} [AddCommGroup RM] [Module ℂ RM]
variable {g : SuperAut W}

/-- The literal bracket-image span `{(R_V)^g, R_M}`. -/
def bracketSpan (D : SuperRelativePoissonData W g RM) : Submodule ℂ RM :=
  Submodule.span ℂ {y : RM | ∃ a : g.superC2Fixed, ∃ x : RM,
    y = D.bracketAction a x}

/-- The relative invariant Poisson quotient `R_M / {(R_V)^g, R_M}`. -/
noncomputable abbrev HP₀ (D : SuperRelativePoissonData W g RM) : Type v :=
  RM ⧸ D.bracketSpan

/-- The quotient projection onto relative Poisson homology. -/
noncomputable def mkQ (D : SuperRelativePoissonData W g RM) : RM →ₗ[ℂ] D.HP₀ :=
  D.bracketSpan.mkQ

/-- Relative super Etingof finiteness is finite-dimensionality of the displayed quotient. -/
def SuperRelativeEtingofFinite (D : SuperRelativePoissonData W g RM) : Prop :=
  FiniteDimensional ℂ D.HP₀

theorem superRelativeEtingofFinite_iff (D : SuperRelativePoissonData W g RM) :
    D.SuperRelativeEtingofFinite ↔
      FiniteDimensional ℂ (RM ⧸ D.bracketSpan) := Iff.rfl

/-- A finite-dimensional module symbol carrier has finite-dimensional relative Poisson homology. -/
theorem superRelativeEtingofFinite_of_finiteDimensional
    (D : SuperRelativePoissonData W g RM) [FiniteDimensional ℂ RM] :
    D.SuperRelativeEtingofFinite := by
  exact Module.Finite.quotient ℂ D.bracketSpan

end SuperRelativePoissonData

/-! ## Twisted-module realization datum -/

/-- The exact missing descent interface for a fixed `g`-twisted module.

It supplies a bilinear operation on the two C2 quotients and certifies that it is represented by
the fractional-label-zero mode.  In particular, changing either representative is forced to give
the same class.  This is representative-descent data, not a package of Poisson-module laws. -/
structure SuperTwistedRelativePoissonData {g : SuperAut W} {N : ℕ}
    (T : SuperTwistedModule W g N M) where
  /-- The descended action of `(R_V)^g` on `R_M`. -/
  bracketAction : g.superC2Fixed →ₗ[ℂ] T.SuperC2Symbol →ₗ[ℂ] T.SuperC2Symbol
  /-- The descended action agrees with the zero fractional mode on representatives. -/
  bracketAction_mk : ∀ (a : VType) (ha : superC2Mk W a ∈ g.superC2Fixed) (x : M),
    bracketAction ⟨superC2Mk W a, ha⟩ (T.superC2Mk x) =
      T.superC2Mk (T.act a 0 x)

/-! ## Exact zero-mode descent obligations -/

/-- State representatives whose C2 classes are fixed by `g`.

This is deliberately the preimage of the fixed subspace in the quotient, rather than the
generally smaller subspace of states fixed by `g`. -/
noncomputable def SuperAut.superC2FixedPreimage (g : SuperAut W) : Submodule ℂ VType :=
  g.superC2Fixed.comap (superC2Mk W)

/-- The quotient projection from fixed-class representatives onto `(R_V)^g`. -/
noncomputable def SuperAut.superC2FixedMk (g : SuperAut W) :
    g.superC2FixedPreimage →ₗ[ℂ] g.superC2Fixed where
  toFun a := ⟨superC2Mk W a.1, a.2⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Every fixed C2 class has a representative in `superC2FixedPreimage`; no fixed representative
is chosen or asserted. -/
theorem SuperAut.superC2FixedMk_surjective (g : SuperAut W) :
    Function.Surjective g.superC2FixedMk := by
  intro a
  obtain ⟨b, hb⟩ := Submodule.mkQ_surjective (superO₂ W) a.1
  refine ⟨⟨b, ?_⟩, ?_⟩
  · change (superO₂ W).mkQ b ∈ g.superC2Fixed
    rw [hb]
    exact a.2
  · ext
    exact hb

/-- The raw label-zero action, restricted only by the condition that the state has fixed C2
class and projected on the output to the module C2 quotient. -/
noncomputable def SuperTwistedModule.fixedClassZeroMode {g : SuperAut W} {N : ℕ}
    (T : SuperTwistedModule W g N M) :
    g.superC2FixedPreimage →ₗ[ℂ] M →ₗ[ℂ] T.SuperC2Symbol where
  toFun a := T.superC2Mk.comp (T.YM a.1 0)
  map_add' a b := by
    ext x
    simp
  map_smul' c a := by
    ext x
    simp

/-- The two exact conditions needed for the label-zero action to descend.

`stateC2` says that changing a representative of a fixed state-side C2 class does not change the
output class.  `moduleC2` says that changing the module representative does not change the output
class.  The quantification in the second condition is only over representatives of fixed quotient
classes, so this interface does not require a zero-mode action of all of `R_V` on `R_M`. -/
structure SuperTwistedZeroModeDescent {g : SuperAut W} {N : ℕ}
    (T : SuperTwistedModule W g N M) : Prop where
  /-- State-C2 relations act into the module-C2 relation span. -/
  stateC2 : ∀ (a : g.superC2FixedPreimage), a.1 ∈ superO₂ W → ∀ x : M,
    T.act a.1 0 x ∈ T.superC2Span
  /-- Fixed-class zero modes preserve the module-C2 relation span. -/
  moduleC2 : ∀ (a : g.superC2FixedPreimage) (x : M), x ∈ T.superC2Span →
    T.act a.1 0 x ∈ T.superC2Span

namespace SuperTwistedRelativePoissonData

variable {g : SuperAut W} {N : ℕ} {T : SuperTwistedModule W g N M}

/-- Any already-descended relative action satisfies the two representative-independence
conditions.  Together with `ofZeroModeDescent` below, this shows that the interface adds exactly
the missing descent facts rather than a stronger eigenspace or fixed-representative assumption. -/
theorem toZeroModeDescent (D : SuperTwistedRelativePoissonData T) :
    SuperTwistedZeroModeDescent T where
  stateC2 a ha x := by
    apply (Submodule.Quotient.mk_eq_zero T.superC2Span).1
    change T.superC2Mk (T.act a.1 0 x) = 0
    rw [← D.bracketAction_mk a.1 a.2 x]
    have hzero : superC2Mk W a.1 = 0 := by
      exact (Submodule.Quotient.mk_eq_zero (superO₂ W)).2 ha
    have hfixed : (⟨superC2Mk W a.1, a.2⟩ : g.superC2Fixed) = 0 := by
      ext
      exact hzero
    rw [hfixed]
    simp
  moduleC2 a x hx := by
    apply (Submodule.Quotient.mk_eq_zero T.superC2Span).1
    change T.superC2Mk (T.act a.1 0 x) = 0
    rw [← D.bracketAction_mk a.1 a.2 x]
    have hzero : T.superC2Mk x = 0 :=
      (Submodule.Quotient.mk_eq_zero T.superC2Span).2 hx
    rw [hzero]
    exact LinearMap.map_zero (D.bracketAction ⟨superC2Mk W a.1, a.2⟩)

/-- The raw fixed-class zero-mode action kills the kernel of the state quotient whenever the
state-side descent obligation holds. -/
private theorem fixedClassZeroMode_ker_left (D : SuperTwistedZeroModeDescent T) :
    LinearMap.ker g.superC2FixedMk ≤ LinearMap.ker T.fixedClassZeroMode := by
  intro a ha
  rw [LinearMap.mem_ker] at ha ⊢
  ext x
  apply (Submodule.Quotient.mk_eq_zero T.superC2Span).2
  apply D.stateC2 a
  apply (Submodule.Quotient.mk_eq_zero (superO₂ W)).1
  change superC2Mk W a.1 = 0
  exact congrArg Subtype.val ha

/-- The raw fixed-class zero-mode action kills module C2 relations whenever the module-side
descent obligation holds. -/
private theorem fixedClassZeroMode_ker_right (D : SuperTwistedZeroModeDescent T) :
    T.superC2Span ≤ LinearMap.ker T.fixedClassZeroMode.flip := by
  intro x hx
  rw [LinearMap.mem_ker]
  ext a
  apply (Submodule.Quotient.mk_eq_zero T.superC2Span).2
  exact D.moduleC2 a x hx

/-- Construct the descended relative action from the two exact zero-mode descent obligations.

The construction first quotients fixed-class representatives by the kernel of their projection
onto `(R_V)^g`; the first isomorphism theorem identifies that quotient with the literal fixed
subspace.  It never replaces `g` by `parity * g` and never chooses a fixed representative. -/
noncomputable def ofZeroModeDescent (D : SuperTwistedZeroModeDescent T) :
    SuperTwistedRelativePoissonData T where
  bracketAction :=
    (T.fixedClassZeroMode.liftQ₂ (LinearMap.ker g.superC2FixedMk) T.superC2Span
      (fixedClassZeroMode_ker_left D) (fixedClassZeroMode_ker_right D)).comp
        (g.superC2FixedMk.quotKerEquivOfSurjective
          g.superC2FixedMk_surjective).symm.toLinearMap
  bracketAction_mk a ha x := by
    change
      (T.fixedClassZeroMode.liftQ₂ (LinearMap.ker g.superC2FixedMk) T.superC2Span
        (fixedClassZeroMode_ker_left D) (fixedClassZeroMode_ker_right D))
          ((g.superC2FixedMk.quotKerEquivOfSurjective
            g.superC2FixedMk_surjective).symm ⟨superC2Mk W a, ha⟩)
          (T.superC2Mk x) = T.superC2Mk (T.act a 0 x)
    rw [show (⟨superC2Mk W a, ha⟩ : g.superC2Fixed) =
        g.superC2FixedMk ⟨a, ha⟩ by rfl]
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl

/-- The two representative-independence conditions are equivalent to the existence of a
descended relative zero-mode action with the required representative formula. -/
theorem zeroModeDescent_iff_nonempty :
    SuperTwistedZeroModeDescent T ↔ Nonempty (SuperTwistedRelativePoissonData T) := by
  constructor
  · exact fun D => ⟨ofZeroModeDescent D⟩
  · rintro ⟨D⟩
    exact D.toZeroModeDescent

/-- Forget the representative compatibility and retain the bilinear operation used to form the
relative bracket-image quotient. -/
noncomputable def toRelativePoissonData (D : SuperTwistedRelativePoissonData T) :
    SuperRelativePoissonData W g T.SuperC2Symbol where
  bracketAction := D.bracketAction

/-- The exact relative quotient of a twisted module once zero-mode descent is supplied. -/
noncomputable abbrev HP₀ (D : SuperTwistedRelativePoissonData T) : Type v :=
  D.toRelativePoissonData.HP₀

/-- Relative Etingof finiteness for the fixed spatial twist `g`. -/
def SuperRelativeEtingofFinite (D : SuperTwistedRelativePoissonData T) : Prop :=
  FiniteDimensional ℂ D.HP₀

theorem superRelativeEtingofFinite_iff (D : SuperTwistedRelativePoissonData T) :
    D.SuperRelativeEtingofFinite ↔
      FiniteDimensional ℂ
        (T.SuperC2Symbol ⧸ D.toRelativePoissonData.bracketSpan) := Iff.rfl

end SuperTwistedRelativePoissonData

/-! ## Identity-twist and adjoint carrier specializations -/

/-- The `C2(M)` span of an identity-twisted ordinary supermodule is its ordinary module C2 span. -/
theorem SuperOrdVModule.toIdentityTwist_superC2Span (A : SuperOrdVModule W M) :
    A.toIdentityTwist.superC2Span = A.toSuperWeakModule.superC2Span := by
  rw [SuperTwistedModule.superC2Span, SuperWeakModule.superC2Span]
  congr 1

/-- The corresponding identity-twist and ordinary module C2 symbol spaces are canonically
linearly equivalent. -/
noncomputable def SuperOrdVModule.toIdentityTwistSuperC2SymbolEquiv
    (A : SuperOrdVModule W M) :
    A.toIdentityTwist.SuperC2Symbol ≃ₗ[ℂ] A.toSuperWeakModule.SuperC2Symbol :=
  Submodule.quotEquivOfEq _ _ A.toIdentityTwist_superC2Span

/-- For the adjoint weak module, module `C2(M)` is exactly the state-space `superO₂`. -/
theorem SuperNearVOA.adjointSuperWeakModule_superC2Span (W : SuperVertexOperatorAlgebra VType) :
    W.toSuperNearVOA.adjointSuperWeakModule.superC2Span = superO₂ W := by
  rfl

/-- Consequently the adjoint module C2 carrier is canonically the state symbol space `R_V`. -/
noncomputable def SuperNearVOA.adjointSuperC2SymbolEquiv
    (W : SuperVertexOperatorAlgebra VType) :
    W.toSuperNearVOA.adjointSuperWeakModule.SuperC2Symbol ≃ₗ[ℂ] SuperC2Symbol W :=
  Submodule.quotEquivOfEq _ _
    (SuperNearVOA.adjointSuperWeakModule_superC2Span W)

end VOA
