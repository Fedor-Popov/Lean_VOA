/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SymmetricFunctionals
import VOA.Modules.SuperZhuRing
import VOA.Core.QuotientVOA

/-!
# Supersymmetric functionals and the supercommutator quotient

This file is the algebraic endpoint of the untwisted supertrace version of the
Arike--Nagatomo genus-one bound.  It deliberately assumes neither finite-dimensionality nor
semisimplicity.

For a `ZMod 2`-graded associative complex algebra `A`, a homogeneous supercommutator is

`a * b - koszul p q • (b * a)`,  for `a ∈ A_p` and `b ∈ A_q`.

A linear functional is supersymmetric when it kills every such expression, equivalently when
`phi (a*b) = koszul p q * phi (b*a)` on homogeneous inputs.  The main theorem identifies the
space of these functionals with the full dual of the supercommutator quotient.  No assertion is
made here about ordinary traces, supertraces on modules, or pseudo-supertraces; those are
realisation theorems downstream of this purely algebraic statement.

## Main declarations

* `AssociativeSuperalgebra` -- an internal parity grading compatible with multiplication;
* `superCommSpan` -- the span of homogeneous supercommutators;
* `supersymmetricFunctionals` -- linear functionals satisfying homogeneous Koszul cyclicity;
* `supersymmetricFunctionalsEquivDualQuot` -- the canonical equivalence with the dual quotient;
* `finrank_supersymmetricFunctionals_eq_finrank_quot_superCommSpan`;
* `finiteDimensional_supersymmetricFunctionals_of_quot` and
  `finiteDimensional_supersymmetricFunctionals`.

The final section constructs the parity grading on the super Zhu quotient.  Its substantive input
is proved here: `superO` is stable under both parity projections.

## Status

Proved without `sorry`, `admit`, `native_decide`, or new axioms.
-/

namespace VOA

open Module (finrank)

universe u

variable {A : Type u} [Ring A] [Algebra ℂ A]

/-! ## A small bundle for an associative superalgebra -/

/-- A complex associative algebra with an internal `ZMod 2` grading respected by
multiplication.  This is intentionally data, rather than a typeclass: a single algebra may be
studied with more than one grading, and all relevant parity data should remain visible in theorem
statements. -/
structure AssociativeSuperalgebra (A : Type u) [Ring A] [Algebra ℂ A]
    extends ParityGrading A where
  /-- Products of homogeneous elements have the sum parity. -/
  mul_mem : ∀ {p q : ZMod 2} {a b : A},
    a ∈ parity p → b ∈ parity q → a * b ∈ parity (p + q)

namespace AssociativeSuperalgebra

variable (P : AssociativeSuperalgebra A)

@[simp] theorem toParityGrading_parity (p : ZMod 2) :
    P.toParityGrading.parity p = P.parity p := rfl

/-- Every element is the sum of an even and an odd element. -/
theorem exists_parity_decomp (a : A) :
    ∃ a0 ∈ P.parity 0, ∃ a1 ∈ P.parity 1, a0 + a1 = a :=
  P.toParityGrading.exists_parity_decomp a

end AssociativeSuperalgebra

/-! ## The homogeneous supercommutator quotient -/

/-- The span of homogeneous **supercommutators**
`a*b - (-1)^(p*q) b*a`, with `a` of parity `p` and `b` of parity `q`.

Restricting the generators to homogeneous inputs is essential: the sign has no meaning for an
inhomogeneous input until it is decomposed into parity components. -/
def superCommSpan (P : AssociativeSuperalgebra A) : Submodule ℂ A :=
  Submodule.span ℂ {x : A | ∃ (p q : ZMod 2) (a b : A),
    a ∈ P.parity p ∧ b ∈ P.parity q ∧ x = a * b - koszul p q • (b * a)}

/-- Every homogeneous supercommutator belongs to `superCommSpan`. -/
theorem mul_sub_koszul_smul_mul_mem_superCommSpan (P : AssociativeSuperalgebra A)
    {p q : ZMod 2} {a b : A} (ha : a ∈ P.parity p) (hb : b ∈ P.parity q) :
    a * b - koszul p q • (b * a) ∈ superCommSpan P :=
  Submodule.subset_span ⟨p, q, a, b, ha, hb, rfl⟩

/-! ## Supersymmetric functionals -/

/-- The complex-linear functionals satisfying Koszul cyclicity on homogeneous inputs:
`phi (a*b) = (-1)^(p*q) phi (b*a)` for `a ∈ A_p`, `b ∈ A_q`. -/
def supersymmetricFunctionals (P : AssociativeSuperalgebra A) :
    Submodule ℂ (A →ₗ[ℂ] ℂ) where
  carrier := {phi : A →ₗ[ℂ] ℂ | ∀ (p q : ZMod 2) (a b : A),
    a ∈ P.parity p → b ∈ P.parity q →
      phi (a * b) = koszul p q * phi (b * a)}
  add_mem' := by
    intro phi psi hphi hpsi p q a b ha hb
    change phi (a * b) + psi (a * b) =
      koszul p q * (phi (b * a) + psi (b * a))
    rw [hphi p q a b ha hb, hpsi p q a b ha hb, mul_add]
  zero_mem' := by
    intro p q a b ha hb
    simp
  smul_mem' := by
    intro c phi hphi p q a b ha hb
    change c * phi (a * b) = koszul p q * (c * phi (b * a))
    rw [hphi p q a b ha hb]
    ring

@[simp] theorem mem_supersymmetricFunctionals {P : AssociativeSuperalgebra A}
    {phi : A →ₗ[ℂ] ℂ} :
    phi ∈ supersymmetricFunctionals P ↔
      ∀ (p q : ZMod 2) (a b : A), a ∈ P.parity p → b ∈ P.parity q →
        phi (a * b) = koszul p q * phi (b * a) := Iff.rfl

/-- A supersymmetric functional kills the whole supercommutator span. -/
theorem superCommSpan_le_ker_of_supersymmetric {P : AssociativeSuperalgebra A}
    {phi : A →ₗ[ℂ] ℂ} (hphi : phi ∈ supersymmetricFunctionals P) :
    superCommSpan P ≤ LinearMap.ker phi := by
  rw [superCommSpan, Submodule.span_le]
  rintro _ ⟨p, q, a, b, ha, hb, rfl⟩
  change phi (a * b - koszul p q • (b * a)) = 0
  rw [map_sub, map_smul, hphi p q a b ha hb]
  simp

/-- Conversely, a functional which kills the supercommutator span is supersymmetric. -/
theorem mem_supersymmetricFunctionals_of_superCommSpan_le_ker
    {P : AssociativeSuperalgebra A} {phi : A →ₗ[ℂ] ℂ}
    (hphi : superCommSpan P ≤ LinearMap.ker phi) :
    phi ∈ supersymmetricFunctionals P := by
  rw [mem_supersymmetricFunctionals]
  intro p q a b ha hb
  have hmem := hphi (mul_sub_koszul_smul_mul_mem_superCommSpan P ha hb)
  rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at hmem
  exact hmem

/-! ## Equivalence with the dual quotient -/

/-- A supersymmetric functional descends to the supercommutator quotient. -/
noncomputable def supersymmetricLift (P : AssociativeSuperalgebra A) :
    supersymmetricFunctionals P →ₗ[ℂ] Module.Dual ℂ (A ⧸ superCommSpan P) where
  toFun phi := Submodule.liftQ _ phi.1 (superCommSpan_le_ker_of_supersymmetric phi.2)
  map_add' phi psi := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := (superCommSpan P).mkQ_surjective q
    rfl
  map_smul' c phi := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := (superCommSpan P).mkQ_surjective q
    rfl

@[simp] theorem supersymmetricLift_apply_mk (P : AssociativeSuperalgebra A)
    (phi : supersymmetricFunctionals P) (a : A) :
    supersymmetricLift P phi ((superCommSpan P).mkQ a) = (phi : A →ₗ[ℂ] ℂ) a := rfl

/-- Pulling a functional back from the quotient gives a supersymmetric functional. -/
theorem mem_supersymmetricFunctionals_comp_mkQ (P : AssociativeSuperalgebra A)
    (psi : Module.Dual ℂ (A ⧸ superCommSpan P)) :
    (psi ∘ₗ (superCommSpan P).mkQ) ∈ supersymmetricFunctionals P := by
  apply mem_supersymmetricFunctionals_of_superCommSpan_le_ker
  intro x hx
  rw [LinearMap.mem_ker]
  change psi ((superCommSpan P).mkQ x) = 0
  have hzero : (superCommSpan P).mkQ x = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  rw [hzero, map_zero]

/-- Pullback from the quotient, as a linear map into supersymmetric functionals. -/
noncomputable def supersymmetricOfDualQuot (P : AssociativeSuperalgebra A) :
    Module.Dual ℂ (A ⧸ superCommSpan P) →ₗ[ℂ] supersymmetricFunctionals P where
  toFun psi := ⟨psi ∘ₗ (superCommSpan P).mkQ,
    mem_supersymmetricFunctionals_comp_mkQ P psi⟩
  map_add' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)

@[simp] theorem supersymmetricOfDualQuot_apply_apply (P : AssociativeSuperalgebra A)
    (psi : Module.Dual ℂ (A ⧸ superCommSpan P)) (a : A) :
    ((supersymmetricOfDualQuot P psi : supersymmetricFunctionals P) : A →ₗ[ℂ] ℂ) a =
      psi ((superCommSpan P).mkQ a) := rfl

/-- `supersymmetricOfDualQuot` is a right inverse of `supersymmetricLift`. -/
theorem supersymmetricLift_supersymmetricOfDualQuot (P : AssociativeSuperalgebra A)
    (psi : Module.Dual ℂ (A ⧸ superCommSpan P)) :
    supersymmetricLift P (supersymmetricOfDualQuot P psi) = psi := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨x, rfl⟩ := (superCommSpan P).mkQ_surjective q
  rfl

/-- `supersymmetricLift` is injective. -/
theorem supersymmetricLift_injective (P : AssociativeSuperalgebra A) :
    Function.Injective (supersymmetricLift P) := by
  intro phi psi h
  refine Subtype.ext (LinearMap.ext fun a => ?_)
  have ha := congrArg (fun f => f ((superCommSpan P).mkQ a)) h
  exact ha

/-- `supersymmetricLift` is surjective. -/
theorem supersymmetricLift_surjective (P : AssociativeSuperalgebra A) :
    Function.Surjective (supersymmetricLift P) :=
  fun psi => ⟨supersymmetricOfDualQuot P psi,
    supersymmetricLift_supersymmetricOfDualQuot P psi⟩

/-- Supersymmetric functionals are canonically the full dual of the supercommutator quotient. -/
noncomputable def supersymmetricFunctionalsEquivDualQuot (P : AssociativeSuperalgebra A) :
    supersymmetricFunctionals P ≃ₗ[ℂ] Module.Dual ℂ (A ⧸ superCommSpan P) :=
  LinearEquiv.ofBijective (supersymmetricLift P)
    ⟨supersymmetricLift_injective P, supersymmetricLift_surjective P⟩

@[simp] theorem supersymmetricFunctionalsEquivDualQuot_apply_mk
    (P : AssociativeSuperalgebra A) (phi : supersymmetricFunctionals P) (a : A) :
    supersymmetricFunctionalsEquivDualQuot P phi ((superCommSpan P).mkQ a) =
      (phi : A →ₗ[ℂ] ℂ) a := rfl

/-! ## Dimension and finite-dimensionality -/

/-- The dimension of the supersymmetric functionals equals the dimension of the
supercommutator quotient, without any semisimplicity or finiteness hypothesis. -/
theorem finrank_supersymmetricFunctionals_eq_finrank_quot_superCommSpan
    (P : AssociativeSuperalgebra A) :
    finrank ℂ (supersymmetricFunctionals P) = finrank ℂ (A ⧸ superCommSpan P) := by
  rw [(supersymmetricFunctionalsEquivDualQuot P).finrank_eq, Subspace.dual_finrank_eq]

/-- Sharp finiteness: it suffices for the supercommutator quotient to be finite-dimensional. -/
theorem finiteDimensional_supersymmetricFunctionals_of_quot
    (P : AssociativeSuperalgebra A) [FiniteDimensional ℂ (A ⧸ superCommSpan P)] :
    FiniteDimensional ℂ (supersymmetricFunctionals P) :=
  (supersymmetricFunctionalsEquivDualQuot P).symm.finiteDimensional

/-- In particular, a finite-dimensional associative superalgebra has a finite-dimensional space
of supersymmetric functionals, with no semisimplicity assumption. -/
theorem finiteDimensional_supersymmetricFunctionals (P : AssociativeSuperalgebra A)
    [FiniteDimensional ℂ A] :
    FiniteDimensional ℂ (supersymmetricFunctionals P) :=
  finiteDimensional_supersymmetricFunctionals_of_quot P

/-! ## The canonical parity grading on the super Zhu algebra

The generic theory above does not know about vertex operators or conformal weights.  We next prove
the one compatibility fact needed to apply it to the Dong--Zhao quotient: `superO` is stable under
the two parity projections.  Consequently the images of the two state-space parity pieces form
an internal grading of `superA`, and the descended Zhu product respects it.

Integral weights enter only in this application section, through the definition of `superA`;
they are not entangled with `AssociativeSuperalgebra`, `superCommSpan`, or supersymmetric
cyclicity. -/

section SuperZhuParity

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights)

/-- Every Virasoro mode preserves parity because the conformal vector is even. -/
theorem SuperNearVOA.L_mem_parity (n : ℤ) {p : ZMod 2} {u : 𝒱}
    (hu : u ∈ V.parity p) : V.L n u ∈ V.parity p := by
  have h := V.parity_mode V.conformalVector V.conformal_parity u hu (n + 1)
  rw [zero_add] at h
  exact h

/-- A defining generator of `superO`, built from parity-homogeneous inputs, is homogeneous of the
sum parity. -/
theorem SuperNearVOA.superO_generator_mem_parity {p q : ZMod 2} {u v : 𝒱}
    (hu : u ∈ V.parity p) (hv : v ∈ V.parity q) :
    V.superZhuMul hV (V.L (-1) u + V.L 0 u) v ∈ V.parity (p + q) := by
  apply V.superZhuMul_mem_parity hV
  · exact Submodule.add_mem _ (V.L_mem_parity (-1) hu) (V.L_mem_parity 0 hu)
  · exact hv

/-- The parity projection of a parity-homogeneous defining generator of `superO` remains in
`superO` (it is either that generator or zero). -/
theorem SuperNearVOA.parProj_superO_generator_mem {p q r : ZMod 2} {u v : 𝒱}
    (hu : u ∈ V.parity p) (hv : v ∈ V.parity q) :
    V.parProj r (V.superZhuMul hV (V.L (-1) u + V.L 0 u) v) ∈ V.superO hV := by
  by_cases hdeg : p + q = r
  · rw [V.parProj_of_mem (hdeg ▸ V.superO_generator_mem_parity hV hu hv)]
    exact V.superO_mem_of_L hV u v
  · rw [V.parProj_of_mem_ne hdeg (V.superO_generator_mem_parity hV hu hv)]
    exact Submodule.zero_mem _

/-- `superO` is stable under each state-space parity projection. -/
theorem SuperNearVOA.parProj_mem_superO (r : ZMod 2) {x : 𝒱}
    (hx : x ∈ V.superO hV) : V.parProj r x ∈ V.superO hV := by
  rw [superO] at hx
  refine Submodule.span_induction
    (p := fun x _ => V.parProj r x ∈ V.superO hV) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨u, v, rfl⟩
    let P : ParityGrading 𝒱 := ⟨V.parity, V.parity_isInternal⟩
    obtain ⟨u0, hu0, u1, hu1, hu⟩ := P.exists_parity_decomp u
    obtain ⟨v0, hv0, v1, hv1, hv⟩ := P.exists_parity_decomp v
    have hleft : V.L (-1) (u0 + u1) + V.L 0 (u0 + u1) =
        (V.L (-1) u0 + V.L 0 u0) + (V.L (-1) u1 + V.L 0 u1) := by
      simp only [map_add]
      abel
    rw [← hu, ← hv, hleft, V.superZhuMul_add_left,
      V.superZhuMul_add_right, V.superZhuMul_add_right, map_add, map_add, map_add]
    have h00 := V.parProj_superO_generator_mem hV (r := r) (p := 0) (q := 0) hu0 hv0
    have h01 := V.parProj_superO_generator_mem hV (r := r) (p := 0) (q := 1) hu0 hv1
    have h10 := V.parProj_superO_generator_mem hV (r := r) (p := 1) (q := 0) hu1 hv0
    have h11 := V.parProj_superO_generator_mem hV (r := r) (p := 1) (q := 1) hu1 hv1
    exact Submodule.add_mem _
      (Submodule.add_mem _ h00 h01)
      (Submodule.add_mem _ h10 h11)
  · change V.parProj r (0 : 𝒱) ∈ V.superO hV
    rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy hpx hpy
    change V.parProj r (x + y) ∈ V.superO hV
    rw [map_add]
    exact Submodule.add_mem _ hpx hpy
  · intro c x hx hpx
    change V.parProj r (c • x) ∈ V.superO hV
    rw [map_smul]
    exact Submodule.smul_mem _ c hpx

/-- `superO` is the sum of its intersections with the two parity pieces. -/
theorem SuperNearVOA.superO_eq_iSup_inf_parity :
    V.superO hV = ⨆ p : ZMod 2, V.superO hV ⊓ V.parity p := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hsum, -⟩ := V.exists_sum_parProj x
    rw [← hsum]
    refine Submodule.sum_mem _ fun p _ => ?_
    exact Submodule.mem_iSup_of_mem p ⟨V.parProj_mem_superO hV p hx, V.parProj_mem p x⟩
  · exact iSup_le fun _ => inf_le_left

/-- The parity-`p` piece of the super Zhu quotient is the image of the parity-`p` state space. -/
noncomputable def SuperNearVOA.superAParity (p : ZMod 2) :
    Submodule ℂ (V.superA hV) :=
  (V.parity p).map (V.superMk hV)

/-- A parity-homogeneous state maps to the corresponding quotient parity piece. -/
theorem SuperNearVOA.superMk_mem_superAParity {p : ZMod 2} {u : 𝒱}
    (hu : u ∈ V.parity p) : V.superMk hV u ∈ V.superAParity hV p :=
  Submodule.mem_map_of_mem hu

/-- The two quotient parity pieces form an internal direct sum. -/
theorem SuperNearVOA.superAParity_isInternal :
    DirectSum.IsInternal (V.superAParity hV) := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · exact QuotVOA.iSupIndep_map_mkQ V.parity V.parity_isInternal.submodule_iSupIndep
      (V.superO hV) (V.superO_eq_iSup_inf_parity hV).le
  · change (⨆ p, (V.parity p).map (V.superO hV).mkQ) = ⊤
    rw [← Submodule.map_iSup, V.parity_isInternal.submodule_iSup_eq_top,
      Submodule.map_top, Submodule.range_mkQ]

/-- The parity grading carried by the super Zhu quotient as a complex vector space. -/
noncomputable def SuperNearVOA.superAParityGrading : ParityGrading (V.superA hV) where
  parity := V.superAParity hV
  isInternal := V.superAParity_isInternal hV

variable (hZ : SuperZhuRingData V hV)

/-- Under the descended Zhu multiplication, homogeneous quotient classes multiply with the sum
parity. -/
theorem SuperZhuRingData.superA_mul_mem_parity {p q : ZMod 2}
    {a b : V.superA hV} (ha : a ∈ V.superAParity hV p) (hb : b ∈ V.superAParity hV q) :
    letI := hZ.AsRing
    a * b ∈ V.superAParity hV (p + q) := by
  letI := hZ.AsRing
  obtain ⟨u, hu, hua⟩ := Submodule.mem_map.mp ha
  obtain ⟨v, hv, hvb⟩ := Submodule.mem_map.mp hb
  subst a
  subst b
  rw [hZ.AsRing_mul_eq, hZ.superAmul_mk]
  exact Submodule.mem_map_of_mem (V.superZhuMul_mem_parity hV hu hv)

/-- The canonical associative-superalgebra structure on the Dong--Zhao quotient. -/
noncomputable def SuperZhuRingData.superAAssociativeSuperalgebra :
    letI := hZ.AsRing
    letI := hZ.AsAlgebra
    AssociativeSuperalgebra (V.superA hV) := by
  letI := hZ.AsRing
  letI := hZ.AsAlgebra
  exact
    { parity := V.superAParity hV
      isInternal := V.superAParity_isInternal hV
      mul_mem := fun {p q a b} ha hb =>
        SuperZhuRingData.superA_mul_mem_parity (V := V) (hV := hV) hZ ha hb }

/-- The supercommutator span of the super Zhu algebra, with all ring, algebra, and parity data
supplied canonically by `SuperZhuRingData`. -/
noncomputable def SuperZhuRingData.superZhuCommSpan : Submodule ℂ (V.superA hV) :=
  letI := hZ.AsRing
  letI := hZ.AsAlgebra
  superCommSpan hZ.superAAssociativeSuperalgebra

/-- Supersymmetric linear functionals on the super Zhu algebra. -/
noncomputable def SuperZhuRingData.superZhuSymmetricFunctionals :
    Submodule ℂ (V.superA hV →ₗ[ℂ] ℂ) :=
  letI := hZ.AsRing
  letI := hZ.AsAlgebra
  supersymmetricFunctionals hZ.superAAssociativeSuperalgebra

/-- Specialized quotient-dual equivalence for the super Zhu algebra. -/
noncomputable def SuperZhuRingData.superZhuSymmetricFunctionalsEquivDualQuot :
    SuperZhuRingData.superZhuSymmetricFunctionals (V := V) (hV := hV) hZ ≃ₗ[ℂ]
      Module.Dual ℂ (V.superA hV ⧸
        SuperZhuRingData.superZhuCommSpan (V := V) (hV := hV) hZ) := by
  letI := hZ.AsRing
  letI := hZ.AsAlgebra
  exact supersymmetricFunctionalsEquivDualQuot hZ.superAAssociativeSuperalgebra

/-- Dimension equality specialized to the super Zhu algebra. -/
theorem SuperZhuRingData.finrank_superZhuSymmetricFunctionals_eq :
    finrank ℂ (SuperZhuRingData.superZhuSymmetricFunctionals (V := V) (hV := hV) hZ) =
      finrank ℂ (V.superA hV ⧸
        SuperZhuRingData.superZhuCommSpan (V := V) (hV := hV) hZ) := by
  letI := hZ.AsRing
  letI := hZ.AsAlgebra
  exact finrank_supersymmetricFunctionals_eq_finrank_quot_superCommSpan
    hZ.superAAssociativeSuperalgebra

end SuperZhuParity

end VOA
