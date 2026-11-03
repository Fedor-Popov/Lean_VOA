/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.NonlinearVirasoro
import VOA.Examples.VirasoroConformal
import VOA.Examples.VirasoroInstance
import VOA.Examples.VirasoroPartitionBasis
import VOA.Examples.VirasoroNonvanishing

/-!
# Generators + OPEs = Borcherds, for the Virasoro algebra

⚠ **Scope** (see `Core.NonlinearConformal`).  This is weaker than the slogan in the title: the
relations in `MRtwo (virasoroOPE c)` do not depend on `c` (certificate
`L11Checks.virasoro_MRtwo_indep`, `Notes/Textbook/certificates/L11_Checks.lean`), and the
vertex-algebra structure on the quotient is *transported* from `virasoroVOA c`; the fields are not
derived from the OPE.

`Core.NonlinearConformal` presents a vertex algebra the way a physicist does — strong generators,
conformal weights, a table of singular OPE coefficients (`OPEData`) — and reduces everything to
one structure, `GenFields M`: the generating fields on `U(R) = T(R)/M` together with lower
truncation, mutual locality, the already-constructed creation half, vacuum regularity and
`T`-covariance.  That structure was populated only for the **empty** generator set.

`Core.NonlinearVirasoro` shows the ideal the source file suggested (`MRbot`, the `D = 1` slice of
De Sole–Kac Definition 3.4) makes `GenFields` **false** for `virasoroOPE`, and supplies `MRtwo`,
the genuine two-sided `M(R)` for a linear OPE datum.  This file lands the three deliverables over
a corrected ideal.

## What is proved

* `psiVir : T(R) →ₐ[ℂ] U(𝔙𝔦𝔯)`, `gv ((),k) ↦ L₋ₖ₋₂`, with
  `psiVir_Ttr` (it intertwines `Ttr` with `ad L₋₁`) and `psiVir_rel` (**the relations die in
  `U(𝔙𝔦𝔯)`**, not merely modulo an ideal — this is where the closed form `virasoro_rel` is used).
* `PhiVir c : T(R) →ₗ[ℂ] V(c,0)`, its surjectivity (`PhiVir_surjective`, which is exactly the
  `pbw`-free spanning theorem `negSpanVir_eq_top`), and `MVir c : MIdeal (virasoroOPE c)` — the
  **corrected relation ideal** `ker Φ`, with `MRtwo_le_MVir`.
* `eVir c : UR (MVir c) ≃ₗ[ℂ] VirUniv c`, by the first isomorphism theorem.
* **Deliverable A**: `genFieldsVir c : GenFields (MVir c)` — `GenFields` populated for an
  `OPEData` that *has* generators, at every central charge.  `isFld`, `loc`, `cov` are pure
  transport (`conjDist_isField`, `conjDist_local`, `conjDist_cov`); the one genuinely new
  obligation is `cre`, the numerical match `dpow ((),k) n = C(k+n,n)·gv ((),k+n)` against the
  `zⁿ`-coefficient `C(k+n,n)·L₋ₖ₋ₙ₋₂` of `(k!)⁻¹∂ᵏY(ω,z)` (`genFieldVir_nonneg`).
* **Deliverable B**: `virasoro_UR_YA` (the all-states vertex operator map from `UR_YA`,
  unbundled) and `virasoroURVA c : PreVertexAlgebra (UR (MVir c))` (bundled, via `transportVA`),
  with `virasoroURVA_Y_gv` saying the bundled vertex operator at a strong generator **is** the
  generating field `genFieldsVir` delivers.
* **Deliverable C**: `virasoro_presentation_equivalence` — a linear equivalence
  `UR (MVir c) ≃ₗ[ℂ] VirUniv c` matching the vacuum, the translation operator, and every
  generating field with the corresponding vertex operator of the Borcherds-axiomatised
  `virasoroVOA c`; plus `fldVir_virasoro`, VOA1 for the presented algebra.
* **The vacuity trap, settled**: `UR_MVir_nontrivial` (`U(R) ≠ 0`),
  `sortedWordSt_linearIndependent` (all *sorted* monomials in the strong generators are
  independent in `U(R)`), `gv_linearIndependent` (in particular the strong generators are).
  Transported from `sortedWord_linearIndependent`, which the library proves at every central
  charge from the linear-dilaton free boson — `pbw`-free.

## ⚠ What this is and is not

**It is** a population of `GenFields` for a nonempty generator set, `pbw`-free: the only Virasoro
inputs are `negSpanVir_eq_top` and the operator-first reconstruction `virYA_exists`, both
`pbw`-free.

**It is not** a formalization of De Sole–Kac Lemma 3.2, nor of their §4.  The fields are obtained
by **conjugating an independently constructed realization** (`virYA`) across `eVir`, not by
constructing the annihilation modes from the OPE and proving locality from the mode-commutator
formula.  `Core.NonlinearConformal.local_of_ope` is the bridge a direct construction would use;
it is not used here.

⚠ **The circularity of this file's statements — removed downstream.**  `MVir c` is *defined*
as `ker Φ`, i.e. as the kernel of the map to the answer.  So `virasoro_presentation_equivalence`
over `MVir c` says "the quotient by the kernel of the map to `V(c,0)` is `V(c,0)`", strengthened
by the facts that this kernel is admissible and contains `MRtwo` (`MRtwo_le_MVir`).  The
de-circularising step

  `MRtwo (virasoroOPE c) = ker (PhiVir c)`

is **proved in `Examples.NonlinearVirasoroGenuine`** (`MRtwo_eq_ker_PhiVir`): one half is the
straightening lemma `sortedWstUw_span` (sorted words span `T(R)/MRtwo`, mirroring
`Lop_sorted_insert` — the two-sided ideal is what licenses rewriting inside a word), the other
half is `negWordVir_coef_zero'` from `Examples.VirasoroPartitionBasis`.  That file restates the
whole package over `MRtwo` (`genFieldsVirTwo`, `virasoroURVATwo`,
`virasoro_presentation_equivalence_genuine`), which is the genuine theorem
`T(R)/M(R) ≅ virasoroVOA c` for De Sole–Kac's own `M(R)`.  The statements *in this file* remain
over `ker Φ` and should be cited only through their genuine counterparts.

No `sorry`, no `admit`, no `native_decide`, no new axiom; `VOA.pbw` is not used.
-/
set_option linter.style.longLine false

namespace VOA.VirModule

open VOA
open Module (End)
open VOA.Reconstruction
open VOA.NonlinearConformal
open UniversalEnvelopingAlgebra

/-! ## §1  The comparison map `ψ : T(R) → U(𝔙𝔦𝔯)` -/

/-- The algebra map `T(R) → U(𝔙𝔦𝔯)` sending the divided power `TᵏL/k!` to `L₋ₖ₋₂`. -/
noncomputable def psiVir : TR Unit →ₐ[ℂ] UVir :=
  FreeAlgebra.lift ℂ (fun p : GenIdx Unit => ι ℂ (L (-(p.2 : ℤ) - 2)))

@[simp] theorem psiVir_gv (p : GenIdx Unit) : psiVir (gv p) = ι ℂ (L (-(p.2 : ℤ) - 2)) := by
  rw [gv_eq, psiVir, FreeAlgebra.lift_ι_apply]

/-- `ψ` intertwines the translation derivation of `T(R)` with `ad(L₋₁)` in `U(𝔙𝔦𝔯)`.  Both
sides are `ψ`-derivations and they agree on generators, where the identity is exactly
`⁅L₋₁, L₋ₖ₋₂⁆ = (k+1)L₋ₖ₋₃` (the cocycle is absent because `-k-3 ≠ 0`). -/
theorem psiVir_Ttr (X : TR Unit) :
    psiVir (Ttr X) = ι ℂ (L (-1)) * psiVir X - psiVir X * ι ℂ (L (-1)) := by
  induction X using FreeAlgebra.induction with
  | grade0 r =>
      rw [Algebra.algebraMap_eq_smul_one, map_smul, Ttr_one, smul_zero, map_zero, map_smul,
        map_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_self]
  | grade1 p =>
      rw [← gv_eq, Ttr_gv, map_smul, psiVir_gv, psiVir_gv,
        ← LieRing.of_associative_ring_bracket, ← (ι ℂ).map_lie, virasoro_bracket,
        if_neg (by omega), add_zero, map_smul,
        show (-1 : ℤ) + (-(p.2 : ℤ) - 2) = -((p.2 + 1 : ℕ) : ℤ) - 2 from by push_cast; ring]
      congr 1
      push_cast
      ring
  | mul a b ha hb =>
      rw [Ttr_mul, map_add, map_mul, map_mul, map_mul, ha, hb]
      noncomm_ring
  | add a b ha hb =>
      rw [map_add, map_add, map_add, ha, hb]
      noncomm_ring

/-- **The relations die in `U(𝔙𝔦𝔯)`** — not merely modulo an ideal.  This is the Witt relation
`⁅L₋ₖ₋₂, L₋ₗ₋₂⁆ = (l-k)L₋₍ₖ₊ₗ₊₂₎₋₂`, and it is where `virasoro_rel` (the closed form of `∫₋ᵀ⁰`)
is consumed. -/
theorem psiVir_rel (c : ℂ) (p q : GenIdx Unit) : psiVir (rel (virasoroOPE c) p q) = 0 := by
  obtain ⟨⟨⟩, k⟩ := p
  obtain ⟨⟨⟩, l⟩ := q
  rw [virasoro_rel, map_sub, map_sub, map_mul, map_mul, map_smul, psiVir_gv, psiVir_gv,
    psiVir_gv, ← LieRing.of_associative_ring_bracket, ← (ι ℂ).map_lie, virasoro_bracket,
    if_neg (by omega), add_zero, map_smul,
    show (-(k : ℤ) - 2) + (-(l : ℤ) - 2) = -((k + l + 2 : ℕ) : ℤ) - 2 from by push_cast; ring,
    sub_eq_zero]
  congr 1
  push_cast
  ring

/-! ## §2  The comparison map `Φ : T(R) → V(c,0)` and the ideal it presents -/

/-- The `ℂ`-linear comparison map `Φ : T(R) → V(c,0)`, `X ↦ [ψ X]`. -/
noncomputable def PhiVir (c : ℂ) : TR Unit →ₗ[ℂ] VirUniv c where
  toFun X := Submodule.Quotient.mk (psiVir X)
  map_add' X Y := by rw [map_add, Submodule.Quotient.mk_add]
  map_smul' a X := by rw [RingHom.id_apply, map_smul, ← Submodule.Quotient.mk_smul]

@[simp] theorem PhiVir_apply (c : ℂ) (X : TR Unit) :
    PhiVir c X = Submodule.Quotient.mk (psiVir X) := rfl

theorem PhiVir_one (c : ℂ) : PhiVir c 1 = vacVec c := by
  rw [PhiVir_apply, map_one]
  rfl

/-- Left multiplication by a generator becomes the Virasoro mode `L₋ₖ₋₂`. -/
theorem PhiVir_gv_mul (c : ℂ) (p : GenIdx Unit) (X : TR Unit) :
    PhiVir c (gv p * X) = Lop c (-(p.2 : ℤ) - 2) (PhiVir c X) := by
  rw [PhiVir_apply, map_mul, psiVir_gv, Lop, PhiVir_apply, virVacRho_mk]

theorem PhiVir_gv (c : ℂ) (k : ℕ) : PhiVir c (gv ((), k)) = negWordVir c [k] := by
  rw [show gv (((), k) : GenIdx Unit) = gv ((), k) * 1 from (mul_one _).symm, PhiVir_gv_mul,
    PhiVir_one]
  rfl

/-- `Φ` sends the word basis of `T(R)` onto the creation monomials of `V(c,0)`. -/
theorem PhiVir_wbasis (c : ℂ) (l : List (GenIdx Unit)) :
    PhiVir c (wbasis Unit (FreeMonoid.ofList l)) = negWordVir c (l.map Prod.snd) := by
  induction l with
  | nil =>
      rw [show (FreeMonoid.ofList ([] : List (GenIdx Unit))) = 1 from rfl, wbasis_one, PhiVir_one]
      rfl
  | cons p l ih =>
      have hw : wbasis Unit (FreeMonoid.ofList (p :: l))
          = gv p * wbasis Unit (FreeMonoid.ofList l) := by
        rw [show (FreeMonoid.ofList (p :: l))
          = FreeMonoid.of p * FreeMonoid.ofList l from rfl, wbasis_mul, gv]
      rw [hw, PhiVir_gv_mul, ih, List.map_cons, negWordVir_cons]

/-- `Φ` is **surjective** — this is `negSpanVir_eq_top`, the `pbw`-free spanning theorem. -/
theorem PhiVir_surjective (c : ℂ) : Function.Surjective (PhiVir c) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← negSpanVir_eq_top]
  refine Submodule.span_le.mpr ?_
  rintro x ⟨ws, rfl⟩
  refine ⟨wbasis Unit (FreeMonoid.ofList (ws.map (fun k => (((), k) : GenIdx Unit)))), ?_⟩
  rw [PhiVir_wbasis]
  congr 1
  simp

/-- `Φ` intertwines the translation derivation with `L₋₁`. -/
theorem PhiVir_Ttr (c : ℂ) (X : TR Unit) :
    PhiVir c (Ttr X) = Lop c (-1) (PhiVir c X) := by
  rw [PhiVir_apply, psiVir_Ttr, Lop, PhiVir_apply, virVacRho_mk, Submodule.Quotient.mk_sub,
    sub_eq_self, Submodule.Quotient.mk_eq_zero, ← smul_eq_mul]
  exact (vacIdeal c).smul_mem _ (vacGens_subset_ideal c (Or.inl ⟨-1, le_refl _, rfl⟩))

/-- **The corrected relation ideal**: the kernel of `Φ`.  It is admissible (a `T`-stable left
ideal containing the relations) and contains `MRtwo`, De Sole–Kac's genuine `M(R)` for this linear
datum. -/
noncomputable def MVir (c : ℂ) : MIdeal (virasoroOPE c) where
  car := LinearMap.ker (PhiVir c)
  left := by
    intro A x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have hxm : psiVir x ∈ vacIdeal c := by
      rw [← Submodule.Quotient.mk_eq_zero]
      exact hx
    rw [PhiVir_apply, map_mul, Submodule.Quotient.mk_eq_zero, ← smul_eq_mul]
    exact (vacIdeal c).smul_mem _ hxm
  Tstable := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [PhiVir_Ttr, hx, map_zero]
  rel_mem := by
    intro p q
    rw [LinearMap.mem_ker, PhiVir_apply, psiVir_rel]
    rfl

theorem MRtwo_le_MVir (c : ℂ) : (MRtwo (virasoroOPE c)).car ≤ (MVir c).car := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨⟨A, p, q, B⟩, rfl⟩
  show A * rel (virasoroOPE c) p q * B ∈ LinearMap.ker (PhiVir c)
  rw [LinearMap.mem_ker, PhiVir_apply, map_mul, map_mul, psiVir_rel, mul_zero, zero_mul]
  exact Submodule.Quotient.mk_zero _

/-! ## §3  The linear equivalence `U(R) ≅ V(c,0)` -/

/-- **`T(R)/ker Φ ≅ V(c,0)`**, by the first isomorphism theorem: surjectivity is the
`pbw`-free spanning theorem `negSpanVir_eq_top`. -/
noncomputable def eVir (c : ℂ) : UR (MVir c) ≃ₗ[ℂ] VirUniv c :=
  (PhiVir c).quotKerEquivOfSurjective (PhiVir_surjective c)

@[simp] theorem eVir_mk (c : ℂ) (X : TR Unit) :
    eVir c (Submodule.Quotient.mk X) = PhiVir c X := rfl

theorem eVir_vac (c : ℂ) : eVir c (vacU (MVir c)) = vacVec c := by
  rw [vacU, eVir_mk, PhiVir_one]

theorem eVir_TrU (c : ℂ) (u : UR (MVir c)) : eVir c (TrU (MVir c) u) = Ltrans c (eVir c u) := by
  obtain ⟨X, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  rw [TrU, descendU_mk, eVir_mk, eVir_mk, PhiVir_Ttr, Ltrans]

theorem eVir_leftMul_gv (c : ℂ) (p : GenIdx Unit) (u : UR (MVir c)) :
    eVir c (leftMulU (MVir c) (gv p) u) = Lop c (-(p.2 : ℤ) - 2) (eVir c u) := by
  obtain ⟨X, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  rw [leftMulU_mk, eVir_mk, eVir_mk, PhiVir_gv_mul]

theorem eVir_dpow (c : ℂ) (k n : ℕ) (u : UR (MVir c)) :
    eVir c (leftMulU (MVir c) (dpow ((), k) n) u)
      = (((k + n).choose n : ℕ) : ℂ) • Lop c (-((k + n : ℕ) : ℤ) - 2) (eVir c u) := by
  rw [dpow, leftMulU_smul, LinearMap.smul_apply, map_smul, eVir_leftMul_gv]

/-! ## §4  The generating fields on `V(c,0)`, coefficient by coefficient -/

/-- The `zʲ`-coefficient of an iterated formal `z`-derivative. -/
theorem deriv_iterate_apply {𝒲 : Type*} [AddCommGroup 𝒲] [Module ℂ 𝒲]
    (k : ℕ) (f : FormalDist 𝒲) (j : ℤ) :
    (VOA.deriv^[k] f) j
      = (∏ i ∈ Finset.range k, (j + 1 + (i : ℤ))) • f (j + (k : ℤ)) := by
  induction k generalizing f j with
  | zero => simp
  | succ k ih =>
      have harg : j + (k : ℤ) + 1 = j + ((k + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [Function.iterate_succ_apply, ih, deriv_apply, smul_smul, Finset.prod_range_succ]
      congr 1
      · ring
      · rw [harg]

/-- The `zʲ`-coefficient of the scaled generator field `(k!)⁻¹∂ᵏY(ω,z)`. -/
theorem genFieldVir_apply (c : ℂ) (k : ℕ) (j : ℤ) :
    genFieldVir c k j
      = (((k.factorial : ℕ) : ℂ))⁻¹ •
          ((∏ i ∈ Finset.range k, (j + 1 + (i : ℤ))) • Lop c (-(j + (k : ℤ)) - 2)) := by
  show (((k.factorial : ℕ) : ℂ))⁻¹ • ((VOA.deriv^[k] (YomegaVir c)) j) = _
  rw [deriv_iterate_apply, YomegaVir_apply]

/-- The rising factorial as a factorial times a binomial coefficient. -/
theorem prod_asc_nat (n k : ℕ) :
    ∏ i ∈ Finset.range k, (n + 1 + i) = k.factorial * (k + n).choose k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ, ih, Nat.factorial_succ,
        show n + 1 + k = k + n + 1 from by omega, show k + 1 + n = k + n + 1 from by omega,
        mul_assoc, mul_comm ((k + n).choose k) (k + n + 1), Nat.add_one_mul_choose_eq (k + n) k]
      ring

theorem choose_add_symm (k n : ℕ) : (k + n).choose n = (k + n).choose k := by
  have h := Nat.choose_symm (show n ≤ k + n from Nat.le_add_left n k)
  rw [Nat.add_sub_cancel] at h
  exact h.symm

/-- **The conventions match on the nose**: in the creation range `j = n ≥ 0` the generator
field `(k!)⁻¹∂ᵏY(ω,z)` has `zⁿ`-coefficient `C(k+n,n)·L₋ₖ₋ₙ₋₂`, which is exactly the divided power
`dpow ((),k) n` of the non-linear picture. -/
theorem genFieldVir_nonneg (c : ℂ) (k n : ℕ) :
    genFieldVir c k (n : ℤ)
      = (((k + n).choose n : ℕ) : ℂ) • Lop c (-((k + n : ℕ) : ℤ) - 2) := by
  have hfk : ((k.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hprod : (∏ i ∈ Finset.range k, ((n : ℤ) + 1 + (i : ℤ)))
      = ((k.factorial : ℕ) : ℤ) * (((k + n).choose k : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, ← prod_asc_nat n k, Nat.cast_prod]
    exact Finset.prod_congr rfl (fun i _ => by push_cast; ring)
  rw [genFieldVir_apply, hprod,
    show -((n : ℤ) + (k : ℤ)) - 2 = -((k + n : ℕ) : ℤ) - 2 from by push_cast; ring,
    ← Int.cast_smul_eq_zsmul ℂ, smul_smul, choose_add_symm]
  congr 1
  push_cast
  field_simp

/-- The field of the word `[k]` is the scaled generator field. -/
theorem virYA_gen (c : ℂ) (k : ℕ) : virYA c (PhiVir c (gv ((), k))) = genFieldVir c k := by
  rw [PhiVir_gv, virYA_word, YwordVir_cons]
  change nprod (genFieldVir_isField c k) (idField_isField) = genFieldVir c k
  rw [nprod_idField]

/-! ## §5  `GenFields` for a **nonempty** generator set -/

/-- The generating field of the divided power `TᵏL/k!` on `U(R)`, obtained by conjugating the
Virasoro vertex operator across `eVir`. -/
noncomputable def fldVir (c : ℂ) (p : GenIdx Unit) : FormalDist (End ℂ (UR (MVir c))) :=
  conjDist (eVir c) (virYA c (PhiVir c (gv p)))

/-- The creation half agrees with `creHalf` — the one obligation that is *not* pure transport:
it is the numerical match `C(k+n,n)` between the divided power `dpow` and the `zⁿ`-coefficient of
`(k!)⁻¹∂ᵏY(ω,z)`. -/
theorem fldVir_cre (c : ℂ) (p : GenIdx Unit) (j : ℤ) (hj : 0 ≤ j) :
    fldVir c p j = creHalf (MVir c) p j := by
  obtain ⟨⟨⟩, k⟩ := p
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = (n : ℤ) := ⟨j.toNat, (Int.toNat_of_nonneg hj).symm⟩
  refine LinearMap.ext (fun u => (eVir c).injective ?_)
  rw [fldVir, conjDist_apply, LinearEquiv.apply_symm_apply, creHalf_of_nonneg _ _ hj,
    Int.toNat_natCast, eVir_dpow, virYA_gen, genFieldVir_nonneg, LinearMap.smul_apply]

/-- **Deliverable A over the corrected ideal.**  `GenFields` is populated for an `OPEData`
that *has* generators: the Virasoro datum, at every central charge.  This is the step the source
file calls open.  It is obtained `pbw`-free (the only inputs from the Virasoro side are
`negSpanVir_eq_top` and the reconstruction `virYA_exists`, both `pbw`-free), but it is obtained by
**transport**, not by formalising De Sole–Kac Lemma 3.2 or §4. -/
noncomputable def genFieldsVir (c : ℂ) : GenFields (MVir c) where
  fld := fldVir c
  isFld := fun _ => conjDist_isField _ (virYA_isField c _)
  loc := fun _ _ => conjDist_local _ (virYA_local c _ _)
  cre := fldVir_cre c
  cre_neg := by
    intro p j hj
    apply (eVir c).injective
    rw [fldVir, conjDist_apply, LinearEquiv.apply_symm_apply, eVir_vac, map_zero]
    exact virYA_vacuum_neg c _ hj
  cov := fun _ => conjDist_cov (eVir c) (eVir_TrU c) (virYA_DCov c _)

/-- **Deliverable B, unbundled.**  Feeding `genFieldsVir` into `UR_YA` produces the full
all-states vertex operator map on `U(R) = T(R)/ker Φ`: VA3 creation, VA4 locality, VA5 regularity
and translation covariance — with **no PBW and no basis**. -/
theorem virasoro_UR_YA (c : ℂ) :
    ∃ YA : UR (MVir c) →ₗ[ℂ] FormalDist (End ℂ (UR (MVir c))),
      (∀ l : List (GenIdx Unit),
          YA (wordSt (genFieldsVir c).fld (vacU (MVir c)) l)
            = wordFld (genFieldsVir c).fld (genFieldsVir c).isFld l) ∧
      (∀ u : UR (MVir c), IsField (YA u)) ∧
      (∀ u v : UR (MVir c), Local (YA u) (YA v)) ∧
      (∀ u : UR (MVir c), (YA u) 0 (vacU (MVir c)) = u) ∧
      (∀ u : UR (MVir c), ∀ j : ℤ, j < 0 → (YA u) j (vacU (MVir c)) = 0) ∧
      (∀ u : UR (MVir c), DCovariant (TrU (MVir c)) (YA u)) :=
  UR_YA (genFieldsVir c)

/-! ## §6  Deliverable C: the presentation **is** the Borcherds-axiomatised Virasoro VOA -/

/-- The generating field of the bottom generator is exactly `Y(ω,z)` of `virasoroVOA c`. -/
theorem eVir_fldVir_bot (c : ℂ) (j : ℤ) (u : UR (MVir c)) :
    eVir c (fldVir c ((), 0) j u) = YomegaVir c j (eVir c u) := by
  rw [fldVir, conjDist_apply, LinearEquiv.apply_symm_apply, virYA_gen, genFieldVir_zero]

/-- Every generating field is the corresponding Virasoro vertex operator. -/
theorem eVir_fldVir (c : ℂ) (k : ℕ) (j : ℤ) (u : UR (MVir c)) :
    eVir c (fldVir c ((), k) j u) = (virasoroVOA c).Y (negWordVir c [k]) j (eVir c u) := by
  rw [fldVir, conjDist_apply, LinearEquiv.apply_symm_apply, PhiVir_gv]
  rfl

/-- The `Lₘ` of the presented algebra is the `Lₘ` of `V(c,0)`. -/
theorem eVir_mode_bot (c : ℂ) (m : ℤ) (u : UR (MVir c)) :
    eVir c (mode (fldVir c ((), 0)) (m + 1) u) = Lop c m (eVir c u) := by
  rw [mode, eVir_fldVir_bot, YomegaVir_apply, show -(-(m + 1) - 1) - 2 = m from by ring]

/-- **VOA1 on the presented algebra**: the modes of the strong generator obey the Virasoro
relation at central charge `c` — computed on `T(R)/M`, not on a bespoke realization. -/
theorem fldVir_virasoro (c : ℂ) (m n : ℤ) :
    mode (fldVir c ((), 0)) (m + 1) * mode (fldVir c ((), 0)) (n + 1)
        - mode (fldVir c ((), 0)) (n + 1) * mode (fldVir c ((), 0)) (m + 1)
      = ((m : ℂ) - n) • mode (fldVir c ((), 0)) (m + n + 1)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 * c else 0) •
            (1 : End ℂ (UR (MVir c))) := by
  refine LinearMap.ext (fun u => (eVir c).injective ?_)
  have hbr := congrArg (fun T : End ℂ (VirUniv c) => T (eVir c u)) (Lop_bracket c m n)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply] at hbr
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply, map_sub, map_add, map_smul,
    eVir_mode_bot]
  rw [hbr]

/-- **Deliverable C.**  The algebra presented by *one strong generator of weight two with the
Virasoro singular OPE* is the Borcherds-axiomatised `virasoroVOA c`: there is a linear equivalence
matching the vacuum, the translation operator, and every generating field with the corresponding
vertex operator of `virasoroVOA c`.  `pbw`-free on both sides. -/
theorem virasoro_presentation_equivalence (c : ℂ) :
    ∃ e : UR (MVir c) ≃ₗ[ℂ] VirUniv c,
      e (vacU (MVir c)) = (virasoroVOA c).vacuum
      ∧ (∀ u : UR (MVir c), e (TrU (MVir c) u) = Ltrans c (e u))
      ∧ (∀ (k : ℕ) (j : ℤ) (u : UR (MVir c)),
            e ((genFieldsVir c).fld ((), k) j u)
              = (virasoroVOA c).Y (negWordVir c [k]) j (e u))
      ∧ (∀ (j : ℤ) (u : UR (MVir c)),
            e ((genFieldsVir c).fld ((), 0) j u)
              = (virasoroVOA c).Y (virasoroVOA c).conformalVector j (e u)) :=
  ⟨eVir c, eVir_vac c, eVir_TrU c, eVir_fldVir c, fun j u => by
    have h : (virasoroVOA c).Y (virasoroVOA c).conformalVector = YomegaVir c := virYA_omega c
    rw [h]
    exact eVir_fldVir_bot c j u⟩

/-! ## §7  The vacuity trap, settled for Virasoro -/

/-- `U(R) ≠ 0`. -/
theorem UR_MVir_nontrivial (c : ℂ) : Nontrivial (UR (MVir c)) := by
  refine ⟨⟨vacU (MVir c), 0, fun h => ?_⟩⟩
  have h2 := congrArg (eVir c) h
  rw [eVir_vac, map_zero] at h2
  exact vacVec_ne_zero c h2

/-- **The strong generators stay independent in `U(R)`** — and so do all their sorted
monomials.  This is the statement the file's vacuity warning asks for, and it is `pbw`-free: it
transports `sortedWord_linearIndependent`, which is proved at every central charge from the
linear-dilaton free boson. -/
theorem sortedWordSt_linearIndependent (c : ℂ) :
    LinearIndependent ℂ (fun w : {w : List ℕ // SortedWord w} =>
      wstU (MVir c) (FreeMonoid.ofList (w.1.map (fun k => (((), k) : GenIdx Unit))))) := by
  refine LinearIndependent.of_comp (eVir c).toLinearMap ?_
  have h : ((eVir c).toLinearMap ∘ fun w : {w : List ℕ // SortedWord w} =>
      wstU (MVir c) (FreeMonoid.ofList (w.1.map (fun k => (((), k) : GenIdx Unit)))))
      = fun w : {w : List ℕ // SortedWord w} => negWordVir c w.1 := by
    funext w
    show eVir c (wstU (MVir c) _) = _
    rw [wstU, eVir_mk, PhiVir_wbasis]
    congr 1
    simp
  rw [h]
  exact sortedWord_linearIndependent c

/-- The strong generators themselves are linearly independent in `U(R)`. -/
theorem gv_linearIndependent (c : ℂ) :
    LinearIndependent ℂ
      (fun k : ℕ => (Submodule.Quotient.mk (gv ((), k)) : UR (MVir c))) := by
  have hinj : Function.Injective
      (fun k : ℕ => (⟨[k], sortedWord_singleton k⟩ : {w : List ℕ // SortedWord w})) := by
    intro a b hab
    have := congrArg Subtype.val hab
    simpa using this
  have h := (sortedWordSt_linearIndependent c).comp _ hinj
  convert h using 1

/-! ## §8  Deliverable B, bundled: a `PreVertexAlgebra` structure on `T(R)/M` -/

/-- **An actual `PreVertexAlgebra` instance on the algebra presented by generators and OPEs.**
All ten fields, including the internal `ℤ`-grading and the finite-dimensionality of its
homogeneous pieces, obtained by transporting `virasoroVOA c` along `eVir`. -/
noncomputable def virasoroURVA (c : ℂ) : PreVertexAlgebra (UR (MVir c)) :=
  transportVA (virasoroVOA c).toPreVertexAlgebra (eVir c)

/-- The bundled vertex operator at a strong generator **is** the generating field that
`genFieldsVir` delivers.  So the bundled structure is not an unrelated object: it restricts to the
`GenFields` datum on the generators. -/
theorem virasoroURVA_Y_gv (c : ℂ) (p : GenIdx Unit) :
    (virasoroURVA c).Y (Submodule.Quotient.mk (gv p)) = (genFieldsVir c).fld p := rfl

/-- The bundled vacuum is `vacU`. -/
theorem virasoroURVA_vacuum (c : ℂ) : (virasoroURVA c).vacuum = vacU (MVir c) := by
  rw [virasoroURVA, transportVA_vacuum,
    show (virasoroVOA c).toPreVertexAlgebra.vacuum = eVir c (vacU (MVir c)) from (eVir_vac c).symm,
    LinearEquiv.symm_apply_apply]

/-- The bundled structure sees the strong generator's modes as the Virasoro modes. -/
theorem virasoroURVA_virasoro (c : ℂ) (m n : ℤ) :
    mode ((virasoroURVA c).Y (Submodule.Quotient.mk (gv ((), 0)))) (m + 1)
        * mode ((virasoroURVA c).Y (Submodule.Quotient.mk (gv ((), 0)))) (n + 1)
      - mode ((virasoroURVA c).Y (Submodule.Quotient.mk (gv ((), 0)))) (n + 1)
        * mode ((virasoroURVA c).Y (Submodule.Quotient.mk (gv ((), 0)))) (m + 1)
      = ((m : ℂ) - n) • mode ((virasoroURVA c).Y (Submodule.Quotient.mk (gv ((), 0)))) (m + n + 1)
        + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 * c else 0) •
            (1 : End ℂ (UR (MVir c))) := by
  rw [virasoroURVA_Y_gv]
  exact fldVir_virasoro c m n

end VOA.VirModule





