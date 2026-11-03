/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.BilinearForm
import VOA.Core.SkewSymmetry
import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Quotient vertex operator algebras  `𝒱 / I`

Given a VOA `W` on `𝒱` and an ideal `I ⊆ 𝒱` (Gannon §5.1.3, `Core.BilinearForm.IsIdeal`)
which is moreover **graded**, we build a VOA structure on the quotient module `𝒱 ⧸ I`.
This is the prerequisite for every *simple quotient* construction (`L(c,0)`, minimal
models, simple affine VOAs, …).

## The two subtleties

* **`IsIdeal` is one-sided.**  The repo's

  `IsIdeal W I : ∀ (u v : 𝒱) (n : ℤ), v ∈ I → W.smul u n v ∈ I`

  says only `Y(𝒱,z) I ⊆ I((z))`: `I` absorbs in the **right** slot.  For `Y` to descend
  we also need absorption in the **left** slot, `u ∈ I → u₍ₙ₎v ∈ I` (`AbsorbsLeft`).
  This is *not* part of the definition, but it is a **theorem**
  (`absorbsLeft_of_isIdeal`): skew-symmetry (`Core.SkewSymmetry.skew_mode`)
  `u₍ₙ₎v = ∑ⱼ (1/j!)(-1)^{-n-1-j} Tʲ (v₍-n-1-j₎u)` rewrites the left slot into the right
  slot, and `T = L₋₁ = ω₍₀₎` (`Core.Identities.T_eq_Lneg1`) preserves `I` again by
  one-sided absorption.  So the repo's one-sided `IsIdeal` **is** two-sided; no extra
  hypothesis is needed.

* **The grading only descends for graded ideals.**  A `VertexOperatorAlgebra` carries an
  internal grading (`isInternal`) with finite-dimensional pieces (`finrank`).  The images
  `π(𝒱ₙ)` span `𝒱/I` for any `I`, but they form a *direct* sum only when `I` is
  homogeneous, i.e. `I = ⨆ₙ (I ⊓ 𝒱ₙ)` (`IsGradedIdeal`).

## Main results

* `absorbsLeft_of_isIdeal` — (a) the one-sided `IsIdeal` is automatically two-sided.
* `IsGradedIdeal`, `isInternal_map`, `finiteDimensional_map` — (b) the quotient grading.
* `quotientVOA W I hI hgr : VertexOperatorAlgebra (𝒱 ⧸ I)` — (c) all 19 fields.
* `quotientVOA_centralCharge`, `quotientVOA_mkQ_smul` — (d) the projection as a morphism.
* `maxGradedIdeal`, `vacuum_not_mem_maxGradedIdeal`, `le_maxGradedIdeal` — (e) the maximal
  proper graded ideal, and `isSimple_maxQuotientVOA'` — the quotient by it **is simple**
  (for `W` with `𝟙 ≠ 0`).
* `isGradedIdeal_of_isIdeal` — gradedness is in fact **automatic**: every ideal of a VOA is
  homogeneous (`L₀`-stability plus distinct integer `L₀`-eigenvalues on the graded pieces).
  Hence `quotientVOA'`, the quotient by an arbitrary ideal, with no gradedness hypothesis.

## Which hypothesis is used where

* `hI : W.IsIdeal I` — needed for `Y` to exist at all (right slot), and, through
  `absorbsLeft_of_isIdeal`, for `Y` to be well defined in the left slot.
* `hgr : IsGradedIdeal W I` — needed **only** for `isInternal`.  Every other field
  (including `finrank`, `vacuum_grade`, `positivity`) holds for an arbitrary ideal.
  It is moreover automatic (§7, `isGradedIdeal_of_isIdeal`), so it costs nothing.
* **Properness `W.vacuum ∉ I` is needed by none of the 19 fields.**  If `I = ⊤` the
  quotient is the zero space, which satisfies every VOA axiom (`𝒱₀ = ⊥ = ℂ∙0`).
  Properness is what keeps the quotient *nonzero* downstream, and it is exactly what
  enters part (e).

## Status
Complete & `sorry`-free / axiom-free.  Verified `#print axioms = [propext,
Classical.choice, Quot.sound]` for `absorbsLeft_of_isIdeal`, `isInternal_map`,
`quotientVOA`, `quotientVOA_centralCharge`, `quotientVOA_mkQ_smul`,
`isGradedIdeal_of_isIdeal`, `quotientVOA'`, `maxGradedIdeal`,
`vacuum_not_mem_maxGradedIdeal`, `maxQuotientVOA`, `isSimple_maxQuotientVOA'`.
The theorem `VOA.pbw` is **not** used.

## References
* Gannon §5.1.3 (ideals, simplicity, Def. 5.3.2); Frenkel–Huang–Lepowsky; Lepowsky–Li §4.5.
-/

namespace VOA

open Module (End)

universe u

namespace QuotVOA

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §0.  Small general helpers -/

/-- A `finsum` of elements of a submodule lies in the submodule. -/
theorem finsum_mem_submodule {ι : Type*} (p : Submodule ℂ 𝒱) (F : ι → 𝒱)
    (h : ∀ i, F i ∈ p) : (∑ᶠ i, F i) ∈ p := by
  by_cases hfin : (Function.support F).Finite
  · rw [finsum_eq_sum F hfin]
    exact Submodule.sum_mem _ fun i _ => h i
  · rw [finsum_of_infinite_support hfin]
    exact p.zero_mem

/-- Peeling one factor of `(z₁-z₂)` off `(z₁-z₂)^{N+1}`, in coefficient form. -/
theorem mulBySubPow_succ_apply {𝒲 : Type*} [AddCommGroup 𝒲] [Module ℂ 𝒲] (k : ℕ)
    (H : FormalDist₂ 𝒲) (m n : ℤ) :
    mulBySubPow (k + 1) H m n = mulBySubPow k H (m - 1) n - mulBySubPow k H m (n - 1) := by
  rw [mulBySubPow_succ, LinearMap.comp_apply, mulBySub_apply]

/-! ## §1.  An ideal absorbs on **both** sides  (task (a)) -/

/-- Absorption in the **left** slot: `u ∈ I → u₍ₙ₎v ∈ I`.  Together with the repo's
`IsIdeal` (right slot) this is what makes `Y` descend to `𝒱 ⧸ I`. -/
def AbsorbsLeft (W : VertexOperatorAlgebra 𝒱) (I : Submodule ℂ 𝒱) : Prop :=
  ∀ (u v : 𝒱) (n : ℤ), u ∈ I → W.smul u n v ∈ I

variable {W : VertexOperatorAlgebra 𝒱} {I : Submodule ℂ 𝒱}

/-- An ideal is stable under the translation operator `T = L₋₁ = ω₍₀₎`. -/
theorem T_mem_of_isIdeal (hI : W.IsIdeal I) {x : 𝒱} (hx : x ∈ I) :
    W.toPreVertexAlgebra.T x ∈ I := by
  have h : W.toPreVertexAlgebra.T x = W.smul W.conformalVector 0 x := by
    rw [VertexOperatorAlgebra.T_eq_Lneg1, VertexOperatorAlgebra.L_def,
      PreVertexAlgebra.smul_def, show (-1 : ℤ) + 1 = 0 from by ring]
  rw [h]
  exact hI _ _ _ hx

/-- An ideal is stable under every power `Tʲ`. -/
theorem T_pow_mem_of_isIdeal (hI : W.IsIdeal I) :
    ∀ (j : ℕ) {x : 𝒱}, x ∈ I → ((W.toPreVertexAlgebra.T) ^ j) x ∈ I := by
  intro j
  induction j with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
    intro x hx
    have h : ((W.toPreVertexAlgebra.T) ^ (k + 1)) x
        = ((W.toPreVertexAlgebra.T) ^ k) (W.toPreVertexAlgebra.T x) := by
      rw [pow_succ, Module.End.mul_apply]
    rw [h]
    exact ih (T_mem_of_isIdeal hI hx)

/-- **(a)  The one-sided `IsIdeal` is automatically two-sided.**  Skew-symmetry
`u₍ₙ₎v = ∑ⱼ (1/j!)(-1)^{-n-1-j} Tʲ(v₍-n-1-j₎u)` (`Core.SkewSymmetry.skew_mode`) turns the
left slot into the right slot, and `T` preserves `I` (`T_mem_of_isIdeal`). -/
theorem absorbsLeft_of_isIdeal (hI : W.IsIdeal I) : AbsorbsLeft W I := by
  intro u v n hu
  rw [VertexOperatorAlgebra.skew_mode W u v n]
  refine finsum_mem_submodule I _ fun j => ?_
  refine I.smul_mem _ (I.smul_mem _ (T_pow_mem_of_isIdeal hI j ?_))
  have h : (W.Y v) (-n - 1 - (j : ℤ)) u = W.smul v (n + (j : ℤ)) u := by
    rw [PreVertexAlgebra.smul_def, mode_apply,
      show -(n + (j : ℤ)) - 1 = -n - 1 - (j : ℤ) from by ring]
  rw [h]
  exact hI v u (n + (j : ℤ)) hu

/-! ## §2.  Graded ideals and the quotient grading  (task (b)) -/

/-- `I` is a **graded** (homogeneous) submodule for `W`'s conformal grading: it is the
supremum of its homogeneous pieces, `I = ⨆ₙ (I ⊓ 𝒱ₙ)`. -/
def IsGradedIdeal (W : VertexOperatorAlgebra 𝒱) (I : Submodule ℂ 𝒱) : Prop :=
  I = ⨆ n : ℤ, I ⊓ W.grading n

theorem isGradedIdeal_iff (W : VertexOperatorAlgebra 𝒱) (I : Submodule ℂ 𝒱) :
    IsGradedIdeal W I ↔ I ≤ ⨆ n : ℤ, I ⊓ W.grading n :=
  ⟨fun h => h.le, fun h => le_antisymm h (iSup_le fun _ => inf_le_left)⟩

/-- **Independence descends to the quotient by a graded submodule.**  If the `A i` are
independent and `J` is the sup of its pieces `J ⊓ A i`, then the images `π(A i)` in `M ⧸ J`
are again independent. -/
theorem iSupIndep_map_mkQ {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*}
    (A : ι → Submodule ℂ M) (hA : iSupIndep A) (J : Submodule ℂ M)
    (hJ : J ≤ ⨆ i, J ⊓ A i) : iSupIndep fun i => (A i).map J.mkQ := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
  have hmapsup : (⨆ (j) (_ : j ≠ i), (A j).map J.mkQ)
      = (⨆ (j) (_ : j ≠ i), A j).map J.mkQ := by
    simp only [Submodule.map_iSup]
  rw [hmapsup] at hx'
  obtain ⟨b, hb, hab⟩ := Submodule.mem_map.mp hx'
  have h0 : J.mkQ (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hsub : a - b ∈ J := by
    rw [← Submodule.ker_mkQ J]
    exact h0
  have hmem := hJ hsub
  rw [iSup_split_single (fun k => J ⊓ A k) i] at hmem
  obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp hmem
  have habc : a = b + (c + d) := by rw [hcd]; abel
  have hkey : a - c = b + d := by rw [habc]; abel
  have hAi : a - c ∈ A i := Submodule.sub_mem _ ha hc.2
  have hrest : a - c ∈ ⨆ (j) (_ : j ≠ i), A j := by
    rw [hkey]
    refine Submodule.add_mem _ hb ?_
    exact (iSup₂_mono fun (k : ι) (_ : k ≠ i) => (inf_le_right : J ⊓ A k ≤ A k)) hd
  have hz : a - c = 0 :=
    Submodule.disjoint_def.mp (iSupIndep_def.mp hA i) _ hAi hrest
  have haJ : a ∈ J := by
    rw [sub_eq_zero] at hz
    rw [hz]
    exact hc.1
  rw [← Submodule.ker_mkQ J] at haJ
  exact haJ

/-- **The quotient grading is internal** when `I` is a graded ideal. -/
theorem isInternal_map (W : VertexOperatorAlgebra 𝒱) (I : Submodule ℂ 𝒱)
    (hgr : IsGradedIdeal W I) :
    DirectSum.IsInternal fun n : ℤ => (W.grading n).map I.mkQ := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · exact iSupIndep_map_mkQ W.grading W.isInternal.submodule_iSupIndep I hgr.le
  · rw [← Submodule.map_iSup, W.isInternal.submodule_iSup_eq_top, Submodule.map_top,
      Submodule.range_mkQ]

/-- **The quotient graded pieces stay finite-dimensional** (no gradedness needed). -/
theorem finiteDimensional_map (W : VertexOperatorAlgebra 𝒱) (I : Submodule ℂ 𝒱) (n : ℤ) :
    FiniteDimensional ℂ ((W.grading n).map I.mkQ) := by
  haveI := W.finrank n
  have h : (W.grading n).map I.mkQ = LinearMap.range (I.mkQ ∘ₗ (W.grading n).subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [h]
  infer_instance

/-! ## §3.  Descending `Y` -/

/-- The `m`-th coefficient of `Y(u,z)` is the mode `u₍₋ₘ₋₁₎`. -/
theorem coeff_eq_smul (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (m : ℤ) (x : 𝒱) :
    (W.Y u) m x = W.smul u (-m - 1) x := by
  rw [PreVertexAlgebra.smul_def, mode_apply, show -(-m - 1) - 1 = m from by ring]

/-- Every coefficient of `Y(u,z)` preserves the ideal (right-slot absorption). -/
theorem Y_stable (hI : W.IsIdeal I) (u : 𝒱) (m : ℤ) : I ≤ I.comap ((W.Y u) m) := by
  intro x hx
  rw [Submodule.mem_comap, coeff_eq_smul]
  exact hI u x (-m - 1) hx

/-- The coefficientwise descent of `Y(u,z)` to `End (𝒱 ⧸ I)`. -/
def Ycoeff (hI : W.IsIdeal I) (u : 𝒱) (m : ℤ) : End ℂ (𝒱 ⧸ I) :=
  I.mapQ I ((W.Y u) m) (Y_stable hI u m)

@[simp] theorem Ycoeff_mkQ (hI : W.IsIdeal I) (u : 𝒱) (m : ℤ) (x : 𝒱) :
    Ycoeff hI u m (I.mkQ x) = I.mkQ ((W.Y u) m x) := rfl

/-- `A : End (𝒱 ⧸ I)` is **induced by** `a : End 𝒱`. -/
def Compat {I : Submodule ℂ 𝒱} (a : End ℂ 𝒱) (A : End ℂ (𝒱 ⧸ I)) : Prop :=
  ∀ x : 𝒱, A (I.mkQ x) = I.mkQ (a x)

namespace Compat

variable {a b : End ℂ 𝒱} {A B : End ℂ (𝒱 ⧸ I)}

theorem unique (hA : Compat a A) (hB : Compat a B) : A = B := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := I.mkQ_surjective y
  rw [hA x, hB x]

theorem add (ha : Compat a A) (hb : Compat b B) : Compat (a + b) (A + B) := by
  intro x
  rw [LinearMap.add_apply, ha x, hb x, LinearMap.add_apply, map_add]

theorem sub (ha : Compat a A) (hb : Compat b B) : Compat (a - b) (A - B) := by
  intro x
  rw [LinearMap.sub_apply, ha x, hb x, LinearMap.sub_apply, map_sub]

theorem mul (ha : Compat a A) (hb : Compat b B) : Compat (a * b) (A * B) := by
  intro x
  rw [Module.End.mul_apply, hb x, ha (b x), Module.End.mul_apply]

theorem smul (ha : Compat a A) (c : ℂ) : Compat (c • a) (c • A) := by
  intro x
  rw [LinearMap.smul_apply, ha x, LinearMap.smul_apply, map_smul]

theorem zsmul (ha : Compat a A) (k : ℤ) : Compat (k • a) (k • A) := by
  have h1 : (k • a) = ((k : ℂ) • a) := (Int.cast_smul_eq_zsmul ℂ k a).symm
  have h2 : (k • A) = ((k : ℂ) • A) := (Int.cast_smul_eq_zsmul ℂ k A).symm
  rw [h1, h2]
  exact ha.smul _

theorem one : Compat (1 : End ℂ 𝒱) (1 : End ℂ (𝒱 ⧸ I)) := fun _ => rfl

theorem zero : Compat (0 : End ℂ 𝒱) (0 : End ℂ (𝒱 ⧸ I)) := by
  intro x
  rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

theorem lie (ha : Compat a A) (hb : Compat b B) : Compat ⁅a, b⁆ ⁅A, B⁆ := by
  simp only [Ring.lie_def]
  exact (ha.mul hb).sub (hb.mul ha)

end Compat

theorem compat_Ycoeff (hI : W.IsIdeal I) (u : 𝒱) (m : ℤ) :
    Compat ((W.Y u) m) (Ycoeff hI u m) := fun x => Ycoeff_mkQ hI u m x

/-- The descended state–field correspondence, before quotienting the *source*. -/
def Ydist (hI : W.IsIdeal I) (u : 𝒱) : (End ℂ (𝒱 ⧸ I))⟦z^±⟧ := fun m => Ycoeff hI u m

theorem Ydist_add (hI : W.IsIdeal I) (u v : 𝒱) :
    Ydist hI (u + v) = Ydist hI u + Ydist hI v := by
  refine FormalDist.ext fun m => ?_
  refine Compat.unique (a := (W.Y u) m + (W.Y v) m) ?_ ?_
  · have h2 : (W.Y (u + v)) m = (W.Y u) m + (W.Y v) m := by rw [map_add]; rfl
    rw [← h2]
    exact compat_Ycoeff hI (u + v) m
  · exact (compat_Ycoeff hI u m).add (compat_Ycoeff hI v m)

theorem Ydist_smul (hI : W.IsIdeal I) (c : ℂ) (u : 𝒱) :
    Ydist hI (c • u) = c • Ydist hI u := by
  refine FormalDist.ext fun m => ?_
  refine Compat.unique (a := c • (W.Y u) m) ?_ ?_
  · have h2 : (W.Y (c • u)) m = c • (W.Y u) m := by rw [map_smul]; rfl
    rw [← h2]
    exact compat_Ycoeff hI (c • u) m
  · exact (compat_Ycoeff hI u m).smul c

/-- `u ↦ Y(u,z)` on the quotient, as a linear map out of `𝒱`. -/
def Ylin (hI : W.IsIdeal I) : 𝒱 →ₗ[ℂ] (End ℂ (𝒱 ⧸ I))⟦z^±⟧ where
  toFun := Ydist hI
  map_add' := Ydist_add hI
  map_smul' := Ydist_smul hI

theorem Ylin_ker (hI : W.IsIdeal I) : I ≤ LinearMap.ker (Ylin hI) := by
  intro u hu
  rw [LinearMap.mem_ker]
  refine FormalDist.ext fun m => ?_
  have hz : (0 : (End ℂ (𝒱 ⧸ I))⟦z^±⟧) m = (0 : End ℂ (𝒱 ⧸ I)) := rfl
  have hl : (Ylin hI) u m = Ycoeff hI u m := rfl
  rw [hl, hz]
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := I.mkQ_surjective y
  rw [Ycoeff_mkQ, LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    coeff_eq_smul]
  exact absorbsLeft_of_isIdeal hI u x (-m - 1) hu

/-- **The descended state–field correspondence** `Y : (𝒱 ⧸ I) →ₗ (End (𝒱 ⧸ I))⟦z^±⟧`.
Well defined in the right slot by `hI`, in the left slot by `absorbsLeft_of_isIdeal hI`. -/
def Yq (hI : W.IsIdeal I) : (𝒱 ⧸ I) →ₗ[ℂ] (End ℂ (𝒱 ⧸ I))⟦z^±⟧ :=
  I.liftQ (Ylin hI) (Ylin_ker hI)

theorem Yq_mkQ (hI : W.IsIdeal I) (u : 𝒱) : Yq hI (I.mkQ u) = Ydist hI u :=
  I.liftQ_apply _ u

theorem compat_Yq (hI : W.IsIdeal I) (u : 𝒱) (m : ℤ) :
    Compat ((W.Y u) m) (Yq hI (I.mkQ u) m) := by
  rw [Yq_mkQ]
  exact compat_Ycoeff hI u m

/-- **`Y` descends**: `[u]₍ₙ₎[v] = [u₍ₙ₎v]`. -/
theorem mode_Yq_mkQ (hI : W.IsIdeal I) (u : 𝒱) (n : ℤ) (x : 𝒱) :
    mode (Yq hI (I.mkQ u)) n (I.mkQ x) = I.mkQ (W.smul u n x) := by
  rw [mode_apply, Yq_mkQ]
  exact Ycoeff_mkQ hI u (-n - 1) x

theorem compat_mode (hI : W.IsIdeal I) (u : 𝒱) (n : ℤ) :
    Compat (mode (W.Y u) n) (mode (Yq hI (I.mkQ u)) n) := fun x => mode_Yq_mkQ hI u n x

/-- Transport of `(z₁-z₂)ᴺ` along the projection, used for locality. -/
theorem mulBySubPow_transport (I : Submodule ℂ 𝒱) (F : FormalDist₂ (End ℂ 𝒱))
    (G : FormalDist₂ (End ℂ (𝒱 ⧸ I)))
    (h : ∀ m n x, G m n (I.mkQ x) = I.mkQ (F m n x)) (N : ℕ) :
    ∀ m n x, mulBySubPow N G m n (I.mkQ x) = I.mkQ (mulBySubPow N F m n x) := by
  induction N with
  | zero => intro m n x; exact h m n x
  | succ k ih =>
    intro m n x
    rw [mulBySubPow_succ_apply, LinearMap.sub_apply, ih (m - 1) n x, ih m (n - 1) x,
      ← map_sub, ← LinearMap.sub_apply, ← mulBySubPow_succ_apply]

/-! ## §4.  The quotient VOA  (task (c)) -/

/-- **The quotient vertex operator algebra `𝒱 / I`.**

`hI` (right-slot absorption, plus its automatic left-slot consequence) is what makes `Y`
well defined; `hgr` is needed for — and only for — `isInternal`.  No field needs
properness `W.vacuum ∉ I`: for `I = ⊤` this is the zero VOA. -/
def quotientVOA (W : VertexOperatorAlgebra 𝒱) (I : Submodule ℂ 𝒱)
    (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) : VertexOperatorAlgebra (𝒱 ⧸ I) where
  grading n := (W.grading n).map I.mkQ
  isInternal := isInternal_map W I hgr
  finrank n := finiteDimensional_map W I n
  Y := Yq hI
  vacuum := I.mkQ W.vacuum
  vacuum_mem := Submodule.mem_map_of_mem W.vacuum_mem
  grading_mode := by
    intro k l ubar hu vbar hv n
    obtain ⟨u, hu', rfl⟩ := Submodule.mem_map.mp hu
    obtain ⟨v, hv', rfl⟩ := Submodule.mem_map.mp hv
    rw [mode_Yq_mkQ]
    exact Submodule.mem_map_of_mem (W.smul_mem_grading hu' hv' n)
  vacuum_Y := by
    refine FormalDist.ext fun m => ?_
    refine Compat.unique (compat_Yq hI W.vacuum m) ?_
    rw [W.vacuum_Y, FormalDist.one_apply, FormalDist.one_apply]
    by_cases h : m = 0
    · rw [if_pos h, if_pos h]; exact Compat.one
    · rw [if_neg h, if_neg h]; exact Compat.zero
  creation := by
    intro ubar
    obtain ⟨u, rfl⟩ := I.mkQ_surjective ubar
    refine ⟨?_, ?_⟩
    · rw [mode_Yq_mkQ, PreVertexAlgebra.smul_vacuum_neg_one]
    · intro n hn
      rw [mode_Yq_mkQ, PreVertexAlgebra.smul_vacuum_nonneg _ _ hn, map_zero]
  locality := by
    intro ubar vbar
    obtain ⟨u, rfl⟩ := I.mkQ_surjective ubar
    obtain ⟨v, rfl⟩ := I.mkQ_surjective vbar
    obtain ⟨N, hN⟩ := W.locality u v
    refine ⟨N, ?_⟩
    have hb : ∀ m n x, bracketDist (Yq hI (I.mkQ u)) (Yq hI (I.mkQ v)) m n (I.mkQ x)
        = I.mkQ (bracketDist (W.Y u) (W.Y v) m n x) := by
      intro m n x
      exact (((compat_Yq hI u m).mul (compat_Yq hI v n)).sub
        ((compat_Yq hI v n).mul (compat_Yq hI u m))) x
    refine FormalDist₂.ext fun m n => ?_
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := I.mkQ_surjective y
    rw [mulBySubPow_transport I _ _ hb N m n x, hN]
    change I.mkQ ((0 : End ℂ 𝒱) x) = (0 : End ℂ (𝒱 ⧸ I)) _
    rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
  regularity := by
    intro ubar vbar
    obtain ⟨u, rfl⟩ := I.mkQ_surjective ubar
    obtain ⟨v, rfl⟩ := I.mkQ_surjective vbar
    obtain ⟨N, hN⟩ := W.regularity u v
    refine ⟨N, fun n hn => ?_⟩
    have hz : W.smul u n v = 0 := hN n hn
    rw [mode_Yq_mkQ, hz, map_zero]
  conformalVector := I.mkQ W.conformalVector
  conformal_mem := Submodule.mem_map_of_mem W.conformal_mem
  centralCharge := W.centralCharge
  virasoro := by
    intro m n
    refine Compat.unique
      (a := ⁅mode (W.Y W.conformalVector) (m + 1),
             mode (W.Y W.conformalVector) (n + 1)⁆) ?_ ?_
    · exact (compat_mode hI W.conformalVector (m + 1)).lie
        (compat_mode hI W.conformalVector (n + 1))
    · rw [W.virasoro m n]
      refine Compat.add ((compat_mode hI W.conformalVector (m + n + 1)).smul _) ?_
      by_cases h : m + n = 0
      · rw [if_pos h, if_pos h]; exact Compat.one.smul _
      · rw [if_neg h, if_neg h]; exact Compat.zero
  L0_grading := by
    intro n vbar hv
    obtain ⟨v, hv', rfl⟩ := Submodule.mem_map.mp hv
    have h1 : W.smul W.conformalVector 1 v = (n : ℂ) • v := W.L0_grading v hv'
    rw [mode_Yq_mkQ, h1, map_smul]
  translation := by
    intro vbar
    obtain ⟨v, rfl⟩ := I.mkQ_surjective vbar
    have h0 : mode (Yq hI (I.mkQ W.conformalVector)) 0 (I.mkQ v)
        = I.mkQ (mode (W.Y W.conformalVector) 0 v) := mode_Yq_mkQ hI _ _ _
    rw [h0]
    refine FormalDist.ext fun m => ?_
    refine Compat.unique (a := (m + 1 : ℤ) • (W.Y v) (m + 1)) ?_ ?_
    · have h1 := compat_Yq hI (mode (W.Y W.conformalVector) 0 v) m
      rw [W.translation v, deriv_apply] at h1
      exact h1
    · exact (compat_Yq hI v (m + 1)).zsmul (m + 1)
  vacuum_grade := by
    change (W.grading 0).map I.mkQ = ℂ ∙ (I.mkQ W.vacuum)
    rw [W.vacuum_grade, Submodule.map_span, Set.image_singleton]
  positivity := by
    intro n hn
    change (W.grading n).map I.mkQ = ⊥
    rw [W.positivity n hn, Submodule.map_bot]

/-! ## §5.  The projection is a morphism  (task (d)) -/

@[simp] theorem quotientVOA_grading (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) (n : ℤ) :
    (quotientVOA W I hI hgr).grading n = (W.grading n).map I.mkQ := rfl

@[simp] theorem quotientVOA_vacuum (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) :
    (quotientVOA W I hI hgr).vacuum = I.mkQ W.vacuum := rfl

@[simp] theorem quotientVOA_conformalVector (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) :
    (quotientVOA W I hI hgr).conformalVector = I.mkQ W.conformalVector := rfl

/-- **The central charge is unchanged by the quotient.** -/
@[simp] theorem quotientVOA_centralCharge (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) :
    (quotientVOA W I hI hgr).centralCharge = W.centralCharge := rfl

/-- **The projection intertwines all the products**: `[u₍ₙ₎v] = [u]₍ₙ₎[v]`. -/
theorem quotientVOA_mkQ_smul (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I)
    (u : 𝒱) (n : ℤ) (v : 𝒱) :
    (quotientVOA W I hI hgr).smul (I.mkQ u) n (I.mkQ v) = I.mkQ (W.smul u n v) :=
  mode_Yq_mkQ hI u n v

/-- The projection maps homogeneous vectors to homogeneous vectors. -/
theorem quotientVOA_mkQ_grading (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I) {n : ℤ} {x : 𝒱}
    (hx : x ∈ W.grading n) : I.mkQ x ∈ (quotientVOA W I hI hgr).grading n :=
  Submodule.mem_map_of_mem hx

/-- The projection is surjective. -/
theorem quotientVOA_mkQ_surjective (I : Submodule ℂ 𝒱) : Function.Surjective I.mkQ :=
  I.mkQ_surjective

/-! ## §6.  The maximal proper graded ideal  (task (e)) -/

/-- The set of **proper graded ideals** of `W`. -/
def ProperGradedIdeals (W : VertexOperatorAlgebra 𝒱) : Set (Submodule ℂ 𝒱) :=
  {I | W.IsIdeal I ∧ IsGradedIdeal W I ∧ W.vacuum ∉ I}

/-- A supremum of ideals is an ideal. -/
theorem isIdeal_sSup (W : VertexOperatorAlgebra 𝒱) (S : Set (Submodule ℂ 𝒱))
    (h : ∀ J ∈ S, W.IsIdeal J) : W.IsIdeal (sSup S) := by
  intro u v n hv
  have hle : sSup S ≤ (sSup S).comap ((W.Y u) (-n - 1)) := by
    refine sSup_le fun J hJ x hx => ?_
    rw [Submodule.mem_comap, coeff_eq_smul, show -(-n - 1) - 1 = n from by ring]
    exact le_sSup hJ (h J hJ u x n hx)
  exact hle hv

/-- A supremum of graded ideals is graded. -/
theorem isGradedIdeal_sSup (W : VertexOperatorAlgebra 𝒱) (S : Set (Submodule ℂ 𝒱))
    (h : ∀ J ∈ S, IsGradedIdeal W J) : IsGradedIdeal W (sSup S) := by
  rw [isGradedIdeal_iff]
  refine sSup_le fun J hJ => ?_
  calc J = ⨆ n : ℤ, J ⊓ W.grading n := h J hJ
    _ ≤ ⨆ n : ℤ, sSup S ⊓ W.grading n :=
        iSup_mono fun n => inf_le_inf_right (W.grading n) (le_sSup hJ)

/-- An ideal containing the vacuum is everything (from right-slot absorption and
`u₍₋₁₎𝟙 = u`). -/
theorem eq_top_of_vacuum_mem (hI : W.IsIdeal I) (h : W.vacuum ∈ I) : I = ⊤ := by
  refine eq_top_iff.mpr fun u _ => ?_
  have hu := hI u W.vacuum (-1) h
  rwa [PreVertexAlgebra.smul_vacuum_neg_one] at hu

/-- A proper ideal meets `𝒱₀ = ℂ𝟙` trivially. -/
theorem inf_grading_zero_eq_bot (hv : W.vacuum ∉ I) :
    I ⊓ W.grading 0 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxI : x ∈ I := hx.1
  have hx0 : x ∈ W.grading 0 := hx.2
  rw [W.vacuum_grade, Submodule.mem_span_singleton] at hx0
  obtain ⟨c, rfl⟩ := hx0
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact absurd (by
      have hv' : W.vacuum = c⁻¹ • (c • W.vacuum) := by
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hv']
      exact I.smul_mem _ hxI) hv

/-- A proper **graded** ideal avoids degree `0` entirely. -/
theorem le_iSup_ne_zero (hgr : IsGradedIdeal W I) (hv : W.vacuum ∉ I) :
    I ≤ ⨆ (n : ℤ) (_ : n ≠ 0), W.grading n := by
  rw [hgr]
  refine iSup_le fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · rw [inf_grading_zero_eq_bot hv]; exact bot_le
  · exact le_trans inf_le_right
      (le_iSup₂ (f := fun (k : ℤ) (_ : k ≠ 0) => W.grading k) n hn)

/-- **The maximal proper graded ideal** of `W`. -/
def maxGradedIdeal (W : VertexOperatorAlgebra 𝒱) : Submodule ℂ 𝒱 :=
  sSup (ProperGradedIdeals W)

theorem maxGradedIdeal_isIdeal (W : VertexOperatorAlgebra 𝒱) :
    W.IsIdeal (maxGradedIdeal W) :=
  isIdeal_sSup W _ fun _ hJ => hJ.1

theorem maxGradedIdeal_isGradedIdeal (W : VertexOperatorAlgebra 𝒱) :
    IsGradedIdeal W (maxGradedIdeal W) :=
  isGradedIdeal_sSup W _ fun _ hJ => hJ.2.1

/-- **The maximal graded ideal is proper** (for a nonzero VOA).  This is where
gradedness bites: a proper graded ideal lives in `⨆_{n≠0} 𝒱ₙ`, which is disjoint from
`𝒱₀ ∋ 𝟙`. -/
theorem vacuum_not_mem_maxGradedIdeal (W : VertexOperatorAlgebra 𝒱) (hvac : W.vacuum ≠ 0) :
    W.vacuum ∉ maxGradedIdeal W := by
  intro hmem
  have hle : maxGradedIdeal W ≤ ⨆ (n : ℤ) (_ : n ≠ 0), W.grading n :=
    sSup_le fun J hJ => le_iSup_ne_zero hJ.2.1 hJ.2.2
  have hd : Disjoint (W.grading 0) (⨆ (n : ℤ) (_ : n ≠ 0), W.grading n) :=
    iSupIndep_def.mp W.isInternal.submodule_iSupIndep 0
  exact hvac (Submodule.disjoint_def.mp hd _ W.vacuum_mem (hle hmem))

theorem maxGradedIdeal_mem (W : VertexOperatorAlgebra 𝒱) (hvac : W.vacuum ≠ 0) :
    maxGradedIdeal W ∈ ProperGradedIdeals W :=
  ⟨maxGradedIdeal_isIdeal W, maxGradedIdeal_isGradedIdeal W,
    vacuum_not_mem_maxGradedIdeal W hvac⟩

/-- Maximality: every proper graded ideal is contained in `maxGradedIdeal`. -/
theorem le_maxGradedIdeal {J : Submodule ℂ 𝒱} (hJ : J ∈ ProperGradedIdeals W) :
    J ≤ maxGradedIdeal W := le_sSup hJ

/-- The quotient of `W` by its maximal proper graded ideal. -/
def maxQuotientVOA (W : VertexOperatorAlgebra 𝒱) :
    VertexOperatorAlgebra (𝒱 ⧸ maxGradedIdeal W) :=
  quotientVOA W (maxGradedIdeal W) (maxGradedIdeal_isIdeal W) (maxGradedIdeal_isGradedIdeal W)

/-- The maximal quotient is nonzero: the first clause of `IsSimple`. -/
theorem maxQuotient_top_ne_bot (W : VertexOperatorAlgebra 𝒱) (hvac : W.vacuum ≠ 0) :
    (⊤ : Submodule ℂ (𝒱 ⧸ maxGradedIdeal W)) ≠ ⊥ := by
  intro h
  refine vacuum_not_mem_maxGradedIdeal W hvac ?_
  have hmem : ((maxGradedIdeal W).mkQ W.vacuum) ∈ (⊤ : Submodule ℂ (𝒱 ⧸ maxGradedIdeal W)) :=
    Submodule.mem_top
  rw [h, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
  exact hmem

/-- The pullback of an ideal of the quotient is an ideal of `W`. -/
theorem isIdeal_comap (hI : W.IsIdeal I) (hgr : IsGradedIdeal W I)
    {J : Submodule ℂ (𝒱 ⧸ I)} (hJ : (quotientVOA W I hI hgr).IsIdeal J) :
    W.IsIdeal (J.comap I.mkQ) := by
  intro u v n hv
  rw [Submodule.mem_comap] at hv ⊢
  have h : (quotientVOA W I hI hgr).smul (I.mkQ u) n (I.mkQ v) ∈ J :=
    hJ (I.mkQ u) (I.mkQ v) n hv
  rw [quotientVOA_mkQ_smul] at h
  exact h

/-- **Conditional simplicity of the maximal quotient.**  If every ideal of the quotient
pulls back to a *graded* ideal of `W` — which is the standard `L₀`-diagonalisability fact
(every ideal of a VOA of CFT type is homogeneous), **not proved in this repo** — then the
quotient by the maximal proper graded ideal is simple. -/
theorem isSimple_maxQuotientVOA (W : VertexOperatorAlgebra 𝒱) (hvac : W.vacuum ≠ 0)
    (hgraded : ∀ J : Submodule ℂ (𝒱 ⧸ maxGradedIdeal W), (maxQuotientVOA W).IsIdeal J →
      IsGradedIdeal W (J.comap (maxGradedIdeal W).mkQ)) :
    (maxQuotientVOA W).IsSimple := by
  set M := maxGradedIdeal W with hM
  refine ⟨maxQuotient_top_ne_bot W hvac, fun J hJ => ?_⟩
  have hcomapIdeal : W.IsIdeal (J.comap M.mkQ) :=
    isIdeal_comap (maxGradedIdeal_isIdeal W) (maxGradedIdeal_isGradedIdeal W) hJ
  have hmapcomap : (J.comap M.mkQ).map M.mkQ = J :=
    Submodule.map_comap_eq_self (by rw [Submodule.range_mkQ]; exact le_top)
  by_cases hv : W.vacuum ∈ J.comap M.mkQ
  · right
    have htop : J.comap M.mkQ = ⊤ := eq_top_of_vacuum_mem hcomapIdeal hv
    rw [← hmapcomap, htop, Submodule.map_top, Submodule.range_mkQ]
  · left
    have hmem : J.comap M.mkQ ∈ ProperGradedIdeals W := ⟨hcomapIdeal, hgraded J hJ, hv⟩
    have hle : J.comap M.mkQ ≤ M := le_maxGradedIdeal hmem
    have hbot : (J.comap M.mkQ).map M.mkQ = ⊥ := by
      rw [eq_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ]
      exact hle
    rw [← hmapcomap, hbot]

/-! ## §7.  Gradedness is automatic:  every ideal of a VOA is homogeneous

An ideal is stable under `L₀ = ω₍₁₎`, and `L₀` acts on `𝒱ₙ` as the scalar `n`.  Distinct
homogeneous pieces therefore have distinct `L₀`-eigenvalues, and an induction that applies
`L₀ - k` to kill the weight-`k` component shows that every homogeneous component of a
member of an ideal is again in the ideal.  Consequently `IsGradedIdeal` is *not* an extra
hypothesis: it is a theorem (`isGradedIdeal_of_isIdeal`), and the quotient construction
applies to **every** ideal (`quotientVOA'`).
-/

/-- `L₀ = ω₍₁₎` preserves any ideal. -/
theorem L0_mem_of_isIdeal (hI : W.IsIdeal I) {x : 𝒱} (hx : x ∈ I) : W.L 0 x ∈ I := by
  have h : W.L 0 x = W.smul W.conformalVector 1 x := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def,
      show (0 : ℤ) + 1 = 1 from by ring]
  rw [h]
  exact hI _ _ _ hx

/-- **Homogeneous components of a member of an ideal stay in the ideal.**  Induction on the
finite weight support: `L₀ - k` annihilates the weight-`k` term and rescales the weight-`j`
term by `j - k ≠ 0`, so the shorter sum is again in `I`; the weight-`k` term is then the
difference of two members of `I`. -/
theorem homogeneous_mem_of_sum_mem (hI : W.IsIdeal I) (s : Finset ℤ) :
    ∀ f : ℤ → 𝒱, (∀ k ∈ s, f k ∈ W.grading k) → (∑ k ∈ s, f k) ∈ I → ∀ k ∈ s, f k ∈ I := by
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro f hf hsum k hk
    have hL0 : ∀ j ∈ s, W.L 0 (f j) = (j : ℂ) • f j := fun j hj =>
      W.L_zero_grading _ (hf j hj)
    have hgI : ∀ j ∈ s.erase k, ((j : ℂ) - (k : ℂ)) • f j ∈ I := by
      refine ih (s.erase k) (Finset.erase_ssubset hk)
        (fun j => ((j : ℂ) - (k : ℂ)) • f j) ?_ ?_
      · intro j hj
        exact Submodule.smul_mem _ _ (hf j (Finset.mem_of_mem_erase hj))
      · have hgk : ((k : ℂ) - (k : ℂ)) • f k = 0 := by rw [sub_self, zero_smul]
        have e1 : (∑ j ∈ s.erase k, ((j : ℂ) - (k : ℂ)) • f j)
            = ∑ j ∈ s, ((j : ℂ) - (k : ℂ)) • f j := by
          rw [← Finset.add_sum_erase s (fun j => ((j : ℂ) - (k : ℂ)) • f j) hk, hgk, zero_add]
        have e2 : (∑ j ∈ s, ((j : ℂ) - (k : ℂ)) • f j)
            = W.L 0 (∑ j ∈ s, f j) - (k : ℂ) • (∑ j ∈ s, f j) := by
          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [hL0 j hj, sub_smul]
        rw [e1, e2]
        exact Submodule.sub_mem _ (L0_mem_of_isIdeal hI hsum) (Submodule.smul_mem _ _ hsum)
    have hfI : ∀ j ∈ s.erase k, f j ∈ I := by
      intro j hj
      have hjk : j ≠ k := Finset.ne_of_mem_erase hj
      have hne : ((j : ℂ) - (k : ℂ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hjk)
      have hm := I.smul_mem ((j : ℂ) - (k : ℂ))⁻¹ (hgI j hj)
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at hm
    have hfk : f k = (∑ j ∈ s, f j) - ∑ j ∈ s.erase k, f j := by
      rw [← Finset.add_sum_erase s f hk]; abel
    rw [hfk]
    exact Submodule.sub_mem _ hsum (Submodule.sum_mem _ hfI)

/-- **Every ideal of a vertex operator algebra is graded.**  So `IsGradedIdeal` is a
theorem, not a hypothesis, and `quotientVOA` applies to every ideal. -/
theorem isGradedIdeal_of_isIdeal (hI : W.IsIdeal I) : IsGradedIdeal W I := by
  rw [isGradedIdeal_iff]
  intro x hx
  letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition
  letI : ∀ (i : ℤ) (y : W.grading i), Decidable (y ≠ 0) := fun _ _ => Classical.dec _
  set f : ℤ → 𝒱 := fun n => ((DirectSum.decompose W.grading x n : W.grading n) : 𝒱) with hfdef
  have hsum : (∑ n ∈ (DirectSum.decompose W.grading x).support, f n) = x :=
    DirectSum.sum_support_decompose W.grading x
  have hf : ∀ n : ℤ, f n ∈ W.grading n := fun n => SetLike.coe_mem _
  have hmem : ∀ n ∈ (DirectSum.decompose W.grading x).support, f n ∈ I :=
    homogeneous_mem_of_sum_mem hI _ f (fun n _ => hf n) (by rw [hsum]; exact hx)
  rw [← hsum]
  refine Submodule.sum_mem _ fun n hn => ?_
  exact (le_iSup (fun m : ℤ => I ⊓ W.grading m) n) ⟨hmem n hn, hf n⟩

/-- **The quotient of a VOA by an arbitrary ideal**, gradedness being automatic. -/
def quotientVOA' (W : VertexOperatorAlgebra 𝒱) (I : Submodule ℂ 𝒱) (hI : W.IsIdeal I) :
    VertexOperatorAlgebra (𝒱 ⧸ I) :=
  quotientVOA W I hI (isGradedIdeal_of_isIdeal hI)

/-- **The maximal proper graded ideal is maximal among *all* proper ideals**, since every
ideal is graded. -/
theorem le_maxGradedIdeal' {J : Submodule ℂ 𝒱} (hJ : W.IsIdeal J) (hv : W.vacuum ∉ J) :
    J ≤ maxGradedIdeal W :=
  le_maxGradedIdeal ⟨hJ, isGradedIdeal_of_isIdeal hJ, hv⟩

/-- **The quotient by the maximal proper ideal is a simple VOA** (for `W` with `𝟙 ≠ 0`).
This is the unconditional form of `isSimple_maxQuotientVOA`. -/
theorem isSimple_maxQuotientVOA' (W : VertexOperatorAlgebra 𝒱) (hvac : W.vacuum ≠ 0) :
    (maxQuotientVOA W).IsSimple := by
  refine isSimple_maxQuotientVOA W hvac fun J hJ => ?_
  exact isGradedIdeal_of_isIdeal
    (isIdeal_comap (maxGradedIdeal_isIdeal W) (maxGradedIdeal_isGradedIdeal W) hJ)

end QuotVOA

end VOA

