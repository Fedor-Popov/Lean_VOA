/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.LatticeSimple
import VOA.Classification.COne.LatticeNice
import VOA.Classification.COne.V2PlusV8

/-!
# `V_{2m}⁺` is simple and self-dual; niceness from cited facts

## Proved (unconditional)
* `restrictSubForm`, `restrictSubForm_isFullyInvariant`, `restrictSubForm_normalized`: a fully
  invariant form restricts to a fully invariant form on any vertex operator subalgebra. No
  generation argument is needed: full invariance is a mode identity, and modes, `L₁` and the
  grading of `S.toVOA` are those of `W` (`rfl`).
* `restrictSubForm_leftRadical_zpowers`: on the fixed points of an isometric involution `g`, a
  nondegenerate form stays nondegenerate (pair with `½(y + g y)`).
* `V2mPlus_isSimple`, `V2mPlus_selfDual` (every `m ≥ 1`), via Li's criterion
  `LiRadical.isSimple_iff_leftRadical_eq_bot` applied to `plusInvFormV2m`, the restriction of
  `latInvForm` (θ is an isometry: `Nondeg.latForm_thetaLat`).
* `V2mPlus_centralCharge`, `V2mPlus_stronglyFinite_of_c2`, `nice_V2mPlus_of`.
* `V2mPlus_one_nice`: `V₂⁺` is nice, by transport along `V2Plus_iso_V8`.

## Cited (stages 2–4), as named `Prop`s
`V2mPlusC2CofiniteFact` (Yamskulna 2004), `V2mPlusRationalFact` (Abe 2005),
`V2mPlusPseudoUnitaryFact` (Dong–Nagatomo 1999).  Assembly:
`nice_V2mPlus_of_facts`, `nice_of_hasCOneLabel_plus_of_facts`.

## Why the `C₂` step is not proved in this file
`LatticeC2.lean` proves `C₂`-cofiniteness of `V_L` with the ideals
`J_γ = {q | q ⊗ e^γ ∈ C₂}` of the Fock ring: `J_γ` is an ideal because `h(−k−1)` acts by
multiplication by one oscillator and `h(−1)𝟙 ∈ V_L`.  In `V_L⁺` the vector `h(−1)𝟙` is θ-odd, so
the analogous set `{q | (1+θ)(q ⊗ e^γ) ∈ C₂(V_L⁺)}` is only stable under the even operators
(modes of `h(−1)²𝟙`, `L(−1)`), whose leading symbols `Σ_{a+b=s} x_a x_b` do not kill the linear
oscillators `x_j`; the quotient of the symbol ring by them is infinite-dimensional.  The known
proofs need the strong generation of `M(1)⁺` (Dong–Nagatomo) or an equivalent spanning theorem.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.Moonshine VertexOperatorAlgebra

universe u

section Restrict

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable (S : VOASubalgebra W)

theorem VOASubalgebra.toVOA_smul_coe (u : S.carrier) (n : ℤ) (v : S.carrier) :
    ((S.toVOA.smul u n v : S.carrier) : 𝒱) = W.smul u n v := rfl

theorem VOASubalgebra.toVOA_L_coe (n : ℤ) (v : S.carrier) :
    ((S.toVOA.L n v : S.carrier) : 𝒱) = W.L n v := rfl

theorem VOASubalgebra.toVOA_L_pow_coe (j : ℕ) (v : S.carrier) :
    (((S.toVOA.L 1) ^ j) v : 𝒱) = ((W.L 1) ^ j) (v : 𝒱) := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]; rfl

theorem VOASubalgebra.toVOA_mem_grading {n : ℤ} {v : S.carrier} :
    v ∈ S.toVOA.grading n ↔ (v : 𝒱) ∈ W.grading n := Iff.rfl

/-- The restriction of an invariant form to a vertex operator subalgebra. -/
noncomputable def restrictSubForm (B : InvariantForm W) : InvariantForm S.toVOA where
  form := B.form.compl₁₂ S.carrier.subtype S.carrier.subtype
  virasoro_adj := fun n a b => B.virasoro_adj n a b

theorem restrictSubForm_apply (B : InvariantForm W) (a b : S.carrier) :
    (restrictSubForm S B).form a b = B.form a b := rfl

theorem restrictSubForm_isFullyInvariant {B : InvariantForm W}
    (hB : B.IsFullyInvariant) : (restrictSubForm S B).IsFullyInvariant := by
  intro wt u hu n a b
  have h := hB wt u hu n a b
  simp only [restrictSubForm_apply, VOASubalgebra.toVOA_smul_coe,
    VOASubalgebra.toVOA_L_pow_coe]
  exact h

theorem restrictSubForm_normalized {B : InvariantForm W} (hB : B.Normalized) :
    (restrictSubForm S B).Normalized := hB

/-- **Nondegeneracy on the fixed points of an isometric involution.** If `g² = 1` and `g` preserves
`B`, a vector `x ∈ 𝒱^⟨g⟩` pairing nontrivially with `y` pairs nontrivially with `½(y + g y) ∈ 𝒱^⟨g⟩`. -/
theorem restrictSubForm_leftRadical_zpowers {B : InvariantForm W}
    (hB : InvariantForm.leftRadical B = ⊥) (g : Aut W) (hg : g * g = 1)
    (hiso : ∀ x y : 𝒱, B.form (g x) (g y) = B.form x y) :
    InvariantForm.leftRadical (restrictSubForm (orbifold (Subgroup.zpowers g)) B) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [InvariantForm.mem_leftRadical] at hx
  rw [Submodule.mem_bot]
  by_contra h0
  have hx' : (x : 𝒱) ∉ InvariantForm.leftRadical B := by
    rw [hB, Submodule.mem_bot]; exact fun h => h0 (Subtype.ext h)
  rw [InvariantForm.mem_leftRadical] at hx'
  obtain ⟨y, hy⟩ : ∃ y, B.form (x : 𝒱) y ≠ 0 := by
    by_contra h; push Not at h; exact hx' (LinearMap.ext h)
  have hgg : ∀ z : 𝒱, g (g z) = z := fun z => by
    have := congrArg (fun h : Aut W => h z) hg
    exact this
  have hmem : ((1 / 2 : ℂ) • (y + g y)) ∈ (orbifold (Subgroup.zpowers g)).carrier := by
    rw [mem_orbifold_zpowers_iff]
    rw [map_smul, map_add]
    change (1 / 2 : ℂ) • (g y + g (g y)) = _
    rw [hgg, add_comm]
  have hgx : g (x : 𝒱) = x := (mem_orbifold_zpowers_iff g _).mp x.2
  have h1 := DFunLike.congr_fun hx ⟨_, hmem⟩
  rw [restrictSubForm_apply, LinearMap.zero_apply] at h1
  apply hy
  have hθ : B.form (x : 𝒱) (g y) = B.form (x : 𝒱) y := by
    rw [← hiso (x : 𝒱) y, hgx]
  change B.form (x : 𝒱) ((1 / 2 : ℂ) • (y + g y)) = 0 at h1
  rw [map_smul, map_add, hθ, smul_eq_mul] at h1
  have : (1 / 2 : ℂ) * (B.form (x : 𝒱) y + B.form (x : 𝒱) y) = B.form (x : 𝒱) y := by ring
  rw [this] at h1
  exact h1

end Restrict

/-! ## `V_{2m}⁺` -/

section Plus

variable (m : ℕ) (hm : 1 ≤ m)

/-- The invariant form of `V_{2m}⁺`: the restriction of `latInvForm`. -/
noncomputable def plusInvFormV2m : InvariantForm (V2mPlus m hm) :=
  restrictSubForm (orbifold (Subgroup.zpowers (thetaV2m m hm)))
    (latInvForm (latP m) (latP_even m) (latP_posDef m hm))

theorem plusInvFormV2m_isFullyInvariant : (plusInvFormV2m m hm).IsFullyInvariant :=
  restrictSubForm_isFullyInvariant _ (latInvForm_isFullyInvariant _ _ _)

theorem plusInvFormV2m_normalized : (plusInvFormV2m m hm).Normalized :=
  restrictSubForm_normalized _ (latInvForm_normalized _ _ _)

theorem plusInvFormV2m_leftRadical : InvariantForm.leftRadical (plusInvFormV2m m hm) = ⊥ :=
  restrictSubForm_leftRadical_zpowers (latInvForm_leftRadical _ _ _) (thetaV2m m hm)
    (thetaAut_sq _ _ _) (fun x y => Nondeg.latForm_thetaLat (latP m) x y)

/-- **Stage 1 (simplicity)**: `V_{2m}⁺` is simple, for every `m ≥ 1`. -/
theorem V2mPlus_isSimple : (V2mPlus m hm).IsSimple :=
  (LiRadical.isSimple_iff_leftRadical_eq_bot (plusInvFormV2m_isFullyInvariant m hm)
    (plusInvFormV2m_normalized m hm)).mpr (plusInvFormV2m_leftRadical m hm)

/-- **Stage 1 (self-duality)**: `V_{2m}⁺` is self-dual, for every `m ≥ 1`. -/
theorem V2mPlus_selfDual : (V2mPlus m hm).SelfDual :=
  ⟨plusInvFormV2m m hm, plusInvFormV2m_isFullyInvariant m hm, plusInvFormV2m_leftRadical m hm⟩

/-- `c(V_{2m}⁺) = 1`. -/
theorem V2mPlus_centralCharge : (V2mPlus m hm).centralCharge = 1 := by
  rw [V2mPlus, orbifoldVOA_centralCharge]
  exact V2m_centralCharge m hm

/-- **Stage 2 reduced**: `V_{2m}⁺` is strongly finite as soon as it is `C₂`-cofinite. -/
theorem V2mPlus_stronglyFinite_of_c2 (hC2 : C2Cofinite (V2mPlus m hm)) :
    StronglyFinite (V2mPlus m hm) :=
  ⟨V2mPlus_isSimple m hm, V2mPlus_selfDual m hm, hC2⟩

/-- `V_{2m}⁺` is nice, given its three remaining properties for this `m`. -/
theorem nice_V2mPlus_of (hC2 : C2Cofinite (V2mPlus m hm))
    (hRat : AdmissiblyRational (V2mPlus m hm)) (hPU : PseudoUnitary (V2mPlus m hm)) :
    Nice (V2mPlus m hm) :=
  ⟨{ V2mPlus_stronglyFinite_of_c2 m hm hC2 with rational := hRat }, hPU⟩

end Plus

/-! ## The case `m = 1`, unconditionally: `V₂⁺ ≅ V₈` -/

/-- `V₂⁺` is nice (unconditional), by transport along `V2Plus_iso_V8`. -/
theorem V2mPlus_one_nice : Nice (V2mPlus 1 le_rfl) := by
  obtain ⟨e, he, hω⟩ := V2Plus_iso_V8
  exact ⟨stronglyRational_of_iso e he hω (V2m_stronglyRational 4 (by norm_num)),
    pseudoUnitary_of_iso e he hω (V2m_pseudoUnitary 4 (by norm_num))⟩

/-! ## The cited facts (stages 2–4) and the assembly -/

/-- **Cited fact (stage 2): `V_L⁺` is `C₂`-cofinite**, for the rank-one lattice `L = √(2m) ℤ`.

Source: G. Yamskulna, *`C₂`-cofiniteness of the vertex operator algebra `V_L⁺` when `L` is a rank
one lattice*, Comm. Algebra 32 (2004) 927–954, doi:10.1081/AGB-120027959, arXiv:math/0202056
(checked against the arXiv text and Crossref).  With `⟨α,α⟩ = 2k` (`k = m`), her
Theorem 5.1(2) proves `k ≥ 3`; her Lemma 3.8 covers `k = 1` (`V_L⁺ ≅ V_{L'}`, `⟨β,β⟩ = 8`,
Dong–Griess) and `k = 2` (`V_L⁺ ≅ L(½,0) ⊗ L(½,0)`, Dong–Griess–Höhn) by citation.  See also
Abe–Buhl–Dong, Trans. AMS 356 (2004) 3391–3402, Thm 5.3.  `m = 1` is a theorem here
(`V2mPlus_one_nice`); `ConversePlus.lean` restricts the fact to `m ≥ 2` (`V2mPlusC2CofiniteFactGe2`,
equivalent by `v2mPlusC2CofiniteFact_iff`).  Not formalized here: the Fock-ideal argument of
`LatticeC2.lean` does not transfer, because the `C₂`-ideal of a θ-sector is not stable under
multiplication by a single oscillator `h(−k−1)` (that operator is θ-odd); see the file docstring. -/
def V2mPlusC2CofiniteFact : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), C2Cofinite (V2mPlus m hm)

/-- **Cited fact (stage 3): `V_L⁺` is rational** — every admissible (`ℕ`-gradable) module is
completely reducible — for `L = √(2m) ℤ`.

Source: T. Abe, *Rationality of the vertex operator algebra `V_L⁺` for a positive definite even
lattice `L`*, Math. Z. 249 (2005) 455–484, doi:10.1007/s00209-004-0709-1, arXiv:math/0311210
(checked against the arXiv abstract and Crossref).  The theorem there: "any
`ℤ_{≥0}`-graded weak module is completely reducible", which is `AdmissiblyRational`.  It covers
every positive-definite even `L`, rank one included.  `m ≥ 2` form: `V2mPlusRationalFactGe2`. -/
def V2mPlusRationalFact : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), AdmissiblyRational (V2mPlus m hm)

/-- **Cited fact (stage 4): `V_L⁺` is pseudo-unitary**, for `L = √(2m) ℤ`.

Source: the classification of irreducible `V_L⁺`-modules, C. Dong, K. Nagatomo, *Representations of
vertex operator algebra `V_L⁺` for rank one lattice `L`*, Comm. Math. Phys. 202 (1999) 169–195,
doi:10.1007/s002200050578, arXiv:math/9807168, **Theorem 5.13** (checked against the
arXiv text and Crossref; it lists all irreducible *admissible* modules, and every irreducible
ordinary module is one), building on Dong–Nagatomo, J. Algebra 216 (1999) 384–404
(arXiv:math/9806051) for `M(1)⁺`.  With `⟨α,α⟩ = 2k`, `k = m`.  The irreducible modules and their
lowest conformal weights are: `V_L⁺` (0), `V_L⁻` (1), `V_{L+λ_j}` for `1 ≤ j ≤ m−1`
(`j²/4m`), `V_{L+λ_m}^±` (`m/4`), and the twisted-sector modules `V_L^{T_i,+}` (`1/16`),
`V_L^{T_i,−}` (`9/16`), `i = 1, 2`.  Every module other than `V_L⁺` has positive weights. -/
def V2mPlusPseudoUnitaryFact : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), PseudoUnitary (V2mPlus m hm)

/-- **`V_{2m}⁺` is nice**, `#print axioms`-clean, conditional on the three cited facts
(stage 1 — simplicity and self-duality — is proved here). -/
theorem nice_V2mPlus_of_facts (hC2 : V2mPlusC2CofiniteFact) (hRat : V2mPlusRationalFact)
    (hPU : V2mPlusPseudoUnitaryFact) (m : ℕ) (hm : 1 ≤ m) : Nice (V2mPlus m hm) :=
  nice_V2mPlus_of m hm (hC2 m hm) (hRat m hm) (hPU m hm)

/-- **The plus clause of Gannon–Rayhaun Prop. 3.2**, conditional on the cited facts: a VOA
isomorphic to `V_{2m}⁺` is nice and has `c = 1`. -/
theorem nice_of_hasCOneLabel_plus_of_facts (hC2 : V2mPlusC2CofiniteFact)
    (hRat : V2mPlusRationalFact) (hPU : V2mPlusPseudoUnitaryFact)
    {𝒱 : Type} [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱) (m : ℕ)
    (h : HasCOneLabel V (.plus m)) : Nice V ∧ V.centralCharge = 1 := by
  obtain ⟨hm, -, e, he, hω⟩ := h
  have hN := nice_V2mPlus_of_facts hC2 hRat hPU m hm
  refine ⟨⟨stronglyRational_of_iso e he hω hN.1, pseudoUnitary_of_iso e he hω hN.2⟩, ?_⟩
  rw [centralCharge_eq_of_iso e he hω hN.1.toStronglyFinite.vacuum_ne_zero,
    V2mPlus_centralCharge]

end VOA.Classification.COne
