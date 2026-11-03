/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusC2Zero

/-!
# `C₂(V_{2m}⁺)`: the sector `V⁺(1)` and the assembly

Notation of `PlusC2Sector.lean`; `E = x_α = e^α + e^{−α}`.

## Main results

* `smul_xP_PP_of_theta` — for `θv = v`: `x_a₍ₙ₎P(v) = 2·P(e^a₍ₙ₎v)`.
* `sectorOne_of_viaE : SectorOneViaE m hm → PlusSectorFinite m hm 0 → PlusSectorFinite m hm 1`:
  if `V⁺(1) ⊆ C₂(V⁺) + E₍₋₁₎M(1)⁺` (i.e. `Q₁ = Q₀·Ē` in `Q = V⁺/C₂(V⁺)`), finiteness of the
  `M(1)⁺` sector gives finiteness of `V⁺(1)`.
* `sectorOneViaE_of_fock : FockSpanEvenEE m → SectorOneViaE m hm` — a purely
  polynomial sufficient condition (`FockSpanEvenEE`: the boson dressings
  `EE(α)_d q = Σ_r S_{d+r}(α)·E⁺(α)_{−r} q`, `d ≥ 0`, of **even** Fock states span the Fock space).
* `v2mPlusC2CofiniteFactGe2_of_residuals` — **the cited `C₂` fact
  `V2mPlusC2CofiniteFactGe2` from the two residuals** `M1PlusC2Line` (lattice-free, about the
  Heisenberg orbifold `M(1)⁺` alone) and `SectorOneViaE` (Yamskulna's §4 argument at charge 1).

## The residuals (TRUE, cited; see the docstrings)

* `M1PlusC2Line` (`PlusC2Zero.lean`) — `dim R(M(1)⁺)_w ≤ 1` eventually, detected by `α(−1)^w`.
* `SectorOneViaE` — `V⁺(1) ⊆ C₂(V⁺) + E₍₋₁₎M(1)⁺`.  Yamskulna 2004, Lemmas 4.4, 4.6, 4.7, 4.10,
  run at charge 1: `(α(−n)α(−1)𝟙)₍₋₁₎E = 2k(n + (−1)^{n−1}) α(−n−1)F + α(−n)α(−1)E` and
  `L(−1)α(−n)F = nα(−n−1)F + α(−n)α(−1)E` give
  `(2k(n + (−1)^{n−1}) − n)·α(−n−1)F ∈ C₂ + M(1)⁺₍₋₁₎E`, the factor being nonzero for
  `k = m ≥ 2` (it vanishes at `k = 1, n = 2`); the length filtration (her Lemma 4.6) and
  associativity of `V⁺/C₂(V⁺)` finish.
* `FockSpanEvenEE` (optional, stronger, NOT cited): verified by exact computation for
  `m = 2, 3, 4` and Fock weight `≤ 12` (`scratchpad/q2/testB.py`); FALSE for `m = 1`
  (weight 3), consistent with the factor above.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN VOA.Moonshine LatMod

namespace PlusC2

variable (m : ℕ) (hm : 1 ≤ m)

/-- For `θ`-fixed `v`: `x_a₍ₙ₎P(v) = 2·P(e^a₍ₙ₎v)`. -/
theorem smul_xP_PP_of_theta (a : (latP m).carrier) (n : ℤ) (v : LatModuleGen (latP m))
    (hv : thetaLat (latP m) v = v) :
    (V2mPlus m hm).smul (xP m hm a) n (PP m hm v) =
      (2 : ℂ) • PP m hm ((V2m m hm).smul (latChargeGen (latP m) a) n v) := by
  rw [smul_xP_PP, map_add]
  have : PP m hm ((V2m m hm).smul (latChargeGen (latP m) (-a)) n v) =
      PP m hm ((V2m m hm).smul (latChargeGen (latP m) a) n v) := by
    rw [← PP_theta, theta_smul, thetaLat_latChargeGen, neg_neg, hv]
  rw [this, two_smul]

/-- `E₍₋₁₎M(1)⁺`: the span of `x_α₍₋₁₎P(q ⊗ e⁰)`. -/
noncomputable def eTimesM1Plus : Submodule ℂ (VP m hm) :=
  Submodule.span ℂ {x | ∃ q : FockN (rank (latP m)),
    x = (V2mPlus m hm).smul (xP m hm ((1 : ℤ) : (latP m).carrier)) (-1) (PP m hm (latStateGen (latP m) q 0))}

/-- **Residual for the sector `V⁺(1)`** (TRUE; Yamskulna 2004, Lemmas 4.4, 4.6, 4.7, 4.10 run at
charge 1 — see the module docstring): every `P(f ⊗ e^α)` lies in `C₂(V⁺) + E₍₋₁₎M(1)⁺`, i.e.
`Q₁ = Q₀·Ē` in `Q = V⁺/C₂(V⁺)`.  Needs `m ≥ 2` (the factor `2m(n + (−1)^{n−1}) − n` vanishes at
`m = 1, n = 2`).  NOT proved here. -/
def SectorOneViaE : Prop :=
  ∀ f : FockN (rank (latP m)),
    PP m hm (latStateGen (latP m) f ((1 : ℤ) : (latP m).carrier)) ∈ O₂ (V2mPlus m hm) ⊔ eTimesM1Plus m hm

/-- `V⁺(1)` is finite modulo `C₂` once `M(1)⁺` is, given `Q₁ = Q₀·Ē`. -/
theorem sectorOne_of_viaE (h1 : SectorOneViaE m hm) (h0 : PlusSectorFinite m hm 0) :
    PlusSectorFinite m hm ((1 : ℤ) : (latP m).carrier) := by
  classical
  obtain ⟨S0, hS0⟩ := h0
  set E := xP m hm ((1 : ℤ) : (latP m).carrier)
  set μ : VP m hm →ₗ[ℂ] VP m hm := mode ((V2mPlus m hm).Y E) (-1) with hμ
  have hμapp : ∀ y, μ y = (V2mPlus m hm).smul E (-1) y := fun y => by
    rw [hμ, PreVertexAlgebra.smul_def]
  refine ⟨S0.image μ, ?_⟩
  have hE : eTimesM1Plus m hm ≤ Submodule.span ℂ ((S0.image μ : Finset (VP m hm)) : Set (VP m hm)) ⊔
      O₂ (V2mPlus m hm) := by
    rw [eTimesM1Plus, Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    have hq : PP m hm (latStateGen (latP m) q 0) ∈ Submodule.span ℂ (S0 : Set (VP m hm)) ⊔
        O₂ (V2mPlus m hm) := hS0 (Submodule.subset_span ⟨q, rfl⟩)
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hq
    rw [SetLike.mem_coe, ← hyz, ← hμapp, map_add]
    refine Submodule.add_mem_sup ?_ ?_
    · have : (Submodule.span ℂ (S0 : Set (VP m hm))).map μ ≤
          Submodule.span ℂ ((S0.image μ : Finset (VP m hm)) : Set (VP m hm)) := by
        rw [Submodule.map_span, Finset.coe_image]
      exact this ⟨y, hy, rfl⟩
    · rw [hμapp]
      exact poissonMul_mem_O₂_right _ _ hz
  rw [sectorP, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  have := h1 f
  exact (sup_le (le_sup_right) hE) this

/-! ## A purely polynomial sufficient condition -/

/-- **Fock-space spanning condition** (optional, stronger; NOT cited): the boson dressings
`EE(α)_d q` (`d ≥ 0`) of `θ`-even Fock states span the whole Fock space.  Verified by exact
computation for `m = 2, 3, 4` up to Fock weight 12 (`scratchpad/q2/testB.py`); false for `m = 1`. -/
def FockSpanEvenEE : Prop :=
  ∀ f : FockN (rank (latP m)), f ∈ Submodule.span ℂ {g | ∃ (d : ℕ) (q : FockN (rank (latP m))),
    sigmaN (rank (latP m)) q = q ∧ g = EEVec (latP m) ((1 : ℤ) : (latP m).carrier) (d : ℤ) q}

/-- The polynomial condition implies `Q₁ = Q₀·Ē`. -/
theorem sectorOneViaE_of_fock (h : FockSpanEvenEE m) : SectorOneViaE m hm := by
  intro f
  set a : (latP m).carrier := ((1 : ℤ) : (latP m).carrier) with ha
  set ψ : FockN (rank (latP m)) →ₗ[ℂ] VP m hm :=
    (PP m hm).comp ((TensorProduct.mk ℂ (FockN (rank (latP m))) ((latP m).carrier →₀ ℂ)).flip
      (eGen (latP m) a)) with hψ
  have hψapp : ∀ g, ψ g = PP m hm (latStateGen (latP m) g a) := fun g => rfl
  rw [← hψapp]
  suffices hsub : Submodule.span ℂ {g | ∃ (d : ℕ) (q : FockN (rank (latP m))),
      sigmaN (rank (latP m)) q = q ∧ g = EEVec (latP m) a (d : ℤ) q} ≤
      (O₂ (V2mPlus m hm) ⊔ eTimesM1Plus m hm).comap ψ from hsub (h f)
  rw [Submodule.span_le]
  rintro _ ⟨d, q, hq, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, hψapp]
  have hθ : thetaLat (latP m) (latStateGen (latP m) q 0) = latStateGen (latP m) q 0 := by
    rw [thetaLat_latStateGen, hq, neg_zero]
  have key := smul_xP_PP_of_theta m hm a (-(d : ℤ) - 1) _ hθ
  have hcomp : (V2m m hm).smul (latChargeGen (latP m) a) (-(d : ℤ) - 1) (latStateGen (latP m) q 0) =
      latStateGen (latP m) (EEVec (latP m) a (d : ℤ) q) a := by
    unfold V2m
    rw [latVOA_smul_latChargeGen_state, latticeCocycle_zero_right, one_smul,
      show (latP m).form a 0 = 0 by simp, sub_zero, show -(-(d : ℤ) - 1) - 1 = (d : ℤ) by ring,
      add_zero]
  rw [hcomp] at key
  have hmem : (V2mPlus m hm).smul (xP m hm a) (-(d : ℤ) - 1) (PP m hm (latStateGen (latP m) q 0)) ∈
      O₂ (V2mPlus m hm) ⊔ eTimesM1Plus m hm := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      refine Submodule.mem_sup_right (Submodule.subset_span ⟨q, ?_⟩)
      simp [ha]
    · exact Submodule.mem_sup_left (smul_le_neg_two_mem_O₂ _ _ _ (by omega))
  rw [key] at hmem
  have h2 := Submodule.smul_mem _ ((1 / 2 : ℂ)) hmem
  rwa [smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] at h2

end PlusC2

open PlusC2

/-- **The two residuals of the `C₂` fact** (both TRUE and cited; see `M1PlusC2Line`,
`SectorOneViaE`). -/
def V2mPlusC2Residuals : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → M1PlusC2Line m hm ∧ SectorOneViaE m hm

/-- `C₂`-cofiniteness of `V_{2m}⁺` from the two residuals, for one `m`. -/
theorem c2Cofinite_V2mPlus_of_residuals (m : ℕ) (hm : 1 ≤ m) (h0 : M1PlusC2Line m hm)
    (h1 : SectorOneViaE m hm) : C2Cofinite (V2mPlus m hm) := by
  have hz := sectorZero_of_m1PlusC2Line m hm h0
  exact c2Cofinite_of_sectors m hm hz (sectorOne_of_viaE m hm h1 hz)

/-- **The cited fact `V2mPlusC2CofiniteFactGe2` from the two residuals.** -/
theorem v2mPlusC2CofiniteFactGe2_of_residuals (h : V2mPlusC2Residuals) :
    V2mPlusC2CofiniteFactGe2 := fun m hm h2 =>
  c2Cofinite_V2mPlus_of_residuals m hm (h m hm h2).1 (h m hm h2).2

end VOA.Classification.COne

section AxiomAudit
#print axioms VOA.Classification.COne.PlusC2.vSchur_mem_G
#print axioms VOA.Classification.COne.PlusC2.sectorZero_of_m1PlusC2Line
#print axioms VOA.Classification.COne.PlusC2.sectorOne_of_viaE
#print axioms VOA.Classification.COne.PlusC2.sectorOneViaE_of_fock
#print axioms VOA.Classification.COne.v2mPlusC2CofiniteFactGe2_of_residuals
end AxiomAudit
