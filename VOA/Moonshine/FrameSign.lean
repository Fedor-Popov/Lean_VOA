/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeInvolution
import VOA.Moonshine.ExtraspecialModule

/-!
# Momentum-sign automorphisms of a lattice VOA  (Moonshine step M8e, general part)

For an even positive-definite lattice `L` and an additive character `χ : L → ℤ/2`, the operator

  `g_χ(p ⊗ e^α) = (-1)^{χ(α)} p ⊗ e^α`

is an automorphism of the lattice VOA `V_L = FockN(rank L) ⊗ ℂ{L}` (`LatGen.latticeVOAGen`).  It is
the device that splits `V_L` (and `V_L⁺`) by the coset of the momentum in `ker χ`: the
`g_χ`-fixed vectors are exactly those whose momenta all lie in `ker χ` (`chiLat_eq_self_iff`),
and the `g_χ = -1` vectors those whose momenta all lie outside (`chiLat_eq_neg_iff`).  Being an
automorphism, `g_χ` makes the product `u₍ₙ₎v` respect the induced `ℤ/2`-grading for free.

## Proof route

Exactly the route of `LatGen.thetaAut` (`Moonshine/LatticeInvolution.lean`): `YfullGen` is
determined by the word fields `YwordLatGen l α` on the spanning word states, so it suffices that

* `g_χ h_a(z) g_χ⁻¹ = h_a(z)` (the currents preserve the momentum; `chiLat_alphaLatGen`);
* `g_χ Y(e^α,z) g_χ⁻¹ = (-1)^{χ α} Y(e^α,z)` (`Y(e^α)` shifts momentum by `α` and `χ` is
  additive; `chiLat_Yeαvec`);
* hence `g_χ Y_word(l,α) g_χ⁻¹ = (-1)^{χ α} Y_word(l,α)` (`chiLat_YwordLatGen`, via
  `Intertw.nprod`), matching `g_χ(wordState l α) = (-1)^{χ α} wordState l α`.

## Main declarations
* `LatGen.chiSign`, `LatGen.chiLat`, `LatGen.chiLat_latStateGen`, `LatGen.chiLat_involutive`.
* `LatGen.chiLat_YfullGen`, `LatGen.chiAut : Aut (latticeVOAGen L hEven hPos)`, `chiAut_sq`.
* `LatGen.chiLat_thetaLat`, `LatGen.chiAut_mul_thetaAut` — `g_χ` commutes with `θ`.
* `LatGen.coordEα_chiLat`, `LatGen.chiLat_eq_self_iff`, `LatGen.chiLat_eq_neg_iff` — the
  momentum description of the two eigenspaces.
* `VOA.isCompl_ker_sub_one_ker_add_one` — the `±1`-eigenspaces of a linear involution are
  complementary (characteristic `0`).

## Status
All declarations `sorry`-free and axiom-free beyond the standard three (`#print axioms`:
`[propext, Classical.choice, Quot.sound]`); unconditional given `hEven`/`hPos`.
-/

set_option linter.style.longLine false

namespace VOA

/-- The `±1`-eigenspaces of a linear involution over `ℂ` are complementary. -/
theorem isCompl_ker_sub_one_ker_add_one {M : Type*} [AddCommGroup M] [Module ℂ M]
    (f : M →ₗ[ℂ] M) (hf : ∀ x, f (f x) = x) :
    IsCompl (LinearMap.ker (f - 1)) (LinearMap.ker (f + 1)) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x h1 h2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, h1] at h2
    have h3 : (2 : ℂ) • x = 0 := by rw [two_smul]; exact h2
    exact (smul_eq_zero.mp h3).resolve_left two_ne_zero
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = (2⁻¹ : ℂ) • (x + f x) + (2⁻¹ : ℂ) • (x - f x) := by
      rw [← smul_add]; rw [show x + f x + (x - f x) = (2 : ℂ) • x by rw [two_smul]; abel]
      rw [smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    rw [hx]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_add, hf,
        add_comm (f x) x, sub_self]
    · rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, map_smul, map_sub, hf,
        ← smul_add, show f x - x + (x - f x) = 0 by abel, smul_zero]

end VOA

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN

variable (L : IntegralLattice) (χ : L.carrier →+ ZMod 2)

/-! ## §1  The sign `(-1)^{χ α}` -/

/-- The momentum sign `(-1)^{χ(α)}`. -/
noncomputable def chiSign (α : L.carrier) : ℂ := VOA.Moonshine.Extraspecial.sgn (χ α)

theorem chiSign_add (α β : L.carrier) : chiSign L χ (α + β) = chiSign L χ α * chiSign L χ β := by
  rw [chiSign, chiSign, chiSign, map_add, VOA.Moonshine.Extraspecial.sgn_add]

theorem chiSign_zero : chiSign L χ 0 = 1 := by rw [chiSign, map_zero, VOA.Moonshine.Extraspecial.sgn_zero]

theorem chiSign_mul_self (α : L.carrier) : chiSign L χ α * chiSign L χ α = 1 := by
  unfold chiSign; exact VOA.Moonshine.Extraspecial.sgn_mul_self _

theorem chiSign_neg (α : L.carrier) : chiSign L χ (-α) = chiSign L χ α := by
  rw [chiSign, chiSign, map_neg, ZMod.neg_eq_self_mod_two]

theorem chiSign_of_eq_zero {α : L.carrier} (h : χ α = 0) : chiSign L χ α = 1 := by
  rw [chiSign, h, VOA.Moonshine.Extraspecial.sgn_zero]

theorem chiSign_of_ne_zero {α : L.carrier} (h : χ α ≠ 0) : chiSign L χ α = -1 := by
  have h1 : χ α = 1 := by
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (χ α) with h' | h'
    · exact absurd h' h
    · exact h'
  rw [chiSign, h1, Moonshine.Extraspecial.sgn_one]

/-! ## §2  The operator `g_χ` -/

/-- `e^α ↦ (-1)^{χ α} e^α` on the group algebra `ℂ{L}`. -/
noncomputable def chiGroupMap : (L.carrier →₀ ℂ) →ₗ[ℂ] (L.carrier →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun α => chiSign L χ α • eGen L α)

theorem chiGroupMap_eGen (α : L.carrier) :
    chiGroupMap L χ (eGen L α) = chiSign L χ α • eGen L α := by
  rw [chiGroupMap, eGen, Finsupp.linearCombination_single, one_smul]
  rfl

theorem chiGroupMap_involutive : Function.Involutive (chiGroupMap L χ) := by
  have h : chiGroupMap L χ ∘ₗ chiGroupMap L χ = LinearMap.id := by
    refine Finsupp.lhom_ext fun α c => ?_
    have hs : (Finsupp.single α c : L.carrier →₀ ℂ) = c • eGen L α := by
      rw [eGen, Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [LinearMap.comp_apply, hs, map_smul, chiGroupMap_eGen, smul_smul, LinearMap.id_apply]
    rw [chiSign_mul_self, mul_one]
  intro x
  exact congrArg (fun f : (L.carrier →₀ ℂ) →ₗ[ℂ] (L.carrier →₀ ℂ) => f x) h

/-- `g_χ` on `ℂ{L}` as a linear equivalence. -/
noncomputable def chiGroupEquiv : (L.carrier →₀ ℂ) ≃ₗ[ℂ] (L.carrier →₀ ℂ) :=
  LinearEquiv.ofInvolutive (chiGroupMap L χ) (chiGroupMap_involutive L χ)

/-- **The momentum-sign operator** `g_χ(p ⊗ e^α) = (-1)^{χ α} p ⊗ e^α` on `V_L`. -/
noncomputable def chiLat : LatModuleGen L ≃ₗ[ℂ] LatModuleGen L :=
  TensorProduct.congr (LinearEquiv.refl ℂ (FockN (rank L))) (chiGroupEquiv L χ)

theorem chiLat_tmul (p : FockN (rank L)) (α : L.carrier) :
    chiLat L χ (p ⊗ₜ[ℂ] eGen L α) = chiSign L χ α • (p ⊗ₜ[ℂ] eGen L α) := by
  rw [chiLat, TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  change p ⊗ₜ[ℂ] chiGroupMap L χ (eGen L α) = _
  rw [chiGroupMap_eGen, TensorProduct.tmul_smul]

theorem chiLat_latStateGen (p : FockN (rank L)) (α : L.carrier) :
    chiLat L χ (latStateGen L p α) = chiSign L χ α • latStateGen L p α :=
  chiLat_tmul L χ p α

theorem chiLat_mkEα (α : L.carrier) (p : FockN (rank L)) :
    chiLat L χ (mkEα L α p) = chiSign L χ α • mkEα L α p :=
  chiLat_tmul L χ p α

theorem chiLat_involutive : Function.Involutive (chiLat L χ) := by
  intro x
  have h : (chiLat L χ).toLinearMap ∘ₗ (chiLat L χ).toLinearMap = LinearMap.id := by
    refine LinearMap.ext_on_range (latStateGen_span L) fun q => ?_
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, chiLat_latStateGen, map_smul,
      chiLat_latStateGen, smul_smul, chiSign_mul_self, one_smul, LinearMap.id_apply]
  exact congrArg (fun f : LatModuleGen L →ₗ[ℂ] LatModuleGen L => f x) h

theorem chiLat_chiLat (x : LatModuleGen L) : chiLat L χ (chiLat L χ x) = x :=
  chiLat_involutive L χ x

theorem chiLat_vacuum : chiLat L χ (latVacuumGen L) = latVacuumGen L := by
  rw [latVacuumGen, chiLat_latStateGen, chiSign_zero, one_smul]

theorem chiLat_omega : chiLat L χ (omegaLatGen L) = omegaLatGen L := by
  rw [omegaLatGen, chiLat_mkEα, chiSign_zero, one_smul]

/-- `g_χ` commutes with the lattice involution `θ`. -/
theorem chiLat_thetaLat (x : LatModuleGen L) :
    chiLat L χ (thetaLat L x) = thetaLat L (chiLat L χ x) := by
  have h : (chiLat L χ).toLinearMap ∘ₗ (thetaLat L).toLinearMap
      = (thetaLat L).toLinearMap ∘ₗ (chiLat L χ).toLinearMap := by
    refine LinearMap.ext_on_range (latStateGen_span L) fun q => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [thetaLat_latStateGen, chiLat_latStateGen,
      chiLat_latStateGen, map_smul, thetaLat_latStateGen, chiSign_neg]
  exact congrArg (fun f : LatModuleGen L →ₗ[ℂ] LatModuleGen L => f x) h

/-! ## §3  Momentum description of the eigenspaces -/

/-- A vector of `V_L` is determined by its momentum components. -/
theorem eq_zero_of_coordEα {x : LatModuleGen L} (h : ∀ α, coordEα L α x = 0) : x = 0 := by
  classical
  have hc : ∀ (α : L.carrier) (y : LatModuleGen L), coordEα L α y
      = TensorProduct.finsuppScalarRight ℂ ℂ (FockN (rank L)) L.carrier y α := by
    intro α y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p f =>
        rw [TensorProduct.finsuppScalarRight_apply_tmul_apply, coordEα, LinearMap.comp_apply,
          LinearMap.lTensor_tmul, Finsupp.lapply_apply, LinearEquiv.coe_coe,
          TensorProduct.rid_tmul]
    | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy]
  have h' : TensorProduct.finsuppScalarRight ℂ ℂ (FockN (rank L)) L.carrier x = 0 := by
    ext α : 1
    rw [← hc, h, Finsupp.zero_apply]
  exact (LinearEquiv.map_eq_zero_iff _).mp h'

theorem coordEα_chiLat (α : L.carrier) (x : LatModuleGen L) :
    coordEα L α (chiLat L χ x) = chiSign L χ α • coordEα L α x := by
  have h : (coordEα L α) ∘ₗ (chiLat L χ).toLinearMap = chiSign L χ α • coordEα L α := by
    refine LinearMap.ext_on_range (latStateGen_span L) fun q => ?_
    classical
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, chiLat_latStateGen, map_smul,
      LinearMap.smul_apply, latStateGen, coordEα_apply]
    by_cases hq : α = q.2
    · rw [if_pos hq, hq]
    · rw [if_neg hq, smul_zero, smul_zero]
  exact congrArg (fun f : LatModuleGen L →ₗ[ℂ] FockN (rank L) => f x) h

/-- **`g_χ`-fixed ⇔ all momenta in `ker χ`.** -/
theorem chiLat_eq_self_iff (x : LatModuleGen L) :
    chiLat L χ x = x ↔ ∀ α, χ α ≠ 0 → coordEα L α x = 0 := by
  constructor
  · intro hx α hα
    have h := coordEα_chiLat L χ α x
    rw [hx, chiSign_of_ne_zero L χ hα, neg_one_smul] at h
    have h2 : (2 : ℂ) • coordEα L α x = 0 := by
      rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  · intro hx
    rw [← sub_eq_zero]
    refine eq_zero_of_coordEα L fun α => ?_
    rw [map_sub, coordEα_chiLat, sub_eq_zero]
    by_cases hα : χ α = 0
    · rw [chiSign_of_eq_zero L χ hα, one_smul]
    · rw [hx α hα, smul_zero]

/-- **`g_χ = -1` ⇔ all momenta outside `ker χ`.** -/
theorem chiLat_eq_neg_iff (x : LatModuleGen L) :
    chiLat L χ x = -x ↔ ∀ α, χ α = 0 → coordEα L α x = 0 := by
  constructor
  · intro hx α hα
    have h := coordEα_chiLat L χ α x
    rw [hx, chiSign_of_eq_zero L χ hα, one_smul, map_neg] at h
    have h2 : (2 : ℂ) • coordEα L α x = 0 := by
      rw [two_smul]; nth_rewrite 1 [← h]; exact neg_add_cancel _
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  · intro hx
    rw [← sub_eq_zero, sub_neg_eq_add]
    refine eq_zero_of_coordEα L fun α => ?_
    rw [map_add, coordEα_chiLat]
    by_cases hα : χ α = 0
    · rw [hx α hα, smul_zero, add_zero]
    · rw [chiSign_of_ne_zero L χ hα, neg_one_smul, neg_add_cancel]

/-! ## §4  Intertwining the vertex operators -/

theorem intertw_chi_of_latState {c : ℂ} {A B : FormalDist (End ℂ (LatModuleGen L))}
    (h : ∀ (t : ℤ) (p : FockN (rank L)) (β : L.carrier),
      chiLat L χ (A t (latStateGen L p β)) = c • B t (chiLat L χ (latStateGen L p β))) :
    Intertw (chiLat L χ).toLinearMap c A B := by
  intro t x
  have hext : (chiLat L χ).toLinearMap ∘ₗ A t = (c • B t) ∘ₗ (chiLat L χ).toLinearMap :=
    LinearMap.ext_on_range (latStateGen_span L) fun q => h t q.1 q.2
  exact congrArg (fun f : LatModuleGen L →ₗ[ℂ] LatModuleGen L => f x) hext

/-- `g_χ Y(e^α,z) g_χ⁻¹ = (-1)^{χ α} Y(e^α,z)`. -/
theorem chiLat_Yeαvec (α : L.carrier) :
    Intertw (chiLat L χ).toLinearMap (chiSign L χ α) (Yeαvec L α) (Yeαvec L α) := by
  refine intertw_chi_of_latState L χ fun t p β => ?_
  rw [Yeαvec_tmul, map_smul, chiLat_latStateGen, chiLat_latStateGen, map_smul, Yeαvec_tmul,
    chiSign_add, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

/-- `g_χ h_a(z) g_χ⁻¹ = h_a(z)` (including the momentum zero mode). -/
theorem chiLat_alphaLatGen (a : Fin (rank L)) :
    Intertw (chiLat L χ).toLinearMap 1 (alphaLatGen L a) (alphaLatGen L a) := by
  refine intertw_chi_of_latState L χ fun t p β => ?_
  rw [one_smul, chiLat_latStateGen, map_smul]
  rw [alphaLatGen_apply, LinearMap.add_apply]
  have hr : LinearMap.rTensor (L.carrier →₀ ℂ)
      (currentN (rank L) 1 a t) (latStateGen L p β) = latStateGen L (oscN (rank L) 1 a (-t - 1) p) β := by
    rw [latStateGen, LinearMap.rTensor_tmul, currentN_apply]; rfl
  rw [hr, map_add, chiLat_latStateGen, smul_add]
  congr 1
  split_ifs
  · rw [zGradeOpGen_latStateGen, map_smul, chiLat_latStateGen, smul_comm]
  · rw [LinearMap.zero_apply, map_zero, smul_zero]

theorem chiLat_genFieldLatGen (a : Fin (rank L)) (i : ℕ) :
    Intertw (chiLat L χ).toLinearMap 1 (genFieldLatGen L a i) (genFieldLatGen L a i) :=
  ((chiLat_alphaLatGen L χ a).deriv_iterate i).const_smul _

/-- `g_χ Y_word(l,α) g_χ⁻¹ = (-1)^{χ α} Y_word(l,α)`. -/
theorem chiLat_YwordLatGen (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    Intertw (chiLat L χ).toLinearMap (chiSign L χ α) (YwordLatGen L l α) (YwordLatGen L l α) := by
  induction l with
  | nil => rw [YwordLatGen_nil]; exact chiLat_Yeαvec L χ α
  | cons ia rest ih =>
      rw [YwordLatGen_cons, ← one_mul (chiSign L χ α)]
      exact Intertw.nprod _ _ _ _ (chiLat_genFieldLatGen L χ ia.2 ia.1) ih

theorem chiLat_wordStateLatGen (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    chiLat L χ (wordStateLatGen L l α) = chiSign L χ α • wordStateLatGen L l α := by
  rw [wordStateLatGen_eq, chiLat_tmul]

end VOA.LatGen

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN

variable (L : IntegralLattice) (χ : L.carrier →+ ZMod 2) (hEven : L.Even) (hPos : L.PosDef)

/-- **`g_χ` intertwines the reconstructed vertex map**: `g_χ Y(u,z) g_χ⁻¹ = Y(g_χ u,z)`. -/
theorem chiLat_YfullGen (u : LatModuleGen L) (t : ℤ) (x : LatModuleGen L) :
    chiLat L χ (YfullGen L hEven hPos u t x)
      = YfullGen L hEven hPos (chiLat L χ u) t (chiLat L χ x) := by
  have hu : u ∈ Submodule.span ℂ (Set.range (Function.uncurry (wordStateLatGen L))) := by
    rw [wordStateLatGen_span]; trivial
  induction hu using Submodule.span_induction generalizing x with
  | mem w hw =>
      obtain ⟨⟨l, α⟩, rfl⟩ := hw
      simp only [Function.uncurry_apply_pair]
      rw [YfullGen_word, chiLat_wordStateLatGen, map_smul, YfullGen_word]
      exact chiLat_YwordLatGen L χ l α t x
  | zero => simp only [map_zero]; rfl
  | add v w _ _ hv hw =>
      simp only [map_add]
      change chiLat L χ (YfullGen L hEven hPos v t x + YfullGen L hEven hPos w t x) =
        YfullGen L hEven hPos (chiLat L χ v) t (chiLat L χ x)
          + YfullGen L hEven hPos (chiLat L χ w) t (chiLat L χ x)
      rw [map_add, hv, hw]
  | smul c v _ hv =>
      simp only [map_smul]
      change chiLat L χ (c • YfullGen L hEven hPos v t x) =
        c • YfullGen L hEven hPos (chiLat L χ v) t (chiLat L χ x)
      rw [map_smul, hv]

theorem chiLat_mode (u : LatModuleGen L) (n : ℤ) (v : LatModuleGen L) :
    chiLat L χ (mode (YfullGen L hEven hPos u) n v)
      = mode (YfullGen L hEven hPos (chiLat L χ u)) n (chiLat L χ v) := by
  rw [mode_apply, mode_apply]
  exact chiLat_YfullGen L χ hEven hPos u _ v

/-- **The momentum-sign automorphism `g_χ` of `V_L`.** -/
noncomputable def chiAut : Aut (latticeVOAGen L hEven hPos) where
  toLinearEquiv := chiLat L χ
  map_smul' u n v := chiLat_mode L χ hEven hPos u n v
  map_vacuum := chiLat_vacuum L χ
  map_omega := chiLat_omega L χ

@[simp] theorem chiAut_apply (v : LatModuleGen L) : chiAut L χ hEven hPos v = chiLat L χ v := rfl

theorem chiAut_sq : chiAut L χ hEven hPos * chiAut L χ hEven hPos = 1 :=
  Aut.ext (LinearEquiv.ext fun x => chiLat_chiLat L χ x)

/-- `g_χ` and `θ` commute in `Aut(V_L)`. -/
theorem chiAut_mul_thetaAut :
    chiAut L χ hEven hPos * thetaAut L hEven hPos = thetaAut L hEven hPos * chiAut L χ hEven hPos :=
  Aut.ext (LinearEquiv.ext fun x => chiLat_thetaLat L χ x)

end VOA.LatGen
