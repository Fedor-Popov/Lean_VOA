/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeMorphFock
import VOA.Moonshine.FrameSign
import VOA.Core.SimpleImage

/-!
# Functoriality of the lattice VOA under isometries  (M8g-0 bridge, part 2)

Let `K`, `L` be even positive-definite lattices of the same rank and `ι : K → L` a `ℤ`-linear
isometry.  This file constructs the injective homomorphism of vertex operator algebras

  `Φ_ι : V_K → V_L`,   `Φ_ι(p ⊗ e^α) = c(α) · φ(p) ⊗ e^{ια}`,

where
* `φ = fockMap Q` is the orthogonal change of oscillator variables with matrix
  `Q = oscMatrix K L ι` (`Q · chargeCoord_K α = chargeCoord_L (ια)`, `QᵀQ = QQᵀ = 1`;
  `LatticeMorphFock.lean`), which is needed because both Fock spaces are written in orthonormal
  oscillators relative to *different* chosen bases;
* `c = latCob K L ι` is the coboundary comparing the two FLM cocycles:
  `ε_L(ια,ιβ) c(α) c(β) = ε_K(α,β) c(α+β)` (`latticeCocycle_map_mul_latCob`).  It is a fourth root
  of unity `c(α) = i^{S(α,α)}` with `S` a symmetric integral form, so `c(−α) = c(α)`.

## Proof route
Exactly the word-field route of `LatGen.thetaAut` (`LatticeInvolution.lean`), with the
heterogeneous intertwining relation `IntertwH`:
* `φ E^±(α,z) = E^±(ια,z) φ` (`fockMap_vSchur`, `fockMap_aExpVec`), hence
  `Φ Y(e^α,z) = c(α) Y(e^{ια},z) Φ` (`latMorph_Yeαvec`, using the cocycle comparison);
* `Φ h_a(z) = (∑_b Q_{ba} h_b(z)) Φ`, including the momentum zero mode (`latMorph_alphaLatGen`,
  using `Qᵀ Q = 1`);
* on the `L` side, `Y(h_b(-i-1)v, z) = :∂^{(i)}h_b(z) Y(v,z):` for **every** `v`
  (`YfullGen_rTensor_current`, by linearity from the word states), and `:(∑ Q h) Y: = ∑ Q :h Y:`
  (`nprod_finsetSum_left`);
* induction on the word gives `Φ Y(w,z) = Y(Φ w,z) Φ` on the spanning word states, hence on all of
  `V_K` (`latMorph_YfullGen`).

## Main declarations
* `LatGen.latMorphC ι c` — the general map `p ⊗ e^α ↦ c(α) φ(p) ⊗ e^{ια}` for **any** momentum
  rescaling `c` with `ε_L(ια,ιβ) c(α) c(β) = ε_K(α,β) c(α+β)`; all results below are proved for
  `latMorphC` under the minimal hypotheses on `c` (`c 0 = 1`, the cocycle relation, `c ≠ 0`,
  `c(−α) = c(α)`), then specialised.
* `LatGen.latMorph := latMorphC ι (latCob K L ι)` — `Φ_ι : V_K →ₗ V_L`, with `latMorph_latStateGen`.
* `LatGen.latMorph_mode` — `Φ(u₍ₙ₎v) = (Φu)₍ₙ₎(Φv)`; `latMorph_vacuum`; `latMorph_omega`.
* `LatGen.latMorph_isVOAHom` — `IsVOAHom (latticeVOAGen K …) (latticeVOAGen L …) Φ_ι`.
* `LatGen.coordEα_latMorph`, `LatGen.coordEα_latMorphC_of_not_mem`, `LatGen.latMorph_injective`,
  `LatGen.mem_range_latMorph_iff` — `Φ_ι` is injective with image exactly the states whose momenta
  lie in `ι(K)`.
* `LatGen.latMorph_thetaLat` — `Φ_ι ∘ θ_K = θ_L ∘ Φ_ι` (no correction: `c(−α) = c(α)` and
  `φ` commutes with `σ`).
* `LatGen.latMorph_chiLat` — `Φ_ι ∘ g_{χ∘ι} = g_χ ∘ Φ_ι` for every `χ : L →+ ZMod 2`.
* `LatGen.charAut d` — the automorphism `e^α ↦ d(α) e^α` for any additive character
  `d : L → ℂˣ` (`latMorphC` of the identity), `charLat_thetaLat_conj` (`g_e θ g_e⁻¹ = g_{2e} θ`),
  `exists_half_char` (every character has a square root).

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
Unconditional given evenness, positive-definiteness, the isometry property and equal rank.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct Matrix
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN MvPolynomial

variable (K L : IntegralLattice) (ι : K.carrier →ₗ[ℤ] L.carrier) (c : K.carrier → ℂ)
  (hc0 : c 0 = 1)
  (hcoc : ∀ α β, latticeCocycle L (ι α) (ι β) * (c α * c β) = latticeCocycle K α β * c (α + β))
  (hcne : ∀ α, c α ≠ 0) (hcneg : ∀ α, c (-α) = c α)

/-! ## §1  The Fock factor -/

section Fock

variable (hK : K.PosDef) (hL : L.PosDef) (hι : ∀ α β, L.form (ι α) (ι β) = K.form α β)

include hK hL hι in
theorem fockMap_chargeOsc (α : K.carrier) (m : ℤ) (p : FockN (rank K)) :
    fockMap (oscMatrix K L ι) (chargeOsc K α m p) = chargeOsc L (ι α) m (fockMap (oscMatrix K L ι) p) :=
  fockMap_oscComb _ (oscMatrix_transpose_mul K L hK hL ι hι) (chargeCoord K α) (chargeCoord L (ι α))
    (oscMatrix_chargeCoord K L hK ι α) 1 m p

include hK in
theorem fockMap_vVar (α : K.carrier) (m : ℕ) :
    fockMap (oscMatrix K L ι) (vVar K α m) = vVar L (ι α) m :=
  fockMap_Xcomb _ (chargeCoord K α) (chargeCoord L (ι α)) (oscMatrix_chargeCoord K L hK ι α) m

include hK in
theorem fockMap_vSchur (α : K.carrier) (N : ℕ) :
    fockMap (oscMatrix K L ι) (vSchur K α N) = vSchur L (ι α) N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [vSchur_zero, vSchur_zero, fockMap_one]
    | (M+1) =>
      rw [vSchur_succ, vSchur_succ, map_smul, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [fockMap_mul, fockMap_vVar K L ι hK, ih (M - m) (by simp at hm; omega)]

include hK hL hι in
theorem fockMap_aExpVec (α : K.carrier) (N : ℕ) (p : FockN (rank K)) :
    fockMap (oscMatrix K L ι) (aExpVec K α N p) = aExpVec L (ι α) N (fockMap (oscMatrix K L ι) p) := by
  induction N using Nat.strong_induction_on generalizing p with
  | _ N ih =>
    match N with
    | 0 => rw [aExpVec_zero, aExpVec_zero, LinearMap.id_apply, LinearMap.id_apply]
    | (M+1) =>
      rw [aExpVec_succ, aExpVec_succ, LinearMap.smul_apply, LinearMap.smul_apply, map_smul,
        LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.neg_apply,
        map_neg, fockMap_chargeOsc K L ι hK hL hι, ih (M - m) (by simp at hm; omega)]

include hK in
theorem fockMap_EminusVecField (α : K.carrier) :
    IntertwH (fockMap (oscMatrix K L ι)).toLinearMap 1 (EminusVecField K α)
      (EminusVecField L (ι α)) := by
  intro t x
  rw [one_smul, EminusVecField_apply, EminusVecField_apply]
  split_ifs
  · rw [EminusVec, EminusVec, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply,
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, fockMap_mul, fockMap_vSchur K L ι hK]
  · rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

include hK hL hι in
theorem fockMap_EplusVecField (α : K.carrier) :
    IntertwH (fockMap (oscMatrix K L ι)).toLinearMap 1 (EplusVecField K α)
      (EplusVecField L (ι α)) := by
  intro t x
  rw [one_smul, EplusVecField_apply, EplusVecField_apply]
  split_ifs
  · rw [AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, fockMap_aExpVec K L ι hK hL hι]
  · rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

include hK hL hι in
theorem fockMap_EEVec (α : K.carrier) :
    IntertwH (fockMap (oscMatrix K L ι)).toLinearMap 1 (EEVec K α) (EEVec L (ι α)) := by
  have h := IntertwH.nprod (EminusVecField_isField K α) (EplusVecField_isField K α)
    (EminusVecField_isField L (ι α)) (EplusVecField_isField L (ι α))
    (fockMap_EminusVecField K L ι hK α) (fockMap_EplusVecField K L ι hK hL hι α)
  rwa [mul_one] at h

end Fock

/-! ## §2  Generic helpers -/

section Helpers

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem formalDist_sum_apply {ι' : Type*} (s : Finset ι') (f : ι' → FormalDist (End ℂ W)) (t : ℤ) :
    (∑ b ∈ s, f b) t = ∑ b ∈ s, f b t :=
  Finset.sum_apply t s f

theorem formalDist_smul_apply (c : ℂ) (f : FormalDist (End ℂ W)) (t : ℤ) :
    (c • f) t = c • f t := rfl

theorem IntertwH.smul_right {g : V →ₗ[ℂ] W} {c : ℂ} {A : FormalDist (End ℂ V)}
    {B : FormalDist (End ℂ W)} (h : IntertwH g c A B) : IntertwH g 1 A (c • B) := by
  intro t x
  rw [h, one_smul, formalDist_smul_apply, LinearMap.smul_apply]

theorem IntertwH.congr_right {g : V →ₗ[ℂ] W} {c : ℂ} {A : FormalDist (End ℂ V)}
    {B B' : FormalDist (End ℂ W)} (h : IntertwH g c A B) (hB : B = B') : IntertwH g c A B' :=
  hB ▸ h

theorem nprod_congr_right {a b b' : FormalDist (End ℂ W)} (ha : IsField a) (hb : IsField b)
    (hb' : IsField b') (h : b = b') : VOA.nprod ha hb = VOA.nprod ha hb' := by
  subst h; rfl

theorem nprod_zero_right' {a : FormalDist (End ℂ W)} (ha : IsField a) (h0 : IsField (0 : FormalDist (End ℂ W))) :
    VOA.nprod ha h0 = 0 := by
  funext s
  apply LinearMap.ext
  intro x
  rw [nprod_apply]
  refine (finsum_eq_zero_of_forall_eq_zero fun m => ?_).trans rfl
  rw [normalOrdered_apply]
  split_ifs
  · change (a m * (0 : End ℂ W)) x = 0; rw [mul_zero]; rfl
  · change ((0 : End ℂ W) * a m) x = 0; rw [zero_mul]; rfl

end Helpers

/-! ## §3  The morphism `Φ_ι` -/

section Morph

/-- The momentum part of `Φ_ι`: `e^α ↦ c(α) e^{ια}`. -/
noncomputable def momMap (c : K.carrier → ℂ) : (K.carrier →₀ ℂ) →ₗ[ℂ] (L.carrier →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun α => c α • eGen L (ι α))

/-- **The lattice-VOA morphism** `Φ_ι(p ⊗ e^α) = c(α) · φ(p) ⊗ e^{ια}`. -/
noncomputable def latMorphC (c : K.carrier → ℂ) : LatModuleGen K →ₗ[ℂ] LatModuleGen L :=
  TensorProduct.map (fockMap (oscMatrix K L ι)).toLinearMap (momMap K L ι c)

theorem latMorphC_latStateGen (p : FockN (rank K)) (α : K.carrier) :
    latMorphC K L ι c (latStateGen K p α)
      = c α • latStateGen L (fockMap (oscMatrix K L ι) p) (ι α) := by
  rw [latMorphC, latStateGen, TensorProduct.map_tmul, momMap, eGen,
    Finsupp.linearCombination_single, one_smul, TensorProduct.tmul_smul]
  rfl

theorem latMorphC_intertw_of_latState {s : ℂ} {A : FormalDist (End ℂ (LatModuleGen K))}
    {B : FormalDist (End ℂ (LatModuleGen L))}
    (h : ∀ (t : ℤ) (p : FockN (rank K)) (β : K.carrier),
      latMorphC K L ι c (A t (latStateGen K p β)) = s • B t (latMorphC K L ι c (latStateGen K p β))) :
    IntertwH (latMorphC K L ι c) s A B := by
  intro t x
  have hext : (latMorphC K L ι c) ∘ₗ A t = (s • B t) ∘ₗ (latMorphC K L ι c) :=
    LinearMap.ext_on_range (latStateGen_span K) fun q => h t q.1 q.2
  exact congrArg (fun f : LatModuleGen K →ₗ[ℂ] LatModuleGen L => f x) hext

include hc0 in
theorem latMorphC_vacuum : latMorphC K L ι c (latVacuumGen K) = latVacuumGen L := by
  rw [latVacuumGen, latMorphC_latStateGen, hc0, one_smul, vacuumN, fockMap_one, map_zero]
  rfl

theorem latMorphC_latChargeGen (α : K.carrier) :
    latMorphC K L ι c (latChargeGen K α) = c α • latChargeGen L (ι α) := by
  rw [latChargeGen, latMorphC_latStateGen, vacuumN, fockMap_one]
  rfl

variable (hK : K.PosDef) (hL : L.PosDef) (hι : ∀ α β, L.form (ι α) (ι β) = K.form α β)

include hK hL hι hc0 in
theorem latMorphC_omega (hr : rank K = rank L) : latMorphC K L ι c (omegaLatGen K) = omegaLatGen L := by
  rw [omegaLatGen, mkEα_apply, ← latStateGen, latMorphC_latStateGen, hc0, one_smul,
    fockMap_ωN _ (oscMatrix_mul_transpose K L hK hL ι hι hr), map_zero]
  rfl

variable (hKe : K.Even) (hLe : L.Even)

include hK hL hι hcoc in
/-- `Φ Y(e^α,z) = c(α) Y(e^{ια},z) Φ`. -/
theorem latMorphC_Yeαvec (α : K.carrier) :
    IntertwH (latMorphC K L ι c) (c α) (Yeαvec K α) (Yeαvec L (ι α)) := by
  refine latMorphC_intertw_of_latState K L ι c fun t p β => ?_
  have hE := fockMap_EEVec K L ι hK hL hι α (t - K.form α β) p
  rw [one_smul] at hE
  simp only [AlgHom.toLinearMap_apply] at hE
  rw [Yeαvec_tmul, map_smul, latMorphC_latStateGen, latMorphC_latStateGen, map_smul, Yeαvec_tmul,
    hι, map_add]
  change latticeCocycle K α β • c (α + β) •
      latStateGen L (fockMap (oscMatrix K L ι) (EEVec K α (t - K.form α β) p)) (ι α + ι β) = _
  rw [hE, smul_smul, smul_smul, smul_smul, ← hcoc α β]
  congr 1
  ring

end Morph

/-! ## §4  The currents -/

section Currents

theorem alphaLatGen_latStateGen (a : Fin (rank L)) (t : ℤ) (p : FockN (rank L)) (β : L.carrier) :
    alphaLatGen L a t (latStateGen L p β)
      = latStateGen L (oscN (rank L) 1 a (-t - 1) p
          + (if t = -1 then chargeCoord L β a • p else 0)) β := by
  rw [alphaLatGen_apply, LinearMap.add_apply, latStateGen, LinearMap.rTensor_tmul, currentN_apply,
    latStateGen, TensorProduct.add_tmul]
  congr 1
  split_ifs
  · rw [← latStateGen, zGradeOpGen_latStateGen, latStateGen, TensorProduct.smul_tmul']
  · rw [LinearMap.zero_apply, TensorProduct.zero_tmul]

theorem rTensor_latStateGen (f : FockN (rank L) →ₗ[ℂ] FockN (rank L)) (p : FockN (rank L))
    (β : L.carrier) :
    LinearMap.rTensor (L.carrier →₀ ℂ) f (latStateGen L p β) = latStateGen L (f p) β := by
  rw [latStateGen, LinearMap.rTensor_tmul]; rfl

theorem latStateGen_sum_smul {ι' : Type*} (s : Finset ι') (e : ι' → ℂ) (f : ι' → FockN (rank L))
    (γ : L.carrier) :
    ∑ b ∈ s, e b • latStateGen L (f b) γ = latStateGen L (∑ b ∈ s, e b • f b) γ := by
  unfold latStateGen
  rw [TensorProduct.sum_tmul]
  exact Finset.sum_congr rfl fun b _ => (TensorProduct.smul_tmul' _ _ _).symm

variable (hK : K.PosDef) (hL : L.PosDef) (hι : ∀ α β, L.form (ι α) (ι β) = K.form α β)

include hK hL hι in
theorem oscMatrix_transpose_chargeCoord (β : K.carrier) (a : Fin (rank K)) :
    ∑ b : Fin (rank L), oscMatrix K L ι b a * chargeCoord L (ι β) b = chargeCoord K β a := by
  have h := congrFun (congrArg (fun M => M *ᵥ chargeCoord K β)
    (oscMatrix_transpose_mul K L hK hL ι hι)) a
  simp only [Matrix.one_mulVec] at h
  rw [← h, ← Matrix.mulVec_mulVec, oscMatrix_chargeCoord K L hK ι β]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

include hK hL hι in
/-- `Φ h_a(z) = (∑_b Q_{ba} h_b(z)) Φ`, including the momentum zero mode. -/
theorem latMorphC_alphaLatGen (a : Fin (rank K)) :
    IntertwH (latMorphC K L ι c) 1 (alphaLatGen K a)
      (∑ b : Fin (rank L), oscMatrix K L ι b a • alphaLatGen L b) := by
  refine latMorphC_intertw_of_latState K L ι c fun t p β => ?_
  rw [one_smul, alphaLatGen_latStateGen, latMorphC_latStateGen, latMorphC_latStateGen,
    formalDist_sum_apply, LinearMap.sum_apply]
  simp only [formalDist_smul_apply, LinearMap.smul_apply, map_smul, alphaLatGen_latStateGen]
  rw [← Finset.smul_sum]
  congr 1
  rw [latStateGen_sum_smul]
  congr 1
  rw [map_add, fockMap_oscN _ (oscMatrix_transpose_mul K L hK hL ι hι)]
  simp only [smul_add, Finset.sum_add_distrib]
  congr 1
  split_ifs
  · rw [map_smul]
    simp only [smul_smul, ← Finset.sum_smul, oscMatrix_transpose_chargeCoord K L ι hK hL hι]
  · simp

include hK hL hι in
theorem latMorphC_genFieldLatGen (a : Fin (rank K)) (i : ℕ) :
    IntertwH (latMorphC K L ι c) 1 (genFieldLatGen K a i)
      (∑ b : Fin (rank L), oscMatrix K L ι b a • genFieldLatGen L b i) := by
  refine IntertwH.congr_right (((latMorphC_alphaLatGen K L ι c hK hL hι a).deriv_iterate i).const_smul
    ((i.factorial : ℂ)⁻¹)) ?_
  rw [deriv_iterate_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fld.deriv_iterate_smul, genFieldLatGen, smul_comm]

theorem isField_sum_genField (a : Fin (rank K)) (i : ℕ) :
    IsField (∑ b : Fin (rank L), oscMatrix K L ι b a • genFieldLatGen L b i) :=
  isField_finsetSum _ _ fun b => Fld.isField_smul _ (genFieldLatGen_isField L b i)

end Currents

/-! ## §5  The vertex operators -/

section Vertex

/-- On the target side, `Y(h_b(-i-1) v, z) = :∂^{(i)} h_b(z) Y(v,z):` for **every** `v` (by
linearity from the word states, where it is `YwordLatGen_cons`). -/
theorem YfullGen_rTensor_current (hEven : L.Even) (hPos : L.PosDef) (b : Fin (rank L)) (i : ℕ)
    (v : LatModuleGen L) :
    YfullGen L hEven hPos (LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 b i) v)
      = VOA.nprod (genFieldLatGen_isField L b i) (YfullGen_isField L hEven hPos v) := by
  have hv : v ∈ Submodule.span ℂ (Set.range (Function.uncurry (wordStateLatGen L))) := by
    rw [wordStateLatGen_span]; trivial
  induction hv using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨⟨l, α⟩, rfl⟩ := hw
      simp only [Function.uncurry_apply_pair]
      rw [← wordStateLatGen_cons L (i, b) l α, YfullGen_word, YwordLatGen_cons]
      exact nprod_congr_right _ _ _ (YfullGen_word L hEven hPos l α).symm
  | zero =>
      rw [nprod_congr_right _ (YfullGen_isField L hEven hPos 0) Fld.isField_zero (map_zero _),
        nprod_zero_right', map_zero, map_zero]
  | add x y _ _ hx hy =>
      rw [map_add, map_add, hx, hy,
        nprod_congr_right _ (YfullGen_isField L hEven hPos (x + y))
          (Fld.isField_add (YfullGen_isField L hEven hPos x) (YfullGen_isField L hEven hPos y))
          (map_add _ x y),
        Fld.nprod_add_right]
  | smul c x _ hx =>
      rw [map_smul, map_smul, hx,
        nprod_congr_right _ (YfullGen_isField L hEven hPos (c • x))
          (Fld.isField_smul c (YfullGen_isField L hEven hPos x)) (map_smul _ c x),
        Fld.nprod_smul_right]

variable (hK : K.PosDef) (hL : L.PosDef) (hι : ∀ α β, L.form (ι α) (ι β) = K.form α β)

include hK hL hι in
/-- `Φ ∘ h_a(-i-1) = (∑_b Q_{ba} h_b(-i-1)) ∘ Φ` on states. -/
theorem latMorphC_rTensor_current (a : Fin (rank K)) (i : ℕ) (x : LatModuleGen K) :
    latMorphC K L ι c (LinearMap.rTensor (K.carrier →₀ ℂ) (currentN (rank K) 1 a i) x)
      = ∑ b : Fin (rank L), oscMatrix K L ι b a •
          LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 b i) (latMorphC K L ι c x) := by
  have h : (latMorphC K L ι c) ∘ₗ LinearMap.rTensor (K.carrier →₀ ℂ) (currentN (rank K) 1 a i)
      = (∑ b : Fin (rank L), oscMatrix K L ι b a •
          LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 b i)) ∘ₗ latMorphC K L ι c := by
    refine LinearMap.ext_on_range (latStateGen_span K) fun q => ?_
    obtain ⟨p, β⟩ := q
    simp only [LinearMap.comp_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
    rw [rTensor_latStateGen, latMorphC_latStateGen, latMorphC_latStateGen]
    simp only [map_smul, rTensor_latStateGen, currentN_apply]
    rw [fockMap_oscN _ (oscMatrix_transpose_mul K L hK hL ι hι), ← latStateGen_sum_smul,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_comm]
  have hx := LinearMap.congr_fun h x
  simp only [LinearMap.comp_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply] at hx
  exact hx

variable (hKe : K.Even) (hLe : L.Even)

include hK hL hι hKe hLe hcoc in
/-- The word-state case of the intertwining, by induction on the word. -/
theorem latMorphC_YfullGen_word (l : List (ℕ × Fin (rank K))) (α : K.carrier) :
    IntertwH (latMorphC K L ι c) 1 (YfullGen K hKe hK (wordStateLatGen K l α))
      (YfullGen L hLe hL (latMorphC K L ι c (wordStateLatGen K l α))) := by
  induction l with
  | nil =>
      rw [YfullGen_word, YwordLatGen_nil, wordStateLatGen_nil, latMorphC_latChargeGen, map_smul,
        ← wordStateLatGen_nil, YfullGen_word, YwordLatGen_nil]
      exact IntertwH.smul_right (latMorphC_Yeαvec K L ι c hcoc hK hL hι α)
  | cons ia rest ih =>
      obtain ⟨i, a⟩ := ia
      rw [YfullGen_word, YwordLatGen_cons, wordStateLatGen_cons, latMorphC_rTensor_current K L ι c hK hL hι,
        map_sum]
      simp only [map_smul, YfullGen_rTensor_current L hLe hL]
      rw [← nprod_finsetSum_left Finset.univ (fun b => oscMatrix K L ι b a)
        (fun b => genFieldLatGen L b i) (fun b => genFieldLatGen_isField L b i)
        (YfullGen_isField L hLe hL _) (isField_sum_genField K L ι a i)]
      have h := IntertwH.nprod (genFieldLatGen_isField K a i) (YfullGen_isField K hKe hK _)
        (isField_sum_genField K L ι a i) (YfullGen_isField L hLe hL _)
        (latMorphC_genFieldLatGen K L ι c hK hL hι a i) ih
      rw [mul_one] at h
      refine IntertwH.congr_right ?_ rfl
      have hw := YfullGen_word K hKe hK rest α
      convert h using 2
      exact hw.symm

include hK hL hι hKe hLe hcoc in
/-- **`Φ_ι` intertwines the vertex operators**: `Φ Y(u,z) = Y(Φu,z) Φ`, coefficientwise. -/
theorem latMorphC_YfullGen (u : LatModuleGen K) (t : ℤ) (x : LatModuleGen K) :
    latMorphC K L ι c (YfullGen K hKe hK u t x)
      = YfullGen L hLe hL (latMorphC K L ι c u) t (latMorphC K L ι c x) := by
  have hu : u ∈ Submodule.span ℂ (Set.range (Function.uncurry (wordStateLatGen K))) := by
    rw [wordStateLatGen_span]; trivial
  induction hu using Submodule.span_induction generalizing x with
  | mem w hw =>
      obtain ⟨⟨l, α⟩, rfl⟩ := hw
      simp only [Function.uncurry_apply_pair]
      rw [latMorphC_YfullGen_word K L ι c hcoc hK hL hι hKe hLe l α t x, one_smul]
  | zero => simp only [map_zero]; rfl
  | add v w _ _ hv hw =>
      simp only [map_add]
      change latMorphC K L ι c (YfullGen K hKe hK v t x + YfullGen K hKe hK w t x) =
        YfullGen L hLe hL (latMorphC K L ι c v) t (latMorphC K L ι c x)
          + YfullGen L hLe hL (latMorphC K L ι c w) t (latMorphC K L ι c x)
      rw [map_add, hv, hw]
  | smul e v _ hv =>
      simp only [map_smul]
      change latMorphC K L ι c (e • YfullGen K hKe hK v t x) =
        e • YfullGen L hLe hL (latMorphC K L ι c v) t (latMorphC K L ι c x)
      rw [map_smul, hv]

include hK hL hι hKe hLe hcoc in
/-- The mode form: `Φ(u₍ₙ₎v) = (Φu)₍ₙ₎(Φv)`. -/
theorem latMorphC_mode (u : LatModuleGen K) (n : ℤ) (v : LatModuleGen K) :
    latMorphC K L ι c (mode (YfullGen K hKe hK u) n v)
      = mode (YfullGen L hLe hL (latMorphC K L ι c u)) n (latMorphC K L ι c v) := by
  rw [mode_apply, mode_apply]
  exact latMorphC_YfullGen K L ι c hcoc hK hL hι hKe hLe u _ v

include hK hL hι hKe hLe hc0 hcoc in
/-- **`Φ_ι` is a homomorphism of vertex operator algebras** `V_K → V_L`. -/
theorem latMorphC_isVOAHom :
    IsVOAHom (latticeVOAGen K hKe hK) (latticeVOAGen L hLe hL) (latMorphC K L ι c) where
  map_vacuum := latMorphC_vacuum K L ι c hc0
  map_smul u n v := latMorphC_mode K L ι c hcoc hK hL hι hKe hLe u n v

end Vertex

/-! ## §6  Injectivity and the image -/

section Image

open Classical in
theorem coordEα_latStateGen (γ : L.carrier) (p : FockN (rank L)) (α : L.carrier) :
    coordEα L γ (latStateGen L p α) = if γ = α then p else 0 :=
  coordEα_apply L γ α p

theorem latStateGen_zero_boson (α : L.carrier) : latStateGen L 0 α = 0 := by
  rw [latStateGen, TensorProduct.zero_tmul]

theorem isometry_injective (hK : K.PosDef) (hι : ∀ α β, L.form (ι α) (ι β) = K.form α β) :
    Function.Injective ι := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro α hα
  by_contra hne
  have h := hK α hne
  rw [← hι, hα, map_zero] at h
  exact lt_irrefl 0 h

variable (hK : K.PosDef) (hι : ∀ α β, L.form (ι α) (ι β) = K.form α β)

include hK hι in
/-- The momentum-`ιβ` component of `Φ x` is `c(β) φ(x_β)`. -/
theorem coordEα_latMorphC (β : K.carrier) (x : LatModuleGen K) :
    coordEα L (ι β) (latMorphC K L ι c x) = c β • fockMap (oscMatrix K L ι) (coordEα K β x) := by
  have h : (coordEα L (ι β)) ∘ₗ latMorphC K L ι c
      = c β • ((fockMap (oscMatrix K L ι)).toLinearMap ∘ₗ coordEα K β) := by
    refine LinearMap.ext_on_range (latStateGen_span K) fun q => ?_
    obtain ⟨p, α⟩ := q
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
    rw [latMorphC_latStateGen, map_smul, coordEα_latStateGen, coordEα_latStateGen]
    by_cases hb : β = α
    · subst hb; simp
    · rw [if_neg ((isometry_injective K L ι hK hι).ne hb), if_neg hb, map_zero, smul_zero,
        smul_zero]
  have hx := LinearMap.congr_fun h x
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply] using hx

/-- Momenta outside `ι(K)` do not occur in `Φ x`. -/
theorem coordEα_latMorphC_of_not_mem {γ : L.carrier} (hγ : γ ∉ Set.range ι) (x : LatModuleGen K) :
    coordEα L γ (latMorphC K L ι c x) = 0 := by
  have h : (coordEα L γ) ∘ₗ latMorphC K L ι c = 0 := by
    refine LinearMap.ext_on_range (latStateGen_span K) fun q => ?_
    obtain ⟨p, α⟩ := q
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [latMorphC_latStateGen, map_smul, coordEα_latStateGen, if_neg (fun h : γ = ι α => hγ ⟨α, h.symm⟩),
      smul_zero]
  exact LinearMap.congr_fun h x

variable (hL : L.PosDef) (hr : rank K = rank L)

include hK hL hι hr hcne in
/-- **`Φ_ι` is injective**, under the **equal-rank** hypothesis `hr : rank K = rank L` (a design
restriction of this file; the general case `rank K ≤ rank L` is not covered). -/
theorem latMorphC_injective : Function.Injective (latMorphC K L ι c) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine eq_zero_of_coordEα K fun β => ?_
  have h := coordEα_latMorphC K L ι c hK hι β x
  rw [hx, map_zero, eq_comm, smul_eq_zero] at h
  rcases h with h | h
  · exact absurd h (hcne β)
  · have he := (fockEquiv (oscMatrix K L ι) (oscMatrix_transpose_mul K L hK hL ι hι)
      (oscMatrix_mul_transpose K L hK hL ι hι hr)).injective
    exact he (by rw [fockEquiv_apply, h, map_zero])

open Classical in
theorem coordEα_eq_finsuppScalarRight (α : L.carrier) (y : LatModuleGen L) :
    coordEα L α y = TensorProduct.finsuppScalarRight ℂ ℂ (FockN (rank L)) L.carrier y α := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul p f =>
      rw [TensorProduct.finsuppScalarRight_apply_tmul_apply, coordEα, LinearMap.comp_apply,
        LinearMap.lTensor_tmul, Finsupp.lapply_apply, LinearEquiv.coe_coe,
        TensorProduct.rid_tmul]
  | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy]

open Classical in
/-- Every state is the finite sum of its momentum components. -/
theorem eq_sum_coordEα (x : LatModuleGen L) :
    x = ∑ γ ∈ (TensorProduct.finsuppScalarRight ℂ ℂ (FockN (rank L)) L.carrier x).support,
      latStateGen L (coordEα L γ x) γ := by
  classical
  rw [← sub_eq_zero]
  refine eq_zero_of_coordEα L fun δ => ?_
  rw [map_sub, map_sum, sub_eq_zero]
  simp only [coordEα_latStateGen]
  rw [Finset.sum_ite_eq]
  split_ifs with hδ
  · rfl
  · rw [Finsupp.notMem_support_iff, ← coordEα_eq_finsuppScalarRight] at hδ
    exact hδ

open Classical in
include hK hL hι hr hcne in
/-- **The image of `Φ_ι`** is exactly the set of states all of whose momenta lie in `ι(K)`. -/
theorem mem_range_latMorphC_iff (x : LatModuleGen L) :
    x ∈ LinearMap.range (latMorphC K L ι c) ↔ ∀ γ, γ ∉ Set.range ι → coordEα L γ x = 0 := by
  classical
  constructor
  · rintro ⟨y, rfl⟩ γ hγ
    exact coordEα_latMorphC_of_not_mem K L ι c hγ y
  · intro hx
    set Q := oscMatrix K L ι
    have hQQ : Q * Qᵀ = 1 := oscMatrix_mul_transpose K L hK hL ι hι hr
    let β : L.carrier → K.carrier := Function.invFun ι
    refine ⟨∑ γ ∈ (TensorProduct.finsuppScalarRight ℂ ℂ (FockN (rank L)) L.carrier x).support,
      (c (β γ))⁻¹ • latStateGen K (fockMap Qᵀ (coordEα L γ x)) (β γ), ?_⟩
    rw [map_sum]
    conv_rhs => rw [eq_sum_coordEα L x]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [map_smul, latMorphC_latStateGen, smul_smul, inv_mul_cancel₀ (hcne _),
      one_smul, fockMap_comp, hQQ, fockMap_id]
    by_cases hγ : γ ∈ Set.range ι
    · rw [Function.invFun_eq hγ]
    · rw [hx γ hγ, latStateGen_zero_boson, latStateGen_zero_boson]

end Image

/-! ## §7  Compatibility with the involution `θ` and the sign automorphisms -/

section Compat

theorem fockMap_sigmaN {r s : ℕ} (Q : Matrix (Fin s) (Fin r) ℂ) (p : FockN r) :
    fockMap Q (sigmaN r p) = sigmaN s (fockMap Q p) := by
  have h : (fockMap Q).comp (sigmaAlg r) = (sigmaAlg s).comp (fockMap Q) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    obtain ⟨k, a⟩ := v
    rw [AlgHom.comp_apply, AlgHom.comp_apply, sigmaAlg_X, map_neg, fockMap_X, map_sum,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, sigmaAlg_X, smul_neg]
  exact congrArg (fun f : FockN r →ₐ[ℂ] FockN s => f p) h

include hcneg in
/-- **`Φ` commutes with the lattice involutions** when `c(−α) = c(α)`:
`Φ ∘ θ_K = θ_L ∘ Φ` (`φ` commutes with `σ`). -/
theorem latMorphC_thetaLat (x : LatModuleGen K) :
    latMorphC K L ι c (thetaLat K x) = thetaLat L (latMorphC K L ι c x) := by
  have h : (latMorphC K L ι c) ∘ₗ (thetaLat K).toLinearMap
      = (thetaLat L).toLinearMap ∘ₗ latMorphC K L ι c := by
    refine LinearMap.ext_on_range (latStateGen_span K) fun q => ?_
    obtain ⟨p, α⟩ := q
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [thetaLat_latStateGen, latMorphC_latStateGen, latMorphC_latStateGen, map_smul,
      thetaLat_latStateGen, hcneg, map_neg]
    rw [fockMap_sigmaN]
  exact LinearMap.congr_fun h x

/-- **`Φ_ι` intertwines the sign automorphisms**: `Φ_ι ∘ g_{χ∘ι} = g_χ ∘ Φ_ι`. -/
theorem latMorphC_chiLat (χ : L.carrier →+ ZMod 2) (x : LatModuleGen K) :
    latMorphC K L ι c (chiLat K (χ.comp ι.toAddMonoidHom) x) = chiLat L χ (latMorphC K L ι c x) := by
  have h : (latMorphC K L ι c) ∘ₗ (chiLat K (χ.comp ι.toAddMonoidHom)).toLinearMap
      = (chiLat L χ).toLinearMap ∘ₗ latMorphC K L ι c := by
    refine LinearMap.ext_on_range (latStateGen_span K) fun q => ?_
    obtain ⟨p, α⟩ := q
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [chiLat_latStateGen, map_smul, latMorphC_latStateGen, map_smul, chiLat_latStateGen,
      smul_comm]
    rfl
  exact LinearMap.congr_fun h x

end Compat

/-! ## §8  The isometry morphism `Φ_ι` (with the comparison coboundary `c = latCob`) -/

section Isometry

/-- **The lattice-VOA morphism of an isometry** `Φ_ι(p ⊗ e^α) = c(α) · φ(p) ⊗ e^{ια}`, with the
cocycle-comparison coboundary `c = latCob K L ι` (`LatticeMorphFock.lean`). -/
noncomputable def latMorph : LatModuleGen K →ₗ[ℂ] LatModuleGen L := latMorphC K L ι (latCob K L ι)

theorem latMorph_latStateGen (p : FockN (rank K)) (α : K.carrier) :
    latMorph K L ι (latStateGen K p α)
      = latCob K L ι α • latStateGen L (fockMap (oscMatrix K L ι) p) (ι α) :=
  latMorphC_latStateGen K L ι _ p α

variable (hK : K.PosDef) (hL : L.PosDef) (hι : ∀ α β, L.form (ι α) (ι β) = K.form α β)
  (hKe : K.Even) (hLe : L.Even) (hr : rank K = rank L)

theorem latMorph_vacuum : latMorph K L ι (latVacuumGen K) = latVacuumGen L :=
  latMorphC_vacuum K L ι _ (latCob_zero K L ι)

include hK hL hι hr in
theorem latMorph_omega : latMorph K L ι (omegaLatGen K) = omegaLatGen L :=
  latMorphC_omega K L ι _ (latCob_zero K L ι) hK hL hι hr

include hK hL hι hKe hLe in
/-- `Φ_ι(u₍ₙ₎v) = (Φ_ι u)₍ₙ₎(Φ_ι v)`. -/
theorem latMorph_mode (u : LatModuleGen K) (n : ℤ) (v : LatModuleGen K) :
    latMorph K L ι (mode (YfullGen K hKe hK u) n v)
      = mode (YfullGen L hLe hL (latMorph K L ι u)) n (latMorph K L ι v) :=
  latMorphC_mode K L ι _ (latticeCocycle_map_mul_latCob K L hKe hLe ι hι) hK hL hι hKe hLe u n v

include hK hL hι hKe hLe in
/-- **`Φ_ι : V_K → V_L` is a homomorphism of vertex operator algebras.** -/
theorem latMorph_isVOAHom :
    IsVOAHom (latticeVOAGen K hKe hK) (latticeVOAGen L hLe hL) (latMorph K L ι) :=
  latMorphC_isVOAHom K L ι _ (latCob_zero K L ι) (latticeCocycle_map_mul_latCob K L hKe hLe ι hι)
    hK hL hι hKe hLe

include hK hL hι hr in
/-- **`Φ_ι` is injective**, under the **equal-rank** hypothesis `hr : rank K = rank L` (a design
restriction; the general case `rank K ≤ rank L` is not covered). -/
theorem latMorph_injective : Function.Injective (latMorph K L ι) :=
  latMorphC_injective K L ι _ (latCob_ne_zero K L ι) hK hι hL hr

include hK hι in
theorem coordEα_latMorph (β : K.carrier) (x : LatModuleGen K) :
    coordEα L (ι β) (latMorph K L ι x)
      = latCob K L ι β • fockMap (oscMatrix K L ι) (coordEα K β x) :=
  coordEα_latMorphC K L ι _ hK hι β x

include hK hL hι hr in
/-- **The image of `Φ_ι`** = the states all of whose momenta lie in `ι(K)`. -/
theorem mem_range_latMorph_iff (x : LatModuleGen L) :
    x ∈ LinearMap.range (latMorph K L ι) ↔ ∀ γ, γ ∉ Set.range ι → coordEα L γ x = 0 :=
  mem_range_latMorphC_iff K L ι _ (latCob_ne_zero K L ι) hK hι hL hr x

/-- **`Φ_ι ∘ θ_K = θ_L ∘ Φ_ι`** — no correction, as `c(−α) = c(α)`. -/
theorem latMorph_thetaLat (x : LatModuleGen K) :
    latMorph K L ι (thetaLat K x) = thetaLat L (latMorph K L ι x) :=
  latMorphC_thetaLat K L ι _ (latCob_neg K L ι) x

/-- `Φ_ι ∘ g_{χ∘ι} = g_χ ∘ Φ_ι`. -/
theorem latMorph_chiLat (χ : L.carrier →+ ZMod 2) (x : LatModuleGen K) :
    latMorph K L ι (chiLat K (χ.comp ι.toAddMonoidHom) x) = chiLat L χ (latMorph K L ι x) :=
  latMorphC_chiLat K L ι _ χ x

end Isometry

/-! ## §9  Complex-character automorphisms `e^α ↦ d(α) e^α` -/

section Character

theorem latMatrix_id : latMatrix L L LinearMap.id = 1 := by
  ext j i
  simp only [latMatrix, Matrix.of_apply, LinearMap.id_apply, coordR, coord, Module.Basis.repr_self,
    Matrix.one_apply, Finsupp.single_apply]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

theorem oscMatrix_id (hL : L.PosDef) : oscMatrix L L LinearMap.id = 1 := by
  rw [oscMatrix, frameMatrix, latMatrix_id, Matrix.mul_one,
    Matrix.mul_nonsing_inv _ (frame_det_isUnit L hL), Matrix.map_one _ (by simp) (by simp),
    Matrix.submatrix_one_equiv]

variable (d : L.carrier →+ Additive ℂˣ)

/-- The complex value `d(α) ∈ ℂˣ` of an additive character. -/
noncomputable def charVal (α : L.carrier) : ℂ := ((Additive.toMul (d α) : ℂˣ) : ℂ)

theorem charVal_zero : charVal L d 0 = 1 := by simp [charVal]

theorem charVal_add (α β : L.carrier) : charVal L d (α + β) = charVal L d α * charVal L d β := by
  simp [charVal]

theorem charVal_ne_zero (α : L.carrier) : charVal L d α ≠ 0 := Units.ne_zero _

theorem charVal_neg_mul (α : L.carrier) : charVal L d (-α) * charVal L d α = 1 := by
  rw [← charVal_add, neg_add_cancel, charVal_zero]

/-- The character map `g_d(p ⊗ e^α) = d(α) p ⊗ e^α` (as `latMorphC` of the identity isometry). -/
noncomputable def charLat : LatModuleGen L →ₗ[ℂ] LatModuleGen L :=
  latMorphC L L LinearMap.id (charVal L d)

theorem charLat_latStateGen (hL : L.PosDef) (p : FockN (rank L)) (α : L.carrier) :
    charLat L d (latStateGen L p α) = charVal L d α • latStateGen L p α := by
  rw [charLat, latMorphC_latStateGen, oscMatrix_id L hL, fockMap_id]
  rfl

theorem charLat_comp (hL : L.PosDef) (d' : L.carrier →+ Additive ℂˣ) (x : LatModuleGen L) :
    charLat L d (charLat L d' x) = charLat L (d + d') x := by
  have h : (charLat L d) ∘ₗ (charLat L d') = charLat L (d + d') := by
    refine LinearMap.ext_on_range (latStateGen_span L) fun q => ?_
    obtain ⟨p, α⟩ := q
    simp only [LinearMap.comp_apply]
    rw [charLat_latStateGen L d' hL, map_smul, charLat_latStateGen L d hL,
      charLat_latStateGen L (d + d') hL, smul_smul]
    congr 1
    simp [charVal, mul_comm]
  exact LinearMap.congr_fun h x

theorem charLat_zero (hL : L.PosDef) (x : LatModuleGen L) : charLat L 0 x = x := by
  have h : charLat L 0 = LinearMap.id := by
    refine LinearMap.ext_on_range (latStateGen_span L) fun q => ?_
    obtain ⟨p, α⟩ := q
    rw [charLat_latStateGen L 0 hL, LinearMap.id_apply]
    simp [charVal]
  rw [h, LinearMap.id_apply]

variable (hEven : L.Even) (hPos : L.PosDef)

/-- **The character automorphism** `g_d ∈ Aut(V_L)`, `e^α ↦ d(α) e^α`, for any additive
character `d : L → ℂˣ` (generalising `chiAut`, which is the case `d = (−1)^χ`). -/
noncomputable def charAut : Aut (latticeVOAGen L hEven hPos) where
  toLinearEquiv := LinearEquiv.ofLinear (charLat L d) (charLat L (-d))
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [charLat_comp L d hPos, add_neg_cancel, charLat_zero L hPos])
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [charLat_comp L (-d) hPos, neg_add_cancel, charLat_zero L hPos])
  map_smul' u n v :=
    latMorphC_mode L L LinearMap.id (charVal L d)
      (fun α β => by simp only [LinearMap.id_apply]; rw [charVal_add])
      hPos hPos (fun _ _ => rfl) hEven hEven u n v
  map_vacuum := latMorphC_vacuum L L LinearMap.id _ (charVal_zero L d)
  map_omega := latMorphC_omega L L LinearMap.id _ (charVal_zero L d) hPos hPos (fun _ _ => rfl) rfl

@[simp] theorem charAut_apply (x : LatModuleGen L) : charAut L d hEven hPos x = charLat L d x := rfl

include hPos in
/-- **Conjugating `θ` by a character**: `g_e θ g_e⁻¹ = g_{2e} θ`. -/
theorem charLat_thetaLat_conj (e : L.carrier →+ Additive ℂˣ) (x : LatModuleGen L) :
    charLat L e (thetaLat L (charLat L (-e) x)) = charLat L (2 • e) (thetaLat L x) := by
  have h : (charLat L e) ∘ₗ (thetaLat L).toLinearMap ∘ₗ (charLat L (-e))
      = (charLat L (2 • e)) ∘ₗ (thetaLat L).toLinearMap := by
    refine LinearMap.ext_on_range (latStateGen_span L) fun q => ?_
    obtain ⟨p, α⟩ := q
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [charLat_latStateGen L _ hPos, map_smul, thetaLat_latStateGen, map_smul,
      charLat_latStateGen L _ hPos, charLat_latStateGen L _ hPos, smul_smul]
    congr 1
    simp only [charVal, map_neg, AddMonoidHom.neg_apply, AddMonoidHom.smul_apply, toMul_neg,
      toMul_nsmul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    have h1 := Units.ne_zero (Additive.toMul (e α))
    field_simp
  exact LinearMap.congr_fun h x

/-- Every additive character `d : L → ℂˣ` of a free lattice has a square root: `d = 2 • e`. -/
theorem exists_half_char : ∃ e : L.carrier →+ Additive ℂˣ, 2 • e = d := by
  have hsq : ∀ u : ℂˣ, ∃ v : ℂˣ, v ^ 2 = u := by
    intro u
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : ℂ) (by norm_num : 0 < 2)
    have hz0 : z ≠ 0 := by
      rintro rfl; rw [zero_pow two_ne_zero] at hz; exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simp [hz])⟩
  choose sq hsq using hsq
  let B := latticeBasis L
  let e : L.carrier →ₗ[ℤ] Additive ℂˣ :=
    B.constr ℤ (fun i => Additive.ofMul (sq (Additive.toMul (d (B i)))))
  refine ⟨e.toAddMonoidHom, ?_⟩
  have h : (2 • e : L.carrier →ₗ[ℤ] Additive ℂˣ) = d.toIntLinearMap := by
    refine B.ext fun i => ?_
    rw [LinearMap.smul_apply, Module.Basis.constr_basis]
    change (2 : ℕ) • Additive.ofMul (sq (Additive.toMul (d (B i)))) = d (B i)
    rw [← ofMul_pow, hsq]
    rfl
  exact AddMonoidHom.ext fun α => LinearMap.congr_fun h α

end Character

end VOA.LatGen
