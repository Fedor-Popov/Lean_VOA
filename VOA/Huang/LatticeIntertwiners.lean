/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.Intertwining
import VOA.Classification.COne.LatticeModulesIrred

/-!
# Lattice intertwining operators among the `V_{L+λ}`

For the rank-one lattice VOA `V_{2m} = V_L`, `L = √(2m)ℤ = ℤα`, and its modules
`V_{L+λ_j} = latticeModule m hm j` (`λ_j = j/(2m)·α`), we construct for **every** `j, k ∈ ℤ` a
nonzero intertwining operator of type `(V_{L+λ_{j+k}} / V_{L+λ_j} V_{L+λ_k})` in the sense of
Frenkel–Huang–Lepowsky (`IsIntertwiningOperator`: truncation, `L₋₁`-derivative, full Jacobi
identity), namely the Dong–Lepowsky generalized vertex operator
`𝒴(e^{λ_j}, z) = E⁻(−λ_j,z) E⁺(−λ_j,z) e_{λ_j} z^{λ_j(0)}`, with its fractional powers
`z^{⟨λ_j, λ_k + β⟩}` carried by the `ℂ`-indexed modes of `IntertwiningModes`.

## Route: a common gluing lattice and a transverse projection

The Jacobi identity for generalized vertex operators is *not* proved from scratch.  Instead:

* All three modules are realised in the **same** even positive-definite lattice
  `N = N_{m,1} = ℤα ⊕ ℤδ` (`glueLat m 1`), with glue vectors `δ_j = j·δ`, `δ_k = k·δ`,
  `δ_j + δ_k` (`glueJ`): `V_{L+λ}` sits inside `V_N` as the image of `Ψ_δ = shiftEmb`.
* The **projection** `Ψ_δ⁻¹ = shiftEmbInv` (the algebra map `fockMap Oᵀ` on oscillators, which
  kills the oscillators transverse to `ι(L)`, together with the momentum restriction) intertwines
  the full `V_L`-action on **all** of `V_N` with the module action (`proj_intertw`): checked on the
  generators `e^β` through the projected boson dressing `fockMapT_EEVec` (an oscillator
  intertwining *without* orthogonality, `fockMap_oscComb'`) and propagated to all of `V_L` by
  generation (`latVOA_generated`, `intertw_smul`).
* The integral modes `Z_k(w₁,w₂) = Ψ_{δ_j+δ_k}⁻¹ (Ψ_{δ_j}w₁)₍ₖ₎ (Ψ_{δ_k}w₂)` (`Zmode`) then
  satisfy the Jacobi identity by applying `Ψ⁻¹` to the **VOA** Jacobi identity of `V_N`
  (`Zmode_jacobi`): no non-integral exponent ever appears in a Jacobi sum.
* The exponents of `Y_N(e^{δ_j},z) e^{δ_k+β}` are `⟨δ_j, δ_k+β⟩ ∈ ℤ`; they differ from the
  fractional `⟨λ_j, λ_k+β⟩` by the **transverse pairing** `s = ⟨ν(δ_j), δ_k⟩` (`sval`,
  `sval_eq : s = ⟨δ_j,δ_k⟩ − ⟨λ_j,λ_k⟩`), `ν = (1 − OOᵀ)·δ` (`nuV`, `Pp`).  The intertwiner is
  `𝒴(w₁,z) = z^{-s} Σ_k Z_k z^{-k-1}`: `(w₁)₍ₖ₊ₛ₎ = Z_k`, and modes off `s + ℤ` vanish (`latIntw`).
* **`L₋₁`-derivative.**  `L₋₁` of `V_N` splits on `im Ψ_{δ_j}` as
  `L₋₁^N = (Φω_L)₍₀₎ + h₍₋₁₎` with `h = ν(-1)𝟙` the transverse Heisenberg state
  (`smul_latMorph_omega_shiftEmb`, from the field identity `Y(ω_N) − Y(Φω_L) = ½Σ_d :γ_d γ_d:`,
  `Y_omega_sub`, with `γ_d = Σ_c P_{dc} h_c` the transverse currents).  By the `ℓ = −1` Jacobi
  identity, `Ψ⁻¹ (h₍₋₁₎x)₍ₖ₎ Ψ_{δ_k}w = s · Ψ⁻¹ x₍ₖ₋₁₎ Ψ_{δ_k}w` (`proj_iterate_hState`:
  transverse creators are killed by `Ψ⁻¹`, transverse annihilators kill `im Ψ_{δ_k}`, the zero mode
  is `s`), so `Z_k(L₋₁w₁, w₂) = −(k+s) Z_{k−1}(w₁,w₂)` (`Zmode_L_neg_one`), which is exactly
  `(L₋₁w₁)₍ₙ₎ = −n (w₁)₍ₙ₋₁₎` at `n = k + s`.
* Finally the modules in `N_{m,1}` are identified with `latticeModule j` (built in `N_{m,j}`) by
  explicit cocycle rescalings `p ⊗ e^{nα} ↦ d(n) p ⊗ e^{nα}` (`isoE`, `isoE_intertw`, via the
  general cocycle formula `kappa_gen`), and intertwiners are transported along module
  isomorphisms (`IsIntertwiningW.transport`).

## Main declarations
* `IsIntertwiningW` — the FHL axioms for weak modules; `IsIntertwiningW.toIsIntertwiningOperator`,
  `IsIntertwiningW.transport` (along isomorphisms), `transportModes_ne_zero`.
* `proj_intertw` — `Ψ_δ⁻¹ ∘ Y_N(Φu,z) = Y_{V_{K+λ}}(u,z) ∘ Ψ_δ⁻¹` on all of `V_N` (general `K ↪ N`).
* `latIntw`, `isIntertwiningW_latIntw`, `latIntw_vacuum`, `latIntw_ne_zero` — the construction
  for a general isometric embedding `K ↪ N` of even positive-definite lattices and any `δ₁, δ₂ ∈ N`.
* `isIntertwiningOperator_latticeIntwModes m hm j k`, `latticeIntertwiner m hm j k`,
  `latticeIntertwiner_ne_zero`, the `Nontrivial` instance on
  `IntertwiningOperator (latticeModule j) (latticeModule k) (latticeModule (j+k))`.
* `latticeIntwModes_leading_ne_zero` — the leading coefficient
  `(e^{λ_j})₍₋ⱼₖ/₂ₘ₋₁₎ e^{λ_k} ≠ 0`: the operator really carries `z^{jk/(2m)}`.
* `one_le_fusionRule_latticeModule` — `N^{λ_{j+k}}_{λ_j λ_k} ≥ 1`, **given** finite-dimensionality
  of the intertwiner space.

## Not done here
* **Finite-dimensionality** of the space
  `intertwiningSpace (latticeModule j) (latticeModule k) (latticeModule l)` (needed for
  `fusionRule` to be meaningful; `Module.finrank` is `0` on infinite-dimensional spaces).
  It needs the `L₀`-conjugation formula (support of `𝒴` in one coset `h₁+h₂−h₃+ℤ`),
  and a bound such as Frenkel–Zhu `A(M)`-bimodules or the lowest-weight-space injection
  `𝒴 ↦ (top of M₁) ⊗ (top of M₂) → (top of M₃)^*`.
* The **vanishing** `N^{λ_l}_{λ_j λ_k} = 0` for `l ≢ j+k (mod 2m)` (an `α(0)`-charge argument via
  the commutator formula), and `N = 1` exactly (the upper bound is the finite-dimensionality step).

## Status
No `sorry`, no new axioms.  Unconditional: the only hypothesis is `1 ≤ m`.
-/

set_option linter.style.longLine false

namespace VOA.Huang.LatInt

open VOA VOA.IntegralLattice VOA.LatGen HeisenbergN MvPolynomial
open Module (End)
open scoped BigOperators TensorProduct Matrix

section FockProj

variable {r s : ℕ} (Q : Matrix (Fin s) (Fin r) ℂ)

/-- Oscillator combinations through `fockMap Q` **without** orthogonality: creation modes need
`Q u = v`, annihilation modes (chain rule) need `Qᵀ v = u`. -/
theorem fockMap_oscComb' (u : Fin r → ℂ) (v : Fin s → ℂ) (huv : Q *ᵥ u = v)
    (hvu : Qᵀ *ᵥ v = u) (k : ℂ) (n : ℤ) (p : FockN r) :
    fockMap Q ((∑ a : Fin r, u a • oscN r k a n) p)
      = (∑ b : Fin s, v b • oscN s k b n) (fockMap Q p) := by
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
  rcases lt_trichotomy n 0 with hn | hn | hn
  · simp only [oscN_apply_neg _ k _ hn]
    simp only [← smul_mul_assoc, ← Finset.sum_mul, map_mul]
    rw [fockMap_Xcomb Q u v huv]
  · subst hn; simp
  · simp only [oscN_apply_pos _ k _ hn, fockMap_pderiv, map_sum, map_smul, Finset.smul_sum,
      smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hu : u a = ∑ b : Fin s, v b * Q b a := by
      rw [← hvu, Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun b _ => by rw [Matrix.transpose_apply, mul_comm]
    rw [← Finset.sum_smul]
    congr 1
    rw [hu, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

end FockProj

section ProjEE

variable (K N : IntegralLattice.{0}) (ι : K.carrier →ₗ[ℤ] N.carrier)
  (hK : K.PosDef) (hN : N.PosDef) (hι : ∀ α β, N.form (ι α) (ι β) = K.form α β)

/-- The projection matrix `Oᵀ` (frames of `N` to frames of `K`). -/
noncomputable abbrev OT : Matrix (Fin (rank K)) (Fin (rank N)) ℂ := (oscMatrix K N ι)ᵀ

include hK hN hι in
theorem OT_mulVec_chargeCoord (β : K.carrier) :
    OT K N ι *ᵥ chargeCoord N (ι β) = chargeCoord K β := by
  funext a
  rw [← oscMatrix_transpose_chargeCoord K N ι hK hN hι β a]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

include hK in
theorem OT_transpose_mulVec_chargeCoord (β : K.carrier) :
    (OT K N ι)ᵀ *ᵥ chargeCoord K β = chargeCoord N (ι β) := by
  rw [Matrix.transpose_transpose]
  exact oscMatrix_chargeCoord K N hK ι β

include hK hN hι in
theorem fockMapT_vVar (β : K.carrier) (m : ℕ) :
    fockMap (OT K N ι) (vVar N (ι β) m) = vVar K β m :=
  fockMap_Xcomb _ (chargeCoord N (ι β)) (chargeCoord K β) (OT_mulVec_chargeCoord K N ι hK hN hι β) m

include hK hN hι in
theorem fockMapT_vSchur (β : K.carrier) (M : ℕ) :
    fockMap (OT K N ι) (vSchur N (ι β) M) = vSchur K β M := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    match M with
    | 0 => rw [vSchur_zero, vSchur_zero, fockMap_one]
    | (M+1) =>
      rw [vSchur_succ, vSchur_succ, map_smul, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [fockMap_mul, fockMapT_vVar K N ι hK hN hι, ih (M - j) (by simp at hj; omega)]

include hK hN hι in
theorem fockMapT_chargeOsc (β : K.carrier) (j : ℤ) (p : FockN (rank N)) :
    fockMap (OT K N ι) (chargeOsc N (ι β) j p) = chargeOsc K β j (fockMap (OT K N ι) p) :=
  fockMap_oscComb' _ (chargeCoord N (ι β)) (chargeCoord K β)
    (OT_mulVec_chargeCoord K N ι hK hN hι β) (OT_transpose_mulVec_chargeCoord K N ι hK β) 1 j p

include hK hN hι in
theorem fockMapT_aExpVec (β : K.carrier) (M : ℕ) (p : FockN (rank N)) :
    fockMap (OT K N ι) (aExpVec N (ι β) M p) = aExpVec K β M (fockMap (OT K N ι) p) := by
  induction M using Nat.strong_induction_on generalizing p with
  | _ M ih =>
    match M with
    | 0 => rw [aExpVec_zero, aExpVec_zero, LinearMap.id_apply, LinearMap.id_apply]
    | (M+1) =>
      rw [aExpVec_succ, aExpVec_succ, LinearMap.smul_apply, LinearMap.smul_apply, map_smul,
        LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.neg_apply,
        map_neg, fockMapT_chargeOsc K N ι hK hN hι, ih (M - j) (by simp at hj; omega)]

include hK hN hι in
theorem fockMapT_EEVec (β : K.carrier) :
    IntertwH (fockMap (OT K N ι)).toLinearMap 1 (EEVec N (ι β)) (EEVec K β) := by
  have hm : IntertwH (fockMap (OT K N ι)).toLinearMap 1 (EminusVecField N (ι β))
      (EminusVecField K β) := by
    intro t x
    rw [one_smul, EminusVecField_apply, EminusVecField_apply]
    split_ifs
    · rw [EminusVec, EminusVec, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply,
        AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, fockMap_mul,
        fockMapT_vSchur K N ι hK hN hι]
    · rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
  have hp : IntertwH (fockMap (OT K N ι)).toLinearMap 1 (EplusVecField N (ι β))
      (EplusVecField K β) := by
    intro t x
    rw [one_smul, EplusVecField_apply, EplusVecField_apply]
    split_ifs
    · rw [AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, fockMapT_aExpVec K N ι hK hN hι]
    · rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
  have h := IntertwH.nprod (EminusVecField_isField N (ι β)) (EplusVecField_isField N (ι β))
    (EminusVecField_isField K β) (EplusVecField_isField K β) hm hp
  rwa [mul_one] at h

end ProjEE


/-! ## §2  Generic: intertwining is closed under `n`-th products, for any linear map -/

section Closure

variable {𝒱 : Type} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']

/-- Finite support of the `m = 0` Jacobi summand of a weak module. -/
theorem jacobiZero_support_finite (A : WeakModule W M) (u v : 𝒱) (x : M) (n t : ℤ) :
    (Function.support (fun i : ℤ => (negOnePow i * cbz n i) •
      (mode (A.YM u) (n + 0 - i) (mode (A.YM v) (t + i) x)
        - negOnePow n • mode (A.YM v) (n + t - i) (mode (A.YM u) (0 + i) x)))).Finite := by
  obtain ⟨N₁, hN₁⟩ := A.truncation v x
  obtain ⟨N₂, hN₂⟩ := A.truncation u x
  refine (Set.finite_Ico (0 : ℤ) (max (N₁ - t) N₂)).subset (fun i hi => ?_)
  simp only [Function.mem_support] at hi
  simp only [Set.mem_Ico]
  by_contra hcon
  apply hi
  rcases lt_or_ge i 0 with hneg | hnn
  · simp [cbz_apply_neg n hneg]
  · have hge : max (N₁ - t) N₂ ≤ i := by
      by_contra h; exact hcon ⟨hnn, not_le.mp h⟩
    have h1 : mode (A.YM v) (t + i) x = 0 := hN₁ _ (by have := le_trans (le_max_left _ _) hge; omega)
    have h2 : mode (A.YM u) (0 + i) x = 0 := hN₂ _ (by have := le_trans (le_max_right _ _) hge; omega)
    simp only [h1, h2, map_zero, smul_zero, sub_zero]

/-- If a linear map (not necessarily injective) intertwines the modes of `u` and `v`, it
intertwines the modes of every product `u₍ₙ₎v`. -/
theorem intertw_smul (A : WeakModule W M) (B : WeakModule W M') (e : M →ₗ[ℂ] M') {u v : 𝒱}
    (hu : ∀ (k : ℤ) (x : M), e (mode (A.YM u) k x) = mode (B.YM u) k (e x))
    (hv : ∀ (k : ℤ) (x : M), e (mode (A.YM v) k x) = mode (B.YM v) k (e x)) (n t : ℤ) (x : M) :
    e (mode (A.YM (W.smul u n v)) t x) = mode (B.YM (W.smul u n v)) t (e x) := by
  rw [Classification.COne.LatMod.jacobi_zero A u v x n t,
    Classification.COne.LatMod.jacobi_zero B u v (e x) n t,
    map_finsum e (jacobiZero_support_finite A u v x n t)]
  refine finsum_congr fun i => ?_
  rw [map_smul, map_sub, map_smul, hu, hv, hv, hu]

end Closure

/-! ## §3  The projection `Ψ_δ⁻¹ : V_N → V_K` intertwines the full `V_K`-action -/

section Proj

variable (K N : IntegralLattice.{0}) (ι : K.carrier →ₗ[ℤ] N.carrier) (δ : N.carrier)
  (hKe : K.Even) (hK : K.PosDef) (hNe : N.Even) (hN : N.PosDef)
  (hι : ∀ α β, N.form (ι α) (ι β) = K.form α β)

open Classification.COne Classification.COne.LatMod

include hK hι in
theorem shiftEmbInv_latStateGen_of (q : FockN (rank N)) (γ : K.carrier) :
    shiftEmbInv K N ι δ (latStateGen N q (ι γ + δ)) = latStateGen K (fockMap (OT K N ι) q) γ := by
  rw [shiftEmbInv, latStateGen, TensorProduct.map_tmul, momShiftInv, eGen,
    Finsupp.linearCombination_single, one_smul]
  have hex : ∃ γ', ι γ' + δ = ι γ + δ := ⟨γ, rfl⟩
  rw [dif_pos hex]
  have hch : hex.choose = γ := by
    have := hex.choose_spec
    exact isometry_injective K N ι hK hι (add_right_cancel this)
  rw [hch]
  rfl

theorem shiftEmbInv_latStateGen_of_not (q : FockN (rank N)) (η : N.carrier)
    (h : ∀ γ : K.carrier, ι γ + δ ≠ η) :
    shiftEmbInv K N ι δ (latStateGen N q η) = 0 := by
  rw [shiftEmbInv, latStateGen, TensorProduct.map_tmul, momShiftInv, eGen,
    Finsupp.linearCombination_single, one_smul]
  rw [dif_neg (not_exists.mpr h), TensorProduct.tmul_zero]

/-- `V_N` as a weak `V_K`-module through `Φ = latMorph` (restriction of the adjoint module). -/
noncomputable def resModule : WeakModule (latticeVOAGen K hKe hK) (LatModuleGen N) :=
  transportWeakModule (latMorph_isVOAHom K N ι hK hN hι hKe hNe) (Ψ := LinearMap.id)
    (Ψ' := LinearMap.id) (fun _ => rfl) (fun _ _ _ => ⟨_, rfl⟩)

theorem resModule_YM (u : LatModuleGen K) (t : ℤ) (x : LatModuleGen N) :
    (resModule K N ι hKe hK hNe hN hι).YM u t x = (latticeVOAGen N hNe hN).Y (latMorph K N ι u) t x :=
  rfl

include hK hN hι in
theorem proj_latChargeGen (β : K.carrier) (t : ℤ) (x : LatModuleGen N) :
    shiftEmbInv K N ι δ ((latticeVOAGen N hNe hN).Y (latMorph K N ι (latChargeGen K β)) t x)
      = (shiftWeakModule K N ι δ hKe hK hNe hN hι).YM (latChargeGen K β) t
          (shiftEmbInv K N ι δ x) := by
  have hext : (shiftEmbInv K N ι δ) ∘ₗ
        (latticeVOAGen N hNe hN).Y (latMorph K N ι (latChargeGen K β)) t
      = (shiftWeakModule K N ι δ hKe hK hNe hN hι).YM (latChargeGen K β) t ∘ₗ
        (shiftEmbInv K N ι δ) := by
    refine LinearMap.ext_on_range (latStateGen_span N) fun qη => ?_
    obtain ⟨q, η⟩ := qη
    simp only [LinearMap.comp_apply]
    rw [latMorph, latMorphC_latChargeGen, map_smul, latVOA_Y_latChargeGen N hNe hN]
    change shiftEmbInv K N ι δ (latCob K N ι β • Yeαvec N (ι β) t (latStateGen N q η)) = _
    rw [Yeαvec_tmul]
    by_cases hη : ∃ γ : K.carrier, ι γ + δ = η
    · obtain ⟨γ, rfl⟩ := hη
      rw [shiftEmbInv_latStateGen_of K N ι δ hK hι, shiftWeakModule_latChargeGen,
        show ι β + (ι γ + δ) = ι (β + γ) + δ by rw [map_add, add_assoc], map_smul, map_smul,
        shiftEmbInv_latStateGen_of K N ι δ hK hι, smul_smul]
      have hE := fockMapT_EEVec K N ι hK hN hι β (t - N.form (ι β) (ι γ + δ)) q
      rw [one_smul] at hE
      simp only [AlgHom.toLinearMap_apply] at hE
      rw [hE, show t - N.form (ι β) (ι γ + δ) = t - K.form β γ - N.form (ι β) δ by
        rw [map_add, hι]; ring]
    · have hη' : ∀ γ : K.carrier, ι γ + δ ≠ η := fun γ h => hη ⟨γ, h⟩
      have hη2 : ∀ γ : K.carrier, ι γ + δ ≠ ι β + η := fun γ h =>
        hη ⟨γ - β, by rw [map_sub, sub_add_eq_add_sub, h]; abel⟩
      rw [map_smul, map_smul, shiftEmbInv_latStateGen_of_not K N ι δ _ _ hη2,
        shiftEmbInv_latStateGen_of_not K N ι δ _ _ hη', map_zero, smul_zero, smul_zero]
  exact LinearMap.congr_fun hext x

include hK hN hι in
/-- **The projection intertwines**: `Ψ_δ⁻¹ ∘ Y_N(Φu, z) = Y_{V_{K+λ}}(u, z) ∘ Ψ_δ⁻¹` on all of
`V_N`, for every `u ∈ V_K` (generation by the `e^β`). -/
theorem proj_intertw (u : LatModuleGen K) (t : ℤ) (x : LatModuleGen N) :
    shiftEmbInv K N ι δ ((latticeVOAGen N hNe hN).Y (latMorph K N ι u) t x)
      = (shiftWeakModule K N ι δ hKe hK hNe hN hι).YM u t (shiftEmbInv K N ι δ x) := by
  set A := resModule K N ι hKe hK hNe hN hι
  set B := shiftWeakModule K N ι δ hKe hK hNe hN hι
  let S : Submodule ℂ (LatModuleGen K) :=
    { carrier := {u | ∀ (k : ℤ) (x : LatModuleGen N),
        shiftEmbInv K N ι δ (mode (A.YM u) k x) = mode (B.YM u) k (shiftEmbInv K N ι δ x)}
      add_mem' := fun {u v} hu hv k x => by
        simp only [Set.mem_setOf_eq, map_add, mode_add, LinearMap.add_apply] at hu hv ⊢
        rw [hu, hv]
      zero_mem' := fun k x => by simp
      smul_mem' := fun c u hu k x => by
        simp only [Set.mem_setOf_eq, map_smul, mode_smul, LinearMap.smul_apply] at hu ⊢
        rw [hu] }
  have htop : S = ⊤ := by
    refine latVOA_generated K hKe hK S (fun u hu v hv n => ?_) (fun β => ?_)
    · exact fun k x => intertw_smul A B (shiftEmbInv K N ι δ) hu hv n k x
    · intro k x
      rw [mode_apply, mode_apply]
      exact proj_latChargeGen K N ι δ hKe hK hNe hN hι β _ x
  have hu : u ∈ S := by rw [htop]; trivial
  have h := hu (-t - 1) x
  rw [mode_apply, mode_apply, show -(-t - 1) - 1 = t by ring] at h
  exact h

end Proj


/-! ## §4  The orthogonal complement of `ι(K)` in the oscillator frame of `N` -/

section Perp

variable (K N : IntegralLattice.{0}) (ι : K.carrier →ₗ[ℤ] N.carrier)
  (hK : K.PosDef) (hN : N.PosDef) (hι : ∀ α β, N.form (ι α) (ι β) = K.form α β)

/-- The orthogonal projection `P = 1 - O Oᵀ` onto the complement of `ι(K) ⊗ ℂ` (frame coordinates). -/
noncomputable def Pp : Matrix (Fin (rank N)) (Fin (rank N)) ℂ :=
  1 - oscMatrix K N ι * (oscMatrix K N ι)ᵀ

include hK hN hι in
theorem Pp_mul_O : Pp K N ι * oscMatrix K N ι = 0 := by
  rw [Pp, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
    oscMatrix_transpose_mul K N hK hN ι hι, Matrix.mul_one, sub_self]

theorem Pp_transpose : (Pp K N ι)ᵀ = Pp K N ι := by
  rw [Pp, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
    Matrix.transpose_transpose]

include hK hN hι in
theorem OT_mul_Pp : (oscMatrix K N ι)ᵀ * Pp K N ι = 0 := by
  rw [← Pp_transpose K N ι, ← Matrix.transpose_mul, Pp_mul_O K N ι hK hN hι,
    Matrix.transpose_zero]

include hK hN hι in
theorem Pp_mul_Pp : Pp K N ι * Pp K N ι = Pp K N ι := by
  rw [show Pp K N ι * Pp K N ι = (1 - oscMatrix K N ι * (oscMatrix K N ι)ᵀ) * Pp K N ι from rfl,
    Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, OT_mul_Pp K N ι hK hN hι,
    Matrix.mul_zero, sub_zero]

/-- The frame coordinates of the component of `δ` orthogonal to `ι(K)`. -/
noncomputable def nuV (δ : N.carrier) : Fin (rank N) → ℂ := Pp K N ι *ᵥ chargeCoord N δ

include hK hN hι in
theorem OT_mulVec_nuV (δ : N.carrier) : (oscMatrix K N ι)ᵀ *ᵥ nuV K N ι δ = 0 := by
  rw [nuV, Matrix.mulVec_mulVec, OT_mul_Pp K N ι hK hN hι, Matrix.zero_mulVec]

include hK hN hι in
theorem Pp_mulVec_nuV (δ : N.carrier) : Pp K N ι *ᵥ nuV K N ι δ = nuV K N ι δ := by
  rw [nuV, Matrix.mulVec_mulVec, Pp_mul_Pp K N ι hK hN hι]

include hK hN hι in
theorem Pp_mulVec_iota_add (γ : K.carrier) (δ : N.carrier) :
    Pp K N ι *ᵥ chargeCoord N (ι γ + δ) = nuV K N ι δ := by
  have hc : chargeCoord N (ι γ + δ) = oscMatrix K N ι *ᵥ chargeCoord K γ + chargeCoord N δ := by
    funext b
    rw [chargeCoord_add, oscMatrix_chargeCoord K N hK ι γ, Pi.add_apply]
  rw [hc, Matrix.mulVec_add, Matrix.mulVec_mulVec, Pp_mul_O K N ι hK hN hι, Matrix.zero_mulVec,
    zero_add, nuV]

include hK hN hι in
/-- `⟨ν, ιγ⟩ = 0`. -/
theorem nuV_dot_iota (δ : N.carrier) (γ : K.carrier) :
    ∑ c : Fin (rank N), nuV K N ι δ c * chargeCoord N (ι γ) c = 0 := by
  rw [← oscMatrix_chargeCoord K N hK ι γ]
  change nuV K N ι δ ⬝ᵥ (oscMatrix K N ι *ᵥ chargeCoord K γ) = 0
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, OT_mulVec_nuV K N ι hK hN hι,
    zero_dotProduct]

/-- Annihilators in a direction orthogonal to `ι(K)` kill the image of `fockMap O`. -/
theorem annihilator_perp_fockMap (w : Fin (rank N) → ℂ) (hw : (oscMatrix K N ι)ᵀ *ᵥ w = 0)
    {n : ℤ} (hn : 0 < n) (p : FockN (rank K)) :
    (∑ c : Fin (rank N), w c • oscN (rank N) 1 c n) (fockMap (oscMatrix K N ι) p) = 0 := by
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, oscN_apply_pos _ 1 _ hn,
    fockMap_pderiv, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← Finset.sum_smul]
  have h0 : ∑ c : Fin (rank N), w c * (↑n * (1 * oscMatrix K N ι c a)) = 0 := by
    have := congrFun hw a
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at this
    rw [show ∑ c : Fin (rank N), w c * (↑n * (1 * oscMatrix K N ι c a))
        = (n : ℂ) * ∑ c : Fin (rank N), oscMatrix K N ι c a * w c by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring, this, mul_zero]
  rw [h0, zero_smul]

/-- Creators in a direction orthogonal to `ι(K)` are killed by `fockMap Oᵀ`. -/
theorem fockMapT_creator_perp (w : Fin (rank N) → ℂ) (hw : (oscMatrix K N ι)ᵀ *ᵥ w = 0)
    {n : ℤ} (hn : n < 0) (q : FockN (rank N)) :
    fockMap (OT K N ι) ((∑ c : Fin (rank N), w c • oscN (rank N) 1 c n) q) = 0 := by
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, oscN_apply_neg _ 1 _ hn]
  simp only [← smul_mul_assoc, ← Finset.sum_mul, map_mul]
  rw [fockMap_Xcomb (OT K N ι) w 0 hw]
  simp

end Perp


/-! ## §5  Bilinearity of `:ab:` and the transverse Sugawara field -/

section Bilin

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem nprod_finsetSum_right {ι' : Type*} (s : Finset ι') (e : ι' → ℂ)
    (f : ι' → FormalDist (End ℂ W)) (hf : ∀ b, IsField (f b)) {g : FormalDist (End ℂ W)}
    (hg : IsField g) (hs : IsField (∑ b ∈ s, e b • f b)) :
    VOA.nprod hg hs = ∑ b ∈ s, e b • VOA.nprod hg (hf b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact nprod_zero_right' hg hs
  | insert b s hb ih =>
      have h1 : IsField (∑ b ∈ s, e b • f b) :=
        isField_finsetSum s _ fun b => Fld.isField_smul (e b) (hf b)
      rw [nprod_congr_right hg hs (Fld.isField_add (Fld.isField_smul (e b) (hf b)) h1)
        (Finset.sum_insert hb), Fld.nprod_add_right hg (Fld.isField_smul (e b) (hf b)) h1,
        Fld.nprod_smul_right, ih h1, Finset.sum_insert hb]

/-- `:(∑ u_b f_b)(∑ v_c f_c): = ∑_{b,c} u_b v_c :f_b f_c:`. -/
theorem nprod_sum_sum {r : ℕ} (f : Fin r → FormalDist (End ℂ W)) (hf : ∀ b, IsField (f b))
    (u v : Fin r → ℂ) (hu : IsField (∑ b, u b • f b)) (hv : IsField (∑ c, v c • f c)) :
    VOA.nprod hu hv = ∑ b, ∑ c, (u b * v c) • VOA.nprod (hf b) (hf c) := by
  rw [nprod_finsetSum_left Finset.univ u f hf hv hu]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [nprod_finsetSum_right Finset.univ v f hf (hf b) hv, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_smul]

/-- Evaluation of `:a b:` at `z⁻¹` on a vector killed by all annihilators `a_j, b_j`, `j < -1`. -/
theorem nprod_neg_one_apply {a b : FormalDist (End ℂ W)} (ha : IsField a) (hb : IsField b) (x : W)
    (hax : ∀ j : ℤ, j < -1 → a j x = 0) (hbx : ∀ j : ℤ, j < -1 → b j x = 0) :
    VOA.nprod ha hb (-1) x = a 0 (b (-1) x) + b 0 (a (-1) x) := by
  rw [nprod_apply]
  have hsupp : Function.support (fun m : ℤ => normalOrdered a b m (-1 - m) x) ⊆ ({0, -1} : Finset ℤ) := by
    intro m hm
    rw [Function.mem_support, normalOrdered_apply] at hm
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hc
    push Not at hc
    apply hm
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0, Module.End.mul_apply, hbx _ (by omega), map_zero]
    · rw [if_neg h0, Module.End.mul_apply, hax _ (by omega), map_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_pair (by norm_num),
    normalOrdered_apply, normalOrdered_apply, if_pos le_rfl, if_neg (by norm_num)]
  simp only [Module.End.mul_apply]
  norm_num

end Bilin

section Transverse

variable (K N : IntegralLattice.{0}) (ι : K.carrier →ₗ[ℤ] N.carrier)
  (hKe : K.Even) (hK : K.PosDef) (hNe : N.Even) (hN : N.PosDef)
  (hι : ∀ α β, N.form (ι α) (ι β) = K.form α β)

/-- The transverse current `γ_d(z) = ∑_c P_{dc} h_c(z)`. -/
noncomputable def gamField (d : Fin (rank N)) : FormalDist (End ℂ (LatModuleGen N)) :=
  ∑ c : Fin (rank N), Pp K N ι d c • genFieldLatGen N c 0

theorem gamField_isField (d : Fin (rank N)) : IsField (gamField K N ι d) :=
  isField_finsetSum _ _ fun c => Fld.isField_smul _ (genFieldLatGen_isField N c 0)

theorem idField_eq_one : (idField : FormalDist (End ℂ (LatModuleGen N))) = 1 := by
  funext j
  rw [idField_apply, FormalDist.one_apply]
  rfl

include hKe hK hN hι in
/-- `Y(Φ ω_K, z) = ½ ∑_a :β_a(z) β_a(z):`, `β_a = ∑_b O_{ba} h_b`. -/
theorem Y_latMorph_omega :
    YfullGen N hNe hN (latMorph K N ι (omegaLatGen K))
      = ∑ a : Fin (rank K), (1 / 2 : ℂ) •
          VOA.nprod (isField_sum_genField K N ι a 0) (isField_sum_genField K N ι a 0) := by
  rw [Classification.COne.LatMod.omegaLatGen_eq_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, map_smul, Classification.COne.LatMod.YN_latMorph_current K N ι hK hNe hN hι]
  congr 1
  refine nprod_congr_right _ _ _ ?_
  rw [Classification.COne.LatMod.YN_latMorph_current K N ι hK hNe hN hι]
  have hv : YfullGen N hNe hN (latMorph K N ι (latVacuumGen K)) = idField := by
    have hv := (latMorph_isVOAHom K N ι hK hN hι hKe hNe).map_vacuum
    change latMorph K N ι (latVacuumGen K) = latVacuumGen N at hv
    rw [hv, idField_eq_one]
    exact (latticeVOAGen N hNe hN).vacuum_Y
  rw [nprod_congr_right _ _ idField_isField hv, Classification.COne.LatMod.nprod_idField_right]

theorem sugFieldGen_eq_gen :
    sugFieldGen N = (1 / 2 : ℂ) • ∑ b : Fin (rank N),
      VOA.nprod (genFieldLatGen_isField N b 0) (genFieldLatGen_isField N b 0) := by
  rw [sugFieldGen]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fld.raw_nprod_congr (alphaLatGen_isField N b) (genFieldLatGen_isField N b 0)
      (alphaLatGen_isField N b) (genFieldLatGen_zero N b).symm,
    nprod_congr_right _ (alphaLatGen_isField N b) (genFieldLatGen_isField N b 0)
      (genFieldLatGen_zero N b).symm]

include hKe hK hN hι in
/-- **The transverse Sugawara field**: `Y(ω_N) − Y(Φ ω_K) = ½ ∑_d :γ_d γ_d:`. -/
theorem Y_omega_sub :
    YfullGen N hNe hN (omegaLatGen N) - YfullGen N hNe hN (latMorph K N ι (omegaLatGen K))
      = (1 / 2 : ℂ) • ∑ d : Fin (rank N),
          VOA.nprod (gamField_isField K N ι d) (gamField_isField K N ι d) := by
  rw [Y_latMorph_omega K N ι hKe hK hNe hN hι, YfullGen_omega_eq, sugFieldGen_eq_gen]
  set n := fun b c : Fin (rank N) =>
    VOA.nprod (genFieldLatGen_isField N b 0) (genFieldLatGen_isField N c 0) with hn
  have hf := fun b : Fin (rank N) => genFieldLatGen_isField N b 0
  have e1 : ∑ b : Fin (rank N), n b b
      = ∑ b : Fin (rank N), ∑ c : Fin (rank N), (1 : Matrix (Fin (rank N)) (Fin (rank N)) ℂ) b c • n b c := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_eq_single b (fun c _ hc => by rw [Matrix.one_apply_ne (Ne.symm hc), zero_smul])
      (fun h => absurd (Finset.mem_univ b) h), Matrix.one_apply_eq, one_smul]
  have e2 : ∑ a : Fin (rank K), VOA.nprod (isField_sum_genField K N ι a 0) (isField_sum_genField K N ι a 0)
      = ∑ b : Fin (rank N), ∑ c : Fin (rank N),
          (oscMatrix K N ι * (oscMatrix K N ι)ᵀ) b c • n b c := by
    have e2a : ∀ a : Fin (rank K), VOA.nprod (isField_sum_genField K N ι a 0) (isField_sum_genField K N ι a 0)
        = ∑ b : Fin (rank N), ∑ c : Fin (rank N), (oscMatrix K N ι b a * oscMatrix K N ι c a) • n b c :=
      fun a => nprod_sum_sum (fun b => genFieldLatGen N b 0) hf
        (fun b => oscMatrix K N ι b a) (fun b => oscMatrix K N ι b a) _ _
    rw [Finset.sum_congr rfl fun a _ => e2a a]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul, Matrix.mul_apply]
    simp only [Matrix.transpose_apply]
  have e3 : ∑ d : Fin (rank N), VOA.nprod (gamField_isField K N ι d) (gamField_isField K N ι d)
      = ∑ b : Fin (rank N), ∑ c : Fin (rank N), Pp K N ι b c • n b c := by
    have e3a : ∀ d : Fin (rank N), VOA.nprod (gamField_isField K N ι d) (gamField_isField K N ι d)
        = ∑ b : Fin (rank N), ∑ c : Fin (rank N), (Pp K N ι d b * Pp K N ι d c) • n b c :=
      fun d => nprod_sum_sum (fun b => genFieldLatGen N b 0) hf
        (fun b => Pp K N ι d b) (fun b => Pp K N ι d b) _ _
    rw [Finset.sum_congr rfl fun d _ => e3a d]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have h := congrFun (congrFun (Pp_mul_Pp K N ι hK hN hι) b) c
    rw [Matrix.mul_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hs := congrFun (congrFun (Pp_transpose K N ι) b) d
    rw [Matrix.transpose_apply] at hs
    rw [hs]
  rw [← Finset.smul_sum, ← smul_sub, e1, e2, e3, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← sub_smul, Pp, Matrix.sub_apply]

end Transverse


/-! ## §6  The transverse Heisenberg state `h = ν(-1)𝟙` -/

section HState

variable (K N : IntegralLattice.{0}) (ι : K.carrier →ₗ[ℤ] N.carrier)
  (hKe : K.Even) (hK : K.PosDef) (hNe : N.Even) (hN : N.PosDef)
  (hι : ∀ α β, N.form (ι α) (ι β) = K.form α β)

open Classification.COne Classification.COne.LatMod

/-- The transverse Heisenberg state `h_δ = ∑_c ν_c h_c(-1)𝟙`, `ν = P·δ`. -/
noncomputable def hState (δ : N.carrier) : LatModuleGen N :=
  ∑ c : Fin (rank N), nuV K N ι δ c • hVec N c

theorem Y_hVec (c : Fin (rank N)) : YfullGen N hNe hN (hVec N c) = alphaLatGen N c := by
  rw [hVec, YfullGen_rTensor_current N hNe hN c 0 (latVacuumGen N)]
  have hv : YfullGen N hNe hN (latVacuumGen N) = idField := by
    rw [idField_eq_one]; exact YfullGen_vacuum N hNe hN
  rw [nprod_congr_right _ _ idField_isField hv, nprod_idField_right, genFieldLatGen_zero]

theorem smul_hState_latStateGen (δ : N.carrier) (n : ℤ) (q : FockN (rank N)) (η : N.carrier) :
    (latticeVOAGen N hNe hN).smul (hState K N ι δ) n (latStateGen N q η)
      = latStateGen N ((∑ c : Fin (rank N), nuV K N ι δ c • oscN (rank N) 1 c n) q
          + if n = 0 then (∑ c : Fin (rank N), nuV K N ι δ c * chargeCoord N η c) • q else 0) η := by
  rw [PreVertexAlgebra.smul_eq_coeff]
  change YfullGen N hNe hN (hState K N ι δ) (-n - 1) (latStateGen N q η) = _
  rw [hState, map_sum, formalDist_sum_apply, LinearMap.sum_apply]
  simp only [map_smul, formalDist_smul_apply, LinearMap.smul_apply, Y_hVec, alphaLatGen_latStateGen,
    show -(-n - 1) - 1 = n by ring, show ((-n - 1 = -1) ↔ n = 0) by omega]
  rw [latStateGen_sum_smul]
  congr 1
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_add,
    Finset.sum_add_distrib]
  congr 1
  split_ifs
  · rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun c _ => by rw [smul_smul]
  · simp

include hK hN hι in
/-- Negative modes of `h_δ` are transverse creators, killed by the projection. -/
theorem proj_smul_hState_neg (δ δ₃ : N.carrier) {n : ℤ} (hn : n < 0) (z : LatModuleGen N) :
    shiftEmbInv K N ι δ₃ ((latticeVOAGen N hNe hN).smul (hState K N ι δ) n z) = 0 := by
  have hext : (shiftEmbInv K N ι δ₃) ∘ₗ mode ((latticeVOAGen N hNe hN).Y (hState K N ι δ)) n = 0 := by
    refine LinearMap.ext_on_range (latStateGen_span N) fun qη => ?_
    obtain ⟨q, η⟩ := qη
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [← PreVertexAlgebra.smul_def, smul_hState_latStateGen, if_neg (by omega), add_zero]
    by_cases hη : ∃ γ : K.carrier, ι γ + δ₃ = η
    · obtain ⟨γ, rfl⟩ := hη
      rw [shiftEmbInv_latStateGen_of K N ι δ₃ hK hι,
        fockMapT_creator_perp K N ι _ (OT_mulVec_nuV K N ι hK hN hι δ) hn, latStateGen_zero_boson]
    · exact shiftEmbInv_latStateGen_of_not K N ι δ₃ _ _ fun γ h => hη ⟨γ, h⟩
  exact LinearMap.congr_fun hext z

/-- `s(δ₁,δ₂) = ⟨ν(δ₁), δ₂⟩`: the transverse pairing, the non-integral exponent shift. -/
noncomputable def sval (δ₁ δ₂ : N.carrier) : ℂ :=
  ∑ c : Fin (rank N), nuV K N ι δ₁ c * chargeCoord N δ₂ c

include hK hN hι in
/-- Non-negative modes of `h_{δ₁}` on the image of `Ψ_{δ₂}`: annihilators vanish, the zero mode is
the transverse pairing `s(δ₁,δ₂)`. -/
theorem smul_hState_shiftEmb (δ₁ δ₂ : N.carrier) {n : ℤ} (hn : 0 ≤ n) (w : LatModuleGen K) :
    (latticeVOAGen N hNe hN).smul (hState K N ι δ₁) n (shiftEmb K N ι δ₂ w)
      = if n = 0 then sval K N ι δ₁ δ₂ • shiftEmb K N ι δ₂ w else 0 := by
  have hext : mode ((latticeVOAGen N hNe hN).Y (hState K N ι δ₁)) n ∘ₗ shiftEmb K N ι δ₂
      = (if n = 0 then sval K N ι δ₁ δ₂ • shiftEmb K N ι δ₂ else 0) := by
    refine LinearMap.ext_on_range (latStateGen_span K) fun pγ => ?_
    obtain ⟨p, γ⟩ := pγ
    simp only [LinearMap.comp_apply]
    rw [← PreVertexAlgebra.smul_def, shiftEmb_latStateGen, smul_hState_latStateGen]
    rcases lt_or_eq_of_le hn with hpos | hzero
    · rw [if_neg (by omega), if_neg (by omega), add_zero,
        annihilator_perp_fockMap K N ι _ (OT_mulVec_nuV K N ι hK hN hι δ₁) hpos,
        latStateGen_zero_boson, LinearMap.zero_apply]
    · subst hzero
      rw [if_pos rfl, if_pos rfl]
      simp only [oscN_zero, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply, zero_add]
      rw [LinearMap.smul_apply, shiftEmb_latStateGen, ← latStateGen_csmul]
      congr 2
      simp only [sval, chargeCoord_add, mul_add, Finset.sum_add_distrib,
        nuV_dot_iota K N ι hK hN hι, zero_add]
  have h := LinearMap.congr_fun hext w
  simp only [LinearMap.comp_apply] at h
  rw [PreVertexAlgebra.smul_def, h]
  split_ifs <;> rfl

theorem gamField_latStateGen (d : Fin (rank N)) (j : ℤ) (q : FockN (rank N)) (η : N.carrier) :
    gamField K N ι d j (latStateGen N q η)
      = latStateGen N ((∑ c : Fin (rank N), Pp K N ι d c • oscN (rank N) 1 c (-j - 1)) q
          + if j = -1 then (Pp K N ι *ᵥ chargeCoord N η) d • q else 0) η := by
  rw [gamField, formalDist_sum_apply, LinearMap.sum_apply]
  simp only [formalDist_smul_apply, LinearMap.smul_apply, genFieldLatGen_zero,
    alphaLatGen_latStateGen]
  rw [latStateGen_sum_smul]
  congr 1
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_add,
    Finset.sum_add_distrib]
  congr 1
  split_ifs
  · rw [Matrix.mulVec, dotProduct, Finset.sum_smul]
    exact Finset.sum_congr rfl fun c _ => by rw [smul_smul]
  · simp

include hK hN hι in
theorem OT_mulVec_Prow (d : Fin (rank N)) :
    (oscMatrix K N ι)ᵀ *ᵥ (fun c => Pp K N ι d c) = 0 := by
  funext a
  have h := congrFun (congrFun (OT_mul_Pp K N ι hK hN hι) a) d
  rw [Matrix.mul_apply, Matrix.zero_apply] at h
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  rw [← h]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hs := congrFun (congrFun (Pp_transpose K N ι) c) d
  rw [Matrix.transpose_apply] at hs
  rw [hs]

include hK hN hι in
/-- The transverse Sugawara field at `z⁻¹` on the image of `Ψ_{δ₁}` is `h_{δ₁}(-1)`. -/
theorem transverse_neg_one_shiftEmb (δ₁ : N.carrier) (w : LatModuleGen K) :
    ((1 / 2 : ℂ) • ∑ d : Fin (rank N),
        VOA.nprod (gamField_isField K N ι d) (gamField_isField K N ι d)) (-1) (shiftEmb K N ι δ₁ w)
      = (latticeVOAGen N hNe hN).smul (hState K N ι δ₁) (-1) (shiftEmb K N ι δ₁ w) := by
  have hext : ((1 / 2 : ℂ) • ∑ d : Fin (rank N),
        VOA.nprod (gamField_isField K N ι d) (gamField_isField K N ι d)) (-1) ∘ₗ shiftEmb K N ι δ₁
      = mode ((latticeVOAGen N hNe hN).Y (hState K N ι δ₁)) (-1) ∘ₗ shiftEmb K N ι δ₁ := by
    refine LinearMap.ext_on_range (latStateGen_span K) fun pγ => ?_
    obtain ⟨p, γ⟩ := pγ
    simp only [LinearMap.comp_apply]
    rw [← PreVertexAlgebra.smul_def, shiftEmb_latStateGen, smul_hState_latStateGen, if_neg (by norm_num),
      add_zero, formalDist_smul_apply, formalDist_sum_apply, LinearMap.smul_apply, LinearMap.sum_apply]
    have hd : ∀ d : Fin (rank N),
        VOA.nprod (gamField_isField K N ι d) (gamField_isField K N ι d) (-1)
            (latStateGen N (fockMap (oscMatrix K N ι) p) (ι γ + δ₁))
          = (2 * nuV K N ι δ₁ d) • latStateGen N
              ((∑ c : Fin (rank N), Pp K N ι d c • oscN (rank N) 1 c (-1))
                (fockMap (oscMatrix K N ι) p)) (ι γ + δ₁) := by
      intro d
      have hann : ∀ j : ℤ, j < -1 → gamField K N ι d j
          (latStateGen N (fockMap (oscMatrix K N ι) p) (ι γ + δ₁)) = 0 := by
        intro j hj
        rw [gamField_latStateGen, if_neg (by omega), add_zero,
          annihilator_perp_fockMap K N ι _ (OT_mulVec_Prow K N ι hK hN hι d) (by omega),
          latStateGen_zero_boson]
      rw [nprod_neg_one_apply _ _ _ hann hann]
      have hm1 : gamField K N ι d (-1) (latStateGen N (fockMap (oscMatrix K N ι) p) (ι γ + δ₁))
          = nuV K N ι δ₁ d • latStateGen N (fockMap (oscMatrix K N ι) p) (ι γ + δ₁) := by
        rw [gamField_latStateGen, if_pos rfl, show -(-1 : ℤ) - 1 = 0 by ring]
        simp only [oscN_zero, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply, zero_add]
        rw [Pp_mulVec_iota_add K N ι hK hN hι, latStateGen_csmul]
      rw [hm1, map_smul, gamField_latStateGen, if_neg (by norm_num), add_zero,
        show -(0 : ℤ) - 1 = -1 by ring, ← add_smul, two_mul]
    simp only [hd]
    rw [Finset.smul_sum]
    simp only [smul_smul, show ∀ d, (1 / 2 : ℂ) * (2 * nuV K N ι δ₁ d) = nuV K N ι δ₁ d from
      fun d => by ring]
    rw [latStateGen_sum_smul]
    congr 1
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
      smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    conv_rhs => rw [← Pp_mulVec_nuV K N ι hK hN hι δ₁]
    rw [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hs := congrFun (congrFun (Pp_transpose K N ι) c) d
    rw [Matrix.transpose_apply] at hs
    rw [← hs, mul_comm]
  have h := LinearMap.congr_fun hext w
  simp only [LinearMap.comp_apply] at h
  rw [h, PreVertexAlgebra.smul_def]

include hKe hK hN hι in
/-- **`L₋₁` splits** on the image of `Ψ_{δ₁}`: `(Φω_K)₍₀₎ = L₋₁^N − h₍₋₁₎`. -/
theorem smul_latMorph_omega_shiftEmb (δ₁ : N.carrier) (w : LatModuleGen K) :
    (latticeVOAGen N hNe hN).smul (latMorph K N ι (omegaLatGen K)) 0 (shiftEmb K N ι δ₁ w)
      = (latticeVOAGen N hNe hN).smul (omegaLatGen N) 0 (shiftEmb K N ι δ₁ w)
        - (latticeVOAGen N hNe hN).smul (hState K N ι δ₁) (-1) (shiftEmb K N ι δ₁ w) := by
  have hY : YfullGen N hNe hN (latMorph K N ι (omegaLatGen K))
      = YfullGen N hNe hN (omegaLatGen N) - (1 / 2 : ℂ) • ∑ d : Fin (rank N),
          VOA.nprod (gamField_isField K N ι d) (gamField_isField K N ι d) := by
    rw [← Y_omega_sub K N ι hKe hK hNe hN hι, sub_sub_cancel]
  rw [← transverse_neg_one_shiftEmb K N ι hK hNe hN hι δ₁ w, PreVertexAlgebra.smul_eq_coeff,
    PreVertexAlgebra.smul_eq_coeff]
  change YfullGen N hNe hN (latMorph K N ι (omegaLatGen K)) (-0 - 1) _
    = YfullGen N hNe hN (omegaLatGen N) (-0 - 1) _ - _
  rw [hY, show (-0 - 1 : ℤ) = -1 by ring]
  rfl

end HState


/-! ## §7  Finite supports of the VOA Jacobi sums -/

section VJac

variable {𝒱 : Type} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)

theorem vJacL_support_finite (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support (fun i : ℤ => (negOnePow i * cbz ℓ i) •
      (W.smul u (ℓ + m - i) (W.smul v (n + i) x)
        - negOnePow ℓ • W.smul v (ℓ + n - i) (W.smul u (m + i) x)))).Finite := by
  obtain ⟨N₁, hN₁⟩ := W.regularity v x
  obtain ⟨N₂, hN₂⟩ := W.regularity u x
  refine (Set.finite_Ico (0 : ℤ) (max (N₁ - n) (N₂ - m))).subset (fun i hi => ?_)
  simp only [Function.mem_support] at hi
  simp only [Set.mem_Ico]
  by_contra hcon
  apply hi
  rcases lt_or_ge i 0 with hneg | hnn
  · simp [cbz_apply_neg ℓ hneg]
  · have hge : max (N₁ - n) (N₂ - m) ≤ i := by
      by_contra h; exact hcon ⟨hnn, not_le.mp h⟩
    have h1 : W.smul v (n + i) x = 0 := hN₁ _ (by have := le_trans (le_max_left _ _) hge; omega)
    have h2 : W.smul u (m + i) x = 0 := hN₂ _ (by have := le_trans (le_max_right _ _) hge; omega)
    simp only [h1, h2, PreVertexAlgebra.smul_zero_right, smul_zero, sub_zero]

theorem vJacR_support_finite (u v x : 𝒱) (ℓ m n : ℤ) :
    (Function.support (fun i : ℤ => cbz m i • W.smul (W.smul u (ℓ + i) v) (m + n - i) x)).Finite := by
  obtain ⟨N, hN⟩ := W.regularity u v
  refine (Set.finite_Ico (0 : ℤ) (N - ℓ)).subset (fun i hi => ?_)
  simp only [Function.mem_support] at hi
  simp only [Set.mem_Ico]
  by_contra hcon
  apply hi
  rcases lt_or_ge i 0 with hneg | hnn
  · simp [cbz_apply_neg m hneg]
  · have h : W.smul u (ℓ + i) v = 0 := hN (ℓ + i) (by
      by_contra h; exact hcon ⟨hnn, by omega⟩)
    simp only [h, PreVertexAlgebra.smul_zero_left, smul_zero]

end VJac

/-! ## §8  The integral modes `Z_k(w₁,w₂) = Ψ_{δ₁+δ₂}⁻¹ (Ψ_{δ₁}w₁)₍ₖ₎ (Ψ_{δ₂}w₂)` -/

section Zmodes

variable (K N : IntegralLattice.{0}) (ι : K.carrier →ₗ[ℤ] N.carrier)
  (hKe : K.Even) (hK : K.PosDef) (hNe : N.Even) (hN : N.PosDef)
  (hι : ∀ α β, N.form (ι α) (ι β) = K.form α β) (δ₁ δ₂ : N.carrier)

open Classification.COne Classification.COne.LatMod

/-- The integral modes of the untwisted operator. -/
noncomputable def Zmode (k : ℤ) : LatModuleGen K →ₗ[ℂ] LatModuleGen K →ₗ[ℂ] LatModuleGen K :=
  LinearMap.mk₂ ℂ (fun w₁ w₂ => shiftEmbInv K N ι (δ₁ + δ₂)
      ((latticeVOAGen N hNe hN).smul (shiftEmb K N ι δ₁ w₁) k (shiftEmb K N ι δ₂ w₂)))
    (fun a b c => by simp only [map_add, PreVertexAlgebra.smul_add_left])
    (fun c a b => by simp only [map_smul, PreVertexAlgebra.smul_smul_left])
    (fun a b c => by simp only [map_add, PreVertexAlgebra.smul_add_right])
    (fun c a b => by simp only [map_smul, PreVertexAlgebra.smul_smul_right])

theorem Zmode_apply (k : ℤ) (w₁ w₂ : LatModuleGen K) :
    Zmode K N ι hNe hN δ₁ δ₂ k w₁ w₂ = shiftEmbInv K N ι (δ₁ + δ₂)
      ((latticeVOAGen N hNe hN).smul (shiftEmb K N ι δ₁ w₁) k (shiftEmb K N ι δ₂ w₂)) := rfl

include hK hN hι in
theorem proj_smul (δ : N.carrier) (u : LatModuleGen K) (p : ℤ) (z : LatModuleGen N) :
    shiftEmbInv K N ι δ ((latticeVOAGen N hNe hN).smul (latMorph K N ι u) p z)
      = mode ((shiftWeakModule K N ι δ hKe hK hNe hN hι).YM u) p (shiftEmbInv K N ι δ z) := by
  rw [PreVertexAlgebra.smul_eq_coeff, mode_apply, proj_intertw K N ι δ hKe hK hNe hN hι]

theorem shiftEmb_mode (δ : N.carrier) (u : LatModuleGen K) (p : ℤ) (w : LatModuleGen K) :
    shiftEmb K N ι δ (mode ((shiftWeakModule K N ι δ hKe hK hNe hN hι).YM u) p w)
      = (latticeVOAGen N hNe hN).smul (latMorph K N ι u) p (shiftEmb K N ι δ w) := by
  rw [mode_apply, shiftWeakModule_intertw, PreVertexAlgebra.smul_eq_coeff]

include hK hN hι in
/-- **Jacobi identity for the integral modes.** -/
theorem Zmode_jacobi (u : LatModuleGen K) (w₁ w₂ : LatModuleGen K) (ℓ m k : ℤ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (mode ((shiftWeakModule K N ι (δ₁ + δ₂) hKe hK hNe hN hι).YM u) (ℓ + m - i)
            (Zmode K N ι hNe hN δ₁ δ₂ (k + i) w₁ w₂)
          - negOnePow ℓ • Zmode K N ι hNe hN δ₁ δ₂ (ℓ + k - i) w₁
              (mode ((shiftWeakModule K N ι δ₂ hKe hK hNe hN hι).YM u) (m + i) w₂)))
      = ∑ᶠ i : ℤ, cbz m i • Zmode K N ι hNe hN δ₁ δ₂ (m + k - i)
          (mode ((shiftWeakModule K N ι δ₁ hKe hK hNe hN hι).YM u) (ℓ + i) w₁) w₂ := by
  set VN := latticeVOAGen N hNe hN
  set P := shiftEmbInv K N ι (δ₁ + δ₂)
  set x := shiftEmb K N ι δ₁ w₁
  set y := shiftEmb K N ι δ₂ w₂
  set U := latMorph K N ι u
  have hJ := VN.jacobi U x y ℓ m k
  have hL : ∀ i : ℤ, (negOnePow i * cbz ℓ i) •
        (mode ((shiftWeakModule K N ι (δ₁ + δ₂) hKe hK hNe hN hι).YM u) (ℓ + m - i)
            (Zmode K N ι hNe hN δ₁ δ₂ (k + i) w₁ w₂)
          - negOnePow ℓ • Zmode K N ι hNe hN δ₁ δ₂ (ℓ + k - i) w₁
              (mode ((shiftWeakModule K N ι δ₂ hKe hK hNe hN hι).YM u) (m + i) w₂))
      = P ((negOnePow i * cbz ℓ i) • (VN.smul U (ℓ + m - i) (VN.smul x (k + i) y)
          - negOnePow ℓ • VN.smul x (ℓ + k - i) (VN.smul U (m + i) y))) := by
    intro i
    rw [map_smul, map_sub, map_smul, proj_smul K N ι hKe hK hNe hN hι, Zmode_apply, Zmode_apply,
      shiftEmb_mode]
  have hR : ∀ i : ℤ, cbz m i • Zmode K N ι hNe hN δ₁ δ₂ (m + k - i)
          (mode ((shiftWeakModule K N ι δ₁ hKe hK hNe hN hι).YM u) (ℓ + i) w₁) w₂
      = P (cbz m i • VN.smul (VN.smul U (ℓ + i) x) (m + k - i) y) := by
    intro i
    rw [map_smul, Zmode_apply, shiftEmb_mode]
  rw [finsum_congr hL, finsum_congr hR, ← map_finsum P (vJacL_support_finite VN U x y ℓ m k),
    ← map_finsum P (vJacR_support_finite VN U x y ℓ m k), hJ]

theorem Zmode_truncation (w₁ w₂ : LatModuleGen K) :
    ∃ M : ℤ, ∀ k : ℤ, M ≤ k → Zmode K N ι hNe hN δ₁ δ₂ k w₁ w₂ = 0 := by
  obtain ⟨M, hM⟩ := (latticeVOAGen N hNe hN).regularity (shiftEmb K N ι δ₁ w₁) (shiftEmb K N ι δ₂ w₂)
  refine ⟨M, fun k hk => ?_⟩
  rw [Zmode_apply, PreVertexAlgebra.smul_def, hM k hk, map_zero]

theorem negOnePow_neg_one' : negOnePow (-1) = -1 := by
  have h := negOnePow_succ (-1)
  rw [show (-1 : ℤ) + 1 = 0 by ring] at h
  have h0 : negOnePow 0 = 1 := by simp [negOnePow]
  rw [h0] at h
  linear_combination h

include hK hN hι in
/-- **The iterate step**: `Ψ⁻¹ (h₍₋₁₎x)₍ₖ₎ Ψ_{δ₂}w = s · Ψ⁻¹ x₍ₖ₋₁₎ Ψ_{δ₂}w`. -/
theorem proj_iterate_hState (x : LatModuleGen N) (w₂ : LatModuleGen K) (k : ℤ) :
    shiftEmbInv K N ι (δ₁ + δ₂) ((latticeVOAGen N hNe hN).smul
        ((latticeVOAGen N hNe hN).smul (hState K N ι δ₁) (-1) x) k (shiftEmb K N ι δ₂ w₂))
      = sval K N ι δ₁ δ₂ • shiftEmbInv K N ι (δ₁ + δ₂)
          ((latticeVOAGen N hNe hN).smul x (k - 1) (shiftEmb K N ι δ₂ w₂)) := by
  set VN := latticeVOAGen N hNe hN
  set P := shiftEmbInv K N ι (δ₁ + δ₂)
  set y := shiftEmb K N ι δ₂ w₂
  set h := hState K N ι δ₁
  have hJ := VN.jacobi h x y (-1) 0 k
  have hR : (∑ᶠ i : ℤ, cbz 0 i • VN.smul (VN.smul h (-1 + i) x) (0 + k - i) y)
      = VN.smul (VN.smul h (-1) x) k y := by
    rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul]),
      cbz_zero_left, if_pos rfl, one_smul, add_zero, zero_add, sub_zero]
  rw [hR] at hJ
  rw [← hJ, map_finsum P (vJacL_support_finite VN h x y (-1) 0 k), finsum_eq_single _ (0 : ℤ)]
  · rw [map_smul, map_sub, map_smul, proj_smul_hState_neg K N ι hK hNe hN hι _ _ (by norm_num),
      show (0 : ℤ) + 0 = 0 by ring, smul_hState_shiftEmb K N ι hK hNe hN hι δ₁ δ₂ le_rfl, if_pos rfl,
      PreVertexAlgebra.smul_smul_right, map_smul, negOnePow_neg_one']
    simp [cbz, negOnePow, show (-1 : ℤ) + k = k - 1 by ring]
    rfl
  · intro i hi
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · rw [cbz_apply_neg (-1) hneg, mul_zero, zero_smul, map_zero]
    · rw [map_smul, map_sub, map_smul, proj_smul_hState_neg K N ι hK hNe hN hι _ _ (by omega),
        smul_hState_shiftEmb K N ι hK hNe hN hι δ₁ δ₂ (by omega), if_neg (by omega),
        PreVertexAlgebra.smul_zero_right, map_zero, smul_zero, sub_zero, smul_zero]

include hKe hK hN hι in
/-- **`L₋₁` for the integral modes**: `Z_k(L₋₁w₁, w₂) = −(k + s) Z_{k−1}(w₁, w₂)`. -/
theorem Zmode_L_neg_one (w₁ w₂ : LatModuleGen K) (k : ℤ) :
    Zmode K N ι hNe hN δ₁ δ₂ k
        (mode ((shiftWeakModule K N ι δ₁ hKe hK hNe hN hι).YM
          (latticeVOAGen K hKe hK).conformalVector) 0 w₁) w₂
      = (-(k : ℂ) - sval K N ι δ₁ δ₂) • Zmode K N ι hNe hN δ₁ δ₂ (k - 1) w₁ w₂ := by
  rw [Zmode_apply, shiftEmb_mode]
  change shiftEmbInv K N ι (δ₁ + δ₂) ((latticeVOAGen N hNe hN).smul
    ((latticeVOAGen N hNe hN).smul (latMorph K N ι (omegaLatGen K)) 0 (shiftEmb K N ι δ₁ w₁)) k
      (shiftEmb K N ι δ₂ w₂)) = _
  have hsub : ∀ (a b z : LatModuleGen N) (j : ℤ), (latticeVOAGen N hNe hN).smul (a - b) j z
      = (latticeVOAGen N hNe hN).smul a j z - (latticeVOAGen N hNe hN).smul b j z := by
    intro a b z j
    rw [sub_eq_add_neg, PreVertexAlgebra.smul_add_left, ← neg_one_smul ℂ b,
      PreVertexAlgebra.smul_smul_left, neg_one_smul, ← sub_eq_add_neg]
  rw [smul_latMorph_omega_shiftEmb K N ι hKe hK hNe hN hι, hsub, map_sub,
    proj_iterate_hState K N ι hK hNe hN hι δ₁ δ₂]
  have hT := act_T_covariance (adjointModule (latticeVOAGen N hNe hN)).toWeakModule
    (shiftEmb K N ι δ₁ w₁) k (shiftEmb K N ι δ₂ w₂)
  simp only [WeakModule.act_def, VertexOperatorAlgebra.L_def] at hT
  change (latticeVOAGen N hNe hN).smul ((latticeVOAGen N hNe hN).smul (omegaLatGen N) (-1 + 1)
    (shiftEmb K N ι δ₁ w₁)) k (shiftEmb K N ι δ₂ w₂) = _ at hT
  rw [show (-1 + 1 : ℤ) = 0 by ring] at hT
  rw [hT, map_smul, Zmode_apply, sub_smul]
  rfl

end Zmodes


/-! ## §9  The intertwining axioms for weak modules, and transport along isomorphisms -/

section WeakIntw

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {M₁ M₂ M₃ M₁' M₂' M₃' : Type*}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₁'] [Module ℂ M₁'] [AddCommGroup M₂'] [Module ℂ M₂'] [AddCommGroup M₃']
  [Module ℂ M₃']

/-- The FHL axioms (`IsIntertwiningOperator`) for **weak** modules (no grading needed). -/
structure IsIntertwiningW (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂) (A₃ : WeakModule W M₃)
    (Y : IntertwiningModes M₁ M₂ M₃) : Prop where
  truncation : ∀ (w₁ : M₁) (w₂ : M₂) (n : ℂ), ∃ N : ℤ, ∀ k : ℤ, N ≤ k → Y (n + k) w₁ w₂ = 0
  L_neg_one : ∀ (w₁ : M₁) (n : ℂ),
    Y n (mode (A₁.YM W.conformalVector) 0 w₁) = (-n) • Y (n - 1) w₁
  jacobi : ∀ (u : 𝒱) (w₁ : M₁) (w₂ : M₂) (ℓ m : ℤ) (n : ℂ),
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (mode (A₃.YM u) (ℓ + m - i) (Y (n + i) w₁ w₂)
          - negOnePow ℓ • Y (ℓ + n - i) w₁ (mode (A₂.YM u) (m + i) w₂)))
      = ∑ᶠ i : ℤ, cbz m i • Y (m + n - i) (mode (A₁.YM u) (ℓ + i) w₁) w₂

theorem IsIntertwiningW.toIsIntertwiningOperator {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}
    {A₃ : OrdVModule W M₃} {Y : IntertwiningModes M₁ M₂ M₃}
    (h : IsIntertwiningW A₁.toWeakModule A₂.toWeakModule A₃.toWeakModule Y) :
    IsIntertwiningOperator A₁ A₂ A₃ Y :=
  ⟨h.truncation, h.L_neg_one, h.jacobi⟩

/-- Transport of mode data along linear equivalences. -/
noncomputable def transportModes (e₁ : M₁ ≃ₗ[ℂ] M₁') (e₂ : M₂ ≃ₗ[ℂ] M₂') (e₃ : M₃ ≃ₗ[ℂ] M₃')
    (Y : IntertwiningModes M₁ M₂ M₃) : IntertwiningModes M₁' M₂' M₃' := fun n =>
  ((Y n).compr₂ e₃.toLinearMap).compl₁₂ e₁.symm.toLinearMap e₂.symm.toLinearMap

theorem transportModes_apply (e₁ : M₁ ≃ₗ[ℂ] M₁') (e₂ : M₂ ≃ₗ[ℂ] M₂') (e₃ : M₃ ≃ₗ[ℂ] M₃')
    (Y : IntertwiningModes M₁ M₂ M₃) (n : ℂ) (w₁ : M₁') (w₂ : M₂') :
    transportModes e₁ e₂ e₃ Y n w₁ w₂ = e₃ (Y n (e₁.symm w₁) (e₂.symm w₂)) := rfl

theorem symm_intertw {A : WeakModule W M₁} {B : WeakModule W M₁'} (e : M₁ ≃ₗ[ℂ] M₁')
    (he : ∀ (u : 𝒱) (k : ℤ) (x : M₁), e (mode (A.YM u) k x) = mode (B.YM u) k (e x))
    (u : 𝒱) (k : ℤ) (x : M₁') : e.symm (mode (B.YM u) k x) = mode (A.YM u) k (e.symm x) := by
  apply e.injective
  rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- **Transport of intertwining operators along module isomorphisms.** -/
theorem IsIntertwiningW.transport {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂}
    {A₃ : WeakModule W M₃} {B₁ : WeakModule W M₁'} {B₂ : WeakModule W M₂'}
    {B₃ : WeakModule W M₃'} {Y : IntertwiningModes M₁ M₂ M₃} (h : IsIntertwiningW A₁ A₂ A₃ Y)
    (e₁ : M₁ ≃ₗ[ℂ] M₁') (e₂ : M₂ ≃ₗ[ℂ] M₂') (e₃ : M₃ ≃ₗ[ℂ] M₃')
    (he₁ : ∀ (u : 𝒱) (k : ℤ) (x : M₁), e₁ (mode (A₁.YM u) k x) = mode (B₁.YM u) k (e₁ x))
    (he₂ : ∀ (u : 𝒱) (k : ℤ) (x : M₂), e₂ (mode (A₂.YM u) k x) = mode (B₂.YM u) k (e₂ x))
    (he₃ : ∀ (u : 𝒱) (k : ℤ) (x : M₃), e₃ (mode (A₃.YM u) k x) = mode (B₃.YM u) k (e₃ x)) :
    IsIntertwiningW B₁ B₂ B₃ (transportModes e₁ e₂ e₃ Y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w₁ w₂ n
    obtain ⟨N, hN⟩ := h.truncation (e₁.symm w₁) (e₂.symm w₂) n
    exact ⟨N, fun k hk => by rw [transportModes_apply, hN k hk, map_zero]⟩
  · intro w₁ n
    ext w₂
    rw [LinearMap.smul_apply, transportModes_apply, transportModes_apply, symm_intertw e₁ he₁,
      h.L_neg_one, LinearMap.smul_apply, map_smul]
  · intro u w₁ w₂ ℓ m n
    have hJ := h.jacobi u (e₁.symm w₁) (e₂.symm w₂) ℓ m n
    have hL : ∀ i : ℤ, (negOnePow i * cbz ℓ i) •
        (mode (B₃.YM u) (ℓ + m - i) (transportModes e₁ e₂ e₃ Y (n + i) w₁ w₂)
          - negOnePow ℓ • transportModes e₁ e₂ e₃ Y (ℓ + n - i) w₁ (mode (B₂.YM u) (m + i) w₂))
        = e₃ ((negOnePow i * cbz ℓ i) •
          (mode (A₃.YM u) (ℓ + m - i) (Y (n + i) (e₁.symm w₁) (e₂.symm w₂))
            - negOnePow ℓ • Y (ℓ + n - i) (e₁.symm w₁) (mode (A₂.YM u) (m + i) (e₂.symm w₂)))) := by
      intro i
      rw [map_smul, map_sub, map_smul, he₃, transportModes_apply, transportModes_apply,
        symm_intertw e₂ he₂]
    have hR : ∀ i : ℤ, cbz m i • transportModes e₁ e₂ e₃ Y (m + n - i) (mode (B₁.YM u) (ℓ + i) w₁) w₂
        = e₃ (cbz m i • Y (m + n - i) (mode (A₁.YM u) (ℓ + i) (e₁.symm w₁)) (e₂.symm w₂)) := by
      intro i
      rw [map_smul, transportModes_apply, symm_intertw e₁ he₁]
    have key : ∀ f : ℤ → M₃, ∑ᶠ i, e₃ (f i) = e₃ (∑ᶠ i, f i) := fun f =>
      (Classification.COne.LatMod.map_finsum_of_injective e₃.toLinearMap e₃.injective f).symm
    rw [finsum_congr hL, finsum_congr hR, key, key]
    exact congrArg e₃ hJ

theorem transportModes_ne_zero (e₁ : M₁ ≃ₗ[ℂ] M₁') (e₂ : M₂ ≃ₗ[ℂ] M₂') (e₃ : M₃ ≃ₗ[ℂ] M₃')
    {Y : IntertwiningModes M₁ M₂ M₃} {n : ℂ} {w₁ : M₁} {w₂ : M₂} (h : Y n w₁ w₂ ≠ 0) :
    transportModes e₁ e₂ e₃ Y n (e₁ w₁) (e₂ w₂) ≠ 0 := by
  rw [transportModes_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact fun h0 => h (e₃.injective (by rw [h0, map_zero]))

/-- Positivity of a fusion rule from a nonzero intertwiner, given finite-dimensionality. -/
theorem one_le_fusionRule_of_nontrivial {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
    (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂) (A₃ : OrdVModule W M₃)
    [Nontrivial (IntertwiningOperator A₁ A₂ A₃)] [FiniteDimensional ℂ (IntertwiningOperator A₁ A₂ A₃)] :
    1 ≤ fusionRule A₁ A₂ A₃ :=
  (_root_.Module.finrank_pos_iff_of_free ℂ _).mpr inferInstance

end WeakIntw

/-! ## §10  The complex-indexed intertwining operator `𝒴(w₁,z) = z^{-s} Ψ⁻¹ Y_N(Ψw₁,z) Ψ` -/

section Complex

variable (K N : IntegralLattice.{0}) (ι : K.carrier →ₗ[ℤ] N.carrier)
  (hKe : K.Even) (hK : K.PosDef) (hNe : N.Even) (hN : N.PosDef)
  (hι : ∀ α β, N.form (ι α) (ι β) = K.form α β) (δ₁ δ₂ : N.carrier)

open Classification.COne Classification.COne.LatMod

open Classical in
/-- **The lattice intertwining operator** `𝒴(w₁,z)w₂ = z^{-s} Ψ_{δ₁+δ₂}⁻¹ Y_N(Ψ_{δ₁}w₁, z) Ψ_{δ₂}w₂`,
`s = ⟨ν(δ₁), δ₂⟩` (the transverse pairing): the mode `(w₁)₍ₖ₊ₛ₎` is `Z_k`, and modes off the coset
`s + ℤ` vanish.  The factor `z^{-s}` removes exactly the transverse part `z^{⟨δ₁^⊥,δ₂^⊥⟩}` of
`z^{⟨δ₁,δ₂+β⟩}`, leaving the fractional powers `z^{⟨λ₁,λ₂+β⟩}` of the generalized vertex operator. -/
noncomputable def latIntw : IntertwiningModes (LatModuleGen K) (LatModuleGen K) (LatModuleGen K) :=
  fun n => if h : ∃ k : ℤ, (k : ℂ) + sval K N ι δ₁ δ₂ = n then Zmode K N ι hNe hN δ₁ δ₂ h.choose
    else 0

theorem latIntw_intCast_add (k : ℤ) :
    latIntw K N ι hNe hN δ₁ δ₂ ((k : ℂ) + sval K N ι δ₁ δ₂) = Zmode K N ι hNe hN δ₁ δ₂ k := by
  have h : ∃ k' : ℤ, (k' : ℂ) + sval K N ι δ₁ δ₂ = (k : ℂ) + sval K N ι δ₁ δ₂ := ⟨k, rfl⟩
  rw [latIntw, dif_pos h]
  have : h.choose = k := Int.cast_injective (add_right_cancel h.choose_spec)
  rw [this]

theorem latIntw_of_not {n : ℂ} (hn : ∀ k : ℤ, (k : ℂ) + sval K N ι δ₁ δ₂ ≠ n) :
    latIntw K N ι hNe hN δ₁ δ₂ n = 0 := by
  rw [latIntw, dif_neg (not_exists.mpr hn)]

include hKe hK hN hι in
/-- **The lattice intertwining operator satisfies all FHL axioms**: truncation, `L₋₁`-derivative
and the full Jacobi identity, for the modules `V_{K+λ(δ₁)}`, `V_{K+λ(δ₂)}`, `V_{K+λ(δ₁+δ₂)}`. -/
theorem isIntertwiningW_latIntw :
    IsIntertwiningW (shiftWeakModule K N ι δ₁ hKe hK hNe hN hι)
      (shiftWeakModule K N ι δ₂ hKe hK hNe hN hι)
      (shiftWeakModule K N ι (δ₁ + δ₂) hKe hK hNe hN hι) (latIntw K N ι hNe hN δ₁ δ₂) := by
  set s := sval K N ι δ₁ δ₂
  refine ⟨?_, ?_, ?_⟩
  · intro w₁ w₂ n
    by_cases hn : ∃ k : ℤ, (k : ℂ) + s = n
    · obtain ⟨k, rfl⟩ := hn
      obtain ⟨M, hM⟩ := Zmode_truncation K N ι hNe hN δ₁ δ₂ w₁ w₂
      refine ⟨M - k, fun j hj => ?_⟩
      rw [show (k : ℂ) + s + (j : ℂ) = ((k + j : ℤ) : ℂ) + s by push_cast; ring, latIntw_intCast_add]
      exact hM _ (by omega)
    · refine ⟨0, fun j _ => ?_⟩
      rw [latIntw_of_not K N ι hNe hN δ₁ δ₂ (n := n + j)
        (fun k hk => hn ⟨k - j, by push_cast; rw [sub_add_eq_add_sub, hk]; ring⟩)]
      rfl
  · intro w₁ n
    by_cases hn : ∃ k : ℤ, (k : ℂ) + s = n
    · obtain ⟨k, rfl⟩ := hn
      rw [latIntw_intCast_add, show (k : ℂ) + s - 1 = ((k - 1 : ℤ) : ℂ) + s by push_cast; ring,
        latIntw_intCast_add]
      refine LinearMap.ext fun w₂ => ?_
      rw [LinearMap.smul_apply, Zmode_L_neg_one K N ι hKe hK hNe hN hι δ₁ δ₂]
      congr 1
      ring
    · rw [latIntw_of_not K N ι hNe hN δ₁ δ₂ (fun k hk => hn ⟨k, hk⟩),
        latIntw_of_not K N ι hNe hN δ₁ δ₂ (n := n - 1)
          (fun k hk => hn ⟨k + 1, by push_cast; rw [add_right_comm, hk]; ring⟩)]
      simp
  · intro u w₁ w₂ ℓ m n
    by_cases hn : ∃ k : ℤ, (k : ℂ) + s = n
    · obtain ⟨k, rfl⟩ := hn
      have h := Zmode_jacobi K N ι hKe hK hNe hN hι δ₁ δ₂ u w₁ w₂ ℓ m k
      convert h using 2
      · funext i
        rw [show (k : ℂ) + s + (i : ℂ) = ((k + i : ℤ) : ℂ) + s by push_cast; ring,
          show ((ℓ : ℂ) + ((k : ℂ) + s) - (i : ℂ)) = ((ℓ + k - i : ℤ) : ℂ) + s by push_cast; ring,
          latIntw_intCast_add, latIntw_intCast_add]
      · funext i
        rw [show ((m : ℂ) + ((k : ℂ) + s) - (i : ℂ)) = ((m + k - i : ℤ) : ℂ) + s by push_cast; ring,
          latIntw_intCast_add]
    · have hz : ∀ j : ℤ, latIntw K N ι hNe hN δ₁ δ₂ (n + j) = 0 := fun j =>
        latIntw_of_not K N ι hNe hN δ₁ δ₂ (fun k hk => hn ⟨k - j, by
          push_cast; rw [sub_add_eq_add_sub, hk]; ring⟩)
      have h2 : ∀ i : ℤ, latIntw K N ι hNe hN δ₁ δ₂ (ℓ + n - i) = 0 := fun i => by
        rw [show (ℓ : ℂ) + n - i = n + ((ℓ - i : ℤ) : ℂ) by push_cast; ring]; exact hz _
      have h3 : ∀ i : ℤ, latIntw K N ι hNe hN δ₁ δ₂ (m + n - i) = 0 := fun i => by
        rw [show (m : ℂ) + n - i = n + ((m - i : ℤ) : ℂ) by push_cast; ring]; exact hz _
      simp [hz, h2, h3]

include hK hN hι in
/-- **Non-vanishing**: the leading coefficient `(e^{λ₁})₍₋⟨δ₁,δ₂⟩₋₁₊ₛ₎ e^{λ₂} = ε(δ₁,δ₂) e^{λ₁+λ₂}`. -/
theorem latIntw_vacuum :
    latIntw K N ι hNe hN δ₁ δ₂ (((-N.form δ₁ δ₂ - 1 : ℤ) : ℂ) + sval K N ι δ₁ δ₂)
        (latVacuumGen K) (latVacuumGen K)
      = latticeCocycle N δ₁ δ₂ • latVacuumGen K := by
  rw [latIntw_intCast_add, Zmode_apply]
  have hv : ∀ δ : N.carrier, shiftEmb K N ι δ (latVacuumGen K) = latChargeGen N δ := by
    intro δ
    rw [latVacuumGen, shiftEmb_latStateGen, map_zero, zero_add, vacuumN, fockMap_one]
    rfl
  rw [hv, hv, show latChargeGen N δ₂ = latStateGen N (vacuumN (rank N)) δ₂ from rfl,
    latVOA_smul_latChargeGen_state,
    show -(-N.form δ₁ δ₂ - 1) - 1 - N.form δ₁ δ₂ = 0 by ring, EEVec_vacuum, if_pos le_rfl,
    Int.toNat_zero, vSchur_zero, map_smul]
  have he := shiftEmbInv_latStateGen_of K N ι (δ₁ + δ₂) hK hι 1 0
  rw [map_zero, zero_add, fockMap_one] at he
  rw [he]
  rfl

include hK hN hι in
theorem latIntw_ne_zero :
    latIntw K N ι hNe hN δ₁ δ₂ (((-N.form δ₁ δ₂ - 1 : ℤ) : ℂ) + sval K N ι δ₁ δ₂)
        (latVacuumGen K) (latVacuumGen K) ≠ 0 := by
  rw [latIntw_vacuum K N ι hK hNe hN hι]
  exact smul_ne_zero (LatGen.latticeCocycle_ne_zero N δ₁ δ₂) (latVacuumGen_ne_zero K)

include hN in
/-- The transverse pairing: `s(δ₁,δ₂) = ⟨δ₁,δ₂⟩ − ⟨λ(δ₁),λ(δ₂)⟩`. -/
theorem sval_eq :
    sval K N ι δ₁ δ₂ = ((N.form δ₁ δ₂ : ℤ) : ℂ)
      - ∑ a : Fin (rank K), lamShift K N ι δ₁ a * lamShift K N ι δ₂ a := by
  rw [← sum_chargeCoord N hN δ₁ δ₂]
  change (Pp K N ι *ᵥ chargeCoord N δ₁) ⬝ᵥ chargeCoord N δ₂ = _
  rw [Pp, Matrix.sub_mulVec, Matrix.one_mulVec, sub_dotProduct, ← Matrix.mulVec_mulVec,
    dotProduct_comm (oscMatrix K N ι *ᵥ _), Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    dotProduct_comm]
  rw [dotProduct_comm (chargeCoord N δ₂), dotProduct_comm ((oscMatrix K N ι)ᵀ *ᵥ chargeCoord N δ₂)]
  rfl

end Complex


/-! ## §11  Comparing shifted modules built in different gluing lattices -/

section ChargeIso

variable (L : IntegralLattice.{0}) (hE : L.Even) (hP : L.PosDef)
  {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']

open Classification.COne

/-- A linear map intertwining the vertex operators of all `e^β` intertwines every `u ∈ V_L`
(weak-module version of `moduleEquivOfCharge`; no injectivity needed). -/
theorem intertw_of_charge (A : WeakModule (latticeVOAGen L hE hP) M)
    (B : WeakModule (latticeVOAGen L hE hP) M') (e : M →ₗ[ℂ] M')
    (hgen : ∀ (β : L.carrier) (t : ℤ) (x : M),
      e (A.YM (latChargeGen L β) t x) = B.YM (latChargeGen L β) t (e x))
    (u : LatModuleGen L) (k : ℤ) (x : M) :
    e (mode (A.YM u) k x) = mode (B.YM u) k (e x) := by
  let S : Submodule ℂ (LatModuleGen L) :=
    { carrier := {u | ∀ (k : ℤ) (x : M), e (mode (A.YM u) k x) = mode (B.YM u) k (e x)}
      add_mem' := fun {u v} hu hv k x => by
        simp only [Set.mem_setOf_eq, map_add, mode_add, LinearMap.add_apply] at hu hv ⊢
        rw [hu, hv]
      zero_mem' := fun k x => by simp
      smul_mem' := fun c u hu k x => by
        simp only [Set.mem_setOf_eq, map_smul, mode_smul, LinearMap.smul_apply] at hu ⊢
        rw [hu] }
  have htop : S = ⊤ := by
    refine latVOA_generated L hE hP S (fun u hu v hv n => ?_) (fun β => ?_)
    · exact fun k x => intertw_smul A B e hu hv n k x
    · intro k x
      rw [mode_apply, mode_apply]
      exact hgen β _ x
  have hu : u ∈ S := by rw [htop]; trivial
  exact hu k x

variable (K N : IntegralLattice.{0}) (ι : K.carrier →ₗ[ℤ] N.carrier) (hKe : K.Even) (hNe : N.Even)
  (hι : ∀ α β, N.form (ι α) (ι β) = K.form α β)

include hKe hNe hι in
/-- The module cocycle of `V_{K+λ(δ)}` (any gluing lattice): `ε_K(β,n) σ_δ(β) c(β+n)/c(n)`. -/
theorem kappa_gen (δ : N.carrier) (β n : K.carrier) :
    latCob K N ι β * latticeCocycle N (ι β) (ι n + δ)
      = latticeCocycle K β n * latticeCocycle N (ι β) δ * latCob K N ι (β + n)
          * (latCob K N ι n)⁻¹ := by
  have h := latticeCocycle_map_mul_latCob K N hKe hNe ι hι β n
  have hn := latCob_ne_zero K N ι n
  rw [latticeCocycle_add_right]
  field_simp
  linear_combination latticeCocycle N (ι β) δ * h

end ChargeIso

/-! ## §12  The rank-one case: intertwiners of type `(j+k / j k)` among the `V_{L+λ_j}` -/

section RankOne

open Classification.COne Classification.COne.LatMod VOA.LatGen.Triplet

variable (m : ℕ) (hm : 1 ≤ m)

/-- `V_{L+λ}` realised inside the **common** gluing lattice `N_{m,1}` with glue vector `δ`. -/
noncomputable abbrev shiftMod (δ : (glueLat m 1).carrier) :
    WeakModule (latticeVOAGen (latP m) (latP_even m) (latP_posDef m hm)) (LatModuleGen (latP m)) :=
  shiftWeakModule (latP m) (glueLat m 1) (glueIota m 1) δ (latP_even m) (latP_posDef m hm)
    (glueLat_even m 1) (glueLat_posDef m hm 1) (glueIota_isometry m 1)

/-- The rescaling `p ⊗ e^{nα} ↦ d(n) p ⊗ e^{nα}` comparing `N_{m,1}` with `N_{m,j}`. -/
noncomputable def isoC (j : ℤ) (δ : (glueLat m 1).carrier) (n : ℤ) : ℂ :=
  (latCob (latP m) (glueLat m 1) (glueIota m 1) n)⁻¹ * latCob (latP m) (glueLat m j) (glueIota m j) n
    * (latticeCocycle (glueLat m 1) (glueIota m 1 n) δ * sig m j n)

theorem isoC_ne_zero (j : ℤ) (δ : (glueLat m 1).carrier) (n : ℤ) : isoC m j δ n ≠ 0 := by
  have h1 := latCob_ne_zero (latP m) (glueLat m 1) (glueIota m 1) n
  have h2 := latCob_ne_zero (latP m) (glueLat m j) (glueIota m j) n
  have h3 : latticeCocycle (glueLat m 1) (glueIota m 1 n) δ ≠ 0 := LatGen.latticeCocycle_ne_zero _ _ _
  have h4 : sig m j n ≠ 0 := LatGen.latticeCocycle_ne_zero _ _ _
  unfold isoC
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero h1) h2) (mul_ne_zero h3 h4)

theorem isoC_scalar (j : ℤ) (δ : (glueLat m 1).carrier) (β n : ℤ) :
    (latCob (latP m) (glueLat m 1) (glueIota m 1) β
        * latticeCocycle (glueLat m 1) (glueIota m 1 β) (glueIota m 1 n + δ)) * isoC m j δ (β + n)
      = isoC m j δ n * (latCob (latP m) (glueLat m j) (glueIota m j) β
        * latticeCocycle (glueLat m j) (glueIota m j β) (glueIota m j n + glueDelta m j)) := by
  rw [kappa_gen (latP m) (glueLat m 1) (glueIota m 1) (latP_even m) (glueLat_even m 1)
    (glueIota_isometry m 1), kappa_eq]
  set σ : ℤ → ℂ := fun n => latticeCocycle (glueLat m 1) (glueIota m 1 n) δ with hσ
  have hsa : σ (β + n) = σ β * σ n := by
    have e : glueIota m 1 (β + n) = glueIota m 1 β + glueIota m 1 n := (glueIota m 1).map_add β n
    simp only [hσ]
    rw [e, latticeCocycle_add_left]
  have hs2 : σ β * σ β = 1 := latticeCocycle_sq _ _ _
  have hja := sig_add m j β n
  have hn := latCob_ne_zero (latP m) (glueLat m 1) (glueIota m 1) n
  have hn' := latCob_ne_zero (latP m) (glueLat m j) (glueIota m j) n
  have hbn := latCob_ne_zero (latP m) (glueLat m 1) (glueIota m 1) (β + n)
  change latticeCocycle (latP m) β n * σ β * latCob (latP m) (glueLat m 1) (glueIota m 1) (β + n)
      * (latCob (latP m) (glueLat m 1) (glueIota m 1) n)⁻¹
      * ((latCob (latP m) (glueLat m 1) (glueIota m 1) (β + n))⁻¹
        * latCob (latP m) (glueLat m j) (glueIota m j) (β + n) * (σ (β + n) * sig m j (β + n)))
    = (latCob (latP m) (glueLat m 1) (glueIota m 1) n)⁻¹
        * latCob (latP m) (glueLat m j) (glueIota m j) n * (σ n * sig m j n) * _
  rw [hsa, hja]
  field_simp
  linear_combination (latticeCocycle (latP m) β n * σ n * sig m j β * sig m j n
    * latCob (latP m) (glueLat m j) (glueIota m j) (β + n)) * hs2

/-- The comparison isomorphism `V_{L+λ}` (in `N_{m,1}`, glue `δ`) `≅` `latticeModule j`. -/
noncomputable def isoE (j : ℤ) (δ : (glueLat m 1).carrier) :
    LatModuleGen (latP m) ≃ₗ[ℂ] LatModuleGen (latP m) :=
  relabelEquiv (latP m) (isoC m j δ) (0 : ℤ) (isoC_ne_zero m j δ)

theorem isoE_intertw (j : ℤ) (δ : (glueLat m 1).carrier)
    (hδ : ∀ n : ℤ, (glueLat m 1).form (glueIota m 1 n) δ = j * n)
    (u : LatModuleGen (latP m)) (k : ℤ) (x : LatModuleGen (latP m)) :
    isoE m j δ (mode ((shiftMod m hm δ).YM u) k x)
      = mode ((latticeModule m hm j).YM u) k (isoE m j δ x) := by
  refine intertw_of_charge (latP m) (latP_even m) (latP_posDef m hm) (shiftMod m hm δ)
    (latticeModule m hm j).toWeakModule (isoE m j δ).toLinearMap (fun (β : ℤ) t x => ?_) u k x
  have hext := linearMap_ext_latStateGen (latP m)
    (f := (isoE m j δ).toLinearMap ∘ₗ (shiftMod m hm δ).YM (latChargeGen (latP m) β) t)
    (g := (latticeModule m hm j).YM (latChargeGen (latP m) β) t ∘ₗ (isoE m j δ).toLinearMap)
    (fun p (n : ℤ) => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, isoE]
      rw [shiftWeakModule_latChargeGen, map_smul, relabel_latP, relabel_latP, map_smul,
        latticeModule_latChargeGen, smul_smul, smul_smul]
      simp only [add_zero]
      erw [isoC_scalar]
      rw [latP_form, hδ]
      rfl)
  exact LinearMap.congr_fun hext x

/-- The glue vector `j·δ` of `N_{m,1}`, realising `λ_j = j/(2m)·α`. -/
noncomputable abbrev glueJ (j : ℤ) : (glueLat m 1).carrier := j • glueDelta m 1

theorem glue_form_smul (j : ℤ) (n : ℤ) :
    (glueLat m 1).form (glueIota m 1 n) (glueJ m j) = j * n := by
  rw [glueJ, map_zsmul, glueIota_delta, smul_eq_mul]
  ring

theorem glue_form_add (j k : ℤ) (n : ℤ) :
    (glueLat m 1).form (glueIota m 1 n) (glueJ m j + glueJ m k) = (j + k) * n := by
  rw [map_add, glue_form_smul, glue_form_smul]
  ring

/-- **The lattice intertwining operator of type `(V_{L+λ_{j+k}} / V_{L+λ_j} V_{L+λ_k})`**: the
generalized vertex operator `𝒴(e^{λ_j}, z) = E⁻ E⁺ e_{λ_j} z^{λ_j(0)}`, realised as
`z^{-s} Ψ⁻¹ Y_{N}(Ψ ·, z) Ψ` in the common gluing lattice `N = N_{m,1}` and transported to the
modules `latticeModule j`, `latticeModule k`, `latticeModule (j+k)`. -/
noncomputable def latticeIntwModes (j k : ℤ) :
    IntertwiningModes (LatModuleGen (latP m)) (LatModuleGen (latP m)) (LatModuleGen (latP m)) :=
  transportModes (isoE m j (glueJ m j)) (isoE m k (glueJ m k)) (isoE m (j + k) (glueJ m j + glueJ m k))
    (latIntw (latP m) (glueLat m 1) (glueIota m 1) (glueLat_even m 1) (glueLat_posDef m hm 1)
      (glueJ m j) (glueJ m k))

/-- **H1b: the lattice intertwiners satisfy all FHL axioms** (truncation, `L₋₁`-derivative,
full Jacobi identity), for every `j, k ∈ ℤ`. -/
theorem isIntertwiningOperator_latticeIntwModes (j k : ℤ) :
    IsIntertwiningOperator (latticeModule m hm j) (latticeModule m hm k)
      (latticeModule m hm (j + k)) (latticeIntwModes m hm j k) := by
  refine IsIntertwiningW.toIsIntertwiningOperator ?_
  exact (isIntertwiningW_latIntw (latP m) (glueLat m 1) (glueIota m 1) (latP_even m)
    (latP_posDef m hm) (glueLat_even m 1) (glueLat_posDef m hm 1) (glueIota_isometry m 1)
    (glueJ m j) (glueJ m k)).transport _ _ _
    (isoE_intertw m hm j (glueJ m j) (glue_form_smul m j))
    (isoE_intertw m hm k (glueJ m k) (glue_form_smul m k))
    (isoE_intertw m hm (j + k) (glueJ m j + glueJ m k) (glue_form_add m j k))

/-- The lattice intertwiner as an element of the space of intertwining operators. -/
noncomputable def latticeIntertwiner (j k : ℤ) :
    IntertwiningOperator (latticeModule m hm j) (latticeModule m hm k) (latticeModule m hm (j + k)) :=
  ⟨latticeIntwModes m hm j k, isIntertwiningOperator_latticeIntwModes m hm j k⟩

/-- **Non-vanishing**: the lattice intertwiner is nonzero. -/
theorem latticeIntertwiner_ne_zero (j k : ℤ) : latticeIntertwiner m hm j k ≠ 0 := by
  intro h
  have hne := transportModes_ne_zero (isoE m j (glueJ m j)) (isoE m k (glueJ m k))
    (isoE m (j + k) (glueJ m j + glueJ m k))
    (latIntw_ne_zero (latP m) (glueLat m 1) (glueIota m 1) (latP_posDef m hm) (glueLat_even m 1)
      (glueLat_posDef m hm 1) (glueIota_isometry m 1) (glueJ m j) (glueJ m k))
  apply hne
  have h1 : latticeIntwModes m hm j k = 0 := congrArg Subtype.val h
  rw [show transportModes (isoE m j (glueJ m j)) (isoE m k (glueJ m k))
      (isoE m (j + k) (glueJ m j + glueJ m k))
      (latIntw (latP m) (glueLat m 1) (glueIota m 1) (glueLat_even m 1) (glueLat_posDef m hm 1)
        (glueJ m j) (glueJ m k)) = latticeIntwModes m hm j k from rfl, h1]
  rfl

include hm in
/-- In rank one, `⟨λ_j, λ_k⟩ = jk/(2m)`. -/
theorem lamShift_mul_rankOne (j k : ℤ) :
    ∑ a, lamShift (latP m) (glueLat m 1) (glueIota m 1) (glueJ m j) a
        * lamShift (latP m) (glueLat m 1) (glueIota m 1) (glueJ m k) a
      = (j : ℂ) * k / (2 * m) := by
  have hK := latP_posDef m hm
  have hN := glueLat_posDef m hm 1
  have hcc := sum_chargeCoord (latP m) hK (1 : ℤ) (1 : ℤ)
  have hcj := sum_chargeCoord_lamShift (latP m) (glueLat m 1) (glueIota m 1) (glueJ m j) hK hN (1 : ℤ)
  have hck := sum_chargeCoord_lamShift (latP m) (glueLat m 1) (glueIota m 1) (glueJ m k) hK hN (1 : ℤ)
  rw [sum_rankOne] at hcc hcj hck ⊢
  rw [latP_form] at hcc
  rw [glue_form_smul] at hcj hck
  set c := chargeCoord (latP m) (1 : ℤ) (a0 m)
  set lj := lamShift (latP m) (glueLat m 1) (glueIota m 1) (glueJ m j) (a0 m)
  set lk := lamShift (latP m) (glueLat m 1) (glueIota m 1) (glueJ m k) (a0 m)
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcc' : c * c = 2 * (m : ℂ) := by rw [hcc]; push_cast; ring
  have hcj' : c * lj = (j : ℂ) := by rw [hcj]; push_cast; ring
  have hck' : c * lk = (k : ℂ) := by rw [hck]; push_cast; ring
  have key : (2 * (m : ℂ)) * (lj * lk) = (j : ℂ) * k := by
    rw [← hcc', ← hcj', ← hck']; ring
  field_simp
  linear_combination key

/-- **The fractional power**: the leading coefficient of `𝒴(e^{λ_j}, z) e^{λ_k}` sits at
`z^{jk/(2m)}` (mode `n = −jk/(2m) − 1`), and it is nonzero — the intertwiner is the
Dong–Lepowsky generalized vertex operator `E⁻E⁺ e_{λ_j} z^{λ_j(0)}`. -/
theorem latticeIntwModes_leading_ne_zero (j k : ℤ) :
    latticeIntwModes m hm j k (-((j : ℂ) * k / (2 * m)) - 1)
        (isoE m j (glueJ m j) (latVacuumGen (latP m))) (isoE m k (glueJ m k) (latVacuumGen (latP m)))
      ≠ 0 := by
  have h := transportModes_ne_zero (isoE m j (glueJ m j)) (isoE m k (glueJ m k))
    (isoE m (j + k) (glueJ m j + glueJ m k))
    (latIntw_ne_zero (latP m) (glueLat m 1) (glueIota m 1) (latP_posDef m hm) (glueLat_even m 1)
      (glueLat_posDef m hm 1) (glueIota_isometry m 1) (glueJ m j) (glueJ m k))
  have hs : (((-(glueLat m 1).form (glueJ m j) (glueJ m k) - 1 : ℤ) : ℂ)
      + sval (latP m) (glueLat m 1) (glueIota m 1) (glueJ m j) (glueJ m k))
      = -((j : ℂ) * k / (2 * m)) - 1 := by
    rw [sval_eq _ _ _ (glueLat_posDef m hm 1), lamShift_mul_rankOne m hm j k]
    push_cast
    ring
  rw [hs] at h
  exact h

instance (j k : ℤ) : Nontrivial (IntertwiningOperator (latticeModule m hm j) (latticeModule m hm k)
    (latticeModule m hm (j + k))) :=
  ⟨⟨latticeIntertwiner m hm j k, 0, latticeIntertwiner_ne_zero m hm j k⟩⟩

/-- **`N^{λ_{j+k}}_{λ_j λ_k} ≥ 1`** for the rank-one lattice VOA `V_{2m}`, *given* that the
space of intertwining operators is finite-dimensional (the finiteness is proved separately). -/
theorem one_le_fusionRule_latticeModule (j k : ℤ)
    [FiniteDimensional ℂ (IntertwiningOperator (latticeModule m hm j) (latticeModule m hm k)
      (latticeModule m hm (j + k)))] :
    1 ≤ fusionRule (latticeModule m hm j) (latticeModule m hm k) (latticeModule m hm (j + k)) :=
  one_le_fusionRule_of_nontrivial _ _ _

end RankOne

end VOA.Huang.LatInt
