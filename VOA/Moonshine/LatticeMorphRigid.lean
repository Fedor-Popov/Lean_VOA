/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeMorph
import VOA.Examples.TripletLattice
import VOA.Examples.TripletScreening
import VOA.Moonshine.TrialityTheta

/-!
# Rigidity of lifts of `−1` to a lattice VOA  (M8g-0 bridge, part 3)

FLM's lifts of `−1 ∈ O(L)` to `Aut V_L` are unique up to the characters of `L`.  This file proves
the VOA-level statement needed for the `c_λ` residual of M8g-0:

  `exists_char_of_lift`: if `ψ ∈ Aut(V_L)` negates every Heisenberg weight-one state
  `h_a(−1)𝟙` and maps each momentum sector `F_λ = chargeSec λ` into `F_{−λ}`, then there is an
  additive character `d : L → ℂˣ` with `ψ = g_d ∘ θ` (`g_d = charLat d`, `e^λ ↦ d(λ) e^λ`).

So the unknown scalars of `Θ e^λ = c_λ e^{−λ}` are automatically a character, `c_λ = d(−λ)`, and
by `exists_half_char` / `charLat_thetaLat_conj` (`LatticeMorph.lean`) the lift is **conjugate to the
standard `θ`**: `ψ = g_e θ g_e⁻¹` with `2e = d` (`lift_eq_conj_theta`).

## Proof
`φ := ψ θ` fixes every `h_a(−1)𝟙`, preserves each `F_λ` and (being an automorphism) the
`L₀`-grading.  Hence `φ(e^λ) ∈ F_λ ∩ (V_L)_{½⟨λ,λ⟩} = ℂ e^λ` (`mem_bigradα_of_grading_of_charge`,
`gradingWN_zero_eq_span_one`), say `φ(e^λ) = d(λ) e^λ`.  Since the word states are iterated
Heisenberg modes `h_a(−1)𝟙₍₋ᵢ₋₁₎` applied to `e^λ` (`smul_heisSt`), `φ = d(λ)` on `F_λ`.
Applying `φ` to `e^α₍₋⟨α,β⟩₋₁₎ e^β = ε(α,β) e^{α+β} ≠ 0` gives `d(α+β) = d(α) d(β)`.

## Status
`sorry`-free; `#print axioms`: `[propext, Classical.choice, Quot.sound]`.  Unconditional.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct Matrix
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN MvPolynomial

variable (L : IntegralLattice) (hEven : L.Even) (hPos : L.PosDef)

/-- The Heisenberg weight-one state `h_a(−1)𝟙`. -/
noncomputable abbrev heisSt (a : Fin (rank L)) : LatModuleGen L := wordStateLatGen L [(0, a)] 0

/-- `h_a(−1)𝟙₍₋ᵢ₋₁₎ = h_a(−i−1)` on every state. -/
theorem smul_heisSt (a : Fin (rank L)) (i : ℕ) (w : LatModuleGen L) :
    (latticeVOAGen L hEven hPos).smul (heisSt L a) (-(i : ℤ) - 1) w
      = LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 a i) w := by
  change mode (YfullGen L hEven hPos (wordStateLatGen L [(0, a)] 0)) (-(i : ℤ) - 1) w = _
  rw [YfullGen_word, BgA.YwordLatGen_singleton, genFieldLatGen_zero, mode_apply,
    show -(-(i : ℤ) - 1) - 1 = (i : ℤ) by ring, alphaLatGen_apply, if_neg (by omega), add_zero]

/-- `e^α₍₋⟨α,β⟩₋₁₎ e^β = ε(α,β) e^{α+β}`. -/
theorem smul_latChargeGen (α β : L.carrier) :
    (latticeVOAGen L hEven hPos).smul (latChargeGen L α) (-(L.form α β) - 1) (latChargeGen L β)
      = latticeCocycle L α β • latChargeGen L (α + β) := by
  change mode (YfullGen L hEven hPos (wordStateLatGen L [] α)) _ (latStateGen L _ β) = _
  rw [YfullGen_word, YwordLatGen_nil, mode_apply, Yeαvec_tmul,
    show -(-(L.form α β) - 1) - 1 - L.form α β = 0 by ring, EEVec_vacuum, if_pos le_rfl,
    show Int.toNat 0 = 0 from rfl, vSchur_zero]
  rfl

theorem latticeCocycle_ne_zero (α β : L.carrier) : latticeCocycle L α β ≠ 0 := by
  intro h
  have := latticeCocycle_sq L α β
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem Aut.mem_grading {W : VertexOperatorAlgebra (LatModuleGen L)} (g : Aut W) {k : ℤ}
    {x : LatModuleGen L} (hx : x ∈ W.grading k) : g x ∈ W.grading k := by
  rw [← piHom_of_mem W hx, Aut.map_piHom]
  exact piHom_mem W k _

/-- The charge-`γ` vacuum spans the lowest piece: `F_γ ∩ (V_L)_{½⟨γ,γ⟩} = ℂ e^γ`. -/
theorem exists_smul_of_grading_of_charge (γ : L.carrier) {x : LatModuleGen L}
    (hg : x ∈ gradingLatGen L (halfNorm L γ)) (hc : x ∈ chargeSec L γ) :
    ∃ c : ℂ, x = c • latChargeGen L γ := by
  have h := Triplet.mem_bigradα_of_grading_of_charge L (halfNorm L γ) γ hg hc
  rw [sub_self] at h
  obtain ⟨q, hq, rfl⟩ := h
  rw [gradingZN_of_nonneg le_rfl, show (0 : ℤ).toNat = 0 from rfl,
    gradingWN_zero_eq_span_one] at hq
  rw [SetLike.mem_coe, Submodule.mem_span_singleton] at hq
  obtain ⟨c, rfl⟩ := hq
  refine ⟨c, ?_⟩
  rw [map_smul, mkEα_apply, latChargeGen, latStateGen, vacuumN]

theorem latChargeGen_mem_grading (γ : L.carrier) :
    latChargeGen L γ ∈ gradingLatGen L (halfNorm L γ) := by
  have hb : latChargeGen L γ ∈ bigradα L (0, γ) :=
    ⟨vacuumN (rank L), by rw [gradingZN_of_nonneg le_rfl]; exact vacuumN_mem_gradingWN _, rfl⟩
  have h := bigradα_le_gradingLatGen L 0 γ hb
  rwa [zero_add] at h

theorem thetaLat_mem_chargeSec {γ : L.carrier} {x : LatModuleGen L} (hx : x ∈ chargeSec L γ) :
    thetaLat L x ∈ chargeSec L (-γ) := by
  obtain ⟨q, rfl⟩ := hx
  rw [mkEα_apply, ← latStateGen, thetaLat_latStateGen]
  exact mem_chargeSec L _ _

/-- **Rigidity of lifts of `−1`.**  An automorphism of `V_L` that negates the Heisenberg
weight-one states and maps `F_λ` into `F_{−λ}` is `g_d ∘ θ` for an additive character
`d : L → ℂˣ`. -/
theorem exists_char_of_lift (ψ : Aut (latticeVOAGen L hEven hPos))
    (hh : ∀ a, ψ (heisSt L a) = -heisSt L a)
    (hsec : ∀ (γ : L.carrier) (x : LatModuleGen L), x ∈ chargeSec L γ → ψ x ∈ chargeSec L (-γ)) :
    ∃ d : L.carrier →+ Additive ℂˣ, ∀ x, ψ x = charLat L d (thetaLat L x) := by
  classical
  -- `φ = ψ θ`
  let φ : LatModuleGen L →ₗ[ℂ] LatModuleGen L := ψ.toLinearEquiv.toLinearMap ∘ₗ (thetaLat L).toLinearMap
  have hφ : ∀ x, φ x = ψ (thetaLat L x) := fun x => rfl
  have hφinj : Function.Injective φ := ψ.toLinearEquiv.injective.comp (thetaLat L).injective
  have hφsmul : ∀ u n v, φ ((latticeVOAGen L hEven hPos).smul u n v) = (latticeVOAGen L hEven hPos).smul (φ u) n (φ v) := by
    intro u n v
    rw [hφ, hφ, hφ]
    have h := thetaLat_mode L hEven hPos u n v
    change thetaLat L ((latticeVOAGen L hEven hPos).smul u n v) = (latticeVOAGen L hEven hPos).smul (thetaLat L u) n (thetaLat L v) at h
    rw [h, Aut.map_smul]
  have hφh : ∀ a, φ (heisSt L a) = heisSt L a := by
    intro a
    rw [hφ, heisSt, thetaLat_wordStateLatGen, List.length_singleton, pow_one, neg_zero,
      neg_one_smul, map_neg]
    erw [hh a]
    rw [neg_neg]
  have hφsec : ∀ γ x, x ∈ chargeSec L γ → φ x ∈ chargeSec L γ := by
    intro γ x hx
    have := hsec (-γ) _ (thetaLat_mem_chargeSec L hx)
    rwa [neg_neg] at this
  have hφgr : ∀ k x, x ∈ gradingLatGen L k → φ x ∈ gradingLatGen L k := by
    intro k x hx
    exact Aut.mem_grading L ψ (thetaLat_mem_gradingLatGen L hx)
  -- the scalars `d(γ)`
  have hex : ∀ γ, ∃ c : ℂ, φ (latChargeGen L γ) = c • latChargeGen L γ := fun γ =>
    exists_smul_of_grading_of_charge L γ (hφgr _ _ (latChargeGen_mem_grading L γ))
      (hφsec γ _ (mem_chargeSec L γ _))
  choose dfun hdfun using hex
  -- `φ = d(γ)` on the word states, hence on `F_γ`
  have hword : ∀ (l : List (ℕ × Fin (rank L))) γ,
      φ (wordStateLatGen L l γ) = dfun γ • wordStateLatGen L l γ := by
    intro l γ
    induction l with
    | nil => exact hdfun γ
    | cons ia rest ih =>
        obtain ⟨i, a⟩ := ia
        rw [wordStateLatGen_cons, ← smul_heisSt L hEven hPos, hφsmul, hφh, ih,
          PreVertexAlgebra.smul_smul_right]
  have hlat : ∀ (p : FockN (rank L)) γ, φ (latStateGen L p γ) = dfun γ • latStateGen L p γ := by
    intro p γ
    have h : φ ∘ₗ mkEα L γ = dfun γ • mkEα L γ := by
      refine (MvPolynomial.basisMonomials (ℕ × Fin (rank L)) ℂ).ext fun d => ?_
      rw [MvPolynomial.coe_basisMonomials, LinearMap.comp_apply, LinearMap.smul_apply, mkEα_apply]
      change φ (MvPolynomial.monomial d (1 : ℂ) ⊗ₜ[ℂ] eGen L γ)
        = dfun γ • (MvPolynomial.monomial d (1 : ℂ) ⊗ₜ[ℂ] eGen L γ)
      rw [← HeisenbergN.wordStateN_monoWordN, ← wordStateLatGen_eq, hword]
    exact LinearMap.congr_fun h p
  have hne : ∀ γ, dfun γ ≠ 0 := by
    intro γ h0
    have h := hdfun γ
    rw [h0, zero_smul] at h
    exact Screen.latStateGen_ne_zero L one_ne_zero γ (hφinj (h.trans (map_zero φ).symm))
  have hadd : ∀ α β, dfun (α + β) = dfun α * dfun β := by
    intro α β
    have h := hφsmul (latChargeGen L α) (-(L.form α β) - 1) (latChargeGen L β)
    rw [smul_latChargeGen, map_smul, hdfun, hdfun, hdfun, PreVertexAlgebra.smul_smul_left,
      PreVertexAlgebra.smul_smul_right, smul_latChargeGen, smul_smul, smul_smul] at h
    have hx : latticeCocycle L α β • latChargeGen L (α + β) ≠ 0 :=
      smul_ne_zero (latticeCocycle_ne_zero L α β) (Screen.latStateGen_ne_zero L one_ne_zero _)
    have h2 : (dfun (α + β) - dfun α * dfun β) • (latticeCocycle L α β • latChargeGen L (α + β)) = 0 := by
      rw [sub_smul, smul_smul, smul_smul, mul_comm (dfun (α + β)), h, smul_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hx
  have h0 : dfun 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    have : dfun 0 * (dfun 0 - 1) = 0 := by rw [mul_sub, ← h]; ring
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (hne 0)
    · exact sub_eq_zero.mp h1
  let d : L.carrier →+ Additive ℂˣ :=
    { toFun := fun γ => Additive.ofMul (Units.mk0 (dfun γ) (hne γ))
      map_zero' := by
        apply Additive.toMul.injective
        exact Units.ext (by simp [h0])
      map_add' := fun α β => by
        apply Additive.toMul.injective
        exact Units.ext (by simp [hadd]) }
  refine ⟨d, fun x => ?_⟩
  have hφd : φ = charLat L d := by
    refine LinearMap.ext_on_range (latStateGen_span L) fun q => ?_
    obtain ⟨p, γ⟩ := q
    rw [hlat, charLat_latStateGen L d hPos]
    rfl
  have := LinearMap.congr_fun hφd (thetaLat L x)
  rw [hφ, thetaLat_thetaLat] at this
  exact this

/-- **A lift of `−1` is conjugate to the standard `θ`**: under the hypotheses of
`exists_char_of_lift` there is a character `e` with `ψ = g_e θ g_e⁻¹`. -/
theorem lift_eq_conj_theta (ψ : Aut (latticeVOAGen L hEven hPos))
    (hh : ∀ a, ψ (heisSt L a) = -heisSt L a)
    (hsec : ∀ (γ : L.carrier) (x : LatModuleGen L), x ∈ chargeSec L γ → ψ x ∈ chargeSec L (-γ)) :
    ∃ e : L.carrier →+ Additive ℂˣ, ∀ x, ψ x = charLat L e (thetaLat L (charLat L (-e) x)) := by
  obtain ⟨d, hd⟩ := exists_char_of_lift L hEven hPos ψ hh hsec
  obtain ⟨e, he⟩ := exists_half_char L d
  refine ⟨e, fun x => ?_⟩
  rw [hd, charLat_thetaLat_conj L hPos e, he]

/-! ## The Heisenberg states `α(−1)𝟙` -/

theorem hSt_add (α β : L.carrier) : hSt L (α + β) = hSt L α + hSt L β := by
  rw [hSt_eq_sum, hSt_eq_sum, hSt_eq_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by rw [chargeCoord_add, add_smul]

theorem hSt_zero : hSt L 0 = 0 := by
  rw [hSt_eq_sum]; exact Finset.sum_eq_zero fun a _ => by rw [chargeCoord_zero, zero_smul]

theorem hSt_nsmul (n : ℕ) (α : L.carrier) : hSt L (n • α) = (n : ℂ) • hSt L α := by
  induction n with
  | zero => rw [zero_smul, hSt_zero, Nat.cast_zero, zero_smul]
  | succ n ih => rw [succ_nsmul, hSt_add, ih, Nat.cast_succ, add_smul, one_smul]

theorem coordR_basis (i : Fin (latRank L)) : coordR L (latticeBasis L i) = Pi.single i 1 := by
  funext j
  simp only [coordR, coord, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

include hPos in
/-- The Heisenberg states `h_a(−1)𝟙` lie in the span of the `α(−1)𝟙`, `α ∈ L`. -/
theorem heisSt_mem_span_hSt (a : Fin (rank L)) :
    heisSt L a ∈ Submodule.span ℂ (Set.range (hSt L)) := by
  classical
  set F : Matrix (Fin (latRank L)) (Fin (latRank L)) ℂ := (frame L).map Complex.ofRealHom
  have hF : IsUnit F.det := by
    rw [show F.det = Complex.ofRealHom (frame L).det from (RingHom.map_det _ _).symm]
    exact (frame_det_isUnit L hPos).map _
  set t : Fin (latRank L) → ℂ := Pi.single (rankEquiv L a) 1
  set u : Fin (latRank L) → ℂ := F⁻¹ *ᵥ t
  have hu : F *ᵥ u = t := by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hF, Matrix.one_mulVec]
  have hcc : ∀ (i : Fin (latRank L)) (b : Fin (rank L)),
      chargeCoord L (latticeBasis L i) b = F (rankEquiv L b) i := by
    intro i b
    rw [chargeCoord, orthCoord, coordR_basis]
    simp [F, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hsum : ∑ i, u i • hSt L (latticeBasis L i) = heisSt L a := by
    simp only [hSt_eq_sum, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single a]
    · rw [← Finset.sum_smul]
      have h := congrFun hu (rankEquiv L a)
      simp only [Matrix.mulVec, dotProduct, t, Pi.single_eq_same] at h
      rw [show ∑ i, u i * chargeCoord L (latticeBasis L i) a = 1 by
        rw [← h]; exact Finset.sum_congr rfl fun i _ => by rw [hcc, mul_comm]]
      rw [one_smul]
    · intro b _ hb
      rw [← Finset.sum_smul]
      have h := congrFun hu (rankEquiv L b)
      simp only [Matrix.mulVec, dotProduct, t] at h
      rw [Pi.single_apply, if_neg ((rankEquiv L).injective.ne hb)] at h
      rw [show ∑ i, u i * chargeCoord L (latticeBasis L i) b = 0 by
        rw [← h]; exact Finset.sum_congr rfl fun i _ => by rw [hcc, mul_comm]]
      rw [zero_smul]
    · intro h; exact absurd (Finset.mem_univ a) h
  rw [← hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- Variant of `lift_eq_conj_theta` with the Heisenberg hypothesis on all `α(−1)𝟙`. -/
theorem lift_eq_conj_theta' (ψ : Aut (latticeVOAGen L hEven hPos))
    (hh : ∀ α, ψ (hSt L α) = -hSt L α)
    (hsec : ∀ (γ : L.carrier) (x : LatModuleGen L), x ∈ chargeSec L γ → ψ x ∈ chargeSec L (-γ)) :
    ∃ e : L.carrier →+ Additive ℂˣ, ∀ x, ψ x = charLat L e (thetaLat L (charLat L (-e) x)) := by
  refine lift_eq_conj_theta L hEven hPos ψ (fun a => ?_) hsec
  suffices h : ∀ x ∈ Submodule.span ℂ (Set.range (hSt L)), ψ x = -x from
    h _ (heisSt_mem_span_hSt L hPos a)
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨α, rfl⟩ := hx
      exact hh α
  | zero => simp
  | add x y _ _ hx hy =>
      rw [map_add, hx, hy, neg_add]
  | smul c x _ hx =>
      rw [Aut.map_smul_c, hx, smul_neg]

end VOA.LatGen

namespace VOA.LatGen

open VOA VOA.IntegralLattice HeisenbergN

variable (K L : IntegralLattice) (ι : K.carrier →ₗ[ℤ] L.carrier)

theorem latMorphC_hSt (c : K.carrier → ℂ) (hc0 : c 0 = 1) (hK : K.PosDef) (α : K.carrier) :
    latMorphC K L ι c (hSt K α) = hSt L (ι α) := by
  rw [hSt, latMorphC_latStateGen, hc0, one_smul, fockMap_vSchur K L ι hK, map_zero]
  rfl

theorem coordEα_of_mem_chargeSec' {μ ν : L.carrier} (h : μ ≠ ν) {x : LatModuleGen L}
    (hx : x ∈ chargeSec L ν) : coordEα L μ x = 0 := by
  obtain ⟨q, rfl⟩ := hx
  rw [mkEα_apply, coordEα_apply, if_neg h]

/-- Momentum sectors pull back along `Φ`: `Φ y ∈ F_{ιμ} ⇒ y ∈ F_μ`. -/
theorem mem_chargeSec_of_latMorphC (c : K.carrier → ℂ) (hcne : ∀ α, c α ≠ 0) (hK : K.PosDef)
    (hL : L.PosDef) (hι : ∀ α β, L.form (ι α) (ι β) = K.form α β) (hr : rank K = rank L)
    {μ : K.carrier} {y : LatModuleGen K} (hy : latMorphC K L ι c y ∈ chargeSec L (ι μ)) :
    y ∈ chargeSec K μ := by
  apply mem_chargeSec_of_coordEα
  intro ν hν
  have h := coordEα_latMorphC K L ι c hK hι ν y
  rw [coordEα_of_mem_chargeSec' L ((isometry_injective K L ι hK hι).ne hν) hy, eq_comm,
    smul_eq_zero] at h
  rcases h with h | h
  · exact absurd h (hcne ν)
  · have he := (fockEquiv (oscMatrix K L ι) (oscMatrix_transpose_mul K L hK hL ι hι)
      (oscMatrix_mul_transpose K L hK hL ι hι hr)).injective
    exact he (by rw [fockEquiv_apply, h, map_zero])

end VOA.LatGen

namespace VOA

section Pullback

variable {𝒱 𝒲 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] [AddCommGroup 𝒲] [Module ℂ 𝒲]
  {V : VertexOperatorAlgebra 𝒱} {W : VertexOperatorAlgebra 𝒲} (Φ : 𝒱 →ₗ[ℂ] 𝒲)
  (hinj : Function.Injective Φ) (g : Aut W)
  (hg : (LinearMap.range Φ).map g.toLinearEquiv.toLinearMap = LinearMap.range Φ)

/-- The linear equivalence `Φ⁻¹ g Φ` of `𝒱`. -/
noncomputable def pullbackEquiv : 𝒱 ≃ₗ[ℂ] 𝒱 :=
  (LinearEquiv.ofInjective Φ hinj).trans
    ((g.toLinearEquiv.ofSubmodules _ _ hg).trans (LinearEquiv.ofInjective Φ hinj).symm)

theorem pullbackEquiv_spec (x : 𝒱) : Φ (pullbackEquiv Φ hinj g hg x) = g (Φ x) := by
  rw [pullbackEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.ofInjective_symm_apply]
  rfl

/-- **Pulling an automorphism back along an injective VOA homomorphism** whose image it
preserves. -/
noncomputable def Aut.pullback (hΦ : IsVOAHom V W Φ)
    (hω : Φ V.conformalVector = W.conformalVector) : Aut V where
  toLinearEquiv := pullbackEquiv Φ hinj g hg
  map_smul' u n v := by
    apply hinj
    rw [pullbackEquiv_spec, hΦ.map_smul, hΦ.map_smul, pullbackEquiv_spec, pullbackEquiv_spec]
    exact g.map_smul _ _ _
  map_vacuum := by
    apply hinj
    rw [pullbackEquiv_spec, hΦ.map_vacuum]
    exact g.map_vacuum
  map_omega := by
    apply hinj
    rw [pullbackEquiv_spec, hω]
    exact g.map_omega

theorem Aut.pullback_apply (hΦ : IsVOAHom V W Φ)
    (hω : Φ V.conformalVector = W.conformalVector) (x : 𝒱) :
    Φ (Aut.pullback Φ hinj g hg hΦ hω x) = g (Φ x) :=
  pullbackEquiv_spec Φ hinj g hg x

end Pullback

end VOA
