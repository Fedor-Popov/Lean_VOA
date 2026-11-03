/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaExistZhu
import VOA.Moonshine.FrameWeightTwo
import VOA.Moonshine.InvFormTP

/-!
# Top-level zero modes on `V₃⁺`, and the letters of `G = (V₀⁺)₂`  (R-top, source side)

The top-level residual `TopSigmaV3 s φ` (`SigmaExistLeech.lean`) needs, through
`topSigmaV3_of_zhuGenerated` (`SigmaExistZhu.lean`), the zero-mode identities
`φ (o(g) x) = o(σ g) φ x` for `g` in a Zhu-generating set `G` and `x ∈ (V₃⁺)₂`.  For the candidate
`G = (V₀⁺)₂` this file computes the **source** side explicitly and
reduces the clause to finitely many identities on basis vectors.

## The letters and the basis
* `qV a b = h_a(−1)h_b(−1)𝟙` (orthonormal coordinates `a, b` of `Λ ⊗ ℂ`, `quadSt`) and
  `lV γ = e^γ + e^{−γ}` (`γ ∈ Λ₀`) are elements of `V₀⁺`; they span `(V₀⁺)₂`
  (`grading_two_V0_le_span`, `G2_le_span`, with `γ` in the half `S₀ = halfFourChi 0`).
* `(V₃⁺)₂` is spanned by `x_n = e^n + e^{−n}`, `n ∈ S₁ = halfFourChi 1` (`OmegaV3_le_span`).
  Both spanning statements are dimension counts against `finrank_plusTwoChi` (`FrameWeightTwo`).

## The source zero modes (no `σ` involved)
* `smul_neg_one_one` — VOA-generic: if `u, v` act on `x` through their zero modes only, then
  `(u₍₋₁₎v)₍₁₎ x = μν x` (from `mode_iterate`).
* `actV_qV` — `o(h_a h_b) x_n = n_a n_b x_n` (diagonal).
* `actV_lV` — `o(e^γ + e^{−γ}) x_n = [⟨γ,n⟩ = −2] ε(γ,n) x_{γ+n} + [⟨γ,n⟩ = 2] ε(γ,−n) x_{γ−n}`
  (monomial; `form_bound`: `|⟨γ,n⟩| ≤ 2` because `Λ` has no roots).

## The reduction
* `hGφ_V3_of_basis` — the `hGφ` input of `topSigmaV3_of_zhuGenerated` for `G2 = (V₀⁺)₂`
  follows from the identities on the letters `qV a b`, `lV' γ` (`γ ∈ S₀`) and the basis vectors
  `x_n` (`n ∈ S₁`).  (`ZM`, `ZM_span`, `ZM_of_basis` are the linear-algebra wrappers.)

## Status
`sorry`-free; `#print axioms`: `[propext, Classical.choice, Quot.sound]`.  Unconditional.  
Reached from the umbrella `VOA/Moonshine.lean`.  Nothing here concerns `σ`; the target side is
`SigmaTopTarget.lean`/`SigmaTopFrame.lean`, `σ` is `SigmaTopSigma.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaTop

open VOA VOA.Moonshine VOA.Moonshine.TrialityTw VOA.Moonshine.SigmaExist VOA.IntegralLattice
open VOA.LatGen HeisenbergN MvPolynomial
open VOA.Moonshine.LatticeTwisted (hgen echg)
open Module (End)
open Submodule

/-! ## §1  A generic zero-mode computation -/

/-- If `u, v` act on `x` with only a zero mode (`u₍ᵢ₎x = δᵢ₀ μ x`, `v₍ᵢ₎x = δᵢ₀ ν x`, `i ≥ 0`),
then `(u₍₋₁₎v)₍₁₎ x = μν x`. -/
theorem smul_neg_one_one {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)
    (u v x : 𝒱) (μ ν : ℂ) (hu : ∀ i : ℕ, W.smul u i x = if i = 0 then μ • x else 0)
    (hv : ∀ i : ℕ, W.smul v i x = if i = 0 then ν • x else 0) :
    W.smul (W.smul u (-1) v) 1 x = (μ * ν) • x := by
  rw [VertexOperatorAlgebra.mode_iterate]
  rw [finsum_eq_single _ 0]
  · have h1 : W.smul v (1 + ((0 : ℕ) : ℤ)) x = 0 := by
      have := hv 1; simp only [one_ne_zero, if_false] at this
      rw [show (1 : ℤ) + ((0 : ℕ) : ℤ) = ((1 : ℕ) : ℤ) by norm_num, this]
    rw [h1, PreVertexAlgebra.smul_zero_right, zero_sub]
    have h2 := hu 0
    simp only [if_true] at h2
    rw [show ((0 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) from rfl, h2]
    rw [show (-1 : ℤ) + 1 - ((0 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) by norm_num,
      PreVertexAlgebra.smul_smul_right, hv 0]
    simp only [if_true, pow_zero, gBinom_zero, mul_one, one_smul, smul_smul]
    rw [show ((-1 : ℂ) ^ (-1 : ℤ)) = -1 by norm_num]
    rw [← neg_smul]; congr 1; ring
  · intro i hi
    have h1 : W.smul v (1 + (i : ℤ)) x = 0 := by
      have := hv (1 + i); simp only [show 1 + i ≠ 0 by omega, if_false] at this
      rw [show (1 : ℤ) + (i : ℤ) = ((1 + i : ℕ) : ℤ) by push_cast; ring, this]
    rw [h1, PreVertexAlgebra.smul_zero_right, hu i, if_neg hi, PreVertexAlgebra.smul_zero_right,
      smul_zero, sub_zero, smul_zero]

/-! ## §2  Weight-one Heisenberg states on charged vacua (general lattice) -/

section General

variable (L : IntegralLattice) (hEven : L.Even) (hPos : L.PosDef)

theorem hgen_eq_word (a : Fin (rank L)) : wordStateLatGen L [(0, a)] 0 = hgen L a := by
  rw [wordStateLatGen_eq, wordStateN_cons, wordStateN_nil, mul_one]; rfl

/-- `(h_a(−1)𝟙)₍ᵢ₎ e^γ = δᵢ₀ γ_a e^γ`. -/
theorem smul_hgen_echg (a : Fin (rank L)) (γ : L.carrier) (i : ℕ) :
    (latticeVOAGen L hEven hPos).smul (hgen L a) i (echg L γ)
      = if i = 0 then chargeCoord L γ a • echg L γ else 0 := by
  rw [LatticeTwisted.smul_hgen_echg_nonneg L hEven hPos a (Int.natCast_nonneg i)]
  simp only [Nat.cast_eq_zero]

/-- `(α(−1)𝟙)₍ᵢ₎ e^γ = δᵢ₀ ⟨α,γ⟩ e^γ`. -/
theorem smul_hSt_echg (α γ : L.carrier) (i : ℕ) :
    (latticeVOAGen L hEven hPos).smul (hSt L α) i (echg L γ)
      = if i = 0 then ((L.form α γ : ℤ) : ℂ) • echg L γ else 0 := by
  rw [hSt_eq_sum, smul_sum_left]
  simp only [PreVertexAlgebra.smul_smul_left, hgen_eq_word, smul_hgen_echg]
  split_ifs with hi
  · simp only [smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    rw [← sum_chargeCoord L hPos α γ]
  · simp

/-- `Q(a,b) = h_a(−1)h_b(−1)𝟙`. -/
noncomputable def quadSt (a b : Fin (rank L)) : LatModuleGen L :=
  (latticeVOAGen L hEven hPos).smul (hgen L a) (-1) (hgen L b)

theorem quadSt_eq (a b : Fin (rank L)) :
    quadSt L hEven hPos a b = ((X (0, a) : FockN (rank L)) * X (0, b)) ⊗ₜ[ℂ] eGen L 0 := by
  rw [quadSt, show (-1 : ℤ) = -((0 : ℕ) : ℤ) - 1 by norm_num, LatticeTwisted.smul_hgen_neg]
  rfl

/-- `D(α,β) = α(−1)β(−1)𝟙`. -/
noncomputable def quadH (α β : L.carrier) : LatModuleGen L :=
  (latticeVOAGen L hEven hPos).smul (hSt L α) (-1) (hSt L β)

/-- `o(h_a h_b) e^γ = γ_a γ_b e^γ`. -/
theorem quadSt_one_echg (a b : Fin (rank L)) (γ : L.carrier) :
    (latticeVOAGen L hEven hPos).smul (quadSt L hEven hPos a b) 1 (echg L γ)
      = (chargeCoord L γ a * chargeCoord L γ b) • echg L γ :=
  smul_neg_one_one _ _ _ _ _ _ (smul_hgen_echg L hEven hPos a γ) (smul_hgen_echg L hEven hPos b γ)

/-- `o(α(−1)β(−1)𝟙) e^γ = ⟨α,γ⟩⟨β,γ⟩ e^γ`. -/
theorem quadH_one_echg (α β γ : L.carrier) :
    (latticeVOAGen L hEven hPos).smul (quadH L hEven hPos α β) 1 (echg L γ)
      = (((L.form α γ : ℤ) : ℂ) * ((L.form β γ : ℤ) : ℂ)) • echg L γ :=
  smul_neg_one_one _ _ _ _ _ _ (smul_hSt_echg L hEven hPos α γ) (smul_hSt_echg L hEven hPos β γ)

end General

section GeneralLat

variable (L : IntegralLattice) (hEven : L.Even) (hPos : L.PosDef)

/-- `e^γ₍₁₎ e^n = [⟨γ,n⟩ = −2] ε(γ,n) e^{γ+n}` when `⟨γ,n⟩ ≥ −2`. -/
theorem echg_one_echg (γ n : L.carrier) (hge : -2 ≤ L.form γ n) :
    (latticeVOAGen L hEven hPos).smul (echg L γ) 1 (echg L n)
      = if L.form γ n = -2 then latticeCocycle L γ n • echg L (γ + n) else 0 := by
  rw [LatticeTwisted.smul_echg_echg]
  split_ifs with h1 h2 h2
  · rw [show (-1 - 1 - L.form γ n).toNat = 0 by omega, vSchur_zero]; rfl
  · omega
  · omega
  · rw [TensorProduct.zero_tmul, smul_zero]

end GeneralLat

/-! ## §3  The Leech lattice: norms -/

theorem leech_form_ge_four {v : leech.carrier} (hv : v ≠ 0) : 4 ≤ leech.form v v := by
  have hpos := leech_posDef v hv
  obtain ⟨k, hk⟩ := leech_even v
  have h2 := leech_no_roots v
  omega

theorem form_bound {γ n : leech.carrier} (hγ : γ ∈ lambda0) (hn : n ∉ lambda0)
    (hγ4 : leech.form γ γ = 4) (hn4 : leech.form n n = 4) :
    -2 ≤ leech.form γ n ∧ leech.form γ n ≤ 2 := by
  have hp : γ + n ≠ 0 := by
    intro h
    apply hn
    rw [show n = -γ by rw [← sub_eq_zero, sub_neg_eq_add, add_comm, h]]
    exact lambda0.neg_mem hγ
  have hm : γ - n ≠ 0 := by
    intro h
    apply hn
    rw [show n = γ by rw [sub_eq_zero] at h; exact h.symm]
    exact hγ
  have h1 := leech_form_ge_four hp
  have h2 := leech_form_ge_four hm
  have hs := leech.isSymm.eq n γ
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at h1 h2
  constructor <;> omega

/-- **`o(e^γ + e^{−γ})` on `e^n + e^{−n}`** (`γ ∈ Λ₀`, `n ∉ Λ₀`, both of norm 4): monomial,
`x_n ↦ [⟨γ,n⟩ = −2] ε(γ,n) x_{γ+n} + [⟨γ,n⟩ = 2] ε(γ,−n) x_{γ−n}`. -/
theorem frameX0_one_frameX0 {γ n : leech.carrier} (hγ : γ ∈ lambda0) (hn : n ∉ lambda0)
    (hγ4 : leech.form γ γ = 4) (hn4 : leech.form n n = 4) :
    leechVOA.smul (frameX0 γ) 1 (frameX0 n)
      = (if leech.form γ n = -2 then latticeCocycle leech γ n • frameX0 (γ + n) else 0)
        + (if leech.form γ n = 2 then latticeCocycle leech γ (-n) • frameX0 (γ - n) else 0) := by
  obtain ⟨hlo, hhi⟩ := form_bound hγ hn hγ4 hn4
  have e1 := echg_one_echg leech leech_even leech_posDef γ n hlo
  have e2 := echg_one_echg leech leech_even leech_posDef γ (-n)
    (by rw [leech_form_neg_right]; omega)
  have e3 := echg_one_echg leech leech_even leech_posDef (-γ) n
    (by rw [leech_form_neg_left]; omega)
  have e4 := echg_one_echg leech leech_even leech_posDef (-γ) (-n)
    (by rw [leech_form_neg_left, leech_form_neg_right, neg_neg]; omega)
  rw [leech_form_neg_right] at e2
  rw [leech_form_neg_left] at e3
  rw [leech_form_neg_left, leech_form_neg_right, neg_neg, latticeCocycle_neg_neg] at e4
  have h3 : latticeCocycle leech (-γ) n = latticeCocycle leech γ (-n) := by
    rw [← latticeCocycle_neg_neg, neg_neg]
  rw [h3] at e3
  rw [frameX0, frameX0, PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    PreVertexAlgebra.smul_add_right]
  change leechVOA.smul (echg leech γ) 1 (echg leech n) + leechVOA.smul (echg leech γ) 1 (echg leech (-n))
    + (leechVOA.smul (echg leech (-γ)) 1 (echg leech n) + leechVOA.smul (echg leech (-γ)) 1 (echg leech (-n))) = _
  rw [show leechVOA = latticeVOAGen leech leech_even leech_posDef from rfl, e1, e2, e3, e4]
  by_cases hc : leech.form γ n = -2
  · rw [if_pos hc, if_neg (by omega), if_neg (by omega), if_pos hc, if_pos hc, if_neg (by omega),
      frameX0, smul_add, add_zero, add_zero, neg_add]; rfl
  · by_cases hc' : leech.form γ n = 2
    · rw [if_neg hc, if_pos (by omega), if_pos (by omega), if_neg hc, if_neg hc, if_pos hc',
        frameX0, smul_add, zero_add, add_zero, zero_add, sub_eq_add_neg, neg_add, neg_neg]
    · rw [if_neg hc, if_neg (by omega), if_neg (by omega), if_neg hc, if_neg hc, if_neg hc']
      simp

/-! ## §4  The weight-two letters of `V₀⁺` and the basis of `(V₃⁺)₂` -/

/-- `h_a(−1)h_b(−1)𝟙 ∈ V_Λ` (orthonormal coordinates `a, b` of `S[θ]`/`M(1)`). -/
noncomputable abbrev qL (a b : Fin (rank leech)) : LatModuleGen leech :=
  quadSt leech leech_even leech_posDef a b

theorem qL_theta (a b : Fin (rank leech)) : thetaLat leech (qL a b) = qL a b := by
  unfold qL
  rw [quadSt_eq, thetaLat_tmul, sigmaN_mul, sigmaN_X, sigmaN_X, neg_mul_neg, neg_zero]

theorem qL_frame (a b : Fin (rank leech)) : chiLat leech frameChar (qL a b) = qL a b := by
  unfold qL
  rw [quadSt_eq, chiLat_tmul, chiSign_zero, one_smul]

/-- `h_a(−1)h_b(−1)𝟙 ∈ V_Λ⁺`. -/
noncomputable def qP (a b : Fin (rank leech)) : VPlus :=
  ⟨qL a b, (mem_leechVOAPlus_iff _).mpr (qL_theta a b)⟩

theorem qP_mem (a b : Fin (rank leech)) : qP a b ∈ V0Sub.carrier := by
  rw [V0Sub_carrier, mem_frameSector, Extraspecial.sgn_zero, one_smul]
  exact qL_frame a b

/-- The quadratic letter `h_a(−1)h_b(−1)𝟙 ∈ V₀⁺`. -/
noncomputable def qV (a b : Fin (rank leech)) : V0Sub.carrier := ⟨qP a b, qP_mem a b⟩

theorem frameX0P_mem_V0 {γ : leech.carrier} (hγ : γ ∈ lambda0) : frameX0P γ ∈ V0Sub.carrier := by
  rw [V0Sub_carrier, mem_frameSector_zero_iff]
  intro α hα
  have h1 : α ≠ γ := fun h => hα (h ▸ hγ)
  have h2 : α ≠ -γ := fun h => hα (by rw [h]; exact lambda0.neg_mem hγ)
  change coordEα leech α (frameX0 γ) = 0
  rw [frameX0, map_add, coordEα_latChargeGen, coordEα_latChargeGen, if_neg h1, if_neg h2, add_zero]

/-- The lattice letter `e^γ + e^{−γ} ∈ V₀⁺` (`γ ∈ Λ₀`). -/
noncomputable def lV (γ : leech.carrier) (hγ : γ ∈ lambda0) : V0Sub.carrier :=
  ⟨frameX0P γ, frameX0P_mem_V0 hγ⟩

/-- **Source, Heisenberg letters**: `o(h_a h_b) x_n = n_a n_b x_n` on `x_n = e^n + e^{−n}`. -/
theorem actV_qV (a b : Fin (rank leech)) (n : leech.carrier) :
    actV (qV a b) 1 (frameX0P n)
      = (chargeCoord leech n a * chargeCoord leech n b) • frameX0P n := by
  apply Subtype.ext
  change leechVOA.smul (qL a b) 1 (frameX0 n) = _
  rw [frameX0, PreVertexAlgebra.smul_add_right]
  change (latticeVOAGen leech leech_even leech_posDef).smul (qL a b) 1 (echg leech n)
    + (latticeVOAGen leech leech_even leech_posDef).smul (qL a b) 1 (echg leech (-n)) = _
  rw [quadSt_one_echg, quadSt_one_echg, chargeCoord_neg, chargeCoord_neg, neg_mul_neg]
  change _ = (chargeCoord leech n a * chargeCoord leech n b) • (echg leech n + echg leech (-n))
  rw [smul_add]

/-- **Source, lattice letters**: `o(e^γ + e^{−γ})` permutes the `x_n` monomially. -/
theorem actV_lV {γ n : leech.carrier} (hγ : γ ∈ lambda0) (hn : n ∉ lambda0)
    (hγ4 : leech.form γ γ = 4) (hn4 : leech.form n n = 4) :
    actV (lV γ hγ) 1 (frameX0P n)
      = (if leech.form γ n = -2 then latticeCocycle leech γ n • frameX0P (γ + n) else 0)
        + (if leech.form γ n = 2 then latticeCocycle leech γ (-n) • frameX0P (γ - n) else 0) := by
  apply Subtype.ext
  change leechVOA.smul (frameX0 γ) 1 (frameX0 n) = _
  rw [frameX0_one_frameX0 hγ hn hγ4 hn4]
  split_ifs <;> simp [frameX0P]

theorem qP_mem_grading (a b : Fin (rank leech)) : qP a b ∈ leechVOAPlus.grading 2 := by
  change qL a b ∈ gradingLatGen leech 2
  have hq : ((X (0, a) : FockN (rank leech)) * X (0, b)) ∈ quadFock (rank leech) := by
    refine Submodule.subset_span ⟨s(a, b), ?_⟩
    change MvPolynomial.monomial (quadExp (rank leech) s(a, b)) 1 = _
    rw [quadExp_mk, ← mul_one (1 : ℂ), ← MvPolynomial.monomial_mul]
    rfl
  have := quad_mem_plusTwoChi_zero hq
  unfold qL
  rw [quadSt_eq]
  exact ((mem_plusTwo leech).mp (mem_plusTwoChi.mp this).1).1

theorem lV_mem_grading {γ : leech.carrier} (hγ : γ ∈ lambda0) (hγ4 : leech.form γ γ = 4) :
    ((lV γ hγ : V0Sub.carrier) : VPlus) ∈ leechVOAPlus.grading 2 := by
  have h := InvForm.frameX0P_mem_grading γ
  have h2 : LatGen.halfNorm leech γ = 2 := by
    have := two_halfNorm leech leech_even γ
    omega
  rwa [h2] at h

/-! ## §5  Spanning: `(V₃⁺)₂` and `(V₀⁺)₂` by the explicit letters -/

open Classical in
theorem mem_halfFourChi {i : ZMod 2} {α : leech.carrier} (h : α ∈ halfFourChi i) :
    leech.form α α = 4 ∧ frameChar α = i := by
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
  exact ⟨(mem_normFour leech leech_posDef).mp (Finset.mem_filter.mp h1).1, h2⟩

theorem bigradα_zero_eq (α : leech.carrier) :
    bigradα leech (0, α) = span ℂ {latChargeGen leech α} := by
  haveI : FiniteDimensional ℂ (bigradα leech (0, α)) :=
    Module.finite_of_finrank_eq_succ (finrank_bigradα_zero leech α)
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [span_le, Set.singleton_subset_iff]; exact latChargeGen_mem_bigradα leech α
  · rw [finrank_bigradα_zero, finrank_span_singleton]
    exact Screen.latStateGen_ne_zero leech one_ne_zero α

theorem fPlus_latChargeGen (α : leech.carrier) : fPlus (latChargeGen leech α) = frameX0 α := by
  rw [fPlus_apply, thetaLat_latChargeGen]; rfl

theorem chargeHalfChi_le_comap (i : ZMod 2) :
    chargeHalfChi i ≤ (span ℂ (frameX0 '' (halfFourChi i : Set leech.carrier))).comap fPlus := by
  refine iSup₂_le fun α hα => ?_
  rw [bigradα_zero_eq, span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_comap,
    fPlus_latChargeGen]
  exact subset_span ⟨α, hα, rfl⟩

theorem plusTwoChi_one_eq : plusTwoChi 1 = (chargeHalfChi 1).map fPlus := by
  haveI : FiniteDimensional ℂ (gradingLatGen leech 2) :=
    gradingLatGen_finrank_of_posDef leech leech_even leech_posDef 2
  haveI : FiniteDimensional ℂ (plusTwo leech) := Submodule.finiteDimensional_of_le inf_le_left
  haveI : FiniteDimensional ℂ (plusTwoChi 1) := Submodule.finiteDimensional_of_le inf_le_left
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩; exact fPlus_mem_plusTwoChi 1 hy
  · rw [finrank_map_fPlus, finrank_plusTwoChi.2]

theorem coe_mem_span_frameX0P {S : Set leech.carrier} {x : VPlus}
    (h : (x : LatModuleGen leech) ∈ span ℂ (frameX0 '' S)) : x ∈ span ℂ (frameX0P '' S) := by
  have hS : frameX0 '' S = (orbifold (Subgroup.zpowers leechTheta)).carrier.subtype '' (frameX0P '' S) := by
    rw [Set.image_image]; rfl
  rw [hS, Submodule.span_image] at h
  obtain ⟨x', hx', hxx'⟩ := h
  rwa [show x' = x from Subtype.ext hxx'] at hx'

/-- **`(V₃⁺)₂ = span {e^n + e^{−n} : n ∈ S₁}`** (`S₁` = half of the odd norm-4 vectors). -/
theorem OmegaV3_le_span : OmegaV3 ≤ span ℂ (frameX0P '' (halfFourChi 1 : Set leech.carrier)) := by
  intro x hx
  apply coe_mem_span_frameX0P
  have hy : (x : LatModuleGen leech) ∈ plusTwoChi 1 :=
    mem_plusTwoChi.mpr ⟨(mem_plusTwo leech).mpr ⟨hx.2, (mem_leechVOAPlus_iff _).mp x.2⟩,
      mem_frameSector.mp hx.1⟩
  rw [plusTwoChi_one_eq] at hy
  obtain ⟨z, hz, hzx⟩ := hy
  rw [← hzx]
  exact chargeHalfChi_le_comap 1 hz

theorem frameX0P_mem_OmegaV3 {n : leech.carrier} (hn : n ∈ halfFourChi 1) : frameX0P n ∈ OmegaV3 := by
  obtain ⟨h4, h1⟩ := mem_halfFourChi hn
  have hn0 : n ∉ lambda0 := by rw [mem_lambda0, h1]; exact one_ne_zero
  refine ⟨frameX0_mem_frameSector_one hn0, ?_⟩
  have h := InvForm.frameX0P_mem_grading n
  have h2 : LatGen.halfNorm leech n = 2 := by
    have := two_halfNorm leech leech_even n
    omega
  rwa [h2] at h

/-- `quadFock.map (mkEα 0) ⊆ span {h_a(−1)h_b(−1)𝟙}`. -/
theorem quadFock_map_le :
    (quadFock (rank leech)).map (mkEα leech 0) ≤ span ℂ (Set.range fun p : Fin (rank leech) × Fin (rank leech) => qL p.1 p.2) := by
  rw [quadFock, Submodule.map_span, span_le]
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  induction s using Sym2.ind with
  | h a b =>
    refine subset_span ⟨(a, b), ?_⟩
    change quadSt leech leech_even leech_posDef a b = mkEα leech 0 (MvPolynomial.monomial (quadExp (rank leech) s(a, b)) 1)
    rw [quadExp_mk, ← mul_one (1 : ℂ), ← MvPolynomial.monomial_mul, quadSt_eq]
    rfl

theorem plusTwoChi_zero_eq :
    plusTwoChi 0 = (quadFock (rank leech)).map (mkEα leech 0) ⊔ (chargeHalfChi 0).map fPlus := by
  haveI : FiniteDimensional ℂ (gradingLatGen leech 2) :=
    gradingLatGen_finrank_of_posDef leech leech_even leech_posDef 2
  haveI : FiniteDimensional ℂ (plusTwo leech) := Submodule.finiteDimensional_of_le inf_le_left
  haveI : FiniteDimensional ℂ (plusTwoChi 0) := Submodule.finiteDimensional_of_le inf_le_left
  haveI := gradingWN_finiteDimensional (rank leech) 2
  haveI : FiniteDimensional ℂ (quadFock (rank leech)) :=
    Submodule.finiteDimensional_of_le (quadFock_le _)
  haveI : FiniteDimensional ℂ (chargeHalfChi 0) :=
    (finrank_biSup_of_iSupIndep _ (iSupIndep_bigradα_zero leech) _).1
  have hle0 : (quadFock (rank leech)).map (mkEα leech 0) ⊔ (chargeHalfChi 0).map fPlus
      ≤ plusTwoChi 0 := by
    refine sup_le ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩; exact quad_mem_plusTwoChi_zero hp
    · rintro _ ⟨y, hy, rfl⟩; exact fPlus_mem_plusTwoChi 0 hy
  have hdisj : Disjoint ((quadFock (rank leech)).map (mkEα leech 0)) ((chargeHalfChi 0).map fPlus) := by
    refine (disjoint_bigradα_chargeFour leech leech_posDef).mono ?_ ?_
    · rw [bigradα]; refine Submodule.map_mono ?_
      rw [gradingZN_of_nonneg (by norm_num)]; exact quadFock_le _
    · rintro _ ⟨y, hy, rfl⟩
      rw [fPlus_apply]
      exact Submodule.add_mem _ (chargeHalf_le leech leech_posDef (chargeHalfChi_le 0 hy))
        (chargeHalfNeg_le leech leech_posDef
          (thetaLat_mem_chargeHalfNeg leech leech_posDef (chargeHalfChi_le 0 hy)))
  have hquad : Module.finrank ℂ ↥((quadFock (rank leech)).map (mkEα leech 0)) = 300 := by
    rw [← (Submodule.equivMapOfInjective _ (mkEα_injective leech 0) _).finrank_eq,
      finrank_quadFock, leech_rank]
    rfl
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    ((quadFock (rank leech)).map (mkEα leech 0)) ((chargeHalfChi 0).map fPlus)
  rw [hdisj.eq_bot, finrank_bot, add_zero, hquad, finrank_map_fPlus] at hs
  symm
  refine Submodule.eq_of_le_of_finrank_eq hle0 ?_
  rw [hs, finrank_plusTwoChi.1]

/-- **`(V₀⁺)₂ = span {h_a(−1)h_b(−1)𝟙} + span {e^γ + e^{−γ} : γ ∈ S₀}`.** -/
theorem grading_two_V0_le_span {g : VPlus} (hg : g ∈ frameSector 0) (h2 : g ∈ leechVOAPlus.grading 2) :
    g ∈ span ℂ (Set.range (fun p : Fin (rank leech) × Fin (rank leech) => qP p.1 p.2)
      ∪ frameX0P '' (halfFourChi 0 : Set leech.carrier)) := by
  have hy : (g : LatModuleGen leech) ∈ plusTwoChi 0 :=
    mem_plusTwoChi.mpr ⟨(mem_plusTwo leech).mpr ⟨h2, (mem_leechVOAPlus_iff _).mp g.2⟩,
      mem_frameSector.mp hg⟩
  rw [plusTwoChi_zero_eq] at hy
  have hS : (fun x : LatModuleGen leech => x) '' ((Set.range fun p : Fin (rank leech) × Fin (rank leech) => qL p.1 p.2)
      ∪ frameX0 '' (halfFourChi 0 : Set leech.carrier)) =
      (orbifold (Subgroup.zpowers leechTheta)).carrier.subtype '' (Set.range (fun p : Fin (rank leech) × Fin (rank leech) => qP p.1 p.2)
      ∪ frameX0P '' (halfFourChi 0 : Set leech.carrier)) := by
    rw [Set.image_id', Set.image_union, ← Set.range_comp, Set.image_image]; rfl
  have hmem : (g : LatModuleGen leech) ∈ span ℂ ((fun x : LatModuleGen leech => x) ''
      ((Set.range fun p : Fin (rank leech) × Fin (rank leech) => qL p.1 p.2)
      ∪ frameX0 '' (halfFourChi 0 : Set leech.carrier))) := by
    rw [Set.image_id', Submodule.span_union]
    obtain ⟨y, hy1, z, hz, hyz⟩ := Submodule.mem_sup.mp hy
    rw [← hyz]
    refine Submodule.add_mem_sup (quadFock_map_le hy1) ?_
    obtain ⟨z', hz', rfl⟩ := hz
    exact chargeHalfChi_le_comap 0 hz'
  rw [hS, Submodule.span_image] at hmem
  obtain ⟨x', hx', hxx'⟩ := hmem
  rwa [show x' = g from Subtype.ext hxx'] at hx'

/-! ## §6  Reduction of the zero-mode clause on `G = (V₀⁺)₂` to the explicit letters -/

/-- `G = (V₀⁺)₂`, the weight-two letters (the Zhu-generator candidate). -/
def G2 : Set V0Sub.carrier := {g | (g : VPlus) ∈ leechVOAPlus.grading 2}

open Classical in
/-- `γ ↦ e^γ + e^{−γ}` as a total map into `V₀⁺` (junk value `0` off `Λ₀`). -/
noncomputable def lV' (γ : leech.carrier) : V0Sub.carrier :=
  if h : γ ∈ lambda0 then lV γ h else 0

theorem lV'_eq {γ : leech.carrier} (h : γ ∈ lambda0) : lV' γ = lV γ h := by
  rw [lV', dif_pos h]

theorem mem_lambda0_of_halfFourChi_zero {γ : leech.carrier} (h : γ ∈ halfFourChi 0) : γ ∈ lambda0 :=
  (mem_lambda0 γ).mpr (mem_halfFourChi h).2

theorem G2_le_span {g : V0Sub.carrier} (hg : g ∈ G2) :
    g ∈ span ℂ (Set.range (fun p : Fin (rank leech) × Fin (rank leech) => qV p.1 p.2)
      ∪ lV' '' (halfFourChi 0 : Set leech.carrier)) := by
  have h := grading_two_V0_le_span (by rw [← V0Sub_carrier]; exact g.2) hg
  have hS : Set.range (fun p : Fin (rank leech) × Fin (rank leech) => qP p.1 p.2)
      ∪ frameX0P '' (halfFourChi 0 : Set leech.carrier)
      = V0Sub.carrier.subtype '' (Set.range (fun p : Fin (rank leech) × Fin (rank leech) => qV p.1 p.2)
      ∪ lV' '' (halfFourChi 0 : Set leech.carrier)) := by
    rw [Set.image_union, ← Set.range_comp, Set.image_image]
    congr 1
    refine Set.image_congr fun γ hγ => ?_
    rw [lV'_eq (mem_lambda0_of_halfFourChi_zero hγ)]; rfl
  rw [hS, Submodule.span_image] at h
  obtain ⟨g', hg', hgg'⟩ := h
  rwa [show g' = g from Subtype.ext hgg'] at hg'

theorem actV_add_left' (u v : V0Sub.carrier) (n : ℤ) (y : VPlus) :
    actV (u + v) n y = actV u n y + actV v n y := actV_add_left u v n y

theorem actV_smul_left (c : ℂ) (u : V0Sub.carrier) (n : ℤ) (y : VPlus) :
    actV (c • u) n y = c • actV u n y := by
  simp only [actV, Submodule.coe_smul, map_smul, mode_smul, LinearMap.smul_apply]

theorem actT_smul_left (c : ℂ) (u : V0Sub.carrier) (n : ℤ) (y : TP) :
    actT (c • u) n y = c • actT u n y := by
  simp only [actT, Submodule.coe_smul, map_smul, mode_smul, LinearMap.smul_apply]

theorem sig_add (u v : V0Sub.carrier) : sig (u + v) = sig u + sig v :=
  v0Sigma.toLinearEquiv.map_add u v

theorem sig_smul (c : ℂ) (u : V0Sub.carrier) : sig (c • u) = c • sig u :=
  v0Sigma.toLinearEquiv.map_smul c u

theorem sig_zero : sig 0 = 0 := v0Sigma.toLinearEquiv.map_zero

/-- The zero-mode identity for a fixed letter `g`, as a predicate (linear in `g`). -/
def ZM (φ : VPlus →ₗ[ℂ] TP) (X : Set VPlus) (g : V0Sub.carrier) : Prop :=
  ∀ x ∈ X, φ (actV g 1 x) = actT (sig g) 1 (φ x)

theorem ZM_span (φ : VPlus →ₗ[ℂ] TP) (X : Set VPlus) {S : Set V0Sub.carrier}
    (hS : ∀ g ∈ S, ZM φ X g) : ∀ g ∈ span ℂ S, ZM φ X g := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg => exact hS g hg
  | zero =>
    intro x _
    rw [sig_zero]
    simp only [actV, actT, ZeroMemClass.coe_zero, map_zero, mode_zero, LinearMap.zero_apply]
  | add u v _ _ hu hv =>
    intro x hx
    rw [actV_add_left', map_add, hu x hx, hv x hx, sig_add, actT_add_left]
  | smul c u _ hu =>
    intro x hx
    rw [actV_smul_left, map_smul, hu x hx, sig_smul, actT_smul_left]

theorem ZM_of_basis (φ : VPlus →ₗ[ℂ] TP) (g : V0Sub.carrier)
    (h : ∀ n ∈ halfFourChi 1, φ (actV g 1 (frameX0P n)) = actT (sig g) 1 (φ (frameX0P n))) :
    ZM φ OmegaV3 g := by
  intro x hx
  have hxs := OmegaV3_le_span hx
  clear hx
  induction hxs using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, hn, rfl⟩ := hy
    exact h n hn
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]
  | smul c y _ hy => rw [map_smul, map_smul, hy, map_smul, map_smul]

/-- **Basis reduction of the zero-mode clause on `G = (V₀⁺)₂`, source `V₃⁺`.**  It suffices to
check `φ(o(g) x_n) = o(σ g) φ(x_n)` for the letters `g = h_a(−1)h_b(−1)𝟙`, `g = e^γ + e^{−γ}`
(`γ ∈ S₀`) and the basis vectors `x_n = e^n + e^{−n}` (`n ∈ S₁`).  The output is exactly the
`hGφ` input of `topSigmaV3_of_zhuGenerated`. -/
theorem hGφ_V3_of_basis (φ : VPlus →ₗ[ℂ] TP)
    (hQ : ∀ a b : Fin (rank leech), ∀ n ∈ halfFourChi 1,
      φ (actV (qV a b) 1 (frameX0P n)) = actT (sig (qV a b)) 1 (φ (frameX0P n)))
    (hL : ∀ γ ∈ halfFourChi 0, ∀ n ∈ halfFourChi 1,
      φ (actV (lV' γ) 1 (frameX0P n)) = actT (sig (lV' γ)) 1 (φ (frameX0P n))) :
    ∀ g ∈ G2, ∃ k : ℤ, (g : VPlus) ∈ leechVOAPlus.grading k ∧
      ∀ x ∈ OmegaV3, φ (actV g (k - 1) x) = actT (sig g) (k - 1) (φ x) := by
  intro g hg
  refine ⟨2, hg, ?_⟩
  rw [show (2 : ℤ) - 1 = 1 by norm_num]
  have hspan := G2_le_span hg
  have hbasis : ∀ g' ∈ Set.range (fun p : Fin (rank leech) × Fin (rank leech) => qV p.1 p.2)
      ∪ lV' '' (halfFourChi 0 : Set leech.carrier), ZM φ OmegaV3 g' := by
    rintro g' (⟨p, rfl⟩ | ⟨γ, hγ, rfl⟩)
    · exact ZM_of_basis φ _ (hQ p.1 p.2)
    · exact ZM_of_basis φ _ (hL γ hγ)
  exact ZM_span φ OmegaV3 hbasis g hspan

end VOA.Moonshine.SigmaTop
