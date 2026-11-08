/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.AutVnat
import VOA.Moonshine.AutFaithful
import VOA.Moonshine.AutChargeEigen
import VOA.Moonshine.AutTwistedExclusion
import VOA.Moonshine.InvFormTP

/-!
# Faithfulness of `Aut V♮` on the Griess algebra — the eigenvector step on `V♮`
(Aut(V♮) campaign, step 3, route C, node C7 part 1, `Notes/MONSTER_AUT_PLAN.md`)

An automorphism `g` of `V♮` that fixes `V♮₂` pointwise fixes the quadratic states
`q_ab = (h_a(−1)h_b(−1)𝟙, 0)`, hence commutes with their zero modes.  The vector `(x_β, 0)` is a
joint eigenvector of these zero modes with eigenvalues `β_a β_b`, and so is its image under `g`.
On the untwisted block such eigenvectors are multiples of `x_β` (`eigen_quadState_span` and
`θ`-invariance); on the twisted block there are none (`VnatVOA_twisted_outer_eigen_eq_zero`).
Hence `g (x_β, 0) = c_β (x_β, 0)`.

## Main results
* `qP_coe`, `smul_quadState_latChargeGen`, `smul_qP_frameX0P` — `o(q_ab) x_β = β_aβ_b x_β`.
* ⭐ `eigen_plus` — in `V_Λ⁺`, a joint eigenvector with eigenvalues `β_aβ_b` is a multiple of `x_β`.
* `VnatVOA_smul_inl` — the block form of `(u, 0)₍ₙ₎`.
* ⭐ `aut_frameX0P_eigen` — `g (x_β, 0) = c • (x_β, 0)` for `g` fixing `V♮₂`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.AutMonster

open VOA VOA.Moonshine LatGen IntegralLattice HeisenbergN SigmaTop

/-! ## `o(q_ab)` on the lattice vectors -/

theorem qP_coe (a b : Fin (rank leech)) :
    ((qP a b : VPlus) : LatModuleGen leech) = quadState leech a b :=
  (AutZeroTw.quadState_eq_quadSt leech leech_even leech_posDef a b).symm

/-- `o(q_ab) e^γ = γ_aγ_b e^γ` (the Fock part of `e^γ` is the vacuum, killed by `N_ab`). -/
theorem smul_quadState_latChargeGen (L : IntegralLattice) (hEven : L.Even) (hPos : L.PosDef)
    (a b : Fin (rank L)) (γ : L.carrier) :
    (latticeVOAGen L hEven hPos).smul (quadState L a b) 1 (latChargeGen L γ)
      = (chargeCoord L γ a * chargeCoord L γ b) • latChargeGen L γ := by
  have hN : nprod (currentN_isField (rank L) 1 a) (currentN_isField (rank L) 1 b) (-2)
      (vacuumN (rank L)) = 0 := by
    rw [nprod_currentN_neg_two a b _ 0 (fun v hv => by
      rw [vacuumN, MvPolynomial.vars_one] at hv; exact absurd hv (Finset.notMem_empty v))]
    simp
  change _ = _ • latStateGen L (vacuumN (rank L)) γ
  rw [latChargeGen, smul_quadState_one, hN, add_zero, latStateGen, latStateGen,
    TensorProduct.smul_tmul']

/-- `o(q_ab) x_β = β_aβ_b x_β` in `V_Λ⁺`. -/
theorem smul_qP_frameX0P (a b : Fin (rank leech)) (β : leech.carrier) :
    leechVOAPlus.smul (qP a b) 1 (frameX0P β)
      = (chargeCoord leech β a * chargeCoord leech β b) • frameX0P β := by
  apply Subtype.ext
  rw [plus_smul_coe, qP_coe]
  change leechVOA.smul _ 1 (latChargeGen leech β + latChargeGen leech (-β)) = _
  rw [PreVertexAlgebra.smul_add_right]
  change (latticeVOAGen leech leech_even leech_posDef).smul _ 1 _
    + (latticeVOAGen leech leech_even leech_posDef).smul _ 1 _ = _
  rw [smul_quadState_latChargeGen, smul_quadState_latChargeGen, chargeCoord_neg, chargeCoord_neg,
    neg_mul_neg, ← smul_add]
  rfl

/-! ## Joint eigenvectors in `V_Λ⁺` -/

theorem leech_two_le_rank : 2 ≤ rank leech := by rw [leech_rank]; norm_num

/-- ⭐ In `V_Λ⁺`, a joint eigenvector of all `o(q_ab)` with eigenvalues `β_aβ_b` is `c · x_β`. -/
theorem eigen_plus (β : leech.carrier) (x : VPlus)
    (h : ∀ a b, leechVOAPlus.smul (qP a b) 1 x = (chargeCoord leech β a * chargeCoord leech β b) • x) :
    ∃ c : ℂ, x = c • frameX0P β := by
  classical
  have h' : ∀ a b, (latticeVOAGen leech leech_even leech_posDef).smul (quadState leech a b) 1
      (x : LatModuleGen leech) = (chargeCoord leech β a * chargeCoord leech β b) • (x : LatModuleGen leech) := by
    intro a b
    have := congrArg Subtype.val (h a b)
    rwa [plus_smul_coe, qP_coe] at this
  obtain ⟨c₁, c₂, hx⟩ := eigen_quadState_span leech leech_even leech_posDef
    (AutZeroTw.exists_ne_of_two_le leech_two_le_rank) β x h'
  -- `θ`-invariance forces `c₁ = c₂` (or `β = 0`)
  have hθ : thetaLat leech (x : LatModuleGen leech) = x := (mem_leechVOAPlus_iff _).1 x.2
  rw [hx, map_add, map_smul, map_smul, thetaLat_latChargeGen, thetaLat_latChargeGen, neg_neg] at hθ
  by_cases hβ0 : β = 0
  · subst hβ0
    refine ⟨(c₁ + c₂) / 2, Subtype.ext ?_⟩
    rw [hx]
    change _ = ((c₁ + c₂) / 2) • (latChargeGen leech 0 + latChargeGen leech (-0))
    simp only [neg_zero]
    rw [← add_smul, ← two_smul ℂ (latChargeGen leech 0), smul_smul]
    congr 1
    ring
  · have hβn : β ≠ -β := by
      intro hb
      apply hβ0
      have hform : leech.form β β = leech.form β (-β) := by rw [← hb]
      rw [map_neg] at hform
      by_contra hne
      have := leech_posDef β hne
      omega
    have hc : c₁ = c₂ := by
      have := congrArg (coordEα leech β) hθ
      simp only [map_add, map_smul, coordEα_latStateGen, latChargeGen, if_pos rfl,
        if_neg hβn] at this
      simp only [smul_zero, add_zero, zero_add] at this
      have h1 : (vacuumN (rank leech)) ≠ 0 := by
        rw [vacuumN]; exact one_ne_zero
      exact (smul_left_injective ℂ h1 this).symm
    refine ⟨c₁, Subtype.ext ?_⟩
    rw [hx, ← hc]
    change _ = c₁ • (latChargeGen leech β + latChargeGen leech (-β))
    rw [smul_add]

/-! ## The block form of the untwisted action on `V♮` -/

theorem VnatVOA_smul_inl (u : SkewVP) (n : ℤ) (x : SkewVP) (t : TP) :
    VnatVOA.smul ((u, 0) : Vnat) n ((x, t) : Vnat)
      = (leechVOAPlus.smul u n x, mode (plusModule.YM u) n t) := by
  change mode (VnatAxioms.YN (u, 0)) n (x, t) = _
  have hW : leechWbar (0 : TP) = 0 := map_zero VnatAxioms.wbarL
  have hWs : leechWsk (0 : TP) = 0 := map_zero leechWskLin
  rw [VnatAxioms.mode_YN]
  simp only [hW, hWs, mode_zero, LinearMap.zero_apply, add_zero, zero_add]
  rfl

/-! ## The eigenvector step on `V♮` -/

theorem qN_mem_grading_two (a b : Fin (rank leech)) :
    ((qP a b, 0) : Vnat) ∈ VnatVOA.grading 2 := by
  rw [VnatVOA_grading, mem_gradingNat]
  exact ⟨qP_mem_grading a b, Submodule.zero_mem _⟩

/-- `o(q_ab)(x_β, 0) = β_aβ_b (x_β, 0)` in `V♮`. -/
theorem VnatVOA_smul_qN_frameX0P (a b : Fin (rank leech)) (β : leech.carrier) :
    VnatVOA.smul ((qP a b, 0) : Vnat) 1 ((frameX0P β, 0) : Vnat)
      = (chargeCoord leech β a * chargeCoord leech β b) • ((frameX0P β, 0) : Vnat) := by
  rw [VnatVOA_smul_inl, smul_qP_frameX0P, map_zero, Prod.smul_mk, smul_zero]

/-- ⭐ **An automorphism fixing `V♮₂` scales every `(x_β, 0)`.** -/
theorem aut_frameX0P_eigen (g : AutVnat) (hg : ∀ v ∈ VnatVOA.grading 2, g v = v)
    (β : leech.carrier) :
    ∃ c : ℂ, g ((frameX0P β, 0) : Vnat) = c • ((frameX0P β, 0) : Vnat) := by
  set w := g ((frameX0P β, 0) : Vnat) with hw
  have heq : ∀ a b, VnatVOA.smul ((qP a b, 0) : Vnat) 1 w
      = (chargeCoord leech β a * chargeCoord leech β b) • w := by
    intro a b
    rw [hw, ← hg _ (qN_mem_grading_two a b), ← Aut.map_smul, VnatVOA_smul_qN_frameX0P,
      Aut.coe_toLinearEquiv, ← Aut.coe_toLinearEquiv, map_smul]
  have hsplit : ∀ a b, VnatVOA.smul ((qP a b, 0) : Vnat) 1 w
      = (leechVOAPlus.smul (qP a b) 1 w.1, mode (plusModule.YM (qP a b)) 1 w.2) := by
    intro a b
    conv_lhs => rw [show w = (w.1, w.2) from rfl]
    exact VnatVOA_smul_inl _ _ _ _
  have hw1 : ∀ a b, leechVOAPlus.smul (qP a b) 1 w.1
      = (chargeCoord leech β a * chargeCoord leech β b) • w.1 := fun a b => by
    have := congrArg Prod.fst ((hsplit a b).symm.trans (heq a b))
    simpa using this
  have hw2 : w.2 = 0 := by
    refine AutZeroTw.VnatVOA_twisted_outer_eigen_eq_zero (fun a => chargeCoord leech β a) w.2
      fun a b u hu => ?_
    have hu' : u = qP a b := Subtype.ext (hu.trans (qP_coe a b).symm)
    subst hu'
    rw [VnatVOA_smul_inl, PreVertexAlgebra.smul_zero_right]
    have := congrArg Prod.snd ((hsplit a b).symm.trans (heq a b))
    simp only [Prod.smul_snd] at this
    rw [this, Prod.smul_mk, smul_zero]
  obtain ⟨c, hc⟩ := eigen_plus β w.1 hw1
  refine ⟨c, ?_⟩
  change (w.1, w.2) = _
  rw [hc, hw2, Prod.smul_mk, smul_zero]

/-! ## Propagating the scalars along minimal vectors -/

theorem frameX0P_mem_grading_two {α : leech.carrier} (hα : leech.form α α = 4) :
    frameX0P α ∈ leechVOAPlus.grading 2 := by
  have h := InvForm.frameX0P_mem_grading α
  have h2 : LatGen.halfNorm leech α = 2 := by
    rw [LatGen.halfNorm, hα]; rfl
  rwa [h2] at h

theorem xN_mem_grading_two {α : leech.carrier} (hα : leech.form α α = 4) :
    ((frameX0P α, 0) : Vnat) ∈ VnatVOA.grading 2 := by
  rw [VnatVOA_grading, mem_gradingNat]
  exact ⟨frameX0P_mem_grading_two hα, Submodule.zero_mem _⟩

open Classical in
theorem frameX0P_ne_zero (β : leech.carrier) : frameX0P β ≠ 0 := by
  intro h
  have h' := congrArg (fun x : VPlus => coordEα leech β (x : LatModuleGen leech)) h
  simp only [ZeroMemClass.coe_zero, map_zero] at h'
  change coordEα leech β (latChargeGen leech β + latChargeGen leech (-β)) = 0 at h'
  rw [map_add, latChargeGen, latChargeGen, coordEα_latStateGen, coordEα_latStateGen, if_pos rfl,
    vacuumN] at h'
  split_ifs at h' with hb
  · have : (2 : ℂ) • (1 : FockN (rank leech)) = 0 := by rw [two_smul]; exact h'
    rw [smul_eq_zero] at this
    rcases this with h2 | h2
    · norm_num at h2
    · exact one_ne_zero h2
  · rw [add_zero] at h'
    exact one_ne_zero h'

/-- Scalars on `(x_β, 0)` are unique. -/
theorem scalar_unique {β : leech.carrier} {c c' : ℂ}
    (h : c • ((frameX0P β, 0) : Vnat) = c' • ((frameX0P β, 0) : Vnat)) : c = c' := by
  have h1 := congrArg Prod.fst h
  simp only [Prod.smul_fst] at h1
  exact smul_left_injective ℂ (frameX0P_ne_zero β) h1

/-- The leading product in `V♮`: `(x_α,0)₍₋⟨α,γ⟩₋₁₎(x_γ,0) = ε(α,γ) (x_{α+γ},0)` for `⟨α,γ⟩ < 0`. -/
theorem VnatVOA_smul_xN_of_neg (α γ : leech.carrier) (h : leech.form α γ < 0) :
    VnatVOA.smul ((frameX0P α, 0) : Vnat) (-(leech.form α γ) - 1) ((frameX0P γ, 0) : Vnat)
      = latticeCocycle leech α γ • ((frameX0P (α + γ), 0) : Vnat) := by
  rw [VnatVOA_smul_inl, frameX0P_smul_frameX0P_of_neg α γ h, map_zero, Prod.smul_mk, smul_zero]

/-- One step: for `⟨α,γ⟩ < 0` with `α` minimal, the scalars at `γ` and `α + γ` agree. -/
theorem scalar_step_of_neg (g : AutVnat) (hg : ∀ v ∈ VnatVOA.grading 2, g v = v)
    {α γ : leech.carrier} (hα : leech.form α α = 4) (h : leech.form α γ < 0) {c c' : ℂ}
    (hc : g ((frameX0P γ, 0) : Vnat) = c • ((frameX0P γ, 0) : Vnat))
    (hc' : g ((frameX0P (α + γ), 0) : Vnat) = c' • ((frameX0P (α + γ), 0) : Vnat)) : c = c' := by
  have hε : latticeCocycle leech α γ ≠ 0 := latticeCocycle_ne_zero leech α γ
  have key := congrArg (fun v => g v) (VnatVOA_smul_xN_of_neg α γ h)
  simp only at key
  rw [Aut.map_smul, hg _ (xN_mem_grading_two hα), hc, PreVertexAlgebra.smul_smul_right,
    VnatVOA_smul_xN_of_neg α γ h, map_smul, hc', smul_comm c] at key
  have key2 := smul_right_injective Vnat hε key
  exact scalar_unique key2

/-- ⭐ **The scalars agree along every minimal vector**: `c_γ = c_{γ+α}` for `α` minimal. -/
theorem scalar_step (g : AutVnat) (hg : ∀ v ∈ VnatVOA.grading 2, g v = v)
    {α γ : leech.carrier} (hα : leech.form α α = 4) {c c' : ℂ}
    (hc : g ((frameX0P γ, 0) : Vnat) = c • ((frameX0P γ, 0) : Vnat))
    (hc' : g ((frameX0P (α + γ), 0) : Vnat) = c' • ((frameX0P (α + γ), 0) : Vnat)) : c = c' := by
  by_cases h : leech.form α γ < 0
  · exact scalar_step_of_neg g hg hα h hc hc'
  · -- use `−α` against `γ + α`
    have hα' : leech.form (-α) (-α) = 4 := by
      rw [LinearMap.map_neg₂, map_neg, neg_neg, hα]
    have h' : leech.form (-α) (α + γ) < 0 := by
      have e : leech.form (-α) (α + γ) = -(leech.form α α + leech.form α γ) := by
        rw [LinearMap.map_neg₂, map_add]
      rw [e, hα]
      omega
    have hsum : -α + (α + γ) = γ := by abel
    have hc2 : g ((frameX0P (-α + (α + γ)), 0) : Vnat) = c • ((frameX0P (-α + (α + γ)), 0) : Vnat) := by
      rw [hsum]; exact hc
    exact (scalar_step_of_neg g hg hα' h' hc' hc2).symm

end VOA.Moonshine.AutMonster
