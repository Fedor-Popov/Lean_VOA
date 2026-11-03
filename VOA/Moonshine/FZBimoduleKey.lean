/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.KeySkewBlock
import VOA.Moonshine.SigmaExistZhu
import VOA.Modules.FZBimodule

/-!
# `KeyTopV` from Frenkel–Zhu bimodule generation and the finite top-pair identity

`KeySkew.KeyTopV D t` (`KeySkewBlock.lean`) is the top-output identity
`Θ(o(v) x) = (−1)^k (Ψx)₍ₖ₋₁₎ Φ(v)` for homogeneous `v ∈ (V₃⁺)_k`, **all** `k`.  This file
reduces it to two named statements, following Frenkel–Zhu / Li:

* `BimodGenV3` — `V₃⁺` is generated, as an `A(V₀⁺)`-bimodule in the Frenkel–Zhu sense, by its top
  `(V₃⁺)₂` (`FZ.FZGenerated MV3 2`: every subspace containing `O(V₃⁺)` and `(V₃⁺)₂` and closed
  under `a ∗ ·`, `· ∗ a`, `a ∈ V₀⁺` homogeneous, is everything);
* `TopPairs D` — the finite top-level identity `Θ(o(v) Φb) = o(b) Φv` for **all** pairs
  `v, b ∈ (V₃⁺)₂` (checked numerically on samples).

For `y ∈ (T_s⁺)₂` consider the two linear maps `V₃⁺ → (T_{s+1}⁺)₂`

  `φ₁(v) = Θ(o(v) y)`,   `φ₂(v) = (−1)^k (Ψy)₍ₖ₋₁₎ Φ(v)`  (`v ∈ (V₃⁺)_k`),

and `F_y = φ₁ − φ₂` (`Fy`).  The core identities, for `a ∈ (V₀⁺)_p`:

* `Fy_lV`  : `F_y(a ∗ v) = o(σa) F_y(v)`;
* `Fy_cV`  : `F_y(∑_{i<p} C(p−1,i) a₍ᵢ₎v) = o(σa) F_y(v) − F_{o(a)y}(v)`, hence (with the exact
  `a ∗ v − v ∗ a` identity) `F_y(v ∗ a) = F_{o(a)y}(v)`;
* `Fy_resV`: `F_y(O(V₃⁺)) = 0`.

**How the `W`-Jacobi problem is avoided.**  `φ₁` is the zero mode of the `V_Λ⁺`-module `TP`: the
three identities are Zhu's easy direction for the VOA `V_Λ⁺` (`oMod_zhuMul_lowest_all`,
`Pres_mem_O`, `O_le_ker_rhoLW`), since `a ∗ v`, `O(V₃⁺)` are computed inside `V_Λ⁺`.  `φ₂` is the
top component of the skew operator `W(Φv, z)Ψy = e^{zL₋₁}Y^T(Ψy,−z)Φv`, but it is *written* through
`Y^T` modes of `Ψy` acting on `Φv`, and `Φ` turns `a ∗ v` into `σa ∗ Φv`.  The three identities
for `φ₂` are then the transposed top-level identities `FZ.skew_left`/`skew_comm`/`skew_res`, which
need only the **commutator formula** of `Y^T` (`VnatBlock.act_comm`) and the lowest weights
(`V₃⁺` and `TP` start in weight 2).  Neither the intertwining Jacobi identity of `W` nor any
associativity of an intertwining operator is used.

## Main results
* `keyTopAll_of_FZ : BimodGenV3 → TopPairs D → KeyTopAll D` (all top inputs `y`).
* `keyTopV_of_FZ : BimodGenV3 → TopPairs D → KeyTopV D t`.
* `topPairs_of_keyTopAll` — `TopPairs` is also necessary for `KeyTopAll`.
* `keySkew_of_FZ`, `moonshine_of_FZ` — composed with `KeySkewBlock`.

## Status
`sorry`-free; no `VOA.pbw`.  Conditional on `D : SigmaData`, `BimodGenV3` (a pure statement about
the `V₀⁺`-module `V₃⁺`; numerically supported) and `TopPairs D`
(finite, open).  Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.FZKey

open Module (End)
open VnatBlock SkewIntertwiner Reconstruction TrialityTw M8h0 IntegralLattice LatGen M8hKey
open LatticeTwisted TwistedHeisenberg FrameT InvForm SkewAdjoint VertexOperatorAlgebra SigmaExist
open SigmaKey KeySkew FZ

/-! ## §1  The operations on `V_Λ⁺` and the bridge from `MV3` -/

/-- `a ∗ v` on `V_Λ⁺` (for `a` of weight `p`). -/
noncomputable def lV (p : ℕ) (a : V0Sub.carrier) : VPlus →ₗ[ℂ] VPlus :=
  ∑ i ∈ Finset.range (p + 1), cbz (p : ℤ) (i : ℤ) • actV a ((i : ℤ) - 1)

/-- `∑_{i<p} C(p−1,i) a₍ᵢ₎ v` (`= a ∗ v − v ∗ a`). -/
noncomputable def cV (p : ℕ) (a : V0Sub.carrier) : VPlus →ₗ[ℂ] VPlus :=
  ∑ i ∈ Finset.range p, cbz ((p : ℤ) - 1) (i : ℤ) • actV a (i : ℤ)

/-- The residues `∑_i C(p+k,i) a₍ᵢ₋₂₋ₖ₎ v`. -/
noncomputable def resV (p k : ℕ) (a : V0Sub.carrier) : VPlus →ₗ[ℂ] VPlus :=
  ∑ i ∈ Finset.range (p + k + 1), cbz ((p : ℤ) + k) (i : ℤ) • actV a ((i : ℤ) - 2 - k)

theorem lV_apply (p : ℕ) (a : V0Sub.carrier) (v : VPlus) :
    lV p a v = ∑ i ∈ Finset.range (p + 1), cbz (p : ℤ) (i : ℤ) • actV a ((i : ℤ) - 1) v := by
  simp [lV, LinearMap.sum_apply]

theorem cV_apply (p : ℕ) (a : V0Sub.carrier) (v : VPlus) :
    cV p a v = ∑ i ∈ Finset.range p, cbz ((p : ℤ) - 1) (i : ℤ) • actV a (i : ℤ) v := by
  simp [cV, LinearMap.sum_apply]

theorem resV_apply (p k : ℕ) (a : V0Sub.carrier) (v : VPlus) :
    resV p k a v = ∑ i ∈ Finset.range (p + k + 1), cbz ((p : ℤ) + k) (i : ℤ) • actV a ((i : ℤ) - 2 - k) v := by
  simp [resV, LinearMap.sum_apply]

theorem coe_fzLeft (p : ℕ) (a : V0Sub.carrier) (x : frameSector 1) :
    ((fzLeft MV3.toWeakModule p a x : frameSector 1) : VPlus) = lV p a x := by
  rw [lV_apply, fzLeft, Submodule.coe_sum]
  rfl

theorem coe_fzRight (p : ℕ) (a : V0Sub.carrier) (x : frameSector 1) :
    ((fzRight MV3.toWeakModule p a x : frameSector 1) : VPlus) = lV p a x - cV p a x := by
  have h := congrArg Subtype.val (fzLeft_sub_fzRight MV3.toWeakModule p a x)
  rw [Submodule.coe_sub, coe_fzLeft, Submodule.coe_sum] at h
  have h' : ∑ i ∈ Finset.range p, (((cbz ((p : ℤ) - 1) (i : ℤ) • mode (MV3.YM a) (i : ℤ) x :
      frameSector 1)) : VPlus) = cV p a x := by
    rw [cV_apply]
    simp only [Submodule.coe_smul]
    rfl
  rw [h'] at h
  rw [← h]
  abel

theorem coe_fzRes (p k : ℕ) (a : V0Sub.carrier) (x : frameSector 1) :
    ((fzRes MV3.toWeakModule p k a x : frameSector 1) : VPlus) = resV p k a x := by
  rw [resV_apply, fzRes, Submodule.coe_sum]
  rfl

/-- Induction over the weight decomposition of `MV3`. -/
theorem MV3_induction (P : frameSector 1 → Prop) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hhom : ∀ (k : ℤ) (x : frameSector 1), (x : VPlus) ∈ leechVOAPlus.grading k → P x)
    (x : frameSector 1) : P x := by
  have hx : x ∈ ⨆ α, MV3.weight α := by rw [MV3.isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction MV3.weight (motive := P) hx ?_ h0 hadd
  intro α y hy
  by_cases hint : ∃ m : ℤ, (m : ℂ) = α
  · obtain ⟨m, rfl⟩ := hint
    exact hhom m y (by rw [← adjWeight_cast]; exact hy)
  · push Not at hint
    have h1 : (y : VPlus) ∈ adjWeight leechVOAPlus α := hy
    rw [adjWeight_eq_bot leechVOAPlus hint] at h1
    have : y = 0 := Subtype.ext ((Submodule.mem_bot ℂ).mp h1)
    rw [this]; exact h0

/-! ## §2  The two candidate top maps and their difference -/

variable (D : SigmaData)

/-- The weight-`k` slice of `φ₂`: `v ↦ (−1)^k (Ψy)₍ₖ₋₁₎ Φ(v)`. -/
noncomputable def phi2Fam (y : TP) (k : ℤ) : VPlus →ₗ[ℂ] TP :=
  negOnePow k • ((mode (plusModule.YM (D.Ψ y)) (k - 1)) ∘ₗ D.Φ)

/-- `φ₂`, extended over the grading. -/
noncomputable def phi2 (y : TP) : VPlus →ₗ[ℂ] TP := gradedExt leechVOAPlus (phi2Fam D y)

/-- `φ₁(v) = Θ(o(v) y)`. -/
noncomputable def phi1 (y : TP) : VPlus →ₗ[ℂ] TP := D.Θ ∘ₗ (oMod plusModule).flip y

/-- The top-level defect `F_y = φ₁ − φ₂`. -/
noncomputable def Fy (y : TP) : VPlus →ₗ[ℂ] TP := phi1 D y - phi2 D y

theorem phi1_hom (y : TP) {k : ℤ} {v : VPlus} (hv : v ∈ leechVOAPlus.grading k) :
    phi1 D y v = D.Θ (mode (plusModule.YM v) (k - 1) y) := by
  simp only [phi1, LinearMap.comp_apply, LinearMap.flip_apply, oMod_homogeneous plusModule hv]

theorem phi2_hom (y : TP) {k : ℤ} {v : VPlus} (hv : v ∈ leechVOAPlus.grading k) :
    phi2 D y v = negOnePow k • mode (plusModule.YM (D.Ψ y)) (k - 1) (D.Φ v) := by
  rw [phi2, gradedExt_of_mem _ _ hv, phi2Fam, LinearMap.smul_apply, LinearMap.comp_apply]

theorem Fy_hom (y : TP) {k : ℤ} {v : VPlus} (hv : v ∈ leechVOAPlus.grading k) :
    Fy D y v = D.Θ (mode (plusModule.YM v) (k - 1) y)
      - negOnePow k • mode (plusModule.YM (D.Ψ y)) (k - 1) (D.Φ v) := by
  rw [Fy, LinearMap.sub_apply, phi1_hom D y hv, phi2_hom D y hv]

/-! ## §3  Commutator data and top-ness -/

/-- The commutator data for `σa` (weight `p`) against a top vector `b ∈ (V₃⁺)₂`: the
commutator sum stops at `p`, because `(σa)₍ⱼ₎b ∈ V₃⁺` has weight `< 2` for `j ≥ p`. -/
theorem commData_sig {p : ℕ} {a : V0Sub.carrier} (ha : (a : VPlus) ∈ leechVOAPlus.grading (p : ℤ))
    {b : VPlus} (hb : b ∈ OmegaV3) :
    CommData (fun r => actT (sig a) r) (fun r => actT (sig a) r) (fun n => mode (plusModule.YM b) n)
      (fun j n => mode (plusModule.YM (leechVOAPlus.smul ((sig a : V0Sub.carrier) : VPlus) j b)) n) p := by
  intro r n m
  have hJ : ∀ j : ℕ, p ≤ j → leechVOAPlus.smul ((sig a : V0Sub.carrier) : VPlus) j b = 0 := by
    intro j hj
    exact V3_eq_zero_of_lt (actV_stab (sig a) (Set.mem_univ _) j b hb.1)
      (leechVOAPlus.smul_mem_grading (sig_mem_grading ha) hb.2 j) (by omega)
  have := act_comm plusModule.toWeakModule ((sig a : V0Sub.carrier) : VPlus) b r n m p hJ
  simpa only [WeakModule.act_def] using this

/-- `(Ψy)₍ᵣ₎ Φ(v) = 0` above the top mode `r = k − 1` (output weight `< 2`). -/
theorem hlow_Phi {b : VPlus} (hb2 : b ∈ leechVOAPlus.grading 2) {v : VPlus} (hv : v ∈ frameSector 1)
    {k : ℤ} (hk : v ∈ leechVOAPlus.grading k) :
    ∀ r : ℤ, k - 1 < r → mode (plusModule.YM b) r (D.Φ v) = 0 := by
  intro r hr
  have h := mode_mem_weight plusModule hb2 (Phi_weight D hv hk) r
  have e : (k : ℂ) + ((2 : ℤ) : ℂ) - (r : ℂ) - 1 = ((k + 2 - r - 1 : ℤ) : ℂ) := by push_cast; ring
  rw [e] at h
  exact TP_eq_zero_of_lt h (by omega)

theorem Psi_top {y : TP} (hy : y ∈ OmegaT D.s) : D.Ψ y ∈ OmegaV3 :=
  ⟨D.Ψ_mem y hy.1, Psi_L0 D hy.1 (by exact_mod_cast hy.2)⟩

/-! ## §4  The three identities -/

/-- **Left action**: `F_y(a ∗ v) = o(σa) F_y(v)`. -/
theorem Fy_lV {p : ℕ} {a : V0Sub.carrier} (ha : (a : VPlus) ∈ leechVOAPlus.grading (p : ℤ))
    {y : TP} (hy : y ∈ OmegaT D.s) {v : VPlus} (hv : v ∈ frameSector 1) {k : ℤ}
    (hk : v ∈ leechVOAPlus.grading k) :
    Fy D y (lV p a v) = actT (sig a) ((p : ℤ) - 1) (Fy D y v) := by
  have hb := Psi_top D hy
  -- `φ₁`: Zhu's easy direction for `V_Λ⁺`
  have h1 : phi1 D y (lV p a v) = actT (sig a) ((p : ℤ) - 1) (phi1 D y v) := by
    have hz : lV p a v = zhuMul leechVOAPlus (a : VPlus) v := by
      rw [zhuMul_homogeneous' leechVOAPlus ha, lV_apply]
      simp only [Int.toNat_natCast]
      rfl
    have hmem : oMod plusModule v y ∈ TPframe (D.s + 1) := by
      rw [oMod_homogeneous plusModule hk]; exact YM_mode_V3_flip hv hy.1 _
    simp only [phi1, LinearMap.comp_apply, LinearMap.flip_apply]
    rw [hz, oMod_zhuMul_lowest_all plusModule isLowestWeight_plus _ _ hy.2,
      oMod_homogeneous plusModule ha]
    exact D.isSigma_Θ a (Set.mem_univ _) _ _ hmem
  -- `φ₂`: the transposed identity
  have h2 : phi2 D y (lV p a v) = actT (sig a) ((p : ℤ) - 1) (phi2 D y v) := by
    have hl := skew_left p (commData_sig ha hb) (k - 1) (D.Φ v) (hlow_Phi D hb.2 hv hk)
    beta_reduce at hl
    have hterm : ∀ i ∈ Finset.range (p + 1), cbz (p : ℤ) (i : ℤ) • phi2 D y (actV a ((i : ℤ) - 1) v)
        = negOnePow k • ((asgn p i : ℂ) • mode (plusModule.YM (D.Ψ y)) (k - 1 + p - i)
            (actT (sig a) ((i : ℤ) - 1) (D.Φ v))) := by
      intro i hi
      have hi' : i ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hg : actV a ((i : ℤ) - 1) v ∈ leechVOAPlus.grading (k + p - i) := by
        have := leechVOAPlus.smul_mem_grading ha hk ((i : ℤ) - 1)
        rw [show (p : ℤ) + k - ((i : ℤ) - 1) - 1 = k + p - i by ring] at this
        exact this
      rw [phi2_hom D y hg, D.isSigma_Φ a (Set.mem_univ _) _ v hv, smul_smul, smul_smul,
        sign_coeff p hi' k]
      have e : k + (p : ℤ) - i - 1 = k - 1 + p - i := by ring
      rw [e]
    rw [lV_apply, map_sum]
    simp only [map_smul]
    rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, hl, phi2_hom D y hk, map_smul]
  simp only [Fy, LinearMap.sub_apply]
  rw [h1, h2, map_sub]

/-- **Commutator**: `F_y(∑_{i≤q} C(q,i) a₍ᵢ₎ v) = o(σa) F_y(v) − F_{o(a)y}(v)` for `a` of
weight `q + 1`. -/
theorem Fy_cV {q : ℕ} {a : V0Sub.carrier} (ha : (a : VPlus) ∈ leechVOAPlus.grading ((q + 1 : ℕ) : ℤ))
    {y : TP} (hy : y ∈ OmegaT D.s) {v : VPlus} (hv : v ∈ frameSector 1) {k : ℤ}
    (hk : v ∈ leechVOAPlus.grading k) :
    Fy D y (cV (q + 1) a v) = actT (sig a) (q : ℤ) (Fy D y v) - Fy D (actT a (q : ℤ) y) v := by
  have hb := Psi_top D hy
  have hcq : ((q + 1 : ℕ) : ℤ) - 1 = (q : ℤ) := by push_cast; ring
  -- `φ₁`: the module commutator formula for `V_Λ⁺` acting on `TP`
  have h1 : phi1 D y (cV (q + 1) a v)
      = actT (sig a) (q : ℤ) (phi1 D y v) - phi1 D (actT a (q : ℤ) y) v := by
    obtain ⟨N, hN⟩ := PreVertexAlgebra.smul_eventually_zero leechVOAPlus.toPreVertexAlgebra (a : VPlus) v
    set J := N.toNat + q + 1 with hJdef
    have hJ : ∀ j : ℕ, J ≤ j → leechVOAPlus.smul (a : VPlus) j v = 0 := fun j hj => hN j (by omega)
    have hc := act_comm plusModule.toWeakModule (a : VPlus) v (q : ℤ) (k - 1) y J hJ
    simp only [WeakModule.act_def] at hc
    have hsub : ∑ r ∈ Finset.range J, gBinom (q : ℤ) r •
          mode (plusModule.YM (leechVOAPlus.smul (a : VPlus) r v)) ((q : ℤ) + (k - 1) - r) y
        = ∑ r ∈ Finset.range (q + 1), gBinom (q : ℤ) r •
          mode (plusModule.YM (leechVOAPlus.smul (a : VPlus) r v)) ((q : ℤ) + (k - 1) - r) y := by
      symm
      refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun r _ hr => ?_
      rw [gBinom_lt (by positivity) (by simp at hr; omega), zero_smul]
    have hmem : mode (plusModule.YM v) (k - 1) y ∈ TPframe (D.s + 1) := YM_mode_V3_flip hv hy.1 _
    have ho : oMod plusModule (cV (q + 1) a v) y
        = mode (plusModule.YM (a : VPlus)) (q : ℤ) (mode (plusModule.YM v) (k - 1) y)
          - mode (plusModule.YM v) (k - 1) (mode (plusModule.YM (a : VPlus)) (q : ℤ) y) := by
      rw [hc, hsub, cV_apply, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun r _ => ?_
      have hg : actV a (r : ℤ) v ∈ leechVOAPlus.grading ((q : ℤ) + (k - 1) - r + 1) := by
        have := leechVOAPlus.smul_mem_grading ha hk (r : ℤ)
        rw [show ((q + 1 : ℕ) : ℤ) + k - (r : ℤ) - 1 = (q : ℤ) + (k - 1) - r + 1 by push_cast; ring] at this
        exact this
      rw [map_smul, LinearMap.smul_apply, oMod_homogeneous plusModule hg, add_sub_cancel_right, hcq,
        cbz_apply_nonneg _ (by positivity), Int.toNat_natCast]
      rfl
    have e1 : phi1 D y (cV (q + 1) a v) = D.Θ (oMod plusModule (cV (q + 1) a v) y) := rfl
    rw [e1, ho, map_sub, ← actT_eq_mode, D.isSigma_Θ a (Set.mem_univ _) _ _ hmem, phi1_hom D y hk, phi1_hom D _ hk]
    rfl
  -- `φ₂`: the transposed identity
  have h2 : phi2 D y (cV (q + 1) a v)
      = actT (sig a) (q : ℤ) (phi2 D y v) - phi2 D (actT a (q : ℤ) y) v := by
    have hl := skew_comm (q + 1) (by omega) (commData_sig ha hb) (k - 1) (D.Φ v) (hlow_Phi D hb.2 hv hk)
    beta_reduce at hl
    simp only [Nat.add_sub_cancel, hcq] at hl
    have hterm : ∀ i ∈ Finset.range (q + 1), cbz (((q + 1 : ℕ) : ℤ) - 1) (i : ℤ) • phi2 D y (actV a (i : ℤ) v)
        = negOnePow k • ((asgn q i : ℂ) • mode (plusModule.YM (D.Ψ y)) (k - 1 + q - i)
            (actT (sig a) (i : ℤ) (D.Φ v))) := by
      intro i hi
      have hi' : i ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hg : actV a (i : ℤ) v ∈ leechVOAPlus.grading (k + q - i) := by
        have := leechVOAPlus.smul_mem_grading ha hk (i : ℤ)
        rw [show ((q + 1 : ℕ) : ℤ) + k - (i : ℤ) - 1 = k + q - i by push_cast; ring] at this
        exact this
      rw [phi2_hom D y hg, D.isSigma_Φ a (Set.mem_univ _) _ v hv, smul_smul, smul_smul, hcq,
        sign_coeff q hi' k]
      have e : k + (q : ℤ) - i - 1 = k - 1 + q - i := by ring
      rw [e]
    rw [cV_apply, map_sum]
    simp only [map_smul]
    rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, hl, phi2_hom D y hk, phi2_hom D _ hk,
      D.isSigma_Ψ a (Set.mem_univ _) _ y hy.1, smul_sub, map_smul]
    rfl
  simp only [Fy, LinearMap.sub_apply]
  rw [h1, h2, map_sub]
  abel

/-- **`O(V₃⁺)`**: `F_y` kills every residue. -/
theorem Fy_resV {p k' : ℕ} {a : V0Sub.carrier} (ha : (a : VPlus) ∈ leechVOAPlus.grading (p : ℤ))
    {y : TP} (hy : y ∈ OmegaT D.s) {v : VPlus} (hv : v ∈ frameSector 1) {k : ℤ}
    (hk : v ∈ leechVOAPlus.grading k) : Fy D y (resV p k' a v) = 0 := by
  have hb := Psi_top D hy
  -- `φ₁`: the residue lies in `O(V_Λ⁺)`
  have h1 : phi1 D y (resV p k' a v) = 0 := by
    have hP : resV p k' a v = Pres leechVOAPlus p (a : VPlus) v k' := by
      rw [resV_apply, Pres]; rfl
    simp only [phi1, LinearMap.comp_apply, LinearMap.flip_apply]
    rw [hP, oMod_eq_zero_of_mem_O plusModule isLowestWeight_plus (Pres_mem_O leechVOAPlus ha v k')
      hy.2, map_zero]
  -- `φ₂`: the transposed identity
  have h2 : phi2 D y (resV p k' a v) = 0 := by
    have hl := skew_res p k' (commData_sig ha hb) (k - 1) (D.Φ v) (hlow_Phi D hb.2 hv hk)
    beta_reduce at hl
    have hterm : ∀ i ∈ Finset.range (p + k' + 1),
        cbz ((p : ℤ) + k') (i : ℤ) • phi2 D y (actV a ((i : ℤ) - 2 - k') v)
        = negOnePow (k + 1) • ((asgn (p + k') i : ℂ) • mode (plusModule.YM (D.Ψ y))
            (k - 1 + 1 + ((p + k' : ℕ) : ℤ) - i) (actT (sig a) ((i : ℤ) - 2 - k') (D.Φ v))) := by
      intro i hi
      have hi' : i ≤ p + k' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hg : actV a ((i : ℤ) - 2 - k') v ∈ leechVOAPlus.grading (k + 1 + ((p + k' : ℕ) : ℤ) - i) := by
        have := leechVOAPlus.smul_mem_grading ha hk ((i : ℤ) - 2 - k')
        rw [show (p : ℤ) + k - ((i : ℤ) - 2 - k') - 1 = k + 1 + ((p + k' : ℕ) : ℤ) - i by
          push_cast; ring] at this
        exact this
      rw [phi2_hom D y hg, D.isSigma_Φ a (Set.mem_univ _) _ v hv, smul_smul, smul_smul,
        show ((p : ℤ) + k') = ((p + k' : ℕ) : ℤ) by push_cast; ring, sign_coeff (p + k') hi' (k + 1),
        show k + 1 + ((p + k' : ℕ) : ℤ) - i - 1 = k - 1 + 1 + ((p + k' : ℕ) : ℤ) - i by ring]
    rw [resV_apply, map_sum]
    simp only [map_smul]
    rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, hl, smul_zero]
  simp only [Fy, LinearMap.sub_apply]
  rw [h1, h2, sub_zero]

/-! ## §5  The reduction -/

/-- **`KeyTopV` for every top input** `y ∈ (T_s⁺)₂` (in place of the single `x`). -/
def KeyTopAll : Prop :=
  ∀ y ∈ OmegaT D.s, ∀ (k : ℤ), ∀ v ∈ frameSector 1, v ∈ leechVOAPlus.grading k →
    D.Θ (mode (plusModule.YM v) (k - 1) y)
      = negOnePow k • mode (plusModule.YM (D.Ψ y)) (k - 1) (D.Φ v)

/-- **Bimodule generation** (Frenkel–Zhu): `V₃⁺` is generated by `(V₃⁺)₂` as an
`A(V₀⁺)`-bimodule, in the filtered-criterion form `FZ.FZGenerated`.  A pure statement about the
`V₀⁺`-module `V₃⁺`. -/
def BimodGenV3 : Prop := FZGenerated MV3 (2 : ℂ)

/-- **The finite top-pair identity**: `Θ(o(v) Φb) = o(b) Φv` for all `v, b ∈ (V₃⁺)₂`. -/
def TopPairs : Prop :=
  ∀ v ∈ OmegaV3, ∀ b ∈ OmegaV3,
    D.Θ (mode (plusModule.YM v) 1 (D.Φ b)) = mode (plusModule.YM b) 1 (D.Φ v)

/-- **The Frenkel–Zhu reduction** (all top inputs). -/
theorem keyTopAll_of_FZ (hgen : BimodGenV3) (htop : TopPairs D) : KeyTopAll D := by
  let S : Submodule ℂ (frameSector 1) :=
    { carrier := {x | ∀ y ∈ OmegaT D.s, Fy D y (x : VPlus) = 0}
      add_mem' := fun {x x'} hx hx' y hy => by
        rw [Submodule.coe_add, map_add, hx y hy, hx' y hy, add_zero]
      zero_mem' := fun y _ => by rw [ZeroMemClass.coe_zero, map_zero]
      smul_mem' := fun c x hx y hy => by rw [Submodule.coe_smul, map_smul, hx y hy, smul_zero] }
  have hS : S = ⊤ := by
    refine hgen S ?_ ?_ ?_
    · rw [fzO, Submodule.span_le]
      rintro _ ⟨p, k', a, ha, m, rfl⟩ y hy
      have ha' : (a : VPlus) ∈ leechVOAPlus.grading (p : ℤ) := mem_V0P_grading.mp ha
      change Fy D y ((fzRes MV3.toWeakModule p k' a m : frameSector 1) : VPlus) = 0
      rw [coe_fzRes]
      refine MV3_induction (fun x => Fy D y (resV p k' a x) = 0) (by simp)
        (fun x x' hx hx' => by simp only at hx hx' ⊢; rw [Submodule.coe_add, map_add, map_add, hx, hx', add_zero])
        (fun k x hx => Fy_resV D ha' hy x.2 hx) m
    · intro x hx y hy
      have hx2 : (x : VPlus) ∈ leechVOAPlus.grading 2 := mem_MV3_weight_two.mp hx
      have h := htop x ⟨x.2, hx2⟩ (D.Ψ y) (Psi_top D hy)
      rw [D.ΦΨ y hy.1] at h
      rw [Fy_hom D y hx2, show (2 : ℤ) - 1 = 1 by norm_num, h,
        show negOnePow 2 = 1 by simp [negOnePow], one_smul, sub_self]
    · intro p a ha m hm
      have ha' : (a : VPlus) ∈ leechVOAPlus.grading (p : ℤ) := mem_V0P_grading.mp ha
      have hleft : ∀ y ∈ OmegaT D.s, ∀ x : frameSector 1,
          Fy D y (lV p a x) = actT (sig a) ((p : ℤ) - 1) (Fy D y x) := fun y hy =>
        MV3_induction _ (by simp)
          (fun x x' hx hx' => by rw [Submodule.coe_add, map_add, map_add, hx, hx', map_add, map_add])
          (fun k x hx => Fy_lV D ha' hy x.2 hx)
      refine ⟨fun y hy => ?_, fun y hy => ?_⟩
      · rw [coe_fzLeft, hleft y hy, hm y hy, map_zero]
      · rw [coe_fzRight, map_sub, hleft y hy, hm y hy, map_zero, zero_sub, neg_eq_zero]
        rcases Nat.eq_zero_or_pos p with hp | hp
        · subst hp
          simp [cV]
        · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
          have hay : actT a (q : ℤ) y ∈ OmegaT D.s := by
            refine ⟨actT_stab D.s a (Set.mem_univ _) _ y hy.1, ?_⟩
            have := mode_mem_weight plusModule ha' hy.2 (q : ℤ)
            rwa [show (2 : ℂ) + (((q + 1 : ℕ) : ℤ) : ℂ) - ((q : ℤ) : ℂ) - 1 = 2 by push_cast; ring]
              at this
          have hcomm : ∀ x : frameSector 1,
              Fy D y (cV (q + 1) a x) = actT (sig a) (q : ℤ) (Fy D y x) - Fy D (actT a (q : ℤ) y) x :=
            MV3_induction _ (by simp)
              (fun x x' hx hx' => by
                rw [Submodule.coe_add, map_add, map_add, hx, hx', map_add, map_add, map_add]; abel)
              (fun k x hx => Fy_cV D ha' hy x.2 hx)
          rw [hcomm, hm y hy, hm _ hay, map_zero, sub_zero]
  intro y hy k v hv hk
  have hmem : (⟨v, hv⟩ : frameSector 1) ∈ S := by rw [hS]; trivial
  have h := hmem y hy
  rw [Fy_hom D y hk, sub_eq_zero] at h
  exact h

/-- `TopPairs` is necessary: it is the `k = 2` slice of `KeyTopAll` at `y = Φb`. -/
theorem topPairs_of_keyTopAll (h : KeyTopAll D) : TopPairs D := by
  intro v hv b hb
  have hy : D.Φ b ∈ OmegaT D.s :=
    ⟨D.Φ_mem b hb.1, by have := Phi_weight D hb.1 hb.2; exact_mod_cast this⟩
  have e := h _ hy 2 v hv.1 hv.2
  rw [D.ΨΦ b hb.1, show (2 : ℤ) - 1 = 1 by norm_num, show negOnePow 2 = 1 by simp [negOnePow],
    one_smul] at e
  exact e

/-- **`KeyTopV` from bimodule generation and the top-pair identity.** -/
theorem keyTopV_of_FZ {t : ZMod 2 → TLeechT} (ht : ∀ s, t s ∈ leechFrameT s)
    (hgen : BimodGenV3) (htop : TopPairs D) : KeyTopV D t :=
  fun k v hv hk => keyTopAll_of_FZ D hgen htop _ ⟨x0T_mem (ht D.s), x0T_mem_weight _⟩ k v hv hk

/-- **`KeySkew` from bimodule generation and the top-pair identity.** -/
theorem keySkew_of_FZ {t : ZMod 2 → TLeechT} (ht : ∀ s, t s ∈ leechFrameT s) (ht0 : ∀ s, t s ≠ 0)
    (hgen : BimodGenV3) (htop : TopPairs D) : KeySkew D t :=
  keySkew_of_keyTopV D ht ht0 (keyTopV_of_FZ D ht hgen htop)

/-- **The Moonshine module** from `D`, the two finite isometry statements, bimodule
generation, and the top-pair identity. -/
theorem moonshine_of_FZ {β : leech.carrier} (hβ : β ∉ lambda0) {t : ZMod 2 → TLeechT}
    (ht : ∀ s, t s ∈ leechFrameT s) (ht0 : ∀ s, t s ≠ 0)
    (hΦ : PhiTop D t) (hΘ : ThetaTop D t) (hgen : BimodGenV3) (htop : TopPairs D) :
    ∃ V : VertexOperatorAlgebra Vnat,
      V.Y = Ynat VnatAxioms.wbarL ∧ V.vacuum = vacNat ∧ V.conformalVector = omegaNat ∧
      V.centralCharge = 24 ∧
      V.grading 1 = ⊥ ∧
      Module.finrank ℂ (V.grading 2) = 196884 ∧
      (∀ n : ℕ, (Module.finrank ℂ (V.grading (n : ℤ)) : ℂ) = PowerSeries.coeff n JShift) ∧
      V.IsSimple :=
  moonshine_of_keyTopV D hβ ht ht0 hΦ hΘ (keyTopV_of_FZ D ht hgen htop)

end VOA.Moonshine.FZKey
