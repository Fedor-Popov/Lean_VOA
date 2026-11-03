/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaKeyTop
import VOA.Moonshine.SigmaTop2TTOct

/-!
# SigmaAssemble, part 1: top-level facts behind the σ-existence data

Finite (weight-2) statements about the explicit seeded block maps of `SigmaTop2*`, and a
generic top-level reduction for similitudes.  Used by `SigmaAssemble.lean` to build
`M8hKey.SigmaData` and to prove `SigmaKey.PhiTop` / `SigmaKey.ThetaTop`.

## Main results
* `T` side (`ψ_0 = B`, `ψ_m = Z_{0m}B` on `T_s`, for a seed `t ∈ T_s`):
  `TForm_ZZ` (`Z_{0k}` is `TForm`-symmetric, `⟨γ₋,γ₋⟩ = 4`), `TForm_eig_orth` (joint
  `Z`-eigenvectors with different characters are orthogonal), `TForm_psi_symm`,
  `psi_psi` (`ψ_m² = 1` on `T_s`: `ψ_m` acts by `u_m ω^{|N|}` and `4 ∣ |N|` by
  `golay_constraint` + `four_dvd_card_of_orth`), `TForm_psi_psi` (`ψ_m` is a `TForm`-isometry).
* `TPForm` on `(T⁺)₂ = h(−½) ⊗ T`: `fockForm_hvec` (`F(h_v, h_{v'}) = −½ v·v'`), `TPForm_hP`,
  `TPForm_hP_cw` (blocks `h_{w_m}(−½) ⊗ T` are orthogonal, `−4·TForm` on the diagonal),
  `x0T_ne_zero`.
* `phiB_isom`, `phiB_invol`: `φ_B` is a `TPForm`-isometric involution of `(T_s⁺)₂`.
* `V₃⁺` side: `L1_two` (`L₁ = 0` on weight 2, as `(V_Λ⁺)₁ = 0`), `leechBV_zero_mode`,
  `TPForm_Phi_zero_mode` (weight-2 zero modes are symmetric for `leechBV` and for `Φ^*TPForm`),
  `form_sq_ne`, `bilin_sep` / `leechBV_sep` / `TPForm_Phi_sep`: the top basis
  `x_n = e^n + e^{−n}` (`n ∈ S₁`) is orthogonal for both forms, separated by the eigenvalue
  `⟨n,n⟩² = 16 ≠ ⟨n,m⟩²` of `o(n(−1)²𝟙)` (`actV_dV`).  No knowledge of `τ⋆` is needed.
* `simil_of_top` — for **any** `Φ` with `IsSigmaV3T Φ` and any `κ`, the similitude
  `TPForm(Φa, Φb) = κ·leechBV(a, b)` on `V₃⁺` follows from its row against one cyclic top
  vector (the `D`-free, scaled version of `SigmaKey.phiIso_of_top`).

## Status
`sorry`-free; `#print axioms` of `psi_psi`,
`phiB_isom`: `[propext, Classical.choice, Quot.sound]`.  Unconditional apart from the displayed
hypotheses (seed, membership).  Reached from the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaAssemble

open Module (End)
open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen VOA.Moonshine.Triality HeisenbergN
open VOA.Moonshine.TrialityTw VOA.Moonshine.SigmaExist VOA.Moonshine.SigmaTop
open VOA.Moonshine.InvForm VOA.Moonshine.TFormLeech MvPolynomial
open scoped TensorProduct

/-! ## §1  `TForm` and the operators `Z_{0k}`, `ψ_m` -/

theorem TForm_ZZ {j k : Fin 24} (hjk : j ≠ k) (x y : TLeechT) :
    TForm (ZZ j k x) y = TForm x (ZZ j k y) := by
  rw [ZZ_apply, ZZ_apply, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
    TForm_eT, form_gM_self hjk]
  norm_num

theorem psi_mem (s : ZMod 2) (m : Fin 24) (x : TLeechT) : psiOf (Bop s) m x ∈ leechFrameT s := by
  by_cases hm : m = 0
  · subst hm; rw [psiOf_zero]; exact Bop_mem s x
  · rw [psiOf_ne hm, Module.End.mul_apply]; exact ZZ_mem_frame (Bop_mem s x)

theorem exists_uN_ne {N N' : Finset (Fin 24)} (hN0 : (0 : Fin 24) ∉ N) (hN0' : (0 : Fin 24) ∉ N')
    (hne : N ≠ N') : ∃ k, k ≠ 0 ∧ uN N k ≠ uN N' k := by
  obtain ⟨k, hk⟩ : ∃ k, ¬ (k ∈ N ↔ k ∈ N') := by
    by_contra h
    push Not at h
    exact hne (Finset.ext h)
  refine ⟨k, ?_, ?_⟩
  · rintro rfl
    exact hk ⟨fun h => absurd h hN0, fun h => absurd h hN0'⟩
  · unfold uN
    by_cases h1 : k ∈ N <;> by_cases h2 : k ∈ N' <;> simp_all <;> norm_num

/-- Joint `Z`-eigenvectors with different characters are `TForm`-orthogonal. -/
theorem TForm_eig_orth {z z' : TLeechT} {N N' : Finset (Fin 24)} (hN0 : (0 : Fin 24) ∉ N)
    (hN0' : (0 : Fin 24) ∉ N') (hE : IsEigN N z) (hE' : IsEigN N' z') (hne : N ≠ N') :
    TForm z z' = 0 := by
  obtain ⟨k, hk0, hk⟩ := exists_uN_ne hN0 hN0' hne
  have h := TForm_ZZ (Ne.symm hk0) z z'
  rw [hE k hk0, hE' k hk0, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h
  have : (uN N k - uN N' k) * TForm z z' = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hk)

/-- `ψ_m` is `TForm`-symmetric on `T_s`. -/
theorem TForm_psi_symm {s : ZMod 2} (m : Fin 24) {x y : TLeechT} (hx : x ∈ leechFrameT s)
    (hy : y ∈ leechFrameT s) :
    TForm (psiOf (Bop s) m x) y = TForm x (psiOf (Bop s) m y) := by
  refine (eig_induct (s := s) (fun x => ∀ y ∈ leechFrameT s,
      TForm (psiOf (Bop s) m x) y = TForm x (psiOf (Bop s) m y)) ?_ ?_ x hx) y hy
  · intro a b ha hb y hy
    rw [map_add, map_add, LinearMap.add_apply, ha y hy, hb y hy, (TForm).map_add₂]
  · intro z hz N hN0 hE
    refine eig_induct (s := s) (fun y => TForm (psiOf (Bop s) m z) y = TForm z (psiOf (Bop s) m y))
      ?_ ?_
    · intro a b ha hb
      simp only at ha hb ⊢
      rw [map_add, map_add, map_add, ha, hb]
    · intro z' hz' N' hN0' hE'
      rw [psiOf_eigN hz hN0 hE, psiOf_eigN hz' hN0' hE', map_smul, map_smul, LinearMap.smul_apply,
        smul_eq_mul, smul_eq_mul]
      by_cases hNN : N = N'
      · subst hNN; rfl
      · rw [TForm_eig_orth hN0 hN0' hE hE' hNN, mul_zero, mul_zero]

theorem betaN_eq (N : Finset (Fin 24)) : betaN N = ωB ^ N.card := by
  rw [betaN, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

theorem betaN_sq {N : Finset (Fin 24)} (h4 : 4 ∣ N.card) : betaN N * betaN N = 1 := by
  obtain ⟨q, hq⟩ := h4
  rw [betaN_eq, ← pow_add, show N.card + N.card = 8 * q by omega, pow_mul, ωB_eight, one_pow]

theorem uN_sq (N : Finset (Fin 24)) (k : Fin 24) : uN N k * uN N k = 1 := by
  unfold uN; split_ifs <;> norm_num

/-- **`ψ_m² = 1` on `T_s`** (for a seed `t ∈ T_s`): on a joint eigenvector `ψ_m` acts by
`u_m ω^{|N|}`, and `|N| ≡ 0 (4)` by the Golay constraint. -/
theorem psi_psi {s : ZMod 2} {t : TLeechT} (hts : t ∈ leechFrameT s) (ht0 : t ≠ 0) (ht : IsSeed t)
    (m : Fin 24) {x : TLeechT} (hx : x ∈ leechFrameT s) :
    psiOf (Bop s) m (psiOf (Bop s) m x) = x := by
  refine eig_induct (s := s) (fun x => psiOf (Bop s) m (psiOf (Bop s) m x) = x) ?_ ?_ x hx
  · intro a b ha hb
    simp only at ha hb ⊢
    rw [map_add, map_add, ha, hb]
  · intro z hz N hN0 hE
    by_cases hz0 : z = 0
    · subst hz0; simp
    have h4 : 4 ∣ N.card := four_dvd_card_of_orth fun D' hD' =>
      golay_constraint hz0 (fun S' he => dSA_mem_chargesU hts ht0 ht hz hN0 hE he) hD'
    rw [psiOf_eigN hz hN0 hE, map_smul, psiOf_eigN hz hN0 hE, smul_smul]
    have : uN N m * betaN N * (uN N m * betaN N) = 1 := by
      have e : uN N m * betaN N * (uN N m * betaN N) = (uN N m * uN N m) * (betaN N * betaN N) := by ring
      rw [e, uN_sq, betaN_sq h4, one_mul]
    rw [this, one_smul]

/-- **`ψ_m` is a `TForm`-isometry of `T_s`.** -/
theorem TForm_psi_psi {s : ZMod 2} {t : TLeechT} (hts : t ∈ leechFrameT s) (ht0 : t ≠ 0)
    (ht : IsSeed t) (m : Fin 24) {x y : TLeechT} (hx : x ∈ leechFrameT s) (hy : y ∈ leechFrameT s) :
    TForm (psiOf (Bop s) m x) (psiOf (Bop s) m y) = TForm x y := by
  rw [TForm_psi_symm m hx (psi_mem s m y), psi_psi hts ht0 ht m hy]

/-! ## §2  `TPForm` on the top level `h(−½) ⊗ T` -/

theorem fockForm_X_X (a b : Fin (rank leech)) :
    fockForm 24 (X (0, cc a)) (X (0, cc b)) = if a = b then -(1 / 2 : ℂ) else 0 := by
  rw [X, X, fockForm_monomial_monomial]
  by_cases h : a = b
  · subst h
    simp [fockWt, Finsupp.prod_single_index, cVar]
  · rw [if_neg h, if_neg]
    intro he
    have := Finsupp.single_left_injective (one_ne_zero (α := ℕ)) he
    exact h (cc_inj.mp (Prod.mk.inj this).2)

theorem fockForm_hvec (v v' : Fin (rank leech) → ℂ) :
    fockForm 24 (hvec v) (hvec v') = -(1 / 2 : ℂ) * ∑ a, v a * v' a := by
  simp only [hvec, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    fockForm_X_X, mul_ite, mul_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun b _ hb => if_neg hb) (by simp), if_pos rfl]
  ring

theorem TPForm_hP (v v' : Fin (rank leech) → ℂ) (t t' : TLeechT) :
    TPForm (hP v t) (hP v' t') = TForm t t' * fockForm 24 (hvec v) (hvec v') := by
  rw [TPForm_apply, hP_coe, hP_coe]
  rfl

theorem TPForm_hP_cw (m m' : Fin 24) (t t' : TLeechT) :
    TPForm (hP (cw m) t) (hP (cw m') t') = if m = m' then -4 * TForm t t' else 0 := by
  rw [TPForm_hP, fockForm_hvec, cw_orth]
  split_ifs <;> ring

theorem x0T_ne_zero {t : TLeechT} (ht : t ≠ 0) : x0T t ≠ 0 := by
  intro h
  apply ht
  refine TForm_nondegenerate.1 t fun t' => ?_
  have e := TPForm_hP (Pi.single (Fin.cast leech_rank.symm 0) 1)
    (Pi.single (Fin.cast leech_rank.symm 0) 1) t t'
  rw [← x0T_eq_hP, h, map_zero, LinearMap.zero_apply, fockForm_hvec] at e
  have hs : ∑ a, (Pi.single (Fin.cast leech_rank.symm 0) (1 : ℂ) : Fin (rank leech) → ℂ) a *
      (Pi.single (Fin.cast leech_rank.symm 0) (1 : ℂ) : Fin (rank leech) → ℂ) a = 1 := by
    rw [Finset.sum_eq_single (Fin.cast leech_rank.symm 0)]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  rw [hs] at e
  linear_combination 2 * e

/-! ## §3  The block map `φ_B` is an isometric involution of the top level -/

section PhiB

variable {s : ZMod 2} {t : TLeechT} (hts : t ∈ leechFrameT s) (ht0 : t ≠ 0) (ht : IsSeed t)

include hts ht0 ht in
/-- **`φ_B` is a `TPForm`-isometry of `(T_s⁺)₂`.** -/
theorem phiB_isom {x y : TP} (hx : x ∈ OmegaT s) (hy : y ∈ OmegaT s) :
    TPForm (phiTT (psiOf (Bop s)) x) (phiTT (psiOf (Bop s)) y) = TPForm x y := by
  have hx' := OmegaT_le_span s hx
  have hy' := OmegaT_le_span s hy
  clear hx hy
  induction hx' using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨m, t1, ht1, rfl⟩ := ha
    induction hy' using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨m', t2, ht2, rfl⟩ := hb
      rw [phiTT_hP, phiTT_hP, TPForm_hP_cw, TPForm_hP_cw]
      split_ifs with h
      · subst h; rw [TForm_psi_psi hts ht0 ht m ht1 ht2]
      · rfl
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, map_add, map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, map_smul, map_smul, ha]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, LinearMap.add_apply, ha, hb, LinearMap.map_add₂]
  | smul c a _ ha => rw [map_smul, map_smul, LinearMap.smul_apply, ha, LinearMap.map_smul₂]

include hts ht0 ht in
/-- **`φ_B² = 1` on `(T_s⁺)₂`.** -/
theorem phiB_invol {x : TP} (hx : x ∈ OmegaT s) :
    phiTT (psiOf (Bop s)) (phiTT (psiOf (Bop s)) x) = x := by
  have hx' := OmegaT_le_span s hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨m, t1, ht1, rfl⟩ := ha
    rw [phiTT_hP, phiTT_hP, psi_psi hts ht0 ht m ht1]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | smul c a _ ha => rw [map_smul, map_smul, ha]

end PhiB

/-! ## §4  `V₃⁺` side: weight-2 zero modes are symmetric, and the top basis is orthogonal -/

section VSide

open VnatBlock SkewIntertwiner Reconstruction M8h0 M8hKey LatticeTwisted TwistedHeisenberg FrameT
  SkewAdjoint VertexOperatorAlgebra SigmaKey

theorem L1_two {v : VPlus} (hv : v ∈ leechVOAPlus.grading 2) : leechVOAPlus.L 1 v = 0 := by
  have h := VertexOperatorAlgebra.L_one_lower leechVOAPlus hv
  rw [show (2 : ℤ) - 1 = 1 by norm_num, leechVOAPlus_grading_one] at h
  exact (Submodule.mem_bot ℂ).1 h

theorem leechBV_zero_mode (u : V0Sub.carrier) (hu : (u : VPlus) ∈ leechVOAPlus.grading 2)
    (a b : VPlus) : leechBV (actV u 1 a) b = leechBV a (actV u 1 b) := by
  rw [actV_apply, actV_apply, leechBV_qp_two hu (L1_two hu) 1 a b]
  norm_num

theorem TPForm_Phi_zero_mode {Φ : VPlus →ₗ[ℂ] TP} (hΦ : IsSigmaV3T Φ) (u : V0Sub.carrier)
    (hu : (u : VPlus) ∈ leechVOAPlus.grading 2) {a b : VPlus} (ha : a ∈ frameSector 1)
    (hb : b ∈ frameSector 1) :
    TPForm (Φ (actV u 1 a)) (Φ b) = TPForm (Φ a) (Φ (actV u 1 b)) := by
  have hs := sig_mem_grading hu
  rw [hΦ u (Set.mem_univ _) 1 a ha, hΦ u (Set.mem_univ _) 1 b hb, actT_eq_mode, actT_eq_mode,
    TPForm_qp_two hs (L1_two hs) 1]
  norm_num

theorem form_sq_ne {n m : leech.carrier} (hn : n ∈ halfFourChi 1) (hm : m ∈ halfFourChi 1)
    (hne : n ≠ m) : ((leech.form n m : ℤ) : ℂ) * ((leech.form n m : ℤ) : ℂ) ≠ 16 := by
  have hn4 := (mem_halfFourChi hn).1
  have hm4 := (mem_halfFourChi hm).1
  have hsym : leech.form m n = leech.form n m := LinearMap.BilinForm.isSymm_def.mp leech.isSymm m n
  intro h
  have h' : leech.form n m * leech.form n m = 16 := by exact_mod_cast h
  have hcases : leech.form n m = 4 ∨ leech.form n m = -4 := by
    have : (leech.form n m - 4) * (leech.form n m + 4) = 0 := by linear_combination h'
    rcases mul_eq_zero.mp this with h1 | h1
    · left; linarith
    · right; linarith
  rcases hcases with h4 | h4
  · have hz : leech.form (n - m) (n - m) = 0 := by
      simp only [map_sub, LinearMap.sub_apply]
      rw [hn4, hm4, h4, hsym, h4]; norm_num
    have := leech_posDef (n - m) (sub_ne_zero.mpr hne)
    omega
  · have hz : leech.form (n + m) (n + m) = 0 := by
      simp only [map_add, LinearMap.add_apply]
      rw [hn4, hm4, h4, hsym, h4]; norm_num
    by_cases h0 : n + m = 0
    · have : m = -n := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact h0
      exact neg_not_mem_halfFourChi hn (this ▸ hm)
    · have := leech_posDef (n + m) h0
      omega

/-- **Orthogonality of the top basis** for any form for which `o(n(−1)²𝟙)` is symmetric:
`x_n ⟂ x_m` for `n ≠ m` in `S₁` (eigenvalues `⟨n,n⟩² = 16 ≠ ⟨n,m⟩²`). -/
theorem bilin_sep (G : LinearMap.BilinForm ℂ VPlus) {n m : leech.carrier} (hn : n ∈ halfFourChi 1)
    (hm : m ∈ halfFourChi 1) (hne : n ≠ m)
    (hG : G (actV (dV n n) 1 (frameX0P n)) (frameX0P m)
      = G (frameX0P n) (actV (dV n n) 1 (frameX0P m))) :
    G (frameX0P n) (frameX0P m) = 0 := by
  rw [actV_dV, actV_dV, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul,
    (mem_halfFourChi hn).1] at hG
  have h : (16 - ((leech.form n m : ℤ) : ℂ) * ((leech.form n m : ℤ) : ℂ)) * G (frameX0P n) (frameX0P m) = 0 := by
    push_cast at hG ⊢; linear_combination hG
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (form_sq_ne hn hm hne).symm)

theorem leechBV_sep {n m : leech.carrier} (hn : n ∈ halfFourChi 1) (hm : m ∈ halfFourChi 1)
    (hne : n ≠ m) : leechBV (frameX0P n) (frameX0P m) = 0 :=
  bilin_sep leechBV hn hm hne (leechBV_zero_mode _ (dV_mem_grading n n) _ _)

theorem TPForm_Phi_sep {Φ : VPlus →ₗ[ℂ] TP} (hΦ : IsSigmaV3T Φ) {n m : leech.carrier}
    (hn : n ∈ halfFourChi 1) (hm : m ∈ halfFourChi 1) (hne : n ≠ m) :
    TPForm (Φ (frameX0P n)) (Φ (frameX0P m)) = 0 :=
  bilin_sep (TPForm.compl₁₂ Φ Φ) hn hm hne
    (TPForm_Phi_zero_mode hΦ _ (dV_mem_grading n n) (frameX0P_mem_OmegaV3 hn).1
      (frameX0P_mem_OmegaV3 hm).1)

end VSide

/-! ## §5  Similitudes are top-level statements (any `Φ`, any scalar `κ`) -/

section Simil

open VnatBlock SkewIntertwiner Reconstruction M8h0 M8hKey LatticeTwisted TwistedHeisenberg FrameT
  SkewAdjoint VertexOperatorAlgebra SigmaKey

variable {Φ : VPlus →ₗ[ℂ] TP} (hΦ : IsSigmaV3T Φ) (κ : ℂ)

include hΦ in
theorem Phi_weight' {x : VPlus} (hx : x ∈ frameSector 1) {k : ℤ}
    (hk : x ∈ leechVOAPlus.grading k) : Φ x ∈ plusModule.weight (k : ℂ) := by
  apply eigenvector_mem_weight
  have h := IsSigmaV3T.L0_comm hΦ hx
  rw [← h]
  have e : mode (leechVOAPlus.Y leechVOAPlus.conformalVector) 1 x = (k : ℂ) • x :=
    leechVOAPlus.L0_grading x hk
  rw [e, map_smul]

/-- The defect form `F(a,b) = TPForm(Φa, Φb) − κ·leechBV(a, b)`. -/
noncomputable def Fk (Φ : VPlus →ₗ[ℂ] TP) (κ : ℂ) : LinearMap.BilinForm ℂ VPlus :=
  TPForm.compl₁₂ Φ Φ - κ • leechBV

theorem Fk_apply (a b : VPlus) : Fk Φ κ a b = TPForm (Φ a) (Φ b) - κ * leechBV a b := rfl

theorem Fk_symm (a b : VPlus) : Fk Φ κ a b = Fk Φ κ b a := by
  rw [Fk_apply, Fk_apply, TPForm_symm, SimpleNat.leechBV_symm]

include hΦ in
theorem Fk_inv {k : ℤ} (u : V0Sub.carrier) (hu : (u : VPlus) ∈ leechVOAPlus.grading k) (n : ℤ)
    {a b : VPlus} (ha : a ∈ frameSector 1) (hb : b ∈ frameSector 1) :
    Fk Φ κ (actV u n a) b = (-1 : ℂ) ^ k • ∑ j ∈ Finset.range (k.toNat + 1),
      ((j.factorial : ℂ)⁻¹) • Fk Φ κ a (actV (((V0P.L 1) ^ j) u) (2 * k - n - 2 - (j : ℤ)) b) := by
  have hT : TPForm (Φ (actV u n a)) (Φ b) = (-1 : ℂ) ^ k • ∑ j ∈ Finset.range (k.toNat + 1),
      ((j.factorial : ℂ)⁻¹) • TPForm (Φ a) (Φ (actV (((V0P.L 1) ^ j) u) (2 * k - n - 2 - (j : ℤ)) b)) := by
    rw [hΦ u (Set.mem_univ _) n a ha, actT_eq_mode,
      TPForm_fhlInv (sig_mem_grading hu) n (Φ a) (Φ b)]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hΦ _ (Set.mem_univ _) _ b hb, actT_eq_mode, sig_L1_pow_coe]
  have hV : leechBV (actV u n a) b = (-1 : ℂ) ^ k • ∑ j ∈ Finset.range (k.toNat + 1),
      ((j.factorial : ℂ)⁻¹) • leechBV a (actV (((V0P.L 1) ^ j) u) (2 * k - n - 2 - (j : ℤ)) b) := by
    rw [actV_apply, leechBV_inv k u hu n a b]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [actV_apply, V0P_coe_L_pow]
  rw [Fk_apply, hT, hV, smul_eq_mul ((-1 : ℂ) ^ k), smul_eq_mul ((-1 : ℂ) ^ k), Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fk_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

include hΦ in
theorem Fk_orth {z₀ : VPlus} (hz₀ : z₀ ∈ frameSector 1) {w : ℤ} (hzw : z₀ ∈ leechVOAPlus.grading w)
    {c : VPlus} (hc : c ∈ frameSector 1) {w' : ℤ} (hcw : c ∈ leechVOAPlus.grading w') (hne : w ≠ w') :
    Fk Φ κ z₀ c = 0 := by
  rw [Fk_apply, leechBV_orth w w' hne z₀ hzw c hcw,
    TPForm_weightOrth (w : ℂ) (w' : ℂ) (by exact_mod_cast hne) _ (Phi_weight' hΦ hz₀ hzw) _
      (Phi_weight' hΦ hc hcw), mul_zero, sub_zero]

include hΦ in
/-- **A similitude from its top-level row** against a cyclic vector: if
`TPForm(Φz₀, Φb) = κ·leechBV(z₀, b)` for `b ∈ (V₃⁺)_w`, then `TPForm(Φa, Φb) = κ·leechBV(a, b)`
on all of `V₃⁺`. -/
theorem simil_of_top {z₀ : VPlus} (hz₀ : z₀ ∈ frameSector 1) {w : ℤ}
    (hzw : z₀ ∈ leechVOAPlus.grading w)
    (hcyc : Submodule.span ℂ {y | ∃ u ∈ (Set.univ : Set V0Sub.carrier), ∃ n : ℤ, y = actV u n z₀}
      = frameSector 1)
    (htop : ∀ b ∈ frameSector 1, b ∈ leechVOAPlus.grading w →
      TPForm (Φ z₀) (Φ b) = κ * leechBV z₀ b) :
    ∀ a ∈ frameSector 1, ∀ b ∈ frameSector 1, TPForm (Φ a) (Φ b) = κ * leechBV a b := by
  have hhomog : ∀ c ∈ frameSector 1, ∀ w' : ℤ, c ∈ leechVOAPlus.grading w' → Fk Φ κ z₀ c = 0 := by
    intro c hc w' hcw
    by_cases h : w = w'
    · subst h; rw [Fk_apply, htop c hc hcw, sub_self]
    · exact Fk_orth hΦ κ hz₀ hzw hc hcw h
  have hz : ∀ b ∈ frameSector 1, Fk Φ κ b z₀ = 0 := by
    intro b hb
    refine span_V3_induction hcyc (fun b => Fk Φ κ b z₀ = 0) (by simp)
      (fun a b ha hb' => by simp only at ha hb' ⊢; rw [map_add, LinearMap.add_apply, ha, hb', add_zero])
      (fun c a ha => by simp only at ha ⊢; rw [map_smul, LinearMap.smul_apply, ha, smul_zero])
      (fun k u hu n => ?_) hb
    simp only
    rw [Fk_inv hΦ κ u hu n hz₀ hz₀]
    refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => smul_eq_zero_of_right _ ?_)
    have hj := L_one_pow_mem V0P (k := k) (x := u) hu j
    exact hhomog _ (actV_stab _ (Set.mem_univ _) _ _ hz₀) _
      (leechVOAPlus.smul_mem_grading (show (((V0P.L 1) ^ j) u : VPlus) ∈ leechVOAPlus.grading (k - j) from hj) hzw _)
  intro a ha b hb
  have key := span_V3_induction hcyc (fun a => ∀ b ∈ frameSector 1, Fk Φ κ a b = 0)
    (fun b _ => by simp)
    (fun a a' h h' b hb => by rw [map_add, LinearMap.add_apply, h b hb, h' b hb, add_zero])
    (fun c a h b hb => by rw [map_smul, LinearMap.smul_apply, h b hb, smul_zero])
    (fun k u hu n b hb => by
      rw [Fk_inv hΦ κ u hu n hz₀ hb]
      refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => smul_eq_zero_of_right _ ?_)
      rw [Fk_symm]
      exact hz _ (actV_stab _ (Set.mem_univ _) _ _ hb)) ha b hb
  have := key
  rw [Fk_apply, sub_eq_zero] at this
  exact this

end Simil

end VOA.Moonshine.SigmaAssemble
