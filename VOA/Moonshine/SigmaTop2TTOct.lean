/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaTop2TT

/-!
# The octad letters on `T_s⁺`, and the unconditional (R-top) / `σ` on `T_s⁺`

The commuting involutions `Z_{0k}` (`k ≠ 0`) split `T_s` into joint eigenvectors (`eig_induct`);
write `u = uN N` for the character (`u_k = −1` iff `k ∈ N`, `0 ∉ N`).  On such a `z`:

* `B z = β(N) z`, `β(N) = ω^{|N|}`, so `ψ_m z = u_m β(N) z` (`Bop_eigN`, `psiOf_eigN`).
* `e_{γ_S}` flips `u_k` exactly for `[k ∈ D] ≠ [0 ∈ D]` (`eig_flip`, character `flipN D N`).
* **Twisted `ξ`-closure.**  `chargesU z N = {a | W(a) z = ξ(a) χ_N(a) z}`,
  `χ_N(x) = (−1)^{Σ_N x_i}`, is an additive subgroup; it contains `a₀₀` (where `W` is the frame
  scalar, read off at the seed) and `a⁻_{0k}` (where `W` is `Z_{0k}` up to `ξ`), hence every
  `δ_{S'}` (`dSA_mem_chargesU`), so
  `W(a_{S'}) z = ε ξ(−1_{S'}) ∏_{S'} u · W(1_D) z` (`Wop_aSA_eig`).
* **Golay constraint.**  For `z ≠ 0` the codeword relations `W(2b_{D'}) = ξ(1_{D'})` force
  `∏_{D'} u = 1` for every Golay codeword `D'` (`golay_constraint`), so `N` is itself a codeword
  and `|N| ≡ 0 (4)` (`four_dvd_card_of_orth`, by self-duality and double evenness).
* **Hadamard sums.**  The target is `Σ_{S' ⊆ D even} ∏_{S'} (i s_i u_i)` times `W(1_D) z`; for an
  `±1` pattern `ε` with `∏_D ε = 1` this is `16 ∏_D g(ε_i)`, `g(1) = 1`, `g(−1) = i` (`had_I`).
* **Base identity.**  `(∏_S i)(∏_S u) β(N') = β(N) ∏_D g(s_i u_i)` (`base_identity`), proved
  coordinatewise up to a correction `ρ` with `∏ ρ = ω^8 ∏_D u = 1` (`0 ∉ D`) or
  `ω^{16} (−i)^{|N|} = 1` (`0 ∈ D`): this is where both halves of the Golay constraint are used.

## Main results
* `octadTT_eig` — the octad identity on a joint eigenvector; `phiTT_ZMT_aSA` on all of `T_s`.
* `topSigmaTT : ∃ s φ, TopSigmaTT s s φ`.
* `sigmaTT_exists` — a `v0Sigma`-twisted intertwiner `Φ : T_s⁺ → T_s⁺` of `V₀⁺`-modules
  (`IsSigmaTT s Φ`) hitting a nonzero cyclic vector `x0T t₀`, `t₀ ∈ T_s`.
* `topSigma_both` — from one seed, `TopSigmaV3 (s+1)` and `TopSigmaTT s s` together.

## Status
**Unconditional**, `sorry`-free; `#print axioms topSigmaTT`, `sigmaTT_exists`, `topSigma_both`:
`[propext, Classical.choice, Quot.sound]` (no `VOA.pbw`).  Which `s` occurs is not determined by
the library's definitions, hence the `∃ s`.  Imported by the umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaTop

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen VOA.Moonshine.Triality HeisenbergN
open VOA.Moonshine.TrialityTw VOA.Moonshine.SigmaExist
open Module (End)

/-! ## §1  `ω = e^{iπ/4}` -/

theorem ωB_sq : ωB ^ 2 = Complex.I := by
  have hs := sqrt2_mul_self'
  unfold ωB rH
  linear_combination (Complex.I / 2) * hs
    + (((Real.sqrt 2 : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq

theorem ωB_four : ωB ^ 4 = -1 := by
  rw [show ωB ^ 4 = (ωB ^ 2) ^ 2 by ring, ωB_sq, Complex.I_sq]

theorem ωB_eight : ωB ^ 8 = 1 := by
  rw [show ωB ^ 8 = (ωB ^ 4) ^ 2 by ring, ωB_four]; norm_num

theorem ωB_ne_zero : ωB ≠ 0 := by
  intro h; have := ωB_eight; rw [h] at this; norm_num at this

theorem aB_sub_bB : aB - bB = ωB := by unfold aB bB; ring

/-! ## §2  Joint eigenvectors of the `Z_{0k}` -/

/-- The character `u_k = −1` on `N`, `+1` off `N`. -/
noncomputable def uN (N : Finset (Fin 24)) (k : Fin 24) : ℂ := if k ∈ N then -1 else 1

/-- `z` is a joint eigenvector of the `Z_{0k}` (`k ≠ 0`) with character `uN N`. -/
def IsEigN (N : Finset (Fin 24)) (z : TLeechT) : Prop := ∀ k, k ≠ 0 → ZZ 0 k z = uN N k • z

/-- `β(N) = ω^{|N|}`, the eigenvalue of `B` on the character `N`. -/
noncomputable def betaN (N : Finset (Fin 24)) : ℂ := ∏ i, if i ∈ N then ωB else 1

theorem uN_zero {N : Finset (Fin 24)} (h : (0 : Fin 24) ∉ N) : uN N 0 = 1 := by simp [uN, h]

theorem Bop_eigN {s : ZMod 2} {z : TLeechT} (hz : z ∈ leechFrameT s) {N : Finset (Fin 24)}
    (hN0 : (0 : Fin 24) ∉ N) (hE : IsEigN N z) : Bop s z = betaN N • z := by
  rw [Bop_eigen hz (u := uN N) hE, betaN, Fin.prod_univ_def]
  congr 2
  apply List.map_congr_left
  intro k _
  by_cases hk : k = 0
  · subst hk; simp [hN0]
  · simp only [if_neg hk, uN]
    split_ifs
    · rw [mul_neg_one, ← sub_eq_add_neg, aB_sub_bB]
    · rw [mul_one, aB_add_bB]

theorem psiOf_eigN {s : ZMod 2} {z : TLeechT} (hz : z ∈ leechFrameT s) {N : Finset (Fin 24)}
    (hN0 : (0 : Fin 24) ∉ N) (hE : IsEigN N z) (m : Fin 24) :
    psiOf (Bop s) m z = (uN N m * betaN N) • z := by
  by_cases hm : m = 0
  · subst hm; rw [psiOf_zero, Bop_eigN hz hN0 hE, uN_zero hN0, one_mul]
  · rw [psiOf_ne hm, Module.End.mul_apply, Bop_eigN hz hN0 hE, map_smul, hE m hm, smul_smul,
      mul_comm]

theorem commute_ZZ_ZZ (j k l m : Fin 24) : Commute (ZZ j k) (ZZ l m) :=
  (commute_ZZ_AM j k l m).smul_right 2

/-- **`T_s` is spanned by joint `Z`-eigenvectors**, in induction form: an additive property of
vectors of `T_s` holding on every joint eigenvector holds on all of `T_s`. -/
theorem eig_induct {s : ZMod 2} (P : TLeechT → Prop) (hadd : ∀ x y, P x → P y → P (x + y))
    (heig : ∀ z ∈ leechFrameT s, ∀ N : Finset (Fin 24), (0 : Fin 24) ∉ N → IsEigN N z → P z) :
    ∀ z ∈ leechFrameT s, P z := by
  have key : ∀ K : Finset (Fin 24), ∀ z ∈ leechFrameT s,
      (∀ k, k ∉ K → k ≠ 0 → ZZ 0 k z = z ∨ ZZ 0 k z = -z) → P z := by
    intro K
    induction K using Finset.induction_on with
    | empty =>
      intro z hz hpm
      classical
      refine heig z hz (Finset.univ.filter fun k => k ≠ 0 ∧ ZZ 0 k z ≠ z) (by simp) fun k hk => ?_
      rcases hpm k (Finset.notMem_empty k) hk with h | h
      · rw [uN, if_neg (by simp [h]), one_smul, h]
      · by_cases hz' : ZZ 0 k z = z
        · rw [uN, if_neg (by simp [hz']), one_smul, hz']
        · rw [uN, if_pos (by simp [hk, hz']), neg_one_smul, h]
    | insert k K hk ih =>
      intro z hz hpm
      have hsplit : z = (1 / 2 : ℂ) • (z + ZZ 0 k z) + (1 / 2 : ℂ) • (z - ZZ 0 k z) := by
        rw [← smul_add]; rw [show z + ZZ 0 k z + (z - ZZ 0 k z) = (2 : ℂ) • z by
          rw [two_smul]; abel, smul_smul]; norm_num
      have hmem : ∀ c : ℂ, (1 / 2 : ℂ) • (z + c • ZZ 0 k z) ∈ leechFrameT s := fun c =>
        Submodule.smul_mem _ _ (add_mem hz (Submodule.smul_mem _ _ (ZZ_mem_frame hz)))
      have hpart : ∀ c : ℂ, c * c = 1 → ∀ k', k' ∉ K → k' ≠ 0 →
          ZZ 0 k' ((1 / 2 : ℂ) • (z + c • ZZ 0 k z)) = (1 / 2 : ℂ) • (z + c • ZZ 0 k z) ∨
          ZZ 0 k' ((1 / 2 : ℂ) • (z + c • ZZ 0 k z)) = -((1 / 2 : ℂ) • (z + c • ZZ 0 k z)) := by
        intro c hc k' hk' hk'0
        by_cases hkk : k' = k
        · subst hkk
          have hZ : ZZ 0 k' (ZZ 0 k' z) = z := by
            rw [← Module.End.mul_apply, ZZ_mul_self (Ne.symm hk'0), Module.End.one_apply]
          by_cases hc1 : c = 1
          · left; subst hc1
            rw [map_smul, map_add, map_smul, hZ, one_smul, one_smul, add_comm]
          · right
            have hc' : c = -1 := by
              have : (c - 1) * (c + 1) = 0 := by linear_combination hc
              rcases mul_eq_zero.mp this with h | h
              · exact absurd (sub_eq_zero.mp h) hc1
              · exact eq_neg_of_add_eq_zero_left h
            subst hc'
            rw [map_smul, map_add, map_smul, hZ, neg_one_smul, neg_one_smul, ← smul_neg, neg_add,
              neg_neg, add_comm]
        · have hcomm : ZZ 0 k' (ZZ 0 k z) = ZZ 0 k (ZZ 0 k' z) := by
            rw [← Module.End.mul_apply, (commute_ZZ_ZZ 0 k' 0 k).eq, Module.End.mul_apply]
          rcases hpm k' (by simp [hkk, hk']) hk'0 with h | h
          · left; rw [map_smul, map_add, map_smul, hcomm, h]
          · right; rw [map_smul, map_add, map_smul, hcomm, h, map_neg, smul_neg, ← neg_add, smul_neg]
      rw [hsplit]
      refine hadd _ _ ?_ ?_
      · have h1 := ih _ (hmem 1) (hpart 1 (by norm_num))
        rwa [one_smul] at h1
      · have h1 := ih _ (hmem (-1)) (hpart (-1) (by norm_num))
        rwa [neg_one_smul, ← sub_eq_add_neg] at h1
  intro z hz
  exact key Finset.univ z hz fun k hk => absurd (Finset.mem_univ k) hk

/-! ## §3  The octad letters flip the character -/

/-- The character of `e_{γ_S} z`: `u_k` flips exactly when `[k ∈ D] ≠ [0 ∈ D]` (`k ≠ 0`). -/
noncomputable def flipN (D N : Finset (Fin 24)) : Finset (Fin 24) :=
  Finset.univ.filter fun k => k ≠ 0 ∧ (k ∈ N ↔ (k ∈ D ↔ (0 : Fin 24) ∈ D))

section Flip

variable {D : Finset (Fin 24)} (hDA : ind D ∈ Leech.subA)

theorem form_gM_aSA {S : Finset (Fin 24)} (h : _root_.Even S.card) (k : Fin 24) :
    leech.form (gM 0 k) (inclΛ (aSA hDA S)) = (ind D 0 - 2 * ind S 0) - (ind D k - 2 * ind S k) := by
  rw [leech_form_lv, dotProduct]
  simp only [lv_gM_apply, lv_aSA_apply hDA h]
  have e : ∀ m : Fin 24, 4 * ((if m = 0 then (1 : ℤ) else 0) - (if m = k then 1 else 0)) *
      (2 * (ind D m - 2 * ind S m)) = (if m = 0 then 8 * (ind D m - 2 * ind S m) else 0)
        - (if m = k then 8 * (ind D m - 2 * ind S m) else 0) := by
    intro m; split_ifs <;> ring
  rw [Finset.sum_congr rfl fun m _ => e m, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  omega

theorem eig_flip {S : Finset (Fin 24)} (h : _root_.Even S.card) {N : Finset (Fin 24)}
    {z : TLeechT} (hE : IsEigN N z) : IsEigN (flipN D N) (eL (inclΛ (aSA hDA S)) z) := by
  intro k hk
  have hc := eL_comm_apply (gM 0 k) (inclΛ (aSA hDA S)) z
  rw [ZZ_apply]
  change (2 * kM 0 k) • eL (gM 0 k) (eL (inclΛ (aSA hDA S)) z) = _
  rw [hc, smul_comm, ← map_smul]
  change (-1 : ℂ) ^ _ • eL (inclΛ (aSA hDA S)) ((2 * kM 0 k) • eT leech leech_even leech_isUnit_det_gramMat (gM 0 k) z) = _
  rw [← ZZ_apply, hE k hk, map_smul, smul_smul, form_gM_aSA hDA h]
  congr 1
  simp only [uN, flipN, Finset.mem_filter, Finset.mem_univ, true_and, ind]
  by_cases h0D : (0 : Fin 24) ∈ D <;> by_cases h0S : (0 : Fin 24) ∈ S <;>
    by_cases hkD : k ∈ D <;> by_cases hkS : k ∈ S <;> by_cases hkN : k ∈ N <;>
    simp [h0D, h0S, hkD, hkS, hkN, hk] <;> norm_num

end Flip

/-! ## §4  The twisted `ξ`-closure -/

/-- The character `χ_N(x) = (−1)^{Σ_{i ∈ N} x_i}`. -/
noncomputable def chiN (N : Finset (Fin 24)) (x : Fin 24 → ℤ) : ℂ := (-1 : ℂ) ^ (∑ i ∈ N, x i)

/-- The twisted refinement `ξ_N = ξ · χ_N`. -/
noncomputable def xiN (N : Finset (Fin 24)) (x : Fin 24 → ℤ) : ℂ := xi x * chiN N x

theorem chiN_add (N : Finset (Fin 24)) (x y : Fin 24 → ℤ) : chiN N (x + y) = chiN N x * chiN N y := by
  unfold chiN
  rw [show ∑ i ∈ N, (x + y) i = ∑ i ∈ N, x i + ∑ i ∈ N, y i by
    rw [← Finset.sum_add_distrib]; rfl, zpow_add₀ (by norm_num)]

theorem chiN_zero (N : Finset (Fin 24)) : chiN N 0 = 1 := by simp [chiN]

theorem chiN_ne_zero (N : Finset (Fin 24)) (x : Fin 24 → ℤ) : chiN N x ≠ 0 :=
  zpow_ne_zero _ (by norm_num)

theorem xiN_mul (N : Finset (Fin 24)) (x y : Fin 24 → ℤ) :
    xiN N x * xiN N y = εN (phiR x) (phiR y) * xiN N (x + y) := by
  unfold xiN; rw [chiN_add]
  have := xi_mul x y
  linear_combination (chiN N x * chiN N y) * this

theorem xiN_zero (N : Finset (Fin 24)) : xiN N 0 = 1 := by rw [xiN, xi_zero, chiN_zero, one_mul]

theorem xiN_ne_zero (N : Finset (Fin 24)) (x : Fin 24 → ℤ) : xiN N x ≠ 0 :=
  mul_ne_zero (xi_ne_zero x) (chiN_ne_zero N x)

/-- The charges `a ∈ R₀` with `W(a) z = ξ_N(a) z`; an additive subgroup. -/
noncomputable def chargesU (z : TLeechT) (N : Finset (Fin 24)) : AddSubgroup lam0.carrier where
  carrier := {a | ∃ x, inclN a = phiR x ∧ Wop a z = xiN N x • z}
  zero_mem' := ⟨0, by rw [map_zero, map_zero], by rw [Wop_zero, xiN_zero, one_smul]; rfl⟩
  add_mem' := by
    rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
    refine ⟨x + y, by rw [map_add, map_add, hx, hy], ?_⟩
    have hm := congrArg (fun f : End ℂ TLeechT => f z) (Wop_mul a b)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at hm
    rw [hb, map_smul, ha, smul_smul, hx, hy, mul_comm, xiN_mul] at hm
    have hs := εN_sq (phiR x) (phiR y)
    calc Wop (a + b) z = (εN (phiR x) (phiR y) * εN (phiR x) (phiR y)) • Wop (a + b) z := by
          rw [hs, one_smul]
      _ = εN (phiR x) (phiR y) • (εN (phiR x) (phiR y) • Wop (a + b) z) := by rw [smul_smul]
      _ = εN (phiR x) (phiR y) • ((εN (phiR x) (phiR y) * xiN N (x + y)) • z) := by rw [← hm]
      _ = xiN N (x + y) • z := by rw [smul_smul, ← mul_assoc, hs, one_mul]
  neg_mem' := by
    rintro a ⟨x, hx, ha⟩
    refine ⟨-x, by rw [map_neg, map_neg, hx], ?_⟩
    have hm := congrArg (fun f : End ℂ TLeechT => f z) (Wop_mul (-a) a)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, ha, map_smul, neg_add_cancel, Wop_zero,
      Module.End.one_apply] at hm
    have hx' := xiN_mul N x (-x)
    rw [add_neg_cancel, xiN_zero, mul_one, map_neg] at hx'
    simp only [εN, latticeCocycle_neg_right] at hx'
    rw [map_neg, hx] at hm
    simp only [εN, latticeCocycle_neg_left] at hm
    have hne := xiN_ne_zero N x
    have : Wop (-a) z = (xiN N x)⁻¹ • (latticeCocycle golayN (phiR x) (phiR x) • z) := by
      rw [← hm, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this, smul_smul]
    congr 1
    rw [← hx']; field_simp

theorem mem_chargesU {z : TLeechT} {N : Finset (Fin 24)} {a : lam0.carrier} (h : a ∈ chargesU z N)
    {y : Fin 24 → ℤ} (hy : inclN a = phiR y) : Wop a z = xiN N y • z := by
  obtain ⟨x, hx, ha⟩ := h
  rw [ha, phiR_injective (hx.symm.trans hy)]

theorem inclΛ_aP00 : inclΛ (aP 0 0) = frameW := by
  apply Subtype.ext
  change lv (inclΛ (aP 0 0)) = (8 : ℤ) • e0
  rw [lv_inclΛ, aP_valA]
  funext i
  by_cases hi : i = 0 <;> simp [apv, e0, hi]

/-- `W(a₀₀)` is the scalar `ξ(2e₀)` on all of `T_s` (read off at the seed). -/
theorem Wop_aP00_frame {s : ZMod 2} {t : TLeechT} (hts : t ∈ leechFrameT s) (ht0 : t ≠ 0)
    (ht : IsSeed t) {z : TLeechT} (hz : z ∈ leechFrameT s) :
    Wop (aP 0 0) z = xi (Pi.single 0 1 + Pi.single 0 1) • z := by
  have hW : ∀ y ∈ leechFrameT s, Wop (aP 0 0) y
      = (tc (aP 0 0) * (FrameT.sqrtEps leech frameW * Extraspecial.sgn s)) • y := by
    intro y hy
    rw [Wop, LinearMap.smul_apply, inclΛ_aP00]
    change tc (aP 0 0) • eL frameW y = _
    rw [eL_frameW_apply hy, smul_smul]
  have hseed := mem_chargesS (mem_chargesS_aP ht 0 0) (phiR_pair 0 0).symm
  rw [hW t hts] at hseed
  have hc := smul_left_injective ℂ ht0 hseed
  simp only at hc
  rw [hW z hz, hc]

theorem chiN_pair00 {N : Finset (Fin 24)} (hN0 : (0 : Fin 24) ∉ N) :
    chiN N (Pi.single 0 1 + Pi.single 0 1) = 1 := by
  unfold chiN
  rw [Finset.sum_eq_zero fun i hi => by
    have : i ≠ 0 := fun h => hN0 (h ▸ hi)
    simp [this]]
  rfl

theorem chiN_pairM {N : Finset (Fin 24)} (hN0 : (0 : Fin 24) ∉ N) (k : Fin 24) :
    chiN N (Pi.single 0 1 - Pi.single k 1) = uN N k := by
  unfold chiN uN
  have e : ∀ i ∈ N, (Pi.single 0 1 - Pi.single k 1 : Fin 24 → ℤ) i = -(if i = k then 1 else 0) := by
    intro i hi
    have : i ≠ 0 := fun h => hN0 (h ▸ hi)
    simp [Pi.single_apply, this]
  rw [Finset.sum_congr rfl e, Finset.sum_neg_distrib, Finset.sum_ite_eq']
  split_ifs <;> norm_num

section Gen

variable {s : ZMod 2} {t : TLeechT} (hts : t ∈ leechFrameT s) (ht0 : t ≠ 0) (ht : IsSeed t)
  {z : TLeechT} (hz : z ∈ leechFrameT s) {N : Finset (Fin 24)} (hN0 : (0 : Fin 24) ∉ N)
  (hE : IsEigN N z)

include hts ht0 ht hz hN0 in
theorem aP00_mem_chargesU : aP 0 0 ∈ chargesU z N := by
  refine ⟨Pi.single 0 1 + Pi.single 0 1, (phiR_pair 0 0).symm, ?_⟩
  rw [Wop_aP00_frame hts ht0 ht hz, xiN, chiN_pair00 hN0, mul_one]

include hN0 hE in
theorem aM0_mem_chargesU {k : Fin 24} (hk : k ≠ 0) : aM 0 k ∈ chargesU z N := by
  refine ⟨Pi.single 0 1 - Pi.single k 1, (phiR_pairM 0 k).symm, ?_⟩
  have h := hE k hk
  rw [ZZ_eq_Wop (Ne.symm hk), LinearMap.smul_apply] at h
  rw [xiN, chiN_pairM hN0 k, xi_pairM]
  have hs := εN_sq (golayRoot 0) (golayRoot k)
  have he := golayEps_mul_self k
  set c := golayEps k * εN (golayRoot 0) (golayRoot k) with hc
  have hcc : c * c = 1 := by rw [hc]; linear_combination (golayEps k * golayEps k) * hs + he
  have h2 := congrArg (fun x => c • x) h
  simp only [smul_smul] at h2
  rw [hcc, one_smul] at h2
  rw [h2]

include hts ht0 ht hz hN0 hE in
theorem aP0_mem_chargesU (i : Fin 24) : aP 0 i ∈ chargesU z N := by
  by_cases hi : i = 0
  · subst hi; exact aP00_mem_chargesU hts ht0 ht hz hN0
  · have e : aP 0 i = aP 0 0 - aM 0 i := by
      apply inclN_injective
      rw [map_sub, inclN_aP, inclN_aP, inclN_aM]; abel
    rw [e]
    exact sub_mem (aP00_mem_chargesU hts ht0 ht hz hN0) (aM0_mem_chargesU hN0 hE hi)

include hts ht0 ht hz hN0 hE in
theorem dSA_mem_chargesU {S' : Finset (Fin 24)} (he : _root_.Even S'.card) : dSA S' ∈ chargesU z N := by
  rw [dSA_eq_sum he]
  exact sub_mem (sum_mem fun i _ => aP0_mem_chargesU hts ht0 ht hz hN0 hE i)
    (zsmul_mem (aP0_mem_chargesU hts ht0 ht hz hN0 hE 0) _)

end Gen

/-! ## §5  `W(a_{S'})` on a joint eigenvector, and the Golay constraint on characters -/

theorem Wop_aSA_eig {D : Finset (Fin 24)} (hDA : ind D ∈ Leech.subA) {z : TLeechT}
    {N : Finset (Fin 24)} (hd : ∀ S' : Finset (Fin 24), _root_.Even S'.card → dSA S' ∈ chargesU z N)
    {S' : Finset (Fin 24)} (he : _root_.Even S'.card) :
    Wop (aSA hDA S') z = (εN (inclN (bAD hDA)) (dl S') * xiN N (-ind S')) • Wop (bAD hDA) z := by
  have hm := congrArg (fun f : End ℂ TLeechT => f z) (Wop_mul (bAD hDA) (-dSA S'))
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at hm
  have hd' : Wop (-dSA S') z = xiN N (-ind S') • z := by
    refine mem_chargesU (neg_mem (hd S' he)) ?_
    rw [map_neg, inclN_dSA he, map_neg]; rfl
  rw [hd', map_smul, map_neg, inclN_dSA he] at hm
  simp only [εN, latticeCocycle_neg_right, ← sub_eq_add_neg] at hm
  change xiN N (-ind S') • Wop (bAD hDA) z = εN (inclN (bAD hDA)) (dl S') • Wop (aSA hDA S') z at hm
  have hs := εN_sq (inclN (bAD hDA)) (dl S')
  calc Wop (aSA hDA S') z
      = (εN (inclN (bAD hDA)) (dl S') * εN (inclN (bAD hDA)) (dl S')) • Wop (aSA hDA S') z := by
        rw [hs, one_smul]
    _ = εN (inclN (bAD hDA)) (dl S') • (εN (inclN (bAD hDA)) (dl S') • Wop (aSA hDA S') z) := by
        rw [smul_smul]
    _ = _ := by rw [← hm, smul_smul]

theorem chiN_ind (N X : Finset (Fin 24)) : chiN N (ind X) = ∏ i ∈ X, uN N i := by
  unfold chiN uN
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  have : ∑ i ∈ N, ind X i = ((X.filter (· ∈ N)).card : ℤ) := by
    simp only [ind]
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.filter_mem_eq_inter, Finset.inter_comm]
  rw [this, zpow_natCast]

theorem chiN_neg_ind (N X : Finset (Fin 24)) : chiN N (-ind X) = ∏ i ∈ X, uN N i := by
  rw [← chiN_ind]
  unfold chiN
  rw [show ∑ i ∈ N, (-ind X) i = -∑ i ∈ N, ind X i by
    rw [← Finset.sum_neg_distrib]; rfl, zpow_neg, ← inv_zpow]
  norm_num

theorem card_ind (X : Finset (Fin 24)) : ∑ i, ind X i = X.card := by
  simp only [ind, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem valA_bAD {D : Finset (Fin 24)} (hDA : ind D ∈ Leech.subA) : valA (bAD hDA) = ind D := rfl

theorem valA_dSA {S : Finset (Fin 24)} (he : _root_.Even S.card) : valA (dSA S) = (2 : ℤ) • ind S := by
  change (show ↥Leech.subA from dSA S).1 = _
  unfold dSA; rw [dif_pos he]

/-- **The Golay constraint**: a nonzero joint eigenvector has a character even on every codeword. -/
theorem golay_constraint {z : TLeechT} (hz0 : z ≠ 0) {N : Finset (Fin 24)}
    (hd : ∀ S' : Finset (Fin 24), _root_.Even S'.card → dSA S' ∈ chargesU z N)
    {D' : Finset (Fin 24)} (hD' : ind D' ∈ Leech.subA) : ∏ i ∈ D', uN N i = 1 := by
  have h4 : 4 ∣ D'.card := by
    have := hD'.2
    rw [card_ind] at this
    exact_mod_cast this
  have hev : _root_.Even D'.card := by
    obtain ⟨m, hm⟩ := h4; exact ⟨2 * m, by omega⟩
  have hbb : bAD hD' + bAD hD' = dSA D' := by
    apply valA_injective
    rw [map_add, valA_bAD, valA_dSA hev, two_smul]
  have h1 : Wop (bAD hD' + bAD hD') z = xi (ind D') • z := by
    rw [Wop_add_self, LinearMap.smul_apply, Module.End.one_apply,
      eV_sq_codeword (gv_inclN_bAD hD') h4]
  have h2 : Wop (bAD hD' + bAD hD') z = xiN N (ind D') • z := by
    rw [hbb]; exact mem_chargesU (hd D' hev) (inclN_dSA hev)
  rw [h1, xiN] at h2
  have h3 := smul_left_injective ℂ hz0 h2
  simp only at h3
  rw [← chiN_ind]
  have hx := xi_ne_zero (ind D')
  exact (mul_right_eq_self₀.mp h3.symm).resolve_right hx

theorem even_of_prod_uN {N X : Finset (Fin 24)} (h : ∏ i ∈ X, uN N i = 1) : _root_.Even (X ∩ N).card := by
  rw [← chiN_ind] at h
  unfold chiN at h
  have e : ∑ i ∈ N, ind X i = ((X ∩ N).card : ℤ) := by
    simp only [ind]
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]
  rw [e, zpow_natCast] at h
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  rw [hodd.neg_one_pow] at h
  norm_num at h

theorem reduceMod_ind_support (y : Fin 24 → ZMod 2) : reduceMod 2 24 (ind (Code.support y)) = y := by
  funext i
  have h01 : ∀ v : ZMod 2, v ≠ 0 → v = 1 := by decide
  change (((ind (Code.support y) i : ℤ)) : ZMod 2) = y i
  simp only [ind, Code.mem_support]
  by_cases h : y i = 0
  · simp [h]
  · simp [h01 _ h]

theorem cast_dot_ind (X Y : Finset (Fin 24)) :
    reduceMod 2 24 (ind X) ⬝ᵥ reduceMod 2 24 (ind Y) = (((X ∩ Y).card : ℤ) : ZMod 2) := by
  have : ind X ⬝ᵥ ind Y = ((X ∩ Y).card : ℤ) := by
    rw [ind_dot]; simp only [ind]
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter]
  rw [← this, dotProduct, dotProduct]
  push_cast
  rfl

/-- **`|N| ≡ 0 mod 4`** for a character even on every codeword (`N` is a Golay codeword). -/
theorem four_dvd_card_of_orth {N : Finset (Fin 24)}
    (h : ∀ D' : Finset (Fin 24), ind D' ∈ Leech.subA → ∏ i ∈ D', uN N i = 1) : 4 ∣ N.card := by
  have hr : reduceMod 2 24 (ind N) ∈ Code.golay := by
    rw [← Code.golay_isSelfDual, Code.mem_dual]
    intro y hy
    have hD' : ind (Code.support y) ∈ Leech.subA := by
      refine ⟨Leech.mem_preG.mpr (by rw [reduceMod_ind_support]; exact hy), ?_⟩
      rw [card_ind]
      have := Code.golay_isDoublyEven y hy
      rw [Code.weight_eq_card_support] at this
      exact_mod_cast this
    have hev := even_of_prod_uN (h _ hD')
    conv_lhs => rw [← reduceMod_ind_support y]
    rw [cast_dot_ind]
    obtain ⟨m, hm⟩ := hev
    rw [hm]; push_cast
    rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]
  have h4 := Code.golay_isDoublyEven _ hr
  rw [Code.weight_eq_card_support] at h4
  have hs : Code.support (reduceMod 2 24 (ind N)) = N := by
    ext i
    rw [Code.mem_support]
    change (((ind N i : ℤ)) : ZMod 2) ≠ 0 ↔ _
    simp only [ind]
    by_cases hi : i ∈ N <;> simp [hi]
  rwa [hs] at h4

/-! ## §6  Hadamard sums of `±i` patterns -/

/-- `g(1) = 1`, `g(−1) = i`: the square root of a sign, `g(ε)² = ε`. -/
noncomputable def gI (e : ℂ) : ℂ := if e = 1 then 1 else Complex.I

@[simp] theorem gI_one : gI 1 = 1 := by simp [gI]

@[simp] theorem gI_neg_one : gI (-1) = Complex.I := by
  rw [gI, if_neg]; intro h
  have := congrArg Complex.re h; norm_num at this

theorem one_add_I_pow_eight : (1 + Complex.I) ^ 8 = 16 := by
  have h : (1 + Complex.I) ^ 2 = 2 * Complex.I := by ring_nf; rw [Complex.I_sq]; ring
  rw [show (1 + Complex.I) ^ 8 = ((1 + Complex.I) ^ 2) ^ 4 by ring, h]
  ring_nf
  rw [show Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 by ring, Complex.I_sq]; norm_num

theorem one_sub_I_pow_eight : (1 - Complex.I) ^ 8 = 16 := by
  have h : (1 - Complex.I) ^ 2 = -2 * Complex.I := by ring_nf; rw [Complex.I_sq]; ring
  rw [show (1 - Complex.I) ^ 8 = ((1 - Complex.I) ^ 2) ^ 4 by ring, h]
  ring_nf
  rw [show Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 by ring, Complex.I_sq]; norm_num

/-- **The even Hadamard sum of an `±i` pattern** on an octad: `16 ∏ g(ε_i)` when `∏ ε_i = 1`. -/
theorem had_I (D : Finset (Fin 24)) (hD8 : D.card = 8) (ε : Fin 24 → ℂ)
    (hε : ∀ i ∈ D, ε i = 1 ∨ ε i = -1) (hp : ∏ i ∈ D, ε i = 1) :
    ∑ S' ∈ D.powerset.filter (fun S' : Finset (Fin 24) => _root_.Even S'.card),
        ∏ i ∈ S', (Complex.I * ε i) = 16 * ∏ i ∈ D, gI (ε i) := by
  rw [sum_even_prod]
  have h1 : ∏ i ∈ D, (1 + Complex.I * ε i) = ∏ i ∈ D, ((1 + Complex.I) * (ε i * gI (ε i))) :=
    Finset.prod_congr rfl fun i hi => by
      rcases hε i hi with h | h <;> rw [h]
      · simp
      · simp only [gI_neg_one]; ring_nf; rw [Complex.I_sq]; ring
  have h2 : ∏ i ∈ D, (1 + -(Complex.I * ε i)) = ∏ i ∈ D, ((1 - Complex.I) * gI (ε i)) :=
    Finset.prod_congr rfl fun i hi => by
      rcases hε i hi with h | h <;> rw [h]
      · simp; ring
      · simp only [gI_neg_one]; ring_nf; rw [Complex.I_sq]; ring
  rw [h1, h2, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.prod_const, hD8, hp, one_add_I_pow_eight, one_sub_I_pow_eight]
  ring

theorem gI_neg_mul (e : ℂ) (he : e = 1 ∨ e = -1) : gI (-e) = gI e * (Complex.I * e) := by
  rcases he with h | h <;> rw [h]
  · simp
  · simp only [neg_neg, gI_one, gI_neg_one]; ring_nf; rw [Complex.I_sq]; norm_num

/-! ## §7  The base identity -/
theorem ωB_pow_five : ωB ^ 5 = -ωB := by rw [pow_succ, ωB_four]; ring
theorem ωB_pow_six : ωB ^ 6 = -Complex.I := by rw [show ωB ^ 6 = ωB ^ 4 * ωB ^ 2 by ring, ωB_four, ωB_sq]; ring
theorem ωB_pow_seven : ωB ^ 7 = -(Complex.I * ωB) := by
  rw [show ωB ^ 7 = ωB ^ 4 * ωB ^ 2 * ωB by ring, ωB_four, ωB_sq]; ring
theorem ωB_pow_three : ωB ^ 3 = Complex.I * ωB := by rw [pow_succ, ωB_sq]

theorem ωB_pow_six' : ωB ^ 6 = -ωB ^ 2 := by rw [show ωB ^ 6 = ωB ^ 4 * ωB ^ 2 by ring, ωB_four]; ring
theorem ωB_pow_seven' : ωB ^ 7 = -ωB ^ 3 := by rw [show ωB ^ 7 = ωB ^ 4 * ωB ^ 3 by ring, ωB_four]; ring
theorem ωB_pow_nine : ωB ^ 9 = ωB := by rw [show ωB ^ 9 = ωB ^ 8 * ωB by ring, ωB_eight, one_mul]
theorem ωB_pow_ten : ωB ^ 10 = ωB ^ 2 := by rw [show ωB ^ 10 = ωB ^ 8 * ωB ^ 2 by ring, ωB_eight, one_mul]

/-- Close a polynomial identity in `ω`, `i` modulo `ω² = i`, `ω⁸ = 1`. -/
macro "ωB_close" : tactic => `(tactic| first
  | rfl
  | (ring_nf; done)
  | (simp only [← ωB_sq]; ring_nf; done)
  | (simp only [← ωB_sq]; ring_nf;
      simp only [ωB_four, ωB_pow_five, ωB_pow_six', ωB_pow_seven', ωB_eight, ωB_pow_nine, ωB_pow_ten];
      ring_nf; done))

theorem prod_univ_ite (X : Finset (Fin 24)) (f : Fin 24 → ℂ) :
    ∏ i ∈ X, f i = ∏ i, if i ∈ X then f i else 1 := by
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- The sign pattern `s_i = −1` on `S`. -/
noncomputable def sg (S : Finset (Fin 24)) (i : Fin 24) : ℂ := if i ∈ S then -1 else 1

/-- The local correction factor of the base identity. -/
noncomputable def rhoF (D N : Finset (Fin 24)) (i : Fin 24) : ℂ :=
  if (0 : Fin 24) ∈ D then (if i ∈ D then 1 else ωB) * (if i ∈ N then -Complex.I else 1)
  else if i ∈ D then ωB * uN N i else 1

theorem prod_rhoF {D N : Finset (Fin 24)} (hD8 : D.card = 8) (hN4 : 4 ∣ N.card)
    (hND : ∏ i ∈ D, uN N i = 1) : ∏ i, rhoF D N i = 1 := by
  unfold rhoF
  split_ifs with h0
  · rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const,
      Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    have hc : (Finset.univ.filter fun i : Fin 24 => i ∉ D).card = 16 := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 24)))
        (fun i => i ∈ D)
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hD8, Finset.card_univ, Fintype.card_fin] at this
      omega
    rw [hc, show ωB ^ 16 = (ωB ^ 8) ^ 2 by ring, ωB_eight, one_pow, one_mul]
    obtain ⟨m, hm⟩ := hN4
    rw [hm, pow_mul, show (-Complex.I) ^ 4 = 1 by
      rw [show (-Complex.I) ^ 4 = (Complex.I ^ 2) ^ 2 by ring, Complex.I_sq]; norm_num, one_pow]
  · rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_mul_distrib, Finset.prod_const, hD8,
      ωB_eight, hND, one_mul]

set_option linter.flexible false in
/-- **The base identity**: `(∏_S i)(∏_S u) β(N') = β(N) ∏_D g(s_i u_i)`, `N'` the flipped
character, for a character `N ∌ 0` with `|N| ≡ 0 (4)` and `∏_D u = 1`. -/
theorem base_identity {D S N : Finset (Fin 24)} (hD8 : D.card = 8) (hS : S ⊆ D)
    (hN0 : (0 : Fin 24) ∉ N) (hN4 : 4 ∣ N.card) (hND : ∏ i ∈ D, uN N i = 1) :
    (∏ _i ∈ S, Complex.I) * (∏ i ∈ S, uN N i) * betaN (flipN D N)
      = betaN N * ∏ i ∈ D, gI (sg S i * uN N i) := by
  rw [prod_univ_ite S, prod_univ_ite S, prod_univ_ite D, betaN, betaN, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  have hR : ∏ i, ((if i ∈ N then ωB else 1) * (if i ∈ D then gI (sg S i * uN N i) else 1))
      = ∏ i, ((if i ∈ N then ωB else 1) * (if i ∈ D then gI (sg S i * uN N i) else 1)) * rhoF D N i := by
    rw [eq_comm, Finset.prod_mul_distrib, prod_rhoF hD8 hN4 hND, mul_one]
  rw [hR]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold rhoF
  simp only [flipN, uN, sg, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h0 : (0 : Fin 24) ∈ D <;> by_cases hiD : i ∈ D <;> by_cases hiS : i ∈ S <;>
    by_cases hiN : i ∈ N <;> by_cases hi0 : i = 0
  all_goals first
    | (exfalso; exact hiD (hS hiS))
    | (exfalso; subst hi0; exact hN0 hiN)
    | (exfalso; subst hi0; exact h0 hiD)
    | skip
  all_goals (try subst hi0)
  all_goals (try simp [h0, hiD, hiS, hiN])
  all_goals (try simp [hi0])
  all_goals ωB_close

/-! ## §8  Both sides of the octad identity on a joint eigenvector -/

theorem uN_flip {D N : Finset (Fin 24)} (hN0 : (0 : Fin 24) ∉ N) (k : Fin 24) :
    uN (flipN D N) k = (if k ∈ D then -cD D else cD D) * uN N k := by
  simp only [uN, flipN, cD, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hk0 : k = 0
  · subst hk0; by_cases h0 : (0 : Fin 24) ∈ D <;> simp [h0, hN0]
  · by_cases h0 : (0 : Fin 24) ∈ D <;> by_cases hkD : k ∈ D <;> by_cases hkN : k ∈ N <;>
      simp [h0, hkD, hkN, hk0]

theorem I_pow_eq (n : ℕ) : Complex.I ^ n = (-1 : ℂ) ^ n * (Complex.I ^ n)⁻¹ := by
  have h : Complex.I ^ n * Complex.I ^ n = (-1 : ℂ) ^ n := by rw [← mul_pow, Complex.I_mul_I]
  have hne : Complex.I ^ n ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  field_simp; rw [← h]; ring

theorem prod_sg (S X : Finset (Fin 24)) : ∏ i ∈ X, sg S i = (-1 : ℂ) ^ (S ∩ X).card := by
  unfold sg
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  congr 2
  ext i; simp [Finset.mem_inter, and_comm]

theorem prod_zT (S S' N : Finset (Fin 24)) :
    ∏ i ∈ S', (Complex.I * (sg S i * uN N i))
      = (-1 : ℂ) ^ (S ∩ S').card * ((-1 : ℂ) ^ S'.card * (Complex.I ^ S'.card)⁻¹) * ∏ i ∈ S', uN N i := by
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, prod_sg]
  have h := I_pow_eq S'.card
  linear_combination ((-1 : ℂ) ^ (S ∩ S').card * ∏ i ∈ S', uN N i) * h

section OctTT

variable {D : Finset (Fin 24)} (hDA : ind D ∈ Leech.subA) (hD8 : D.card = 8)

/-- The `S'`-independent prefactor on `T_s⁺`. -/
noncomputable def C1 (S : Finset (Fin 24)) : ℂ := 2 * cD D * rH ^ D.card * XS hDA S * (2 : ℂ) ^ (-(4 : ℤ))

include hD8 in
/-- **Each term of the target sum on a joint eigenvector**. -/
theorem termTT {z : TLeechT} {N : Finset (Fin 24)}
    (hd : ∀ S' : Finset (Fin 24), _root_.Even S'.card → dSA S' ∈ chargesU z N)
    {S S' : Finset (Fin 24)} (h : _root_.Even S.card) (hS : S ⊆ D) (he' : _root_.Even S'.card)
    (hS' : S' ⊆ D) :
    (KS hDA S S' * (2 : ℂ) ^ (-(4 : ℤ))) • eL (inclΛ (aSA hDA S')) z
      = (C1 hDA S * ∏ i ∈ S', (Complex.I * (sg S i * uN N i))) • Wop (bAD hDA) z := by
  rw [eL_eq_Wop, Wop_aSA_eig hDA hd he', smul_smul, smul_smul]
  congr 1
  rw [KS, coef_even hDA hD8 h hS hS' he', xiN, chiN_neg_ind, prod_zT, C1]
  have hn := nuC_eps_xi hDA hS'
  have htc : tc (aSA hDA S') * (tc (aSA hDA S'))⁻¹ = 1 := mul_inv_cancel₀ (tc_ne_zero _)
  set K := 2 * cD D * rH ^ D.card * XS hDA S * (-1 : ℂ) ^ (S ∩ S').card * (2 : ℂ) ^ (-(4 : ℤ)) *
    ∏ i ∈ S', uN N i
  linear_combination K * (nuC (inclN (bAD hDA)) S' * εN (inclN (bAD hDA)) (dl S') * xi (-ind S')) * htc
    + K * hn

include hD8 in
/-- **The target, summed, on a joint eigenvector.** -/
theorem rhsTT {z : TLeechT} {N : Finset (Fin 24)}
    (hd : ∀ S' : Finset (Fin 24), _root_.Even S'.card → dSA S' ∈ chargesU z N)
    {S : Finset (Fin 24)} (h : _root_.Even S.card) (hS : S ⊆ D) (b : Fin 24) :
    actT (sig (lV (inclΛ (aSA hDA S)) (inclΛ_mem _))) 1 (hP (cw b) z)
      = (C1 hDA S * ∑ S' ∈ D.powerset.filter (fun S' : Finset (Fin 24) => _root_.Even S'.card),
            ∏ i ∈ S', (Complex.I * (sg S i * uN N i))) • hP (cw b) (Wop (bAD hDA) z)
        - ∑ l, (if b ∈ D ∧ l ∈ D then C1 hDA S * ∑ S' ∈ D.powerset.filter
            (fun S' : Finset (Fin 24) => _root_.Even S'.card),
              ∏ i ∈ S', (Complex.I * (sg S i * uN N i) * etaS b l i)
            else 0) • hP (cw l) (Wop (bAD hDA) z) := by
  rw [actT_sig_lV_aSA hDA hD8 h hS]
  have hterm : ∀ S' ∈ D.powerset.filter (fun S' : Finset (Fin 24) => _root_.Even S'.card),
      (KS hDA S S' * (2 : ℂ) ^ (-(4 : ℤ))) • hP (latL (inclΛ (aSA hDA S')) (cw b))
          (eL (inclΛ (aSA hDA S')) z)
        = (C1 hDA S * ∏ i ∈ S', (Complex.I * (sg S i * uN N i))) • hP (cw b) (Wop (bAD hDA) z)
          - ∑ l, ((if b ∈ D ∧ l ∈ D then C1 hDA S * ∏ i ∈ S', (Complex.I * (sg S i * uN N i) * etaS b l i)
              else 0)) • hP (cw l) (Wop (bAD hDA) z) := by
    intro S' hS'
    obtain ⟨hS'p, he'⟩ := Finset.mem_filter.mp hS'
    rw [← hP_smul_right, termTT hDA hD8 hd h hS he' (Finset.mem_powerset.mp hS'p), latL_cw,
      hP_sub_left, hP_smul_right, hP_sum_left]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [lv_aSA_mul hDA he' (Finset.mem_powerset.mp hS'p), hP_smul_left, hP_smul_right, smul_smul]
    congr 1
    split_ifs
    · simp only [Finset.prod_mul_distrib]; ring
    · ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_smul, Finset.mul_sum,
    Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  split_ifs
  · rw [Finset.mul_sum]
  · simp

include hD8 in
/-- **The source, on a joint eigenvector.** -/
theorem lhsTT {s : ZMod 2} {z : TLeechT} (hz : z ∈ leechFrameT s) {N : Finset (Fin 24)}
    (hE : IsEigN N z)
    (hd : ∀ S' : Finset (Fin 24), _root_.Even S'.card → dSA S' ∈ chargesU z N)
    {S : Finset (Fin 24)} (h : _root_.Even S.card) (hS : S ⊆ D) (b : Fin 24) :
    phiTT (psiOf (Bop s)) (actT (lV (inclΛ (aSA hDA S)) (inclΛ_mem _)) 1 (hP (cw b) z))
      = ((2 : ℂ) ^ (-(3 : ℤ)) * (XS hDA S * ((∏ _i ∈ S, Complex.I) * ∏ i ∈ S, uN N i))) •
          ((uN (flipN D N) b * betaN (flipN D N)) • hP (cw b) (Wop (bAD hDA) z)
            - ∑ l, ((if b ∈ D ∧ l ∈ D then ∏ i ∈ S, etaS b l i else 0) *
                (uN (flipN D N) l * betaN (flipN D N))) • hP (cw l) (Wop (bAD hDA) z)) := by
  have hy : eL (inclΛ (aSA hDA S)) z
      = (XS hDA S * ((∏ _i ∈ S, Complex.I) * ∏ i ∈ S, uN N i)) • Wop (bAD hDA) z := by
    rw [eL_eq_Wop, Wop_aSA_eig hDA hd h, smul_smul, xiN, chiN_neg_ind]
    congr 1
    have := tc_eps_xi_eq hDA hS
    rw [Finset.prod_const, I_pow_eq S.card]
    linear_combination (∏ i ∈ S, uN N i) * this
  have hymem : eL (inclΛ (aSA hDA S)) z ∈ leechFrameT s := by
    have := eT_mem_leechFrameT (inclΛ (aSA hDA S)) hz
    rwa [(mem_lambda0 _).mp (inclΛ_mem _), add_zero] at this
  have hyE := eig_flip hDA h hE
  have hN0' : (0 : Fin 24) ∉ flipN D N := by simp [flipN]
  rw [actT_lV_hP (inclΛ_mem _) (form_aSA hDA S h hS hD8), map_smul, latL_cw, hP_sub_left,
    hP_sum_left, map_sub, map_sum, phiTT_hP, psiOf_eigN hymem hN0' hyE b]
  have hl : ∀ l, phiTT (psiOf (Bop s)) (hP ((((2 * lv (inclΛ (aSA hDA S)) b * lv (inclΛ (aSA hDA S)) l : ℤ) : ℂ) / 8) • cw l)
      (eL (inclΛ (aSA hDA S)) z)) = ((if b ∈ D ∧ l ∈ D then ∏ i ∈ S, etaS b l i else 0) *
                (uN (flipN D N) l * betaN (flipN D N))) • hP (cw l) (eL (inclΛ (aSA hDA S)) z) := by
    intro l
    rw [hP_smul_left, map_smul, phiTT_hP, psiOf_eigN hymem hN0' hyE l, hP_smul_right, smul_smul,
      lv_aSA_mul hDA h hS]
  simp only [hl]
  rw [hy]
  simp only [hP_smul_right, smul_smul, Finset.smul_sum, smul_sub]
  congr 1
  · congr 1; ring
  · refine Finset.sum_congr rfl fun l _ => ?_
    congr 1; ring

end OctTT

/-! ## §9  The octad identity on a joint eigenvector -/

theorem lincomb_eq {M : Type*} [AddCommGroup M] [Module ℂ M] (X : Fin 24 → M) (b : Fin 24)
    (κL κR A B : ℂ) (a r : Fin 24 → ℂ) (h : ∀ l, l ≠ b → κL * a l = κR * r l)
    (hb : κL * (A - a b) = κR * (B - r b)) :
    κL • (A • X b - ∑ l, a l • X l) = κR • (B • X b - ∑ l, r l • X l) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), ← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
  simp only [smul_sub, smul_add, Finset.smul_sum, smul_smul]
  rw [Finset.sum_congr rfl (fun l hl => by rw [h l (Finset.ne_of_mem_erase hl)])]
  have e : κL * A = κR * B - κR * r b + κL * a b := by linear_combination hb
  rw [e, add_smul, sub_smul]
  abel

theorem hP_zero_right' (v : Fin (rank leech) → ℂ) : hP v 0 = 0 := by
  simpa using hP_smul_right v 0 0

theorem etaS_self' (b i : Fin 24) : etaS b b i = 1 := by
  unfold etaS; split_ifs <;> norm_num

theorem prod_etaS_S (S : Finset (Fin 24)) (b l : Fin 24) :
    ∏ i ∈ S, etaS b l i = sg S b * sg S l := by
  unfold etaS
  rw [Finset.prod_mul_distrib, prod_single_sign, prod_single_sign]; rfl

theorem gI_eta {ε : Fin 24 → ℂ} (hε : ∀ i, ε i = 1 ∨ ε i = -1) {D : Finset (Fin 24)} {b l : Fin 24}
    (hb : b ∈ D) (hl : l ∈ D) (hbl : b ≠ l) :
    ∏ i ∈ D, gI (ε i * etaS b l i)
      = (∏ i ∈ D, gI (ε i)) * (Complex.I * ε b) * (Complex.I * ε l) := by
  have hloc : ∀ i, gI (ε i * etaS b l i)
      = gI (ε i) * (if i = b then Complex.I * ε i else 1) * (if i = l then Complex.I * ε i else 1) := by
    intro i
    unfold etaS
    by_cases hib : i = b
    · subst hib
      rw [if_pos rfl, if_neg hbl, if_pos rfl, if_neg hbl, mul_one, mul_one, mul_neg_one,
        gI_neg_mul _ (hε i)]
    · by_cases hil : i = l
      · subst hil
        rw [if_neg hib, if_pos rfl, if_neg hib, if_pos rfl, one_mul, mul_one, mul_neg_one,
          gI_neg_mul _ (hε i)]
      · rw [if_neg hib, if_neg hil, if_neg hib, if_neg hil]; simp
  rw [Finset.prod_congr rfl fun i _ => hloc i, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_ite_eq', Finset.prod_ite_eq', if_pos hb, if_pos hl]

theorem prod_etaS_D {D : Finset (Fin 24)} {b l : Fin 24} (hb : b ∈ D) (hl : l ∈ D) :
    ∏ i ∈ D, etaS b l i = 1 := by
  unfold etaS
  rw [Finset.prod_mul_distrib, prod_single_sign, prod_single_sign, if_pos hb, if_pos hl]; norm_num

theorem uN_sq (N : Finset (Fin 24)) (k : Fin 24) : uN N k * uN N k = 1 := by
  unfold uN; split_ifs <;> norm_num

section OctTT2

variable {D : Finset (Fin 24)} (hDA : ind D ∈ Leech.subA) (hD8 : D.card = 8)

include hD8 in
/-- **The octad identity on a joint `Z`-eigenvector of `T_s`.** -/
theorem octadTT_eig {s : ZMod 2} {t : TLeechT} (hts : t ∈ leechFrameT s) (ht0 : t ≠ 0)
    (ht : IsSeed t) {S : Finset (Fin 24)} (h : _root_.Even S.card) (hS : S ⊆ D) {z : TLeechT}
    (hz : z ∈ leechFrameT s) {N : Finset (Fin 24)} (hN0 : (0 : Fin 24) ∉ N) (hE : IsEigN N z)
    (b : Fin 24) :
    phiTT (psiOf (Bop s)) (actT (lV (inclΛ (aSA hDA S)) (inclΛ_mem _)) 1 (hP (cw b) z))
      = actT (sig (lV (inclΛ (aSA hDA S)) (inclΛ_mem _))) 1 (phiTT (psiOf (Bop s)) (hP (cw b) z)) := by
  by_cases hz0 : z = 0
  · subst hz0; simp [hP_zero_right']
  have hd := fun (S' : Finset (Fin 24)) (he : _root_.Even S'.card) =>
    dSA_mem_chargesU hts ht0 ht hz hN0 hE he
  have hND := golay_constraint hz0 hd hDA
  have hN4 := four_dvd_card_of_orth (fun D' hD' => golay_constraint hz0 hd hD')
  have hBI := base_identity hD8 hS hN0 hN4 hND
  rw [lhsTT hDA hD8 hz hE hd h hS b, phiTT_hP, psiOf_eigN hz hN0 hE b, hP_smul_right, map_smul,
    rhsTT hDA hD8 hd h hS b]
  have hpm : ∀ i, sg S i * uN N i = 1 ∨ sg S i * uN N i = -1 := by
    intro i; unfold sg uN; split_ifs <;> simp
  have hprodD : ∏ i ∈ D, (sg S i * uN N i) = 1 := by
    rw [Finset.prod_mul_distrib, hND, mul_one, prod_sg, Finset.inter_eq_left.mpr hS, h.neg_one_pow]
  have hH := had_I D hD8 _ (fun i _ => hpm i) hprodD
  have hC1 : C1 hDA S = cD D * XS hDA S / 128 := by
    rw [C1, hD8, rH_pow_eight]; norm_num; ring
  have h3 : (2 : ℂ) ^ (-(3 : ℤ)) = 1 / 8 := by norm_num
  rw [hH]
  apply lincomb_eq
  · intro l hlb
    split_ifs with hbl
    · obtain ⟨hb, hl⟩ := hbl
      have hpm' : ∀ i, sg S i * uN N i * etaS b l i = 1 ∨ sg S i * uN N i * etaS b l i = -1 := by
        intro i; unfold etaS
        rcases hpm i with h' | h' <;> rw [h'] <;> split_ifs <;> simp
      have hprod' : ∏ i ∈ D, (sg S i * uN N i * etaS b l i) = 1 := by
        rw [Finset.prod_mul_distrib, hprodD, prod_etaS_D hb hl, mul_one]
      have hH' := had_I D hD8 _ (fun i _ => hpm' i) hprod'
      rw [show (∑ S' ∈ D.powerset.filter (fun S' : Finset (Fin 24) => _root_.Even S'.card),
          ∏ i ∈ S', (Complex.I * (sg S i * uN N i) * etaS b l i))
          = 16 * ∏ i ∈ D, gI (sg S i * uN N i * etaS b l i) by rw [← hH']; simp only [mul_assoc],
        gI_eta (ε := fun i => sg S i * uN N i) hpm hb hl (Ne.symm hlb), prod_etaS_S, uN_flip hN0,
        if_pos hl, hC1, h3]
      have hu2 := uN_sq N b
      have hI := Complex.I_mul_I
      linear_combination (-(1 / 8) * XS hDA S * cD D * sg S b * sg S l * uN N l) * hBI
        + (-(1 / 8) * XS hDA S * cD D * sg S b * sg S l * uN N l * betaN N *
            (∏ i ∈ D, gI (sg S i * uN N i)) * uN N b * uN N b) * hI
        - (-(1 / 8) * XS hDA S * cD D * sg S b * sg S l * uN N l * betaN N *
            (∏ i ∈ D, gI (sg S i * uN N i))) * hu2
    · simp
  · by_cases hb : b ∈ D
    · simp only [hb, and_self, if_true, etaS_self', mul_one, Finset.prod_const_one, one_mul]
      rw [hH]; ring
    · simp only [hb, and_self, if_false, zero_mul, sub_zero]
      rw [uN_flip hN0, if_neg hb, hC1, h3]
      linear_combination ((1 / 8) * XS hDA S * cD D * uN N b) * hBI

include hD8 in
/-- **Every octad letter intertwines on `T_s⁺`** for the seeded block map `φ_B`. -/
theorem phiTT_ZMT_aSA {s : ZMod 2} {t : TLeechT} (hts : t ∈ leechFrameT s) (ht0 : t ≠ 0)
    (ht : IsSeed t) {S : Finset (Fin 24)} (h : _root_.Even S.card) (hS : S ⊆ D) :
    ZMT (phiTT (psiOf (Bop s))) (OmegaT s) (lV (inclΛ (aSA hDA S)) (inclΛ_mem _)) := by
  refine ZMT_of_basis _ s _ fun m t' ht' => ?_
  refine eig_induct (s := s) (fun z => phiTT (psiOf (Bop s))
      (actT (lV (inclΛ (aSA hDA S)) (inclΛ_mem _)) 1 (hP (cw m) z))
      = actT (sig (lV (inclΛ (aSA hDA S)) (inclΛ_mem _))) 1 (phiTT (psiOf (Bop s)) (hP (cw m) z)))
    ?_ ?_ t' ht'
  · intro x y hx hy
    simp only at hx hy ⊢
    rw [hP_add_right, map_add, map_add, hx, hy, map_add, map_add]
  · intro z hz N hN0 hE
    exact octadTT_eig hDA hD8 hts ht0 ht h hS hz hN0 hE m

end OctTT2

/-! ## §10  (R-top) on `T_s⁺`, and `σ : T_s⁺ → T_s⁺`, unconditionally -/

/-- Every weight-2 lattice letter intertwines for `φ_B`. -/
theorem hlatTT {s : ZMod 2} {t : TLeechT} (hts : t ∈ leechFrameT s) (ht0 : t ≠ 0) (ht : IsSeed t) :
    ∀ γ ∈ halfFourChi 0, ZMT (phiTT (psiOf (Bop s))) (OmegaT s) (lV' γ) := by
  intro γ hγ
  rcases classify_S0 hγ with ⟨j, k, hjk, hroot⟩ | ⟨D, hDA, hD8, S, hS, hSD, rfl⟩
  · rcases hroot with rfl | rfl | rfl | rfl
    · rw [lV'_eq (gP_mem j k)]; exact phiTT_ZMT_gP hts ht0 ht hjk
    · rw [lV'_neg, lV'_eq (gP_mem j k)]; exact phiTT_ZMT_gP hts ht0 ht hjk
    · rw [lV'_eq (gM_mem j k)]; exact phiTT_ZMT_gM hts ht0 ht hjk
    · rw [lV'_neg, lV'_eq (gM_mem j k)]; exact phiTT_ZMT_gM hts ht0 ht hjk
  · rw [lV'_eq (inclΛ_mem _)]
    exact phiTT_ZMT_aSA hDA hD8 hts ht0 ht hS hSD

/-- **(R-top) on `T_s⁺`, unconditional**: for a seed `t ∈ T_s`, `φ_B` satisfies `TopSigmaTT s s`. -/
theorem topSigmaTT_of_seed' {s : ZMod 2} {t : TLeechT} (hts : t ∈ leechFrameT s) (ht0 : t ≠ 0)
    (ht : IsSeed t) : TopSigmaTT s s (phiTT (psiOf (Bop s))) :=
  topSigmaTT_of_seedB hts ht0 ht (hlatTT hts ht0 ht)

/-- **(R-top) on `T_s⁺`, unconditional.** -/
theorem topSigmaTT : ∃ s φ, TopSigmaTT s s φ := by
  obtain ⟨s, t, hts, ht0, ht⟩ := seed_in_frame seedExists
  exact ⟨s, _, topSigmaTT_of_seed' hts ht0 ht⟩

/-- **The triality on the twisted sector, `σ : T_s⁺ → T_s⁺`**, unconditional: a
`v0Sigma`-twisted intertwiner of `V₀⁺`-modules on `T_s⁺`, agreeing with `φ_B` on the top and hitting
a nonzero cyclic vector `x0T t₀`, `t₀ ∈ T_s`. -/
theorem sigmaTT_exists :
    ∃ (s : ZMod 2) (Φ : TP →ₗ[ℂ] TP), IsSigmaTT s Φ ∧
      ∃ t₀ : TLeechT, t₀ ∈ leechFrameT s ∧ t₀ ≠ 0 ∧ ∃ x ∈ OmegaT s, Φ x = x0T t₀ := by
  obtain ⟨s, t, hts, ht0, ht⟩ := seed_in_frame seedExists
  obtain ⟨Φ, hΦ, -, t₀, h1, h2, x, hx, hΦx⟩ :=
    sigmaTT_exists_of_top (topSigmaTT_of_seed' hts ht0 ht) hts ht0
  exact ⟨s, Φ, hΦ, t₀, h1, h2, x, hx, hΦx⟩

/-- **Both twisted-sector trialities from one seed**: for the same `s`, `σ : V₃⁺ → T_{s+1}⁺`
(`TopSigmaV3 (s+1)`) and `σ : T_s⁺ → T_s⁺` (`TopSigmaTT s s`). -/
theorem topSigma_both : ∃ s : ZMod 2, (∃ φ, TopSigmaV3 (s + 1) φ) ∧ ∃ φ, TopSigmaTT s s φ := by
  obtain ⟨s, t, hts, ht0, ht⟩ := seed_in_frame seedExists
  exact ⟨s, ⟨_, topSigmaV3_of_octad hts ht0 ht (octadResidualV3 s t hts ht0 ht)⟩,
    ⟨_, topSigmaTT_of_seed' hts ht0 ht⟩⟩

end VOA.Moonshine.SigmaTop
