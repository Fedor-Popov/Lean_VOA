/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.DongMasonCOne
import VOA.Classification.COne.Conditional
import VOA.Classification.COne.LatticeReconstruction

/-!
# DM-1 from the modular data

`heisCommutantTrivial_of_modData : IModData → HeisCommutantTrivial`: the analytic Dong–Mason
step at `c = 1` follows from the modular-data package `IModData`, which the headline already
assumes. With D2 (`heisLatticeReconstruction`, unconditional) this gives
`iDongMason_of_modData : IModData → IDongMason`, so `IDongMason` is not an independent
input.

## The argument (Dong–Mason's effective central charge, specialised to `c = 1`)

Suppose the commutant of the unit Heisenberg vector `h` is not `ℂ𝟙`. Then `x = ω - ω_h ≠ 0`
(`commutant_le_of_conformal_eq`), `x ∈ W₂ ∩ Com⟨h⟩`.

* §1 (algebra) `Lneg1_eq_zero`: `L₋₁` is injective on `W_k`, `k ≥ 1` (the `𝔰𝔩₂` relation
  `[L₁, L₋₁] = 2L₀`); `Tpow_mem_commutant`: `Tʲx = j!·x₍₋ⱼ₋₁₎𝟙 ∈ Com⟨h⟩`. So the Heisenberg vacuum
  space has a nonzero vector in every degree `≥ 2`.
* §2–3 (Fock count) `lower_real`: by injectivity of the Fock map (`HeisSvN.fockMap_injective`)
  the vectors `a(-1)^{e₀} ⋯ a(-K)^{e_{K-1}} Tʲx` are linearly independent, so
  `Σ dim Wₙ qⁿ ≥ ∏_{k ≤ K} (1 - qᵏ)⁻¹ · q²/(1 - q)` for every `K` and `0 ≤ q < 1`.
* §4 (eta) `norm_eta_imag_le`: `‖η(iy)‖ ≤ y^{-1/2} e^{-2π/(24y)}` (Mathlib's
  `η(-1/τ) = √(-iτ) η(τ)`), and the partial products `∏_{k≤K}(1-qᵏ)` tend to `|q^{-1/24}η(iy)|`.
* §5 With `q = e^{-2πy}`: the lower bound gives `q²/(1-q) ≤ ch_W(iy) · ‖η(iy)‖`, while
  `ch_W(iy) = S₀₀ Σ_b d_b ch_b(i/y) ≤ C e^{2π/(24y)}` (`S_transform`, `S_vac_left`,
  and the leading asymptotics `tendsto_chR`, which uses pseudo-unitarity `h_b > 0`). Hence
  `q²/(1-q) ≤ C y^{-1/2}`, impossible as `y → 0` since `q²/(1-q) ~ 1/(2πy)` (`final_contra`).

No `sorry`, no new axioms; the only hypothesis is `IModData`.
-/

set_option linter.style.longLine false

open Complex Finset Module Filter Topology

noncomputable section

namespace VOA.Classification.COne

namespace DMCOne

open VOA VOA.VertexOperatorAlgebra

universe u

variable {𝒲 : Type u} [AddCommGroup 𝒲] [Module ℂ 𝒲] {W : VertexOperatorAlgebra 𝒲}

/-! ## §1 Algebra: a tower of nonzero vectors in the commutant -/

/-- `Lₙ` lowers the degree by `n`. -/
theorem L_mem_grading' {k : ℤ} {y : 𝒲} (hy : y ∈ W.grading k) (n : ℤ) :
    W.L n y ∈ W.grading (k - n) := by
  have := W.smul_mem_grading W.conformal_mem hy (n + 1)
  rw [W.L_def]
  convert this using 2
  ring

/-- `L₁ L₋₁ = L₋₁ L₁ + 2 L₀`. -/
theorem L_one_neg_one_apply (z : 𝒲) :
    W.L 1 (W.L (-1) z) = W.L (-1) (W.L 1 z) + (2 : ℂ) • W.L 0 z := by
  have h := LinearMap.congr_fun W.L_one_L_neg_one z
  rw [Ring.lie_def] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
  rw [← h]; abel

/-- **`L₋₁` is injective in positive degree** (the `𝔰𝔩₂` argument: if `L₋₁ y = 0` with
`y ∈ W_k`, then `L₋₁ L₁^{m+1} y = -(m+1)(2k-m) L₁^m y`, and `L₁^{k+1} y = 0`). -/
theorem Lneg1_eq_zero {k : ℕ} (hk : 1 ≤ k) {y : 𝒲} (hy : y ∈ W.grading k)
    (h0 : W.L (-1) y = 0) : y = 0 := by
  set z : ℕ → 𝒲 := fun m => (W.L 1 ^ m) y with hz
  have hz_succ : ∀ m, z (m + 1) = W.L 1 (z m) := fun m => by
    simp only [hz, pow_succ', Module.End.mul_apply]
  have hz_mem : ∀ m : ℕ, z m ∈ W.grading ((k : ℤ) - m) := by
    intro m
    induction m with
    | zero => simpa [hz] using hy
    | succ m ih =>
      rw [hz_succ]
      convert L_mem_grading' ih 1 using 2
      push_cast; ring
  have hrec : ∀ m : ℕ, W.L (-1) (z (m + 1)) = (-(((m : ℂ) + 1) * (2 * k - m))) • z m := by
    intro m
    induction m with
    | zero =>
      rw [hz_succ]
      have h1 := L_one_neg_one_apply (W := W) y
      rw [h0, map_zero, W.L_zero_grading y hy] at h1
      have h2 : z 0 = y := by simp [hz]
      rw [h2]
      have h3 : W.L (-1) (W.L 1 y) = -((2 : ℂ) • ((k : ℤ) : ℂ) • y) := by
        rw [eq_neg_iff_add_eq_zero, ← h1]
      rw [h3, smul_smul]
      push_cast
      rw [← neg_smul]
      congr 1; ring
    | succ m ih =>
      rw [hz_succ (m + 1)]
      have h1 := L_one_neg_one_apply (W := W) (z (m + 1))
      rw [ih, W.L_zero_grading _ (hz_mem (m + 1)), map_smul, ← hz_succ] at h1
      have : W.L (-1) (W.L 1 (z (m + 1))) =
          (-(((m : ℂ) + 1) * (2 * k - m))) • z (m + 1) -
            (2 : ℂ) • (((k : ℤ) - ((m + 1 : ℕ) : ℤ) : ℤ) : ℂ) • z (m + 1) := by
        rw [h1]; abel
      rw [this, smul_smul, ← sub_smul]
      congr 1
      push_cast; ring
  have hk1 : z (k + 1) = 0 := by
    have := hz_mem (k + 1)
    rw [W.positivity _ (by push_cast; omega), Submodule.mem_bot] at this
    exact this
  have hdown : ∀ i : ℕ, i ≤ k + 1 → z (k + 1 - i) = 0 := by
    intro i
    induction i with
    | zero => intro _; simpa using hk1
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hm : k + 1 - i = (k - i) + 1 := by omega
      rw [hm] at hprev
      have h := hrec (k - i)
      rw [hprev, map_zero] at h
      have hc : (-(((((k - i : ℕ)) : ℂ) + 1) * (2 * k - ((k - i : ℕ) : ℂ)))) ≠ 0 := by
        have h1 : (((k - i : ℕ)) : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k - i)
        have h2 : (2 * (k : ℂ) - ((k - i : ℕ) : ℂ)) ≠ 0 := by
          have : (2 * k - (k - i) : ℕ) ≠ 0 := by omega
          have h3 : ((2 * k - (k - i) : ℕ) : ℂ) = 2 * (k : ℂ) - ((k - i : ℕ) : ℂ) := by
            rw [Nat.cast_sub (by omega)]; push_cast; ring
          rw [← h3]; exact_mod_cast this
        exact neg_ne_zero.mpr (mul_ne_zero h1 h2)
      have := (smul_eq_zero.mp h.symm).resolve_left hc
      rw [show k + 1 - (i + 1) = k - i by omega]
      exact this
  simpa [hz] using hdown (k + 1) le_rfl

/-- The commutant is closed under `x ↦ x₍ₚ₎𝟙`. -/
theorem smul_vacuum_mem_commutant {h x : 𝒲} (hx : x ∈ commutant W h) (p : ℤ) :
    W.smul x p W.vacuum ∈ commutant W h := by
  rw [mem_commutant] at hx ⊢
  intro n hn
  have hJ := W.jacobi h x W.vacuum 0 n p
  rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])] at hJ
  rw [finsum_eq_zero_of_forall_eq_zero (fun i => by
    rcases lt_or_ge i 0 with hneg | hnn
    · rw [cbz_apply_neg _ hneg, zero_smul]
    · rw [zero_add, hx i hnn, W.smul_zero_left, smul_zero])] at hJ
  simp only [zero_add, sub_zero, add_zero, cbz_zero, negOnePow, mul_one] at hJ
  rw [W.smul_vacuum_nonneg h hn, W.smul_zero_right] at hJ
  simpa using hJ


/-- The translates `Tʲx` of a commutant vector stay in the commutant
(`Tʲx = j! x₍₋ⱼ₋₁₎𝟙`). -/
theorem Tpow_mem_commutant {h x : 𝒲} (hx : x ∈ commutant W h) (j : ℕ) :
    (W.toPreVertexAlgebra.T ^ j) x ∈ commutant W h := by
  have e := smul_Tpow_neg_one W x W.vacuum j
  rw [W.smul_vacuum_neg_one] at e
  rw [e]
  exact zsmul_mem (smul_vacuum_mem_commutant hx _) _

theorem Tpow_mem_grading {k : ℤ} {x : 𝒲} (hx : x ∈ W.grading k) (j : ℕ) :
    (W.toPreVertexAlgebra.T ^ j) x ∈ W.grading (k + j) := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, show W.toPreVertexAlgebra.T ((W.toPreVertexAlgebra.T ^ j) x)
      = W.L (-1) ((W.toPreVertexAlgebra.T ^ j) x) from by rw [W.T_eq_Lneg1]]
    convert L_mem_grading' ih (-1) using 2
    push_cast; ring

theorem Tpow_ne_zero {k : ℕ} (hk : 1 ≤ k) {x : 𝒲} (hx : x ∈ W.grading k) (hx0 : x ≠ 0)
    (j : ℕ) : (W.toPreVertexAlgebra.T ^ j) x ≠ 0 := by
  induction j with
  | zero => simpa using hx0
  | succ j ih =>
    intro h0
    rw [pow_succ', Module.End.mul_apply, show W.toPreVertexAlgebra.T ((W.toPreVertexAlgebra.T ^ j) x)
      = W.L (-1) ((W.toPreVertexAlgebra.T ^ j) x) from by rw [W.T_eq_Lneg1]] at h0
    have hmem : (W.toPreVertexAlgebra.T ^ j) x ∈ W.grading ((k + j : ℕ) : ℤ) := by
      have := Tpow_mem_grading hx j; push_cast; exact this
    exact ih (Lneg1_eq_zero (by omega) hmem h0)

/-! ## §2 Fock monomials and their degrees -/

/-- The degree of the Fock monomial `∏ a(-(i+1))^{sᵢ}`. -/
def fdeg (s : ℕ →₀ ℕ) : ℕ := s.sum fun i n => (i + 1) * n

theorem fdeg_add (s t : ℕ →₀ ℕ) : fdeg (s + t) = fdeg s + fdeg t := by
  unfold fdeg
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

theorem fdeg_single (i n : ℕ) : fdeg (Finsupp.single i n) = (i + 1) * n := by
  unfold fdeg
  exact Finsupp.sum_single_index (by simp)

theorem evalOp_monomial_mem {h : 𝒲} (hh : IsHeisVector W h) (s : ℕ →₀ ℕ) {k : ℤ} {x : 𝒲}
    (hx : x ∈ W.grading k) :
    (heisRep hh).evalOp (MvPolynomial.monomial s 1) x ∈ W.grading (k + fdeg s) := by
  induction s using Finsupp.induction_linear generalizing k x with
  | zero =>
    rw [← MvPolynomial.C_apply, (heisRep hh).evalOp_C, one_smul]
    simpa [fdeg] using hx
  | add f g hf hg =>
    rw [show (MvPolynomial.monomial (f + g) (1 : ℂ)) =
        MvPolynomial.monomial f 1 * MvPolynomial.monomial g 1 by
      rw [MvPolynomial.monomial_mul, one_mul], map_mul, Module.End.mul_apply]
    have := hf (hg hx)
    rw [fdeg_add]
    convert this using 2
    push_cast; ring
  | single i n =>
    rw [← MvPolynomial.X_pow_eq_monomial, map_pow, fdeg_single, (heisRep hh).evalOp_X]
    induction n generalizing k x with
    | zero => simpa using hx
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      have h2 := heis_mode_mem hh (ih hx) (-((i : ℤ) + 1))
      simp only [HeisSvN.HeisRep.cr, heisRep_a] at h2 ⊢
      convert h2 using 2
      push_cast; ring

/-! ## §3 Counting: `dim Wₙ` dominates the truncated Fock count -/

/-- `Fin K → ℕ` as finitely supported exponent vectors on `ℕ`. -/
def toFs {K : ℕ} (e : Fin K → ℕ) : ℕ →₀ ℕ :=
  Finsupp.embDomain Fin.valEmbedding (Finsupp.equivFunOnFinite.symm e)

theorem toFs_injective (K : ℕ) : Function.Injective (toFs (K := K)) :=
  (Finsupp.embDomain_injective _).comp Finsupp.equivFunOnFinite.symm.injective

theorem fdeg_toFs {K : ℕ} (e : Fin K → ℕ) :
    fdeg (toFs e) = ∑ i : Fin K, ((i : ℕ) + 1) * e i := by
  unfold fdeg toFs
  rw [Finsupp.sum_embDomain, Finsupp.sum_fintype _ _ (fun i => by simp)]
  simp

/-- The degree of the vector `a(-1)^{e₀} ⋯ a(-K)^{e_{K-1}} Tʲx` for `x ∈ W₂`. -/
def fdegP (K : ℕ) (p : (Fin K → ℕ) × ℕ) : ℕ := (∑ i : Fin K, ((i : ℕ) + 1) * p.1 i) + 2 + p.2

section Count

variable {h x : 𝒲} (hh : IsHeisVector W h) (hxC : x ∈ commutant W h)

/-- `Tʲx` as a Heisenberg vacuum vector. -/
def vacVec (j : ℕ) : (heisRep hh).vac :=
  ⟨(W.toPreVertexAlgebra.T ^ j) x, by
    rw [HeisSvN.HeisRep.mem_vac]
    intro n hn
    exact (mem_commutant.mp (Tpow_mem_commutant hxC j)) n hn.le⟩

variable (hx2 : x ∈ W.grading 2) (hx0 : x ≠ 0)
include hx2 hx0

theorem vacVec_linearIndependent : LinearIndependent ℂ (vacVec hh hxC) := by
  apply LinearIndependent.of_comp (heisRep hh).vac.subtype
  have hp : iSupIndep (fun j : ℕ => W.grading ((2 : ℤ) + j)) :=
    iSupIndep.comp (t := W.grading) W.isInternal.submodule_iSupIndep
      (f := fun j : ℕ => (2 : ℤ) + j) (fun a b hab => by simpa using hab)
  exact hp.linearIndependent _ (fun j => Tpow_mem_grading hx2 j)
    (fun j => Tpow_ne_zero (k := 2) (by norm_num) (by exact_mod_cast hx2) hx0 j)

omit hx0 in
theorem fockVec_mem {K : ℕ} (p : (Fin K → ℕ) × ℕ) :
    (heisRep hh).fockMap (Finsupp.single (toFs p.1) (vacVec hh hxC p.2)) ∈
      W.grading (fdegP K p : ℕ) := by
  rw [HeisSvN.HeisRep.fockMap_single]
  have := evalOp_monomial_mem hh (toFs p.1) (Tpow_mem_grading hx2 p.2)
  rw [fdeg_toFs] at this
  convert this using 2
  unfold fdegP; push_cast; ring

theorem fockVec_linearIndependent (K : ℕ) :
    LinearIndependent ℂ (fun p : (Fin K → ℕ) × ℕ =>
      (heisRep hh).fockMap (Finsupp.single (toFs p.1) (vacVec hh hxC p.2))) := by
  have hG := Finsupp.linearIndependent_single (R := ℂ) (φ := fun _ : ℕ →₀ ℕ => ℕ)
    (fun _ => vacVec hh hxC) (fun _ => vacVec_linearIndependent hh hxC hx2 hx0)
  have hι : Function.Injective (fun p : (Fin K → ℕ) × ℕ =>
      (⟨toFs p.1, p.2⟩ : Σ _ : ℕ →₀ ℕ, ℕ)) := by
    intro a b hab
    simp only [Sigma.mk.injEq, heq_eq_eq] at hab
    exact Prod.ext (toFs_injective K hab.1) hab.2
  have h1 := hG.comp _ hι
  have h2 := h1.map' (heisRep hh).fockMap
    (LinearMap.ker_eq_bot.mpr (heisRep hh).fockMap_injective)
  exact h2

include hh hxC in
/-- **The Fock count.** `Σ_p r^{deg p} ≤ Σ_n dim Wₙ rⁿ` in `ℝ≥0∞`. -/
theorem lower_ennreal (K : ℕ) (r : ENNReal) :
    ∑' p : (Fin K → ℕ) × ℕ, r ^ fdegP K p ≤
      ∑' n : ℕ, (finrank ℂ (W.grading n) : ENNReal) * r ^ n := by
  rw [← (Equiv.sigmaFiberEquiv (fdegP K)).tsum_eq, ENNReal.tsum_sigma']
  refine ENNReal.tsum_le_tsum fun n => ?_
  let F : {p // fdegP K p = n} → W.grading (n : ℤ) := fun p =>
    ⟨(heisRep hh).fockMap (Finsupp.single (toFs p.1.1) (vacVec hh hxC p.1.2)), by
      have := fockVec_mem hh hxC hx2 p.1; rwa [p.2] at this⟩
  have hli : LinearIndependent ℂ F := by
    apply LinearIndependent.of_comp (W.grading (n : ℤ)).subtype
    exact (fockVec_linearIndependent hh hxC hx2 hx0 K).comp _ Subtype.val_injective
  haveI : FiniteDimensional ℂ (W.grading (n : ℤ)) := W.finrank _
  haveI : Finite {p // fdegP K p = n} := hli.finite_of_isNoetherian
  haveI := Fintype.ofFinite {p // fdegP K p = n}
  rw [tsum_fintype]
  have hc : ∀ p : {p // fdegP K p = n},
      r ^ fdegP K ((Equiv.sigmaFiberEquiv (fdegP K)) ⟨n, p⟩) = r ^ n := fun p => by
    rw [Equiv.sigmaFiberEquiv_apply, p.2]
  simp_rw [hc]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  gcongr
  exact_mod_cast hli.fintype_card_le_finrank

end Count

/-- `Σ_{e : Fin K → ℕ} Π gᵢ^{eᵢ} = Π (1 - gᵢ)⁻¹` in `ℝ≥0∞`. -/
theorem tsum_pi_pow : ∀ (K : ℕ) (g : Fin K → ENNReal),
    ∑' e : Fin K → ℕ, ∏ i, g i ^ e i = ∏ i, (1 - g i)⁻¹
  | 0, g => by simp
  | K + 1, g => by
    rw [← (Fin.consEquiv fun _ => ℕ).tsum_eq]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left, tsum_pi_pow K, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]

theorem tsum_fdegP (K : ℕ) (r : ENNReal) :
    ∑' p : (Fin K → ℕ) × ℕ, r ^ fdegP K p =
      (∏ i : Fin K, (1 - r ^ ((i : ℕ) + 1))⁻¹) * (r ^ 2 * (1 - r)⁻¹) := by
  rw [ENNReal.tsum_prod']
  have e1 : ∀ (e : Fin K → ℕ) (j : ℕ), r ^ fdegP K (e, j) =
      (∏ i : Fin K, (r ^ ((i : ℕ) + 1)) ^ e i) * (r ^ 2 * r ^ j) := by
    intro e j
    unfold fdegP
    simp_rw [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum, ← pow_add, ← pow_add, add_assoc]
  simp_rw [e1, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.tsum_mul_right,
    tsum_pi_pow K]

/-- Real form of the Fock count. -/
theorem lower_real {h x : 𝒲} (hh : IsHeisVector W h) (hxC : x ∈ commutant W h)
    (hx2 : x ∈ W.grading 2) (hx0 : x ≠ 0) (K : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hs : Summable fun n : ℕ => (finrank ℂ (W.grading n) : ℝ) * q ^ n) :
    (∏ i ∈ range K, (1 - q ^ (i + 1))⁻¹) * (q ^ 2 * (1 - q)⁻¹) ≤
      ∑' n : ℕ, (finrank ℂ (W.grading n) : ℝ) * q ^ n := by
  have hpos : ∀ i : ℕ, 0 < 1 - q ^ (i + 1) := fun i =>
    sub_pos.mpr (pow_lt_one₀ hq0 hq1 (by omega))
  have hL := lower_ennreal hh hxC hx2 hx0 K (ENNReal.ofReal q)
  rw [tsum_fdegP] at hL
  rw [← ENNReal.ofReal_le_ofReal_iff (tsum_nonneg fun n => by positivity),
    ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs]
  convert hL using 1
  · rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => (inv_pos.mpr (hpos i)).le),
      ENNReal.ofReal_prod_of_nonneg (fun i _ => (inv_pos.mpr (hpos i)).le),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (sub_pos.mpr hq1),
      ENNReal.ofReal_sub _ hq0, ENNReal.ofReal_one, ENNReal.ofReal_pow hq0]
    congr 1
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_inv_of_pos (hpos i), ENNReal.ofReal_sub _ (by positivity),
      ENNReal.ofReal_one, ENNReal.ofReal_pow hq0]
  · refine tsum_congr fun n => ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow hq0]

/-! ## §4 The Dedekind eta function on the imaginary axis -/

theorem cexp_two_pi_I_imag (Y : ℝ) :
    cexp (2 * Real.pi * I * ((Y : ℂ) * I)) = ((Real.exp (-(2 * Real.pi * Y)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]
  ring

theorem exp_neg_two_pi_lt_one {Y : ℝ} (hY : 0 < Y) : Real.exp (-(2 * Real.pi * Y)) < 1 := by
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])

theorem one_sub_eta_q_imag (Y : ℝ) (n : ℕ) :
    1 - ModularForm.eta_q n ((Y : ℂ) * I) =
      ((1 - Real.exp (-(2 * Real.pi * Y)) ^ (n + 1) : ℝ) : ℂ) := by
  rw [ModularForm.eta_q_eq_pow, cexp_two_pi_I_imag]
  push_cast; ring

theorem multipliable_eta_imag {Y : ℝ} (hY : 0 < Y) :
    Multipliable fun n : ℕ => 1 - ModularForm.eta_q n ((Y : ℂ) * I) := by
  simp_rw [ModularForm.eta_q_eq_pow]
  apply ModularForm.multipliable_one_sub_pow
  rw [cexp_two_pi_I_imag, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_neg_two_pi_lt_one hY

/-- The partial products `∏_{i<K} (1 - q^{i+1})` converge to `‖∏' (1 - q^{n+1})‖`. -/
theorem tendsto_partial_prod {Y : ℝ} (hY : 0 < Y) :
    Tendsto (fun K => ∏ i ∈ range K, (1 - Real.exp (-(2 * Real.pi * Y)) ^ (i + 1))) atTop
      (𝓝 ‖∏' n, (1 - ModularForm.eta_q n ((Y : ℂ) * I))‖) := by
  have h := ((multipliable_eta_imag hY).hasProd.tendsto_prod_nat).norm
  refine h.congr fun K => ?_
  rw [norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [one_sub_eta_q_imag, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
  exact sub_pos.mpr (pow_lt_one₀ (Real.exp_pos _).le
    (exp_neg_two_pi_lt_one hY) (by omega))

theorem norm_tprod_eta_le_one {Y : ℝ} (hY : 0 < Y) :
    ‖∏' n, (1 - ModularForm.eta_q n ((Y : ℂ) * I))‖ ≤ 1 := by
  refine le_of_tendsto' (tendsto_partial_prod hY) fun K => ?_
  refine Finset.prod_le_one (fun i _ => ?_) (fun i _ => ?_)
  · exact sub_nonneg.mpr (pow_le_one₀ (Real.exp_pos _).le
      (Real.exp_le_one_iff.mpr (by have := Real.pi_pos; nlinarith)))
  · exact sub_le_self _ (by positivity)

theorem norm_tprod_eta_pos {Y : ℝ} (hY : 0 < Y) :
    0 < ‖∏' n, (1 - ModularForm.eta_q n ((Y : ℂ) * I))‖ :=
  norm_pos_iff.mpr (ModularForm.eta_tprod_ne_zero (by simpa using hY))

theorem norm_eta_imag {Y : ℝ} :
    ‖ModularForm.eta ((Y : ℂ) * I)‖ =
      Real.exp (-(2 * Real.pi * Y / 24)) * ‖∏' n, (1 - ModularForm.eta_q n ((Y : ℂ) * I))‖ := by
  rw [ModularForm.eta, norm_mul, Function.Periodic.qParam, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem norm_csqrt (z : ℂ) (hz : z ≠ 0) :
    ‖Complex.sqrt z‖ = Real.exp (Real.log ‖z‖ / 2) := by
  rw [sqrt_eq_exp hz, Complex.norm_exp, Complex.div_re, Complex.log_re]
  norm_num
  ring

/-- `‖η(iy)‖ ≤ y^{-1/2} e^{-2π/(24y)}`, from `η(-1/τ) = √(-iτ) η(τ)`. -/
theorem norm_eta_imag_le {y : ℝ} (hy : 0 < y) :
    ‖ModularForm.eta ((y : ℂ) * I)‖ ≤
      Real.exp (Real.log (1 / y) / 2) * Real.exp (-(2 * Real.pi * (1 / y) / 24)) := by
  set τ : ℂ := ((1 / y : ℝ) : ℂ) * I with hτ
  have hτim : 0 < τ.im := by simp [hτ, hy]
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτim
  have hS := eta_S hτim
  have hneg : -1 / τ = (y : ℂ) * I := by
    rw [div_eq_iff hτ0, hτ]
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    push_cast
    field_simp
    rw [I_sq]
  rw [hneg] at hS
  rw [hS, norm_mul, norm_inv, norm_mul, norm_csqrt I I_ne_zero, norm_csqrt τ hτ0, norm_I,
    Real.log_one, zero_div, Real.exp_zero, inv_one, one_mul]
  have hτn : ‖τ‖ = 1 / y := by
    rw [hτ, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  rw [hτn]
  gcongr
  rw [norm_eta_imag]
  calc Real.exp (-(2 * Real.pi * (1 / y) / 24)) *
        ‖∏' n, (1 - ModularForm.eta_q n (((1 / y : ℝ) : ℂ) * I))‖
      ≤ Real.exp (-(2 * Real.pi * (1 / y) / 24)) * 1 := by
        gcongr; exact norm_tprod_eta_le_one (by positivity)
    _ = _ := mul_one _

theorem neg_one_div_imag {y : ℝ} (hy : 0 < y) : -1 / (((1 / y : ℝ) : ℂ) * I) = (y : ℂ) * I := by
  have hτ0 : (((1 / y : ℝ) : ℂ) * I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (one_div_pos.mpr hy).ne') I_ne_zero
  rw [div_eq_iff hτ0]
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  push_cast
  field_simp
  rw [I_sq]

/-- The elementary end of the argument: `q²/(1-q) ~ 1/(2πy)` cannot be `O(y^{-1/2})`. -/
theorem final_contra (C S0 : ℝ) (hC : 0 ≤ C)
    (key : ∀ y : ℝ, 0 < y → S0 ≤ 1 / y →
      Real.exp (-(2 * Real.pi * y)) ^ 2 * (1 - Real.exp (-(2 * Real.pi * y)))⁻¹ ≤
        C * Real.exp (Real.log (1 / y) / 2)) : False := by
  have hpi := Real.pi_pos
  set M : ℝ := max S0 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  set e : ℝ := Real.exp (-(4 * Real.pi)) with he
  have he0 : 0 < e := Real.exp_pos _
  set t : ℝ := min (1 / M) (e / (2 * Real.pi * (C + 1))) with ht
  have ht0 : 0 < t := lt_min (by positivity) (by positivity)
  have ht1 : t ≤ 1 / M := min_le_left _ _
  have ht2 : t ≤ e / (2 * Real.pi * (C + 1)) := min_le_right _ _
  have htle1 : t ≤ 1 := ht1.trans (by rw [div_le_one (by positivity)]; exact hM1)
  have hMt : M ≤ 1 / t := by
    rw [le_div_iff₀ ht0]; rw [le_div_iff₀ (by positivity)] at ht1; linarith
  have hS0 : S0 ≤ 1 / t ^ 2 := by
    have h1 : 1 / t ≤ 1 / t ^ 2 := by
      rw [div_le_div_iff₀ ht0 (by positivity)]; nlinarith
    exact (le_max_left _ _).trans (hMt.trans h1)
  have hk := key (t ^ 2) (by positivity) hS0
  have hsq : Real.exp (Real.log (1 / t ^ 2) / 2) = 1 / t := by
    rw [show (1 : ℝ) / t ^ 2 = (1 / t) ^ 2 by ring, Real.log_pow]
    rw [show ((2 : ℕ) : ℝ) * Real.log (1 / t) / 2 = Real.log (1 / t) by push_cast; ring]
    exact Real.exp_log (by positivity)
  rw [hsq] at hk
  set q : ℝ := Real.exp (-(2 * Real.pi * t ^ 2)) with hq
  have hq1 : q < 1 := exp_neg_two_pi_lt_one (by positivity)
  have hq2 : e ≤ q ^ 2 := by
    rw [hq, he, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have : t ^ 2 ≤ 1 := by nlinarith
    push_cast; nlinarith
  have h1q : 1 - q ≤ 2 * Real.pi * t ^ 2 := by
    have := Real.add_one_le_exp (-(2 * Real.pi * t ^ 2))
    rw [hq]; linarith
  have h1q0 : 0 < 1 - q := sub_pos.mpr hq1
  have hlow : e / (2 * Real.pi * t ^ 2) ≤ q ^ 2 * (1 - q)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact div_le_div₀ (by positivity) hq2 h1q0 h1q
  have hfin : e / (2 * Real.pi * t ^ 2) ≤ C * (1 / t) := hlow.trans hk
  rw [div_le_iff₀ (by positivity)] at hfin
  have h3 : e ≤ C * t * (2 * Real.pi) := by
    have : C * (1 / t) * (2 * Real.pi * t ^ 2) = C * t * (2 * Real.pi) := by
      field_simp
    linarith
  rw [le_div_iff₀ (by positivity)] at ht2
  have h4 : C * t * (2 * Real.pi) < e := by
    have h5 : t * (2 * Real.pi * C) ≤ t * (2 * Real.pi * (C + 1)) - t * (2 * Real.pi) := by ring_nf; rfl
    nlinarith
  linarith

end DMCOne

/-! ## §5 DM-1 from the modular data -/

universe u

open DMCOne in
/-- **DM-1 from `IModData`.** For a nice VOA `W` of central charge `1` and a unit Heisenberg
vector `h`, the Heisenberg commutant is `ℂ𝟙`, *assuming only* that `W` has modular data
(`IModData`, already a hypothesis of the headline).

Proof (Dong–Mason's effective-central-charge argument, specialised): if not, `x = ω - ω_h` is a
nonzero vector of the commutant in `W₂` (`conformal_sub_omegaH_mem_commutant`,
`commutant_le_of_conformal_eq`), so `Tʲx ≠ 0` lie in the commutant in every degree `2 + j`
(`Tpow_ne_zero`, `Tpow_mem_commutant`); the Fock space (`fockMap_injective`) then forces
`Σ dim Wₙ qⁿ ≥ ∏_{k≥1}(1-qᵏ)⁻¹ · q²/(1-q)` (`lower_real`). With `η(iy) = y^{-1/2} η(i/y)`
(`norm_eta_imag_le`) this gives `ch_W(iy) ≳ y^{-1/2} e^{2π/(24y)}`, while the `S`-transform and
the leading asymptotics `tendsto_chR` (pseudo-unitarity) give `ch_W(iy) = O(e^{2π/(24y)})`;
`final_contra` closes. -/
theorem heisCommutantTrivial_of_modData (hMD : IModData.{u}) : HeisCommutantTrivial.{u} := by
  intro 𝒲 _ _ W hW hc h hh
  obtain ⟨D, hD⟩ := hMD 𝒲 W hW
  by_contra hne
  set x := W.conformalVector - omegaH W h with hxdef
  have hxC : x ∈ commutant W h := conformal_sub_omegaH_mem_commutant hW.1 hh
  have hx2 : x ∈ W.grading 2 := sub_mem W.conformal_mem (omegaH_mem hh)
  have hx0 : x ≠ 0 := fun h0 => hne (commutant_le_of_conformal_eq (sub_eq_zero.mp h0))
  -- the upper bound from the leading asymptotics of every character
  obtain ⟨S0, hS0⟩ : ∃ S0 : ℝ, ∀ s ≥ S0, ∀ b,
      Real.exp (-(2 * Real.pi * s * 1 / 24)) * D.chR b s ≤ 2 := by
    have : ∀ᶠ s in atTop, ∀ b, Real.exp (-(2 * Real.pi * s * 1 / 24)) * D.chR b s ≤ 2 := by
      rw [Filter.eventually_all]
      intro b
      exact (hD.tendsto_chR hW hc b).eventually (ge_mem_nhds (by split_ifs <;> norm_num))
    exact eventually_atTop.mp this
  set C : ℝ := 2 * D.S00 * ∑ b, D.d b with hCdef
  have hC0 : 0 ≤ C := by
    have := hD.S00_pos
    have : 0 ≤ ∑ b, D.d b := Finset.sum_nonneg fun b _ => le_trans zero_le_one (hD.d_ge_one b)
    positivity
  refine final_contra C (max S0 1) hC0 fun y hy hyS => ?_
  have hS0y : S0 ≤ 1 / y := (le_max_left _ _).trans hyS
  have hy1 : 0 < 1 / y := one_div_pos.mpr hy
  set q : ℝ := Real.exp (-(2 * Real.pi * y)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := exp_neg_two_pi_lt_one hy
  -- the vacuum character as a `q`-series
  have hsum : HasSum (fun n : ℕ => (finrank ℂ (W.grading n) : ℝ) * q ^ n)
      (Real.exp (-(2 * Real.pi * y / 24)) * D.chR D.vac y) := by
    have := (hD.char_vac_imag hc hy).mul_left (Real.exp (-(2 * Real.pi * y / 24)))
    convert this using 1
    funext n
    rw [hq, ← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  set A : ℝ := Real.exp (-(2 * Real.pi * y / 24)) * D.chR D.vac y with hA
  set Pr : ℝ := ‖∏' n, (1 - ModularForm.eta_q n ((y : ℂ) * I))‖ with hPr
  have hPr0 : 0 < Pr := norm_tprod_eta_pos hy
  -- lower bound, in the limit `K → ∞`
  have hlow : Pr⁻¹ * (q ^ 2 * (1 - q)⁻¹) ≤ A := by
    have ht := ((tendsto_partial_prod hy).inv₀ hPr0.ne').mul_const (q ^ 2 * (1 - q)⁻¹)
    refine le_of_tendsto' ht fun K => ?_
    have := lower_real hh hxC hx2 hx0 K hq0 hq1 hsum.summable
    rw [hsum.tsum_eq, Finset.prod_inv_distrib] at this
    exact this
  have hlow' : q ^ 2 * (1 - q)⁻¹ ≤ D.chR D.vac y * ‖ModularForm.eta ((y : ℂ) * I)‖ := by
    rw [norm_eta_imag]
    have := mul_le_mul_of_nonneg_left hlow hPr0.le
    rw [← mul_assoc, mul_inv_cancel₀ hPr0.ne', one_mul] at this
    calc q ^ 2 * (1 - q)⁻¹ ≤ Pr * A := this
      _ = _ := by rw [hA]; ring
  -- upper bound from the `S`-transformation
  have hup : D.chR D.vac y ≤ C * Real.exp (2 * Real.pi * (1 / y) / 24) := by
    have hT := hD.S_transform D.vac (((1 / y : ℝ) : ℂ) * I) (by simpa using hy1)
    rw [neg_one_div_imag hy] at hT
    have hre : D.chR D.vac y = ∑ b, D.S00 * D.d b * D.chR b (1 / y) := by
      unfold ModularData.chR
      rw [hT, Complex.re_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hD.S_vac_left b, (hD.char_imag hc b hy1).2]
      simp [ModularData.chR]
    rw [hre, hCdef, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun b _ => ?_
    have hb := hS0 (1 / y) hS0y b
    have hE : D.chR b (1 / y) ≤ 2 * Real.exp (2 * Real.pi * (1 / y) / 24) := by
      have hpos := Real.exp_pos (2 * Real.pi * (1 / y) / 24)
      have hinv : Real.exp (-(2 * Real.pi * (1 / y) * 1 / 24)) *
          Real.exp (2 * Real.pi * (1 / y) / 24) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      nlinarith [hD.chR_pos hc b hy1]
    have hd := le_trans zero_le_one (hD.d_ge_one b)
    have := hD.S00_pos
    calc D.S00 * D.d b * D.chR b (1 / y)
        ≤ D.S00 * D.d b * (2 * Real.exp (2 * Real.pi * (1 / y) / 24)) := by gcongr
      _ = 2 * D.S00 * D.d b * Real.exp (2 * Real.pi * (1 / y) / 24) := by ring
  have heta := norm_eta_imag_le hy
  have hchR := (hD.chR_pos hc D.vac hy).le
  calc q ^ 2 * (1 - q)⁻¹ ≤ D.chR D.vac y * ‖ModularForm.eta ((y : ℂ) * I)‖ := hlow'
    _ ≤ (C * Real.exp (2 * Real.pi * (1 / y) / 24)) *
        (Real.exp (Real.log (1 / y) / 2) * Real.exp (-(2 * Real.pi * (1 / y) / 24))) := by
      gcongr
    _ = C * Real.exp (Real.log (1 / y) / 2) := by
      have : Real.exp (2 * Real.pi * (1 / y) / 24) * Real.exp (-(2 * Real.pi * (1 / y) / 24)) = 1 := by
        rw [← Real.exp_add]; simp
      calc _ = C * Real.exp (Real.log (1 / y) / 2) *
            (Real.exp (2 * Real.pi * (1 / y) / 24) * Real.exp (-(2 * Real.pi * (1 / y) / 24))) := by
            ring
        _ = _ := by rw [this, mul_one]

/-- **`IDongMason` from `IModData`.** DM-1 (`heisCommutantTrivial_of_modData`) and DM-2
(`heisLatticeReconstruction`, unconditional) assemble via `iDongMason_of_facts`. -/
theorem iDongMason_of_modData (hMD : IModData.{u}) : IDongMason.{u} :=
  iDongMason_of_facts (heisCommutantTrivial_of_modData hMD) heisLatticeReconstruction

end VOA.Classification.COne
