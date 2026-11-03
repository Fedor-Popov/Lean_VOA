/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkHeckeWeil

/-!
# Serre–Stark S3-1d: the theta transport law on generators of `Γ₀(N)`

`ThetaLaw p γ σ`: `ω_i θ(A_i γ τ) θ(τ) = ω_{σ i} θ(γτ) θ(A_{σ i} τ)` on `ℍ`, for every coset
index `i` (no character appears: the law is a statement about `θ` alone).

* `thetaLaw_T`: for `T`;
* `thetaLaw_L`: for `L^N = (1 0; N 1)`, `24 ∣ N`, `p ∤ N`, `p` odd — from the Weil
  representation at level `p²` (`weilWord_transform`), the contraction `contraction` and the
  Fourier relation `dRel`;
* `thetaLaw_G`: for `γ ≡ diag(ℓ, ℓ') (mod N p²)` — from the (proved) Weil Galois law.
-/

open Complex
open scoped MatrixGroups

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

open WeilGalois

/-- The theta transport law for `γ` with induced permutation `σ`. -/
def ThetaLaw (p : ℕ) [Fact p.Prime] (γ : SL(2, ℤ)) (σ : HIdx p → HIdx p) : Prop :=
  ∀ i : HIdx p, ∀ τ : ℂ, 0 < τ.im →
    hw p i * thetaRef (mobZ (cosetMat p i) (mobius γ τ)) * thetaRef τ =
      hw p (σ i) * thetaRef (mobius γ τ) * thetaRef (mobZ (cosetMat p (σ i)) τ)

variable {p : ℕ} (hp : p.Prime)

/-! ## Theta combinations in the Weil representation -/

theorem weilTheta_eq_vec (P : ℕ) (μ : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    weilTheta P μ τ = weilVec P μ τ * ModularForm.eta τ := by
  rw [weilVec, div_mul_cancel₀ _ (ModularForm.eta_ne_zero hτ)]

/-- `Σ_μ v(μ) Θ_μ(γτ) = η(γτ) Σ_j (Σ_μ v(μ) A_{μj}) F_j(τ)`. -/
theorem combo_transform {P : ℕ} (hP : 0 < P) {γ : SL(2, ℤ)}
    {A : Matrix (Fin (2 * P)) (Fin (2 * P)) ℂ} (hA : WeilWord P γ A) (v : ℤ → ℂ) {τ : ℂ}
    (hτ : 0 < τ.im) :
    ∑ μ : Fin (2 * P), v ((μ : ℕ) : ℤ) * weilTheta P ((μ : ℕ) : ℤ) (mobius γ τ) =
      ModularForm.eta (mobius γ τ) * ∑ j : Fin (2 * P),
        (∑ μ : Fin (2 * P), v ((μ : ℕ) : ℤ) * A μ j) * weilVec P ((j : ℕ) : ℤ) τ := by
  have hγτ := im_mobius_pos γ hτ
  simp_rw [weilTheta_eq_vec P _ hγτ, weilWord_transform hP hA hτ, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun μ _ => ?_
  ring

theorem combo_eq {P : ℕ} (v : ℤ → ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    ∑ j : Fin (2 * P), v ((j : ℕ) : ℤ) * weilVec P ((j : ℕ) : ℤ) τ =
      (∑ j : Fin (2 * P), v ((j : ℕ) : ℤ) * weilTheta P ((j : ℕ) : ℤ) τ) /
        ModularForm.eta τ := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weilVec, mul_div_assoc]

/-- A linear relation between Weil vectors transports along `γ`. -/
theorem combo_law {P : ℕ} (hP : 0 < P) {γ : SL(2, ℤ)}
    {A : Matrix (Fin (2 * P)) (Fin (2 * P)) ℂ} (hA : WeilWord P γ A) (v v' : ℤ → ℂ) (c c' : ℂ)
    (hc : ∀ j : Fin (2 * P), c * ∑ μ : Fin (2 * P), v ((μ : ℕ) : ℤ) * A μ j =
      c' * v' ((j : ℕ) : ℤ)) {τ : ℂ} (hτ : 0 < τ.im) :
    c * ∑ μ : Fin (2 * P), v ((μ : ℕ) : ℤ) * weilTheta P ((μ : ℕ) : ℤ) (mobius γ τ) =
      ModularForm.eta (mobius γ τ) *
        (c' * ∑ j : Fin (2 * P), v' ((j : ℕ) : ℤ) * weilTheta P ((j : ℕ) : ℤ) τ) /
          ModularForm.eta τ := by
  rw [combo_transform hP hA v hτ, mul_div_assoc, mul_div_assoc, ← combo_eq _ hτ,
    mul_left_comm]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [← mul_assoc, hc j, mul_assoc]

/-! ## The generator `L^N` -/

include hp in
theorem dRel_thvec {K : ℤ} (k : ℤ) :
    1 * dL p K k * fhat p (thvec p) k = 1 * fhat p (thvec p) k := by
  rw [fhat_thvec hp]
  split_ifs with hk
  · rw [dL_of_dvd hp.pos K hk]; ring
  · ring

include hp in
/-- **The theta transport law for `L^N`.** -/
theorem thetaLaw_L [Fact p.Prime] (hp2 : p ≠ 2) {N : ℕ} {K : ℤ} (hNK : (N : ℤ) = 4 * K)
    (h24 : 24 ∣ N) (hpN : ¬ (p : ℤ) ∣ N) : ThetaLaw p (matL N) (sigmaL hp N) := by
  intro i τ hτ
  have hP : 0 < p ^ 2 := pow_pos hp.pos 2
  have hA := weilWord_matL (p ^ 2) N
  have hL := im_mobius_pos (matL N) hτ
  have hη := ModularForm.eta_ne_zero hτ
  have h1 := combo_law hP hA (cvec p i) (cvec p (sigmaL hp N i)) (hw p i) (hw p (sigmaL hp N i))
    (contraction hp hNK h24 (cvec p i) (cvec p (sigmaL hp N i)) (cvec_periodic hp _)
      (cvec_neg _) _ _ (dRel hp hp2 hNK hpN i)) hτ
  have h2 := combo_law hP hA (thvec p) (thvec p) 1 1
    (contraction hp hNK h24 (thvec p) (thvec p) thvec_periodic thvec_neg _ _
      (dRel_thvec hp)) hτ
  rw [← thetaRef_cosetMat_eq hp i hL, ← thetaRef_cosetMat_eq hp _ hτ] at h1
  rw [← thetaRef_eq_thvec hp hL, ← thetaRef_eq_thvec hp hτ, one_mul, one_mul] at h2
  rw [h1, h2]
  field_simp

/-! ## The translation `T` -/

include hp in
/-- **The theta transport law for `T`.** -/
theorem thetaLaw_T [Fact p.Prime] : ThetaLaw p matT (sigmaT hp) := by
  intro i τ hτ
  have hp0 := hp.pos
  have hT : mobius matT τ = τ + 1 := mobius_matT τ
  have hw' : hw p (sigmaT hp i) = hw p i := by rcases i with b | h | u <;> rfl
  rw [hw', hT, thetaRef_add_one]
  rw [← hT, ← mobZ_cosetMat_mul_SL i matT hτ, factT hp i]
  rw [mobZ_mul _ _ (by rw [denZ_cosetMat]; exact_mod_cast (dCo_pos hp0 _).ne')]
  have hδ : ∃ k : ℤ, deltaT hp i = !![1, k; 0, 1] := by
    rcases i with b | h | u
    · exact ⟨_, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨(p : ℤ) ^ 2, rfl⟩
  obtain ⟨k, hk⟩ := hδ
  rw [hk]
  have : ∀ w : ℂ, mobZ !![1, k; 0, 1] w = w + k := fun w => by simp [mobZ]
  rw [this, thetaRef_add_int]
  ring

/-! ## The diagonal generators -/

theorem isCoprime_of_mul_modEq {M n : ℕ} (hn : n ∣ M) {ℓ : ℕ} {ℓ' : ℤ}
    (h : (ℓ : ℤ) * ℓ' ≡ 1 [ZMOD M]) : IsCoprime ℓ' (n : ℤ) := by
  have h' : (ℓ : ℤ) * ℓ' ≡ 1 [ZMOD n] := Int.ModEq.of_dvd (by exact_mod_cast hn) h
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.1 h'.symm
  exact ⟨ℓ, -t, by linear_combination ht⟩

/-- The Galois action on theta combinations. -/
theorem galois_combo {P M : ℕ} (hP : 0 < P) (hdiv : 4 * P ∣ M) (h24 : 24 ∣ M) (ℓ : ℕ)
    (hℓ : ℓ.Coprime M) (ℓ' : ℤ) (hℓℓ : (ℓ : ℤ) * ℓ' ≡ 1 [ZMOD M]) (γ : SL(2, ℤ))
    (h00 : γ 0 0 ≡ ℓ [ZMOD M]) (h11 : γ 1 1 ≡ ℓ' [ZMOD M]) (h01 : γ 0 1 ≡ 0 [ZMOD M])
    (h10 : γ 1 0 ≡ 0 [ZMOD M]) (c c' : ℤ → ℂ) (hc : ∀ x, c (x + ((2 * P : ℕ) : ℤ)) = c x)
    (hc' : ∀ x, c' (x + ((2 * P : ℕ) : ℤ)) = c' x) (hcc : ∀ x, c' x = c (ℓ' * x)) {τ : ℂ}
    (hτ : 0 < τ.im) :
    ∑ μ : Fin (2 * P), c ((μ : ℕ) : ℤ) * weilTheta P ((μ : ℕ) : ℤ) (mobius γ τ) =
      (jacobiSym (2 * (P : ℤ)) ℓ : ℂ) * ModularForm.eta (mobius γ τ) *
        (∑ x : Fin (2 * P), c' ((x : ℕ) : ℤ) * weilTheta P ((x : ℕ) : ℤ) τ) /
          ModularForm.eta τ := by
  have h2P : 0 < 2 * P := by omega
  have hγτ := im_mobius_pos γ hτ
  have hη := ModularForm.eta_ne_zero hτ
  obtain ⟨A, hA⟩ := exists_weilWord P γ
  set v : ℤ → ℂ := fun x => weilVec P x τ with hv
  have hper : ∀ x, v (x + 2 * P) = v x := fun x =>
    weilVec_congr P (Int.modEq_iff_dvd.2 ⟨-1, by push_cast; ring⟩) τ
  have hev : ∀ x, v (-x) = v x := fun x => by simp only [hv, weilVec, weilTheta_neg]
  have hG := fun μ => weilGaloisLaw P M hP hdiv h24 ℓ hℓ ℓ' hℓℓ γ h00 h11 h01 h10 A hA v hper hev μ
  have hW : ∀ μ : Fin (2 * P), weilVec P ((μ : ℕ) : ℤ) (mobius γ τ) =
      (jacobiSym (2 * (P : ℤ)) ℓ : ℂ) * weilVec P (ℓ * ((μ : ℕ) : ℤ)) τ := fun μ => by
    rw [weilWord_transform hP hA hτ μ]; exact hG μ
  have h2PM : ((2 * P : ℕ) : ℤ) ∣ M := by
    obtain ⟨c, hc⟩ := hdiv; exact ⟨2 * c, by rw [hc]; push_cast; ring⟩
  have hℓℓ2 : (ℓ : ℤ) * ℓ' ≡ 1 [ZMOD ((2 * P : ℕ) : ℤ)] := Int.ModEq.of_dvd h2PM hℓℓ
  -- reindex `μ ↦ ℓ μ`
  have hre : ∑ μ : Fin (2 * P), c ((μ : ℕ) : ℤ) * weilVec P (ℓ * ((μ : ℕ) : ℤ)) τ =
      ∑ x : Fin (2 * P), c' ((x : ℕ) : ℤ) * weilVec P ((x : ℕ) : ℤ) τ := by
    have hF : ∀ x, c' (x + ((2 * P : ℕ) : ℤ)) * weilVec P (x + ((2 * P : ℕ) : ℤ)) τ =
        c' x * weilVec P x τ := fun x => by
      rw [hc', weilVec_congr P (Int.modEq_iff_dvd.2 ⟨-1, by push_cast; ring⟩) τ]
    rw [← resid_sum h2P (fun x => c' x * weilVec P x τ) hF (by simp)
      (fun μ : Fin (2 * P) => (ℓ : ℤ) * ((μ : ℕ) : ℤ))]
    · refine Finset.sum_congr rfl fun μ _ => ?_
      rw [hcc]
      congr 1
      apply periodic_congr' hc
      refine Int.ModEq.symm ?_
      calc ℓ' * ((ℓ : ℤ) * ((μ : ℕ) : ℤ)) = ((ℓ : ℤ) * ℓ') * ((μ : ℕ) : ℤ) := by ring
        _ ≡ 1 * ((μ : ℕ) : ℤ) [ZMOD ((2 * P : ℕ) : ℤ)] := hℓℓ2.mul_right _
        _ = ((μ : ℕ) : ℤ) := one_mul _
    · intro i j hij
      apply fin_eq_of_modEq
      have := hij.mul_left ℓ'
      calc ((i : ℕ) : ℤ) = 1 * ((i : ℕ) : ℤ) := (one_mul _).symm
        _ ≡ ((ℓ : ℤ) * ℓ') * ((i : ℕ) : ℤ) [ZMOD ((2 * P : ℕ) : ℤ)] := (hℓℓ2.mul_right _).symm
        _ = ℓ' * ((ℓ : ℤ) * ((i : ℕ) : ℤ)) := by ring
        _ ≡ ℓ' * ((ℓ : ℤ) * ((j : ℕ) : ℤ)) [ZMOD ((2 * P : ℕ) : ℤ)] := this
        _ = ((ℓ : ℤ) * ℓ') * ((j : ℕ) : ℤ) := by ring
        _ ≡ 1 * ((j : ℕ) : ℤ) [ZMOD ((2 * P : ℕ) : ℤ)] := hℓℓ2.mul_right _
        _ = ((j : ℕ) : ℤ) := one_mul _
  simp_rw [weilTheta_eq_vec P _ hγτ, hW]
  rw [mul_div_assoc, ← combo_eq _ hτ, ← hre, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring

include hp in
/-- **The theta transport law for `γ ≡ diag(ℓ, ℓ') (mod N p²)`.** -/
theorem thetaLaw_G [Fact p.Prime] {N : ℕ} (h4 : 4 ∣ N) (h24 : 24 ∣ N) (ℓ : ℕ)
    (hℓ : ℓ.Coprime (N * p ^ 2)) (ℓ' : ℤ) (hℓℓ : (ℓ : ℤ) * ℓ' ≡ 1 [ZMOD (N * p ^ 2 : ℕ)])
    (γ : SL(2, ℤ)) (h00 : γ 0 0 ≡ ℓ [ZMOD (N * p ^ 2 : ℕ)])
    (h11 : γ 1 1 ≡ ℓ' [ZMOD (N * p ^ 2 : ℕ)]) (h01 : γ 0 1 ≡ 0 [ZMOD (N * p ^ 2 : ℕ)])
    (h10 : γ 1 0 ≡ 0 [ZMOD (N * p ^ 2 : ℕ)]) : ThetaLaw p γ (sigmaG hp ℓ') := by
  intro i τ hτ
  have hp0 := hp.pos
  have hP : 0 < p ^ 2 := pow_pos hp0 2
  have h2P : 0 < 2 * p ^ 2 := by positivity
  have hγτ := im_mobius_pos γ hτ
  have hdivM : 4 * p ^ 2 ∣ N * p ^ 2 := Nat.mul_dvd_mul_right h4 _
  have h24M : 24 ∣ N * p ^ 2 := h24.trans (dvd_mul_right _ _)
  have h2pM : 2 * p ∣ N * p ^ 2 := by
    obtain ⟨c, hc⟩ := h4
    exact ⟨2 * c * p, by rw [hc]; ring⟩
  have h2PM : 2 * p ^ 2 ∣ N * p ^ 2 := by
    obtain ⟨c, hc⟩ := h4
    exact ⟨2 * c, by rw [hc]; ring⟩
  have hcop : IsCoprime ℓ' (2 * (p : ℤ)) := by
    have := isCoprime_of_mul_modEq h2pM hℓℓ; push_cast at this; exact this
  have hη := ModularForm.eta_ne_zero hτ
  have h1 := galois_combo hP hdivM h24M ℓ hℓ ℓ' hℓℓ γ h00 h11 h01 h10 (cvec p i)
    (cvec p (sigmaG hp ℓ' i)) (cvec_periodic hp _) (cvec_periodic hp _)
    (cvec_sigmaG hp hcop i) hτ
  have h2 := galois_combo hP hdivM h24M ℓ hℓ ℓ' hℓℓ γ h00 h11 h01 h10 (thvec p) (thvec p)
    thvec_periodic thvec_periodic (fun x => (thvec_mul hcop x).symm) hτ
  rw [← thetaRef_cosetMat_eq hp i hγτ, ← thetaRef_cosetMat_eq hp _ hτ] at h1
  rw [← thetaRef_eq_thvec hp hγτ, ← thetaRef_eq_thvec hp hτ] at h2
  rw [h1, h2, hw_sigmaG hp hcop]
  field_simp

end SSHecke

end VOA.Classification.COne
