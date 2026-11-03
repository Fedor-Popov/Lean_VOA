import VOA.Huang.GaloisSymVerlinde
import VOA.Huang.CongruenceGaloisSplit

/-!
# The congruence and modular-Galois boundaries

This file proves the group/character implications needed to consume DLN.
It does not prove the congruence theorem or identify a diagonal modular-group
element with a field automorphism. Those are separate from Coste–Gannon's
algebraic signed-permutation theorem.
-/

noncomputable section

namespace VOA.Huang.DLN

open Matrix VOA VOA.Classification.COne VOA.Huang.CongruenceGaloisSplit
  VOA.Huang.GaloisSym

abbrev SL2Z := Matrix.SpecialLinearGroup (Fin 2) ℤ

/-- Reduction modulo `N`, including `N = 0` with Mathlib's convention. -/
def reduction (N : ℕ) : SL2Z →* Matrix.SpecialLinearGroup (Fin 2) (ZMod N) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The genuine kernel condition; no projective scalar is discarded. -/
def KernelContainsGamma (ρ : SL2Z →* Matrix ι ι ℂ) (N : ℕ) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma N, ρ γ = 1

theorem kernelContainsGamma_of_factors (ρ : SL2Z →* Matrix ι ι ℂ) (N : ℕ)
    (r : Matrix.SpecialLinearGroup (Fin 2) (ZMod N) →* Matrix ι ι ℂ)
    (hf : ρ = r.comp (reduction N)) : KernelContainsGamma ρ N := by
  intro γ hγ
  have h := CongruenceSubgroup.Gamma_mem'.mp hγ
  change reduction N γ = 1 at h
  rw [hf, MonoidHom.comp_apply, h, map_one]

theorem gamma_le_of_dvd {n N : ℕ} (hd : n ∣ N) :
    CongruenceSubgroup.Gamma N ≤ CongruenceSubgroup.Gamma n := by
  intro γ hγ
  have lower : ∀ (a b : ℤ), (a : ZMod N) = b → (a : ZMod n) = b := by
    intro a b h
    apply (ZMod.intCast_eq_intCast_iff a b n).mpr
    exact Int.ModEq.of_dvd (by exact_mod_cast hd)
      ((ZMod.intCast_eq_intCast_iff a b N).mp h)
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  exact ⟨by simpa using lower (γ 0 0) 1 (by simpa using hγ.1),
    by simpa using lower (γ 0 1) 0 (by simpa using hγ.2.1),
    by simpa using lower (γ 1 0) 0 (by simpa using hγ.2.2.1),
    by simpa using lower (γ 1 1) 1 (by simpa using hγ.2.2.2)⟩

theorem KernelContainsGamma.of_dvd {ρ : SL2Z →* Matrix ι ι ℂ} {n N : ℕ}
    (h : KernelContainsGamma ρ n) (hd : n ∣ N) : KernelContainsGamma ρ N :=
  fun γ hγ => h γ (gamma_le_of_dvd hd hγ)

/-- Equal reductions give equal representation matrices, once congruence is known. -/
theorem KernelContainsGamma.eq_of_reduction {ρ : SL2Z →* Matrix ι ι ℂ} {N : ℕ}
    (h : KernelContainsGamma ρ N) {γ δ : SL2Z}
    (he : reduction N γ = reduction N δ) : ρ γ = ρ δ := by
  have hg : δ⁻¹ * γ ∈ CongruenceSubgroup.Gamma N := by
    rw [CongruenceSubgroup.Gamma_mem']
    change reduction N (δ⁻¹ * γ) = 1
    rw [map_mul, he, ← map_mul, inv_mul_cancel, map_one]
  have hh := congrArg (fun M => ρ δ * M) (h _ hg)
  simpa only [← map_mul, mul_inv_cancel_left, mul_one] using hh

/-- DLN's exact-order target, retaining finite order to exclude the vacuous
`orderOf = 0`, `Γ(0) = {1}` case. -/
def CongruenceAtOrder (ρ : SL2Z →* Matrix ι ι ℂ) : Prop :=
  IsOfFinOrder (ρ ModularGroup.T) ∧
    KernelContainsGamma ρ (orderOf (ρ ModularGroup.T))

theorem CongruenceAtOrder.at_level {ρ : SL2Z →* Matrix ι ι ℂ}
    (h : CongruenceAtOrder ρ) {N : ℕ} (hT : ρ ModularGroup.T ^ N = 1) :
    KernelContainsGamma ρ N :=
  h.2.of_dvd (orderOf_dvd_of_pow_eq_one hT)

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}

/-- A representation on the specified character family. Character independence
is deliberately not required; inequivalent modules can have equal characters. -/
def CharacterCovariance (D : VOA.Classification.COne.ModularData V)
    (ρ : SL2Z →* Matrix D.ι D.ι ℂ) : Prop :=
  ∀ γ a τ, 0 < Complex.im τ →
    D.ch a (mobius γ τ) = ∑ b, ρ γ a b * D.ch b τ

theorem characters_invariant_of_kernel (D : VOA.Classification.COne.ModularData V)
    (ρ : SL2Z →* Matrix D.ι D.ι ℂ) (hc : CharacterCovariance D ρ) (N : ℕ)
    (hk : KernelContainsGamma ρ N) :
    ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ a τ, 0 < Complex.im τ →
      D.ch a (mobius γ τ) = D.ch a τ := by
  intro γ hγ a τ hτ
  rw [hc γ a τ hτ, hk γ hγ]
  simp [Matrix.one_apply]

/-- Exact consumption of DLN by the existing classification input. Constructing
the representations and proving `CongruenceAtOrder` remain explicit obligations. -/
theorem dlnCongruenceInput_of_representations
    (h : ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱),
      Nice V → ∀ D : VOA.Classification.COne.ModularData V, D.IsModularData →
        ∃ ρ : SL2Z →* Matrix D.ι D.ι ℂ, CharacterCovariance D ρ ∧ CongruenceAtOrder ρ ∧
          ∀ N, D.IsLevel N → ρ ModularGroup.T ^ N = 1) : DLNCongruenceInput.{u} := by
  intro 𝒱 _ _ V hV D hD N hN
  obtain ⟨ρ, hc, hk, hT⟩ := h 𝒱 V hV D hD
  exact characters_invariant_of_kernel D ρ hc N (hk.at_level (hT N hN))

/-- The still-open DLN compatibility, weaker than a specified cyclotomic action:
for every diagonal residue class, some field automorphism realizes its action
on `S`. The intended witness extends `ζ_N ↦ ζ_N^ℓ` from `ℚ(ζ_N)`.
This is a predicate on data, not an assertion for arbitrary representations. -/
def DiagonalGaloisCompatibility (ρ : SL2Z →* Matrix ι ι ℂ)
    (S : Matrix ι ι ℂ) (N : ℕ) : Prop :=
  ∀ ℓ ℓ' : ℤ, ℓ * ℓ' ≡ 1 [ZMOD N] → ∀ γ : SL2Z,
    γ 0 0 ≡ ℓ [ZMOD N] → γ 1 1 ≡ ℓ' [ZMOD N] →
    γ 0 1 ≡ 0 [ZMOD N] → γ 1 0 ≡ 0 [ZMOD N] →
      ∃ σ : ℂ ≃+* ℂ, S.map σ = ρ γ * S

/-- Algebraic signed-row symmetry plus DLN compatibility gives exactly the
character transformation requested by `GaloisCase`. -/
theorem galoisCase_of_verlinde (D : VOA.Classification.COne.ModularData V)
    (ρ : SL2Z →* Matrix D.ι D.ι ℂ) (hc : CharacterCovariance D ρ)
    (F : D.ι → D.ι → D.ι → ℕ) (S : Matrix D.ι D.ι ℂ) (v0 : D.ι)
    (H : VerlindeSystem F S v0) (hn : IntegralColumnNormalization S)
    (hs : S.transpose = S) (γ : SL2Z) (σ : ℂ ≃+* ℂ)
    (hcompat : S.map σ = ρ γ * S) : GaloisCase D γ := by
  obtain ⟨π, ε, he, hrow⟩ := H.galois_signed_rows hn hs σ
  let G : Matrix D.ι D.ι ℂ := fun a b => if π a = b then ε a else 0
  have hG : S.map σ = G * S := by
    ext a b
    simpa [G, Matrix.mul_apply] using hrow a b
  have hr : ρ γ = G := by
    apply H.invertible.mul_right_cancel
    exact hcompat.symm.trans hG
  refine ⟨π, ε, he, fun a τ hτ => ?_⟩
  rw [hc γ a τ hτ, hr]
  simp [G]

theorem galoisSymmetric_of_compatibility (D : VOA.Classification.COne.ModularData V)
    (ρ : SL2Z →* Matrix D.ι D.ι ℂ) (hc : CharacterCovariance D ρ)
    (F : D.ι → D.ι → D.ι → ℕ) (S : Matrix D.ι D.ι ℂ) (v0 : D.ι)
    (H : VerlindeSystem F S v0) (hn : IntegralColumnNormalization S)
    (hs : S.transpose = S) (N : ℕ) (hd : DiagonalGaloisCompatibility ρ S N) :
    D.GaloisSymmetric N := by
  intro ℓ ℓ' hℓ γ h00 h11 h01 h10
  obtain ⟨σ, hσ⟩ := hd ℓ ℓ' hℓ γ h00 h11 h01 h10
  exact galoisCase_of_verlinde D ρ hc F S v0 H hn hs γ σ hσ

end VOA.Huang.DLN
