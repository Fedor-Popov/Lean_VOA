import VOA.Huang.DLNReduction

/-!
# A diagonal word and the precise all-lifts boundary

The word below reduces to `diag(a,b)` when `a * b = 1` modulo the level.
An identity for this one word is weaker than an identity for every lift.
The latter is equivalent to the word identity AND congruence. This prevents
using an all-lifts Galois law as an independent proof of congruence.
-/

noncomputable section

namespace VOA.Huang.DLNAlg

open Matrix VOA.Huang.DLN VOA.Huang.GaloisSym

/-- DLN's word, in Mathlib's convention `S = !![0,-1;1,0]`. -/
def diagonalWord (a b : ℤ) : SL2Z :=
  ModularGroup.T ^ a * ModularGroup.S * ModularGroup.T ^ b *
    ModularGroup.S * ModularGroup.T ^ a * ModularGroup.S⁻¹

theorem coe_diagonalWord (a b : ℤ) :
    (diagonalWord a b : Matrix (Fin 2) (Fin 2) ℤ) =
      !![2 * a-a * a * b, a * b-1; 1-a * b, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalWord, ModularGroup.coe_T_zpow, ModularGroup.S_inv,
      ModularGroup.coe_S] <;> ring

/-- No representation or congruence assumption is used in this residue computation. -/
theorem diagonalWord_reduction {N : ℕ} {a b : ℤ} (hab : a * b ≡ 1 [ZMOD N]) :
    (reduction N (diagonalWord a b) : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      !![(a : ZMod N), 0; 0, (b : ZMod N)] := by
  have h : (a : ZMod N) * (b : ZMod N) = 1 := by
    simpa using (ZMod.intCast_eq_intCast_iff (a * b) 1 N).mpr hab
  change ((diagonalWord a b : Matrix (Fin 2) (Fin 2) ℤ).map
    (Int.castRingHom (ZMod N))) = _
  rw [coe_diagonalWord]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Int.coe_castRingHom, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_sub, Int.cast_mul,
      Int.cast_ofNat, Int.cast_one]
  · calc
      2 * (a : ZMod N) - a * a * b = 2 * a - a * (a * b) := by ring
      _ = a := by rw [h]; ring
  · exact sub_eq_zero.mpr h
  · exact sub_eq_zero.mpr h.symm

/-- A diagonal residue class, expressed without a chosen lift. -/
def HasDiagonalReduction (N : ℕ) (a b : ℤ) (γ : SL2Z) : Prop :=
  (reduction N γ : Matrix (Fin 2) (Fin 2) (ZMod N)) =
    !![(a : ZMod N), 0; 0, (b : ZMod N)]

theorem hasDiagonalReduction_of_modEq {N : ℕ} {a b : ℤ} {γ : SL2Z}
    (h00 : γ 0 0 ≡ a [ZMOD N]) (h11 : γ 1 1 ≡ b [ZMOD N])
    (h01 : γ 0 1 ≡ 0 [ZMOD N]) (h10 : γ 1 0 ≡ 0 [ZMOD N]) :
    HasDiagonalReduction N a b γ := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact (ZMod.intCast_eq_intCast_iff _ _ N).mpr h00
  · simpa using (ZMod.intCast_eq_intCast_iff _ _ N).mpr h01
  · simpa using (ZMod.intCast_eq_intCast_iff _ _ N).mpr h10
  · exact (ZMod.intCast_eq_intCast_iff _ _ N).mpr h11

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem eq_diagonalWord_of_kernel (ρ : SL2Z →* Matrix ι ι ℂ) {N : ℕ}
    (hk : KernelContainsGamma ρ N) {a b : ℤ} (hab : a * b ≡ 1 [ZMOD N])
    {γ : SL2Z} (hγ : HasDiagonalReduction N a b γ) :
    ρ γ = ρ (diagonalWord a b) := by
  apply hk.eq_of_reduction
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact congrFun (congrFun (hγ.trans (diagonalWord_reduction hab).symm) i) j

/-- A Galois law for one explicit word per unit. `σ` is a specified family of
field automorphisms, intended to extend the cyclotomic power automorphisms.
No assertion about arbitrary lifts is included. -/
def WordGaloisLaw (ρ : SL2Z →* Matrix ι ι ℂ) (S : Matrix ι ι ℂ) (N : ℕ)
    (σ : ℤ → ℂ ≃+* ℂ) : Prop :=
  ∀ a b : ℤ, a * b ≡ 1 [ZMOD N] → S.map (σ a) = ρ (diagonalWord a b) * S

/-- The stronger version, for all lifts of every diagonal residue class. -/
def AllLiftsGaloisLaw (ρ : SL2Z →* Matrix ι ι ℂ) (S : Matrix ι ι ℂ) (N : ℕ)
    (σ : ℤ → ℂ ≃+* ℂ) : Prop :=
  ∀ a b : ℤ, a * b ≡ 1 [ZMOD N] → ∀ γ : SL2Z,
    HasDiagonalReduction N a b γ → S.map (σ a) = ρ γ * S

theorem allLiftsGaloisLaw_iff (ρ : SL2Z →* Matrix ι ι ℂ) (S : Matrix ι ι ℂ)
    (hS : IsUnit S) (N : ℕ) (σ : ℤ → ℂ ≃+* ℂ)
    (hσ : σ 1 = RingEquiv.refl ℂ) :
    AllLiftsGaloisLaw ρ S N σ ↔ KernelContainsGamma ρ N ∧ WordGaloisLaw ρ S N σ := by
  constructor
  · intro h
    constructor
    · intro γ hγ
      have hr : HasDiagonalReduction N 1 1 γ := by
        have he := CongruenceSubgroup.Gamma_mem'.mp hγ
        change reduction N γ = 1 at he
        simp [HasDiagonalReduction, he, Matrix.one_fin_two]
      have hh := h 1 1 (by simp) γ hr
      have he : S = ρ γ * S := by simpa [hσ] using hh
      apply hS.mul_right_cancel
      simpa using he.symm
    · intro a b hab
      exact h a b hab _ (diagonalWord_reduction hab)
  · rintro ⟨hk, hw⟩ a b hab γ hγ
    rw [eq_diagonalWord_of_kernel ρ hk hab hγ]
    exact hw a b hab

theorem diagonalGaloisCompatibility_of_word (ρ : SL2Z →* Matrix ι ι ℂ)
    (S : Matrix ι ι ℂ) (N : ℕ) (σ : ℤ → ℂ ≃+* ℂ)
    (hk : KernelContainsGamma ρ N) (hw : WordGaloisLaw ρ S N σ) :
    DiagonalGaloisCompatibility ρ S N := by
  intro a b hab γ h00 h11 h01 h10
  refine ⟨σ a, ?_⟩
  rw [eq_diagonalWord_of_kernel ρ hk hab
    (hasDiagonalReduction_of_modEq h00 h11 h01 h10)]
  exact hw a b hab

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VOA.VertexOperatorAlgebra 𝒱}

/-- At central charge one the vacuum alone forces a factor 24 in every level.
Thus odd-level congruence criteria cannot close the c=1 classification input. -/
theorem twentyFour_dvd_level (D : VOA.Classification.COne.ModularData V)
    (hD : D.IsModularData) (hc : V.centralCharge = 1) {N : ℕ}
    (hN : D.IsLevel N) : 24 ∣ N := by
  obtain ⟨k, hk⟩ := hN.2 D.vac
  rw [hD.h_vac, hc] at hk
  have he : (N : ℂ) = 24 * (-k : ℤ) := by
    push_cast
    push_cast at hk
    linear_combination -24 * hk
  have hi : (N : ℤ) = 24 * (-k) := by exact_mod_cast he
  exact Int.natCast_dvd_natCast.mp ⟨-k, hi⟩

/-- A proved consumer for the full character Galois law. Both genuine
congruence and the word law remain explicit. -/
theorem galoisSymmetric_of_word
    (D : VOA.Classification.COne.ModularData V)
    (ρ : SL2Z →* Matrix D.ι D.ι ℂ) (hc : CharacterCovariance D ρ)
    (F : D.ι → D.ι → D.ι → ℕ) (S : Matrix D.ι D.ι ℂ) (v0 : D.ι)
    (H : VerlindeSystem F S v0) (hn : IntegralColumnNormalization S)
    (hs : S.transpose = S) (N : ℕ) (σ : ℤ → ℂ ≃+* ℂ)
    (hk : KernelContainsGamma ρ N) (hw : WordGaloisLaw ρ S N σ) :
    D.GaloisSymmetric N :=
  galoisSymmetric_of_compatibility D ρ hc F S v0 H hn hs N
    (diagonalGaloisCompatibility_of_word ρ S N σ hk hw)

end VOA.Huang.DLNAlg
