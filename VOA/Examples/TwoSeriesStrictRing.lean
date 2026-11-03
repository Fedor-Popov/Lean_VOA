/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AdamovicSymbolJet

/-!
# The model ring `R[u_j, v_j]` of the two series, its mode derivations, and cyclicity

The jet model of `gr_r L_{k_n}(sl₂)`, `k_n = -2 + 2/(2n+1)`, lives in
`ℂ[u_j, v_j] ⊗ R_n = R_n[u_j, v_j]`, where `R_n = ℂ[T_j]/(jets of Tⁿ)` is inert under the loop
algebra and `T` is the symbol of the `M(2, 2n+1)` Virasoro field.  This file works over an
**arbitrary** commutative `ℂ`-algebra `R` of coefficients and an arbitrary sequence
`t : ℕ → R` (the images of the jets `T_j`); `R_n` is the case of interest, and `R = ℂ, t = 0`
is the level-one model `A_r`.

* `MPoly R = MvPolynomial (Fin 2 × ℕ) R`, `ι : ℂ[u_j, v_j] → R[u_j, v_j]`;
* `mder R k` — the mode derivations of `sl₂[s]` on `R[u_j, v_j]` (`R`-linear, so `R` is inert),
  with `mder_ι` (they extend `jetDer`) and `mder_comm_ι` (commutators extend);
* `evR R` — the base-point evaluation `(u, v) = (0, 1)` with values in `R`;
* `m_cyclic` — **cyclicity over `R`**: if `evR (D_{k_1} ⋯ D_{k_ℓ} Q) = 0` in `R` for every word
  of nonnegative modes then `Q = 0`.  Proved from the proved `jet_cyclic` by applying every
  `ℂ`-linear functional `φ : R → ℂ` coefficientwise;
* `mletter R t`, `mword R t` — the model letter symbols: the level-one Adamović symbols for the
  currents, and `T_n ↦ (-J)_n + t_n` for the Sugawara letters;
* `mder_mletter_current`, `mder_mletter_sugawara` — the letter formulas
  `D_{(a,m)} (b, n) = Σ_c f^{ab}_c (c, n - m)` and `D_{(a,m)} (T, n) = m (a, n + 1 - m)` hold in
  the model, because `D` kills `R`.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SymbolModel
open VOA.AffineVOA.CorrectedR (Generator)
open VOA.AffineVOA (fabc)

noncomputable section

variable (R : Type) [CommRing R] [Algebra ℂ R]

/-- The model polynomial ring `R[u_j, v_j]`. -/
abbrev MPoly : Type := MvPolynomial (Fin 2 × ℕ) R

/-- The inclusion `ℂ[u_j, v_j] → R[u_j, v_j]`. -/
def ι : JetPoly →ₐ[ℂ] MPoly R := MvPolynomial.mapAlgHom (Algebra.ofId ℂ R)

@[simp] theorem ι_X (x : Fin 2 × ℕ) : ι R (X x) = X x := by
  simp [ι]

theorem ι_C (c : ℂ) : ι R (MvPolynomial.C c) = MvPolynomial.C (algebraMap ℂ R c) := by
  simp [ι]

/-- The mode derivations on the model ring: `R`-linear, with the jet values on `u_j, v_j`. -/
def mder (k : Fin 3 × ℕ) : Derivation R (MPoly R) (MPoly R) :=
  mkDerivation R fun x => ι R (jetDerVal k x)

@[simp] theorem mder_X (k : Fin 3 × ℕ) (x : Fin 2 × ℕ) :
    mder R k (X x) = ι R (jetDerVal k x) :=
  mkDerivation_X _ _ _

/-- The mode action as `ℂ`-linear endomorphisms. -/
def mρ (k : Fin 3 × ℕ) : Module.End ℂ (MPoly R) := (mder R k).toLinearMap.restrictScalars ℂ

@[simp] theorem mρ_apply (k : Fin 3 × ℕ) (Q : MPoly R) : mρ R k Q = mder R k Q := rfl

/-- The model derivations extend the jet derivations. -/
theorem mder_ι (k : Fin 3 × ℕ) (P : JetPoly) : mder R k (ι R P) = ι R (jetDer k P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [ι_C, ← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap,
      show (MvPolynomial.C c : JetPoly) = algebraMap ℂ JetPoly c from rfl,
      Derivation.map_algebraMap,
      map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p x hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, hp, ι_X, mder_X, jetDer_X, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, ι_X]

/-- The model derivations kill the coefficient ring. -/
theorem mder_C (k : Fin 3 × ℕ) (a : R) : mder R k (MvPolynomial.C a) = 0 := by
  rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap]

/-! ### Evaluation at the base point, with values in `R` -/

/-- Evaluation at the base point `(u, v) = (0, 1)`, with values in `R`. -/
def evR : MPoly R →ₐ[R] R := aeval fun x => algebraMap ℂ R (baseVal x)

theorem evR_ι (P : JetPoly) : evR R (ι R P) = algebraMap ℂ R (evalBase P) := by
  have h : ((evR R).restrictScalars ℂ).comp (ι R) = (Algebra.ofId ℂ R).comp evalBase :=
    MvPolynomial.algHom_ext fun x => by simp [evR, evalBase]
  exact AlgHom.congr_fun h P

theorem evR_C_mul (a : R) (Q : MPoly R) : evR R (MvPolynomial.C a * Q) = a * evR R Q := by
  rw [map_mul, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply]

/-! ### Coefficientwise functionals -/

/-- Apply a functional `φ : R → ℂ` to every coefficient. -/
def Φ (φ : R →ₗ[ℂ] ℂ) : MPoly R →ₗ[ℂ] JetPoly where
  toFun Q := Finsupp.mapRange φ φ.map_zero Q
  map_add' P Q := by
    apply MvPolynomial.ext
    intro s
    rw [coeff_add]
    change φ (coeff s (P + Q)) = φ (coeff s P) + φ (coeff s Q)
    rw [coeff_add, map_add]
  map_smul' c Q := by
    apply MvPolynomial.ext
    intro s
    rw [RingHom.id_apply, MvPolynomial.coeff_smul]
    change φ (coeff s (c • Q)) = c • φ (coeff s Q)
    rw [MvPolynomial.coeff_smul, map_smul]

theorem coeff_Φ (φ : R →ₗ[ℂ] ℂ) (Q : MPoly R) (s : Fin 2 × ℕ →₀ ℕ) :
    coeff s (Φ R φ Q) = φ (coeff s Q) := rfl

theorem Φ_C_mul_ι (φ : R →ₗ[ℂ] ℂ) (a : R) (P : JetPoly) :
    Φ R φ (MvPolynomial.C a * ι R P) = φ a • P := by
  apply MvPolynomial.ext
  intro s
  rw [coeff_Φ, coeff_C_mul, coeff_smul, smul_eq_mul]
  simp only [ι, MvPolynomial.mapAlgHom_apply, coeff_map]
  rw [mul_comm]
  change φ (algebraMap ℂ R (coeff s P) * a) = _
  rw [← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

theorem monomial_eq_C_mul_ι (s : Fin 2 × ℕ →₀ ℕ) (a : R) :
    (monomial s a : MPoly R) = MvPolynomial.C a * ι R (monomial s 1) := by
  rw [show ι R (monomial s 1) = monomial s 1 by simp [ι], C_mul_monomial, mul_one]

theorem Φ_mρ (φ : R →ₗ[ℂ] ℂ) (k : Fin 3 × ℕ) (Q : MPoly R) :
    Φ R φ (mρ R k Q) = jetRho k (Φ R φ Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [monomial_eq_C_mul_ι, Φ_C_mul_ι, mρ_apply, MvPolynomial.C_mul', Derivation.map_smul,
      mder_ι, ← MvPolynomial.C_mul', Φ_C_mul_ι, jetRho_apply, Derivation.map_smul]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

theorem Φ_word (φ : R →ₗ[ℂ] ℂ) (l : List (Fin 3 × ℕ)) (Q : MPoly R) :
    Φ R φ (VOA.CyclicEval.word (mρ R) l Q) = VOA.CyclicEval.word jetRho l (Φ R φ Q) := by
  induction l generalizing Q with
  | nil => simp [VOA.CyclicEval.word]
  | cons k l ih =>
    simp only [VOA.CyclicEval.word, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
    rw [Φ_mρ, ih]

theorem evalBase_Φ (φ : R →ₗ[ℂ] ℂ) (Q : MPoly R) : evalBase (Φ R φ Q) = φ (evR R Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [monomial_eq_C_mul_ι, Φ_C_mul_ι, evR_C_mul, evR_ι, map_smul, smul_eq_mul, mul_comm,
      mul_comm a, ← Algebra.smul_def, map_smul, smul_eq_mul]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

/-- **Cyclicity of the base-point evaluation over `R`.** -/
theorem m_cyclic (Q : MPoly R)
    (hQ : ∀ l : List (Fin 3 × ℕ), evR R (VOA.CyclicEval.word (mρ R) l Q) = 0) : Q = 0 := by
  have hΦ : ∀ φ : R →ₗ[ℂ] ℂ, Φ R φ Q = 0 := fun φ =>
    jet_cyclic _ fun l => by rw [← Φ_word, evalBase_Φ, hQ l, map_zero]
  apply MvPolynomial.ext
  intro s
  rw [coeff_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (coeff s Q)).mp fun φ => ?_
  have h := congrArg (coeff s) (hΦ φ)
  rwa [coeff_Φ, coeff_zero] at h

/-! ### The model letter symbols -/

variable (t : ℕ → R)

/-- The model letter symbols: the Adamović symbol for the currents, and `(-J)_n + t_n` for the
Sugawara letter `L_{-n-2}`. -/
def mletter : Generator × ℕ → MPoly R
  | (.current a, n) => ι R (letterSym (.current a, n))
  | (.sugawara, n) => ι R (letterSym (.sugawara, n)) + MvPolynomial.C (t n)

/-- The model word symbol: the product of the letter symbols. -/
def mword (w : List (Generator × ℕ)) : MPoly R := (w.map (mletter R t)).prod

@[simp] theorem mword_nil : mword R t [] = 1 := rfl

@[simp] theorem mword_cons (l : Generator × ℕ) (w : List (Generator × ℕ)) :
    mword R t (l :: w) = mletter R t l * mword R t w := by
  simp [mword]

/-- **Current letters in the model.** -/
theorem mder_mletter_current (a b : Fin 3) (m n : ℕ) :
    mder R (a, m) (mletter R t (.current b, n)) =
      if m ≤ n then ∑ c, fabc a b c • mletter R t (.current c, n - m) else 0 := by
  change mder R (a, m) (ι R (letterSym (.current b, n))) = _
  rw [mder_ι, jetDer_letterSym_current]
  split_ifs
  · rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul]; rfl
  · rw [map_zero]

/-- **Sugawara letters in the model** (`D` kills `t`). -/
theorem mder_mletter_sugawara (a : Fin 3) (m n : ℕ) :
    mder R (a, m) (mletter R t (.sugawara, n)) =
      if m ≤ n + 1 then (m : ℂ) • mletter R t (.current a, n + 1 - m) else 0 := by
  change mder R (a, m) (ι R (letterSym (.sugawara, n)) + MvPolynomial.C (t n)) = _
  rw [map_add, mder_C, add_zero, mder_ι, jetDer_letterSym_sugawara]
  split_ifs
  · rw [map_smul]; rfl
  · rw [map_zero]

/-! ### Commutators -/

/-- The commutator of two model derivations is the extension of the jet commutator: if the
jet derivations satisfy a linear commutation relation on the generators, so do the model
derivations, on all of `R[u_j, v_j]`. -/
theorem mder_comm_ι (k k' : Fin 3 × ℕ) (hc : ∀ x, jetDer k (jetDer k' (X x)) =
    jetDer k' (jetDer k (X x))) (Q : MPoly R) :
    mder R k (mder R k' Q) = mder R k' (mder R k Q) := by
  have h : ⁅mder R k, mder R k'⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro x
    rw [Derivation.commutator_apply, Derivation.zero_apply, mder_X, mder_X, mder_ι, mder_ι,
      ← jetDer_X, ← jetDer_X, hc, sub_self]
  have := congrArg (fun D : Derivation R (MPoly R) (MPoly R) => D Q) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at this
  exact sub_eq_zero.mp this

end

end VOA.TwoSeries.StrictModel
