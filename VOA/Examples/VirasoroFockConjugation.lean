/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroTopSymbol

/-!
# Complex conjugation in the Feigin--Fuchs realization

This file supplies the concrete real-form calculation needed to construct the canonical real
structure on a Virasoro vacuum module at real central charge.  Coefficientwise conjugation of the
polynomial Fock space intertwines the oscillator and linear-dilaton actions after conjugating their
parameters.  In particular, a real background charge gives a conjugation commuting with every
Virasoro mode, and every Virasoro creation word is fixed.
-/

set_option linter.style.longLine false

namespace VOA

open scoped BigOperators
open MvPolynomial
open Module (End)
open VOA.VirModule
open UniversalEnvelopingAlgebra

/-- Complex conjugation as a semilinear map over `starRingEnd ℂ`. -/
noncomputable def complexConjSL : ℂ →ₛₗ[starRingEnd ℂ] ℂ where
  toFun z := (starRingEnd ℂ) z
  map_add' x y := map_add _ x y
  map_smul' x y := by simp only [smul_eq_mul, map_mul]

/-- Coefficientwise conjugation in an arbitrary complex basis. -/
noncomputable def basisConj {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) : V →ₛₗ[starRingEnd ℂ] V where
  toFun v := b.repr.symm ((Finsupp.mapRange.linearMap complexConjSL) (b.repr v))
  map_add' x y := by rw [map_add, map_add, map_add]
  map_smul' x y := by simp only [map_smulₛₗ, RingHom.id_apply]

/-- Conjugating coordinates fixes each chosen basis vector, whose coordinates are zero and one. -/
@[simp] theorem basisConj_basis {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) (i : ι) : basisConj b (b i) = b i := by
  simp [basisConj, complexConjSL]

/-- Conjugating coordinates twice returns the original vector. This makes the chosen conjugation an involution. -/
@[simp] theorem basisConj_sq {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) (v : V) : basisConj b (basisConj b v) = v := by
  apply b.repr.injective
  ext i
  simp [basisConj, complexConjSL]

/-- Coefficientwise complex conjugation on the polynomial Fock space. -/
noncomputable def fockConj : Fock →+ Fock :=
  (MvPolynomial.map (starRingEnd ℂ)).toAddMonoidHom

/-- Fock conjugation is precisely complex conjugation of every polynomial coefficient; oscillator variables are retained. -/
@[simp] theorem fockConj_apply (p : Fock) :
    fockConj p = MvPolynomial.map (starRingEnd ℂ) p := rfl

/-- A constant Fock polynomial is conjugated by conjugating its complex value. -/
@[simp] theorem fockConj_C (z : ℂ) :
    fockConj (MvPolynomial.C z) = MvPolynomial.C ((starRingEnd ℂ) z) := by
  simp [fockConj]

/-- Each oscillator variable has real coefficient one and is fixed by Fock conjugation. -/
@[simp] theorem fockConj_X (i : ℕ) : fockConj (X i : Fock) = X i := by
  simp [fockConj]

/-- The Fock vacuum, the constant polynomial one, is fixed by conjugation. -/
@[simp] theorem fockConj_one : fockConj (1 : Fock) = 1 := by
  simp [fockConj]

/-- Coefficient conjugation respects polynomial products, so conjugating a product of creation variables can be performed factor by factor. -/
theorem fockConj_mul (p q : Fock) : fockConj (p * q) = fockConj p * fockConj q := by
  change MvPolynomial.map (starRingEnd ℂ) (p * q) =
    MvPolynomial.map (starRingEnd ℂ) p * MvPolynomial.map (starRingEnd ℂ) q
  rw [map_mul]

/-- Conjugating a scalar multiple conjugates the scalar as well as the state. This is the semilinearity law rather than complex linearity. -/
theorem fockConj_smul (z : ℂ) (p : Fock) :
    fockConj (z • p) = (starRingEnd ℂ) z • fockConj p := by
  simp [fockConj, Algebra.smul_def]

/-- The semilinear packaging of coefficientwise Fock conjugation. -/
noncomputable def fockConjSL : Fock →ₛₗ[starRingEnd ℂ] Fock where
  toFun := fockConj
  map_add' := map_add fockConj
  map_smul' := fockConj_smul

/-- Differentiation with respect to an oscillator variable commutes with coefficient conjugation because its integer multiplicities are real. -/
theorem fockConj_pderiv (i : ℕ) (p : Fock) :
    fockConj (pderiv i p) = pderiv i (fockConj p) := by
  exact (MvPolynomial.pderiv_map).symm

/-- Coefficientwise conjugation is an involution. -/
@[simp] theorem fockConj_sq (p : Fock) : fockConj (fockConj p) = p := by
  rw [fockConj_apply, fockConj_apply, MvPolynomial.map_map]
  convert MvPolynomial.map_id p using 1
  ext z
  simp

/-- Conjugation transports a level-`k` oscillator to the level-`conj k` oscillator. -/
theorem fockConj_osc (k : ℂ) (n : ℤ) (p : Fock) :
    fockConj (osc k n p) = osc ((starRingEnd ℂ) k) n (fockConj p) := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · rw [osc_apply_neg k hn, osc_apply_neg ((starRingEnd ℂ) k) hn, fockConj_mul,
      fockConj_X]
  · rw [osc_zero, osc_zero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
  · rw [osc_apply_pos k hn, osc_apply_pos ((starRingEnd ℂ) k) hn,
      fockConj_smul, fockConj_smul, fockConj_pderiv]
    congr 1
    simp

/-- Conjugation transports each normal-ordered Sugawara summand. -/
theorem fockConj_sugTerm (k : ℂ) (m j : ℤ) (p : Fock) :
    fockConj (sugTerm k m j p) =
      sugTerm ((starRingEnd ℂ) k) m j (fockConj p) := by
  rw [sugTerm_apply, sugTerm_apply]
  split_ifs <;> rw [fockConj_osc, fockConj_osc]

/-- Conjugation transports the Sugawara modes after conjugating the Heisenberg level. -/
theorem fockConj_Lvir (k : ℂ) (m : ℤ) (p : Fock) :
    fockConj (Lvir k m p) = Lvir ((starRingEnd ℂ) k) m (fockConj p) := by
  classical
  rw [Lvir_apply', Lvir_apply', fockConj_smul]
  have hfin : (Function.support (fun j : ℤ => sugTerm k m j p)).Finite :=
    sugTerm_support_finite k m p
  rw [map_finsum fockConj hfin]
  have hscalar : (starRingEnd ℂ) (1 / (2 * k)) =
      1 / (2 * (starRingEnd ℂ) k) := by
    rw [map_div₀, map_one, map_mul, map_ofNat]
  rw [hscalar]
  exact congrArg (fun x : Fock => (1 / (2 * (starRingEnd ℂ) k)) • x)
    (finsum_congr fun j => fockConj_sugTerm k m j p)

/-- The level-one Sugawara action commutes with coefficientwise conjugation. -/
theorem fockConj_Lvir_one (m : ℤ) (p : Fock) :
    fockConj (Lvir 1 m p) = Lvir 1 m (fockConj p) := by
  simpa using fockConj_Lvir (1 : ℂ) m p

/-- Conjugation transports the linear-dilaton Virasoro action after conjugating the background
charge. -/
theorem fockConj_Lld (lam : ℂ) (m : ℤ) (p : Fock) :
    fockConj (Lld lam m p) = Lld ((starRingEnd ℂ) lam) m (fockConj p) := by
  rw [Lld, Lld, LinearMap.add_apply, LinearMap.add_apply, map_add, fockConj_Lvir_one,
    LinearMap.smul_apply, LinearMap.smul_apply, fockConj_smul, fockConj_osc]
  congr 1
  simp only [map_mul, map_add, map_intCast, map_one]

/-- At a real background charge, coefficientwise conjugation commutes with every linear-dilaton
Virasoro mode. -/
theorem fockConj_Lld_of_fixed {lam : ℂ} (hlam : (starRingEnd ℂ) lam = lam)
    (m : ℤ) (p : Fock) : fockConj (Lld lam m p) = Lld lam m (fockConj p) := by
  rw [fockConj_Lld, hlam]

/-- Conjugation transports a Feigin--Fuchs creation word by conjugating its background charge. -/
theorem fockConj_fockWordVir (lam : ℂ) (ws : List ℕ) :
    fockConj (fockWordVir lam ws) = fockWordVir ((starRingEnd ℂ) lam) ws := by
  induction ws with
  | nil => rw [fockWordVir_nil, fockWordVir_nil, fockConj_one]
  | cons i ws ih => rw [fockWordVir_cons, fockWordVir_cons, fockConj_Lld, ih]

/-- Every Virasoro creation word is real when the background charge is real. -/
theorem fockConj_fockWordVir_of_fixed {lam : ℂ} (hlam : (starRingEnd ℂ) lam = lam)
    (ws : List ℕ) : fockConj (fockWordVir lam ws) = fockWordVir lam ws := by
  rw [fockConj_fockWordVir, hlam]

/-! ## Conjugation on the universal Virasoro vacuum module -/

/-- Coefficientwise conjugation in the global sorted-word basis of `V(c,0)`. -/
noncomputable def virBasisConj (c : ℂ) : VirUniv c →ₛₗ[starRingEnd ℂ] VirUniv c :=
  basisConj (sortedBasisVir c)

/-- The conjugation defined by the global partition basis fixes every sorted Virasoro creation word, by construction. -/
@[simp] theorem virBasisConj_sorted (c : ℂ) (w : {w : List ℕ // SortedWord w}) :
    virBasisConj c (negWordVir c w.1) = negWordVir c w.1 := by
  rw [show negWordVir c w.1 = sortedBasisVir c w from (sortedBasisVir_apply c w).symm]
  exact basisConj_basis (sortedBasisVir c) w

/-- Conjugation in the universal vacuum partition basis squares to the identity. This holds at every charge; compatibility with real Fock conjugation is a separate statement. -/
@[simp] theorem virBasisConj_sq (c : ℂ) (v : VirUniv c) :
    virBasisConj c (virBasisConj c v) = v := basisConj_sq (sortedBasisVir c) v

/-- The partition-basis conjugation is transported by the Feigin--Fuchs embedding to ordinary
coefficientwise conjugation on Fock space, whenever the background charge is real. -/
theorem fockMap_virBasisConj {c lam : ℂ} (hlam : 1 - 12 * lam ^ 2 = c)
    (hreal : (starRingEnd ℂ) lam = lam) (v : VirUniv c) :
    fockMap hlam (virBasisConj c v) = fockConj (fockMap hlam v) := by
  have hmaps : (fockMap hlam).comp (virBasisConj c) =
      fockConjSL.comp (fockMap hlam) := by
    apply (sortedBasisVir c).ext
    intro w
    rw [LinearMap.comp_apply, LinearMap.comp_apply, sortedBasisVir_apply]
    change fockMap hlam (virBasisConj c (negWordVir c w.1)) =
      fockConj (fockMap hlam (negWordVir c w.1))
    rw [virBasisConj_sorted, fockMap_negWordVir,
      fockConj_fockWordVir_of_fixed hreal]
  exact LinearMap.congr_fun hmaps v

/-- The Feigin--Fuchs embedding intertwines the abstract and Fock Virasoro modes. -/
theorem fockMap_Lop {c lam : ℂ} (hlam : 1 - 12 * lam ^ 2 = c) (m : ℤ)
    (v : VirUniv c) : fockMap hlam (Lop c m v) = Lld lam m (fockMap hlam v) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (vacIdeal c) v
  rw [Lop, virVacRho_mk, fockMap_mk, fockMap_mk]
  rw [map_mul, Module.End.mul_apply, evAlg, lift_ι_apply, linDilRho_L]

/-- At a real Feigin--Fuchs parameter, partition-basis conjugation commutes with every abstract
Virasoro mode. -/
theorem virBasisConj_Lop {c lam : ℂ} (hlam : 1 - 12 * lam ^ 2 = c)
    (hreal : (starRingEnd ℂ) lam = lam) (m : ℤ) (v : VirUniv c) :
    virBasisConj c (Lop c m v) = Lop c m (virBasisConj c v) := by
  apply fockMap_injective hlam
  rw [fockMap_virBasisConj hlam hreal, fockMap_Lop, fockConj_Lld_of_fixed hreal,
    fockMap_Lop, fockMap_virBasisConj hlam hreal]

end VOA
