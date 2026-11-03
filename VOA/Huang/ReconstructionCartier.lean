/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.Bialgebra.GroupLike
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Tannaka reconstruction — Cartier: group-likes span a finite cocommutative bialgebra

Let `A` be a finite-dimensional **cocommutative** bialgebra over `ℂ` in which every group-like
element is invertible (for `A = End(ω)` this is rigidity).  Then the group-like elements of `A`
**span** `A` (`span_isGroupLikeElem_eq_top`).  This is the density statement of Tannaka
reconstruction; it is a finite form of Cartier's theorem (commutative Hopf algebras in
characteristic zero are reduced).

Route (all finite-dimensional, no Hopf algebra theory beyond the definitions):

* `O := WithConv (A →ₗ[ℂ] ℂ)` is a commutative `ℂ`-algebra (convolution; Mathlib `convCommRing`),
  finite-dimensional, hence Artinian;
* `eq_of_pairing` — functionals `u ⊗ v` separate `A ⊗ A`;
* characters of `O` are evaluations at group-likes (`exists_groupLike_of_algHom`), and every
  maximal ideal of `O` is the kernel of a character (`exists_algHom_ker`, `ℂ` algebraically
  closed);
* `primitive_eq_zero` — **no nonzero primitive elements** (`Δx = x ⊗ 1 + 1 ⊗ x ⟹ x = 0`):
  with `n = deg minpoly x ≥ 2`, the functional `(ψ ⊗ φ) ∘ Δ` (dual to `x` and `x^{n-1}`) kills
  `x^m` for `m < n` but takes the value `n ψ(x) φ(x^{n-1}) ≠ 0` on `x^n` (characteristic zero);
* `isIdempotentElem_ker` — every character kernel `m` satisfies `m = m²`: a functional
  vanishing on `m² + ℂ·1` is a point derivation at the group-like `g`, i.e. an `x ∈ A` with
  `Δx = g ⊗ x + x ⊗ g`; then `g⁻¹x` is primitive, hence zero;
* assembly: idempotent finitely generated maximal ideals are principal, `m = (e_m)`; the product
  `e = Π e_m` is an idempotent in every maximal ideal, so `1 - e` is a unit and `e = 0`; a
  functional vanishing on all group-likes lies in every maximal ideal, hence equals itself times
  `e`, hence vanishes.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace VOA.Huang.TensorCat.Reconstruction

open Coalgebra TensorProduct WithConv Module

section Pairing

variable {A : Type*} [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]

/-- The functional `u ⊗ v` on `A ⊗ A`. -/
def pairing (u v : Module.Dual ℂ A) : A ⊗[ℂ] A →ₗ[ℂ] ℂ :=
  LinearMap.mul' ℂ ℂ ∘ₗ TensorProduct.map u v

@[simp] theorem pairing_tmul (u v : Module.Dual ℂ A) (a b : A) :
    pairing u v (a ⊗ₜ b) = u a * v b := rfl

/-- Functionals `u ⊗ v` separate `A ⊗ A`. -/
theorem eq_of_pairing {t s : A ⊗[ℂ] A} (h : ∀ u v : Module.Dual ℂ A, pairing u v t = pairing u v s) :
    t = s := by
  let b := Module.finBasis ℂ A
  let B := b.tensorProduct b
  have key : ∀ (t : A ⊗[ℂ] A) (i j : Fin (Module.finrank ℂ A)),
      B.repr t (i, j) = pairing (b.coord i) (b.coord j) t := by
    intro t i j
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [Module.Basis.tensorProduct_repr_tmul_apply, pairing_tmul, smul_eq_mul, mul_comm]
      rfl
    | add x y hx hy => simp [hx, hy]
  apply B.repr.injective
  ext ⟨i, j⟩
  rw [key, key, h]

end Pairing

section Primitive

variable {A : Type*} [Ring A] [Bialgebra ℂ A] [FiniteDimensional ℂ A]

theorem comul_pow_of_primitive {x : A} (hx : comul (R := ℂ) x = x ⊗ₜ 1 + 1 ⊗ₜ x) (m : ℕ) :
    comul (R := ℂ) (x ^ m) =
      ∑ k ∈ Finset.range (m + 1), (m.choose k : ℂ) • ((x ^ k) ⊗ₜ[ℂ] (x ^ (m - k))) := by
  have hc : Commute (x ⊗ₜ[ℂ] (1 : A)) ((1 : A) ⊗ₜ[ℂ] x) := by
    simp [Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul]
  rw [← Bialgebra.comulAlgHom_apply, map_pow, Bialgebra.comulAlgHom_apply, hx, hc.add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow, one_pow, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Nat.cast_comm, ← nsmul_eq_mul,
    Nat.cast_smul_eq_nsmul ℂ]

theorem counit_primitive [Nontrivial A] {x : A} (hx : comul (R := ℂ) x = x ⊗ₜ 1 + 1 ⊗ₜ x) :
    counit (R := ℂ) x = 0 := by
  have h := rTensor_counit_comul (R := ℂ) x
  rw [hx, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, Bialgebra.counit_one,
    add_eq_right] at h
  have h2 := congrArg (TensorProduct.lid ℂ A) h
  rw [TensorProduct.lid_tmul, map_zero] at h2
  exact (smul_eq_zero.mp h2).resolve_right one_ne_zero

/-- **No nonzero primitive elements** in a finite-dimensional bialgebra over `ℂ`. -/
theorem primitive_eq_zero {x : A} (hx : comul (R := ℂ) x = x ⊗ₜ 1 + 1 ⊗ₜ x) : x = 0 := by
  nontriviality A
  have hint : IsIntegral ℂ x := Algebra.IsIntegral.isIntegral x
  set n := (minpoly ℂ x).natDegree with hn_def
  have hn : 0 < n := minpoly.natDegree_pos hint
  have hli : LinearIndependent ℂ (fun i : Fin n => x ^ (i : ℕ)) := linearIndependent_pow x
  let P : Submodule ℂ A := Submodule.span ℂ (Set.range fun i : Fin n => x ^ (i : ℕ))
  have hpow_mem : ∀ m < n, x ^ m ∈ P := fun m hm =>
    Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩
  have hxn : x ^ n ∈ P := by
    have hmon := (minpoly.monic hint).as_sum
    have h0 := minpoly.aeval ℂ x
    rw [hmon] at h0
    simp only [map_add, map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C] at h0
    rw [← hn_def, add_eq_zero_iff_eq_neg] at h0
    rw [h0]
    refine P.neg_mem (P.sum_mem fun i hi => ?_)
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact P.smul_mem _ (hpow_mem i (Finset.mem_range.mp hi))
  have hε := counit_primitive hx
  by_cases h1 : n = 1
  · have hx1 : x ∈ P := by
      have := hxn
      rwa [h1, pow_one] at this
    have : P = Submodule.span ℂ {1} := by
      simp only [P]
      congr 1
      ext y
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        have : (i : ℕ) = 0 := by omega
        rw [this, pow_zero]
      · rintro rfl
        exact ⟨⟨0, hn⟩, pow_zero x⟩
    rw [this, Submodule.mem_span_singleton] at hx1
    obtain ⟨c, rfl⟩ := hx1
    rw [map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one] at hε
    rw [hε, zero_smul]
  · have hn2 : 2 ≤ n := by omega
    -- `ψ`: dual to `x` among `1, x, …, x^{n-1}`
    obtain ⟨ψ, hψx, hψ⟩ := Submodule.exists_le_ker_of_notMem
      (hli.notMem_span_image (s := {i : Fin n | (i : ℕ) ≠ 1}) (x := ⟨1, by omega⟩) (by simp))
    -- `φ`: dual to `x^{n-1}`, vanishing on lower powers
    obtain ⟨φ, hφx, hφ⟩ := Submodule.exists_le_ker_of_notMem
      (hli.notMem_span_image (s := {i : Fin n | (i : ℕ) < n - 1}) (x := ⟨n - 1, by omega⟩) (by simp))
    have hψ0 : ∀ k < n, k ≠ 1 → ψ (x ^ k) = 0 := fun k hk hk1 =>
      LinearMap.mem_ker.mp (hψ (Submodule.subset_span ⟨⟨k, hk⟩, hk1, rfl⟩))
    have hφ0 : ∀ k < n - 1, φ (x ^ k) = 0 := fun k hk =>
      LinearMap.mem_ker.mp (hφ (Submodule.subset_span ⟨⟨k, by omega⟩, hk, rfl⟩))
    let Λ : A →ₗ[ℂ] ℂ := pairing ψ φ ∘ₗ comul
    have hΛ : ∀ m, Λ (x ^ m) =
        ∑ k ∈ Finset.range (m + 1), (m.choose k : ℂ) * (ψ (x ^ k) * φ (x ^ (m - k))) := by
      intro m
      simp only [Λ, LinearMap.comp_apply]
      rw [comul_pow_of_primitive hx]
      simp only [map_sum, map_smul,
        pairing_tmul, smul_eq_mul]
    have hlow : ∀ m < n, Λ (x ^ m) = 0 := by
      intro m hm
      rw [hΛ]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      by_cases hk1 : k = 1
      · subst hk1
        rw [hφ0 (m - 1) (by omega), mul_zero, mul_zero]
      · rw [hψ0 k (by omega) hk1, zero_mul, mul_zero]
    have hP : P ≤ LinearMap.ker Λ := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hlow i i.2
    have hzero : Λ (x ^ n) = 0 := hP hxn
    have htop : Λ (x ^ n) = (n : ℂ) * (ψ x * φ (x ^ (n - 1))) := by
      rw [hΛ, Finset.sum_eq_single 1]
      · rw [Nat.choose_one_right, pow_one]
      · intro k hk hk1
        have hk' := Finset.mem_range.mp hk
        by_cases hkn : k = n
        · subst hkn
          rw [Nat.sub_self, hφ0 0 (by omega), mul_zero, mul_zero]
        · rw [hψ0 k (by omega) hk1, zero_mul, mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    rw [htop] at hzero
    have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [mul_eq_zero, this, false_or] at hzero
    rcases hzero with h | h
    · exact absurd (by simpa using h) hψx
    · exact absurd h hφx

end Primitive

section Convolution

variable {A : Type*} [Ring A] [Bialgebra ℂ A] [FiniteDimensional ℂ A] [IsCocomm ℂ A]

/-- The commutative convolution algebra `O = A^*`. -/
abbrev ConvO (A : Type*) [AddCommGroup A] [Module ℂ A] [CoalgebraStruct ℂ A] := WithConv (A →ₗ[ℂ] ℂ)

theorem convO_mul_apply (f g : ConvO A) (a : A) : (f * g) a = pairing f.ofConv g.ofConv (comul a) := rfl

theorem convO_one_apply (a : A) : (1 : ConvO A) a = counit (R := ℂ) a := rfl

theorem convO_smul_apply (t : ℂ) (f : ConvO A) (a : A) : (t • f) a = t * f a := rfl

theorem convO_ext {f g : ConvO A} (h : ∀ a, f a = g a) : f = g :=
  WithConv.ofConv_injective (LinearMap.ext h)

instance convOAlgebra : Algebra ℂ (ConvO A) :=
  Algebra.ofModule
    (fun t f g => convO_ext fun a => by
      simp only [convO_mul_apply, convO_smul_apply, WithConv.ofConv_smul, pairing,
        LinearMap.comp_apply, TensorProduct.map_smul_left, LinearMap.smul_apply, map_smul,
        smul_eq_mul])
    (fun t f g => convO_ext fun a => by
      simp only [convO_mul_apply, convO_smul_apply, WithConv.ofConv_smul, pairing,
        LinearMap.comp_apply, TensorProduct.map_smul_right, LinearMap.smul_apply, map_smul,
        smul_eq_mul])

instance : Module.Finite ℂ (ConvO A) :=
  Module.Finite.equiv (WithConv.linearEquiv ℂ (A →ₗ[ℂ] ℂ)).symm

instance : IsArtinianRing (ConvO A) := IsArtinianRing.of_finite ℂ (ConvO A)
instance : IsNoetherianRing (ConvO A) := IsNoetherianRing.of_finite ℂ (ConvO A)

/-- Every character of `O` is evaluation at a group-like element. -/
theorem exists_groupLike_of_algHom (χ : ConvO A →ₐ[ℂ] ℂ) :
    ∃ g : A, IsGroupLikeElem ℂ g ∧ ∀ f : ConvO A, χ f = f g := by
  let Λ : Module.Dual ℂ (Module.Dual ℂ A) :=
    χ.toLinearMap ∘ₗ (WithConv.linearEquiv ℂ (A →ₗ[ℂ] ℂ)).symm.toLinearMap
  let g := (Module.evalEquiv ℂ A).symm Λ
  have hg : ∀ f : ConvO A, χ f = f g := fun f =>
    (Module.apply_evalEquiv_symm_apply ℂ A f.ofConv Λ).symm
  refine ⟨g, ⟨?_, ?_⟩, hg⟩
  · have := hg 1
    rw [map_one, convO_one_apply] at this
    exact this.symm
  · apply eq_of_pairing
    intro u v
    have := hg (toConv u * toConv v)
    rw [map_mul, hg, hg, convO_mul_apply] at this
    rw [pairing_tmul, ← this]

/-- Every maximal ideal of `O` is the kernel of a character. -/
theorem exists_algHom_ker (m : Ideal (ConvO A)) [hm : m.IsMaximal] :
    ∃ χ : ConvO A →ₐ[ℂ] ℂ, RingHom.ker χ = m := by
  letI := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (ConvO A ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℂ m).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℂ m)
  haveI : Algebra.IsIntegral ℂ (ConvO A ⧸ m) := Algebra.IsIntegral.of_finite ℂ _
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := ConvO A ⧸ m)
  let e : ℂ ≃ₐ[ℂ] ConvO A ⧸ m := AlgEquiv.ofBijective (Algebra.ofId ℂ _) hb
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ m), ?_⟩
  ext f
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/-- **Character kernels are idempotent** (point derivations vanish), provided group-likes are
invertible. -/
theorem isIdempotentElem_ker (hunit : ∀ a : A, IsGroupLikeElem ℂ a → IsUnit a)
    (χ : ConvO A →ₐ[ℂ] ℂ) : IsIdempotentElem (RingHom.ker χ) := by
  obtain ⟨g, hgl, hg⟩ := exists_groupLike_of_algHom χ
  set m := RingHom.ker χ
  refine le_antisymm Ideal.mul_le_left ?_
  intro f hf
  by_contra hf2
  -- a functional vanishing on `m² + ℂ·1` but not on `f`
  let W : Submodule ℂ (ConvO A) := (m * m).restrictScalars ℂ ⊔ Submodule.span ℂ {1}
  have hfW : f ∉ W := by
    intro hW
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hW
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hym : y ∈ m := Ideal.mul_le_left hy
    have h1 : χ (y + c • 1) = 0 := hf
    rw [map_add, hym, zero_add, map_smul, map_one, smul_eq_mul, mul_one] at h1
    rw [h1, zero_smul, add_zero] at hf2
    exact hf2 hy
  obtain ⟨d, hdf, hdW⟩ := Submodule.exists_le_ker_of_notMem hfW
  -- `d` is evaluation at some `x ∈ A`
  let Λ : Module.Dual ℂ (Module.Dual ℂ A) :=
    d ∘ₗ (WithConv.linearEquiv ℂ (A →ₗ[ℂ] ℂ)).symm.toLinearMap
  let x := (Module.evalEquiv ℂ A).symm Λ
  have hx : ∀ u : ConvO A, d u = u x := fun u =>
    (Module.apply_evalEquiv_symm_apply ℂ A u.ofConv Λ).symm
  have hd1 : d 1 = 0 := hdW (Submodule.mem_sup_right (Submodule.mem_span_singleton_self 1))
  have hdmm : ∀ u ∈ m, ∀ v ∈ m, d (u * v) = 0 := fun u hu v hv =>
    hdW (Submodule.mem_sup_left (Ideal.mul_mem_mul hu hv))
  -- the derivation identity
  have hder : ∀ u v : ConvO A, d (u * v) = χ u * d v + χ v * d u := by
    intro u v
    have hu : u - χ u • 1 ∈ m := by
      change χ (u - χ u • 1) = 0
      rw [map_sub, map_smul, map_one, smul_eq_mul, mul_one, sub_self]
    have hv : v - χ v • 1 ∈ m := by
      change χ (v - χ v • 1) = 0
      rw [map_sub, map_smul, map_one, smul_eq_mul, mul_one, sub_self]
    have h := hdmm _ hu _ hv
    have expand : (u - χ u • 1) * (v - χ v • 1) =
        u * v - χ u • v - χ v • u + (χ u * χ v) • 1 := by
      simp only [Algebra.smul_def, map_mul]
      ring
    rw [expand, map_add, map_sub, map_sub, map_smul, map_smul, map_smul, hd1, smul_zero,
      add_zero, sub_sub, sub_eq_zero] at h
    rw [h, smul_eq_mul, smul_eq_mul]
  -- hence `Δx = g ⊗ x + x ⊗ g`
  have hcomul : comul (R := ℂ) x = g ⊗ₜ x + x ⊗ₜ g := by
    apply eq_of_pairing
    intro u v
    have := hder (toConv u) (toConv v)
    rw [hx, hx, hx, hg, hg, convO_mul_apply] at this
    rw [map_add, pairing_tmul, pairing_tmul]
    change pairing u v (comul x) = _
    rw [this]
    change u g * v x + v g * u x = u g * v x + u x * v g
    ring
  -- `g⁻¹ x` is primitive
  obtain ⟨gu, rfl⟩ := hunit g hgl
  have hginv : IsGroupLikeElem ℂ (↑gu⁻¹ : A) := isGroupLikeElem_unitsInv.mpr hgl
  have hprim : comul (R := ℂ) ((↑gu⁻¹ : A) * x) =
      ((↑gu⁻¹ : A) * x) ⊗ₜ 1 + 1 ⊗ₜ ((↑gu⁻¹ : A) * x) := by
    rw [Bialgebra.comul_mul, hginv.comul_eq_tmul_self, hcomul, mul_add,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, Units.inv_mul,
      add_comm]
  have hx0 : x = 0 := by
    have := primitive_eq_zero hprim
    have h2 : (gu : A) * ((↑gu⁻¹ : A) * x) = x := by rw [← mul_assoc, Units.mul_inv, one_mul]
    rw [← h2, this, mul_zero]
  exact hdf (by rw [hx, hx0, map_zero])

/-- **Density (finite Cartier).** In a finite-dimensional cocommutative bialgebra over `ℂ` whose
group-like elements are invertible, the group-like elements span. -/
theorem span_isGroupLikeElem_eq_top (hunit : ∀ a : A, IsGroupLikeElem ℂ a → IsUnit a) :
    Submodule.span ℂ {a : A | IsGroupLikeElem ℂ a} = ⊤ := by
  by_contra hne
  obtain ⟨v, hv⟩ : ∃ v, v ∉ Submodule.span ℂ {a : A | IsGroupLikeElem ℂ a} := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.mpr fun v _ => h v)
  obtain ⟨f, hfv, hf⟩ := Submodule.exists_le_ker_of_notMem hv
  let F : ConvO A := toConv f
  -- `F` lies in every maximal ideal
  have hFm : ∀ m : Ideal (ConvO A), m.IsMaximal → F ∈ m := by
    intro m hm
    obtain ⟨χ, rfl⟩ := exists_algHom_ker m
    obtain ⟨g, hgl, hg⟩ := exists_groupLike_of_algHom χ
    change χ F = 0
    rw [hg]
    exact hf (Submodule.subset_span hgl)
  -- each maximal ideal is generated by an idempotent
  have hidem : ∀ m : Ideal (ConvO A), m.IsMaximal → ∃ e : ConvO A, IsIdempotentElem e ∧ m = Ideal.span {e} := by
    intro m hm
    obtain ⟨χ, rfl⟩ := exists_algHom_ker m
    exact (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian _)).mp
      (isIdempotentElem_ker hunit χ)
  choose! e he hme using hidem
  have hfin := IsArtinianRing.setOf_isMaximal_finite (ConvO A)
  let s := hfin.toFinset
  let E : ConvO A := ∏ m ∈ s, e m
  have hFE : F * E = F := by
    have : ∀ t : Finset (Ideal (ConvO A)), t ⊆ s → F * ∏ m ∈ t, e m = F := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp
      | insert m t hmt ih =>
        intro hts
        have hm : m.IsMaximal := (Set.Finite.mem_toFinset hfin).mp (hts (Finset.mem_insert_self m t))
        have hFem : F * e m = F := by
          have hF := hFm m hm
          rw [hme m hm, Ideal.mem_span_singleton'] at hF
          obtain ⟨r, hr⟩ := hF
          rw [← hr, mul_assoc, (he m hm).eq]
        rw [Finset.prod_insert hmt, ← mul_assoc, hFem,
          ih (fun x hx => hts (Finset.mem_insert_of_mem hx))]
    exact this s subset_rfl
  have hEidem : IsIdempotentElem E := by
    have : ∀ t : Finset (Ideal (ConvO A)), t ⊆ s → IsIdempotentElem (∏ m ∈ t, e m) := by
      intro t
      induction t using Finset.induction_on with
      | empty => intro _; simp [IsIdempotentElem]
      | insert m t hmt ih =>
        intro hts
        rw [Finset.prod_insert hmt]
        have hm : m.IsMaximal := (Set.Finite.mem_toFinset hfin).mp (hts (Finset.mem_insert_self m t))
        exact (he m hm).mul_of_commute (Commute.all _ _)
          (ih fun x hx => hts (Finset.mem_insert_of_mem hx))
    exact this s subset_rfl
  have hEm : ∀ m : Ideal (ConvO A), m.IsMaximal → E ∈ m := by
    intro m hm
    have hms : m ∈ s := (Set.Finite.mem_toFinset hfin).mpr hm
    change ∏ m ∈ s, e m ∈ m
    rw [← Finset.mul_prod_erase s e hms]
    refine Ideal.mul_mem_right _ _ ?_
    have := Ideal.mem_span_singleton_self (e m)
    rwa [← hme m hm] at this
  have hunitE : IsUnit (1 - E) := by
    by_contra hnu
    obtain ⟨m, hm, h1m⟩ := exists_max_ideal_of_mem_nonunits (show 1 - E ∈ nonunits _ from hnu)
    exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr (by
      have := m.add_mem h1m (hEm m hm)
      rwa [sub_add_cancel] at this))
  have hE0 : E = 0 := by
    have h : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hEidem.eq, sub_self]
    exact (hunitE.mul_right_eq_zero).mp h
  have hF0 : F = 0 := by rw [← hFE, hE0, mul_zero]
  apply hfv
  have : f = 0 := WithConv.toConv_injective hF0
  rw [this, LinearMap.zero_apply]

end Convolution

end VOA.Huang.TensorCat.Reconstruction
