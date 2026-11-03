/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.GradedUnitaryCohomologyFiltered
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Cohomology inherits graded unitarity (Beem–Garner Theorem 4.1), at one conformal weight

Continuation of `GradedUnitaryCohomologyKahler` and `GradedUnitaryCohomologyFiltered`.
We add to a `KahlerComplex` the data relating the modified Hermitian form `P = ⟨-|-⟩` to the
invariant **bilinear** form `B = (-,-)` and the conjugation `ρ`, exactly as in Beem–Garner
Corollary 2.24 and this repository's `VOA.GradedUnitary`:

* `h x y = B (ρ x) y` — the shape of `VOA.gradedSesq`;
* `P x y = i^{2R} h x y` for `x` of `ℜ`-degree `R` (`P_eq`): since `ρ` preserves `ℜ`-degree,
  `⟨x|y⟩ = ((σ∘ρ)x, y) = i^{2R} (ρ x, y)`. For integral `R = p` this is `(-1)^p h`,
  i.e. `VOA.signedForm h p`;
* `ρ` maps each harmonic piece of ghost number zero onto itself (`ρ_maps`, `ρ_onto`). In the
  source this follows from `ρ ∘ 𝐐⁻ = i 𝐐⁺ ∘ ρ` (before Proposition 4.2), `ρ² = s`, and the fact
  that `ρ` preserves `ℜ`-degree and sends ghost number `g` to `-g` (Remark 2.31).

The harmonic space of ghost number zero is the model of `H⁰` (Proposition 4.2 / Remark 4.4:
every class has a unique harmonic representative, and the class lies in the `R`-th graded
piece iff its harmonic representative does; see `cohomFilt_eq_map_harm`). On it we take the
induced flag `G_j` (harmonic vectors of ghost number zero with `2R ∈ [L, j]`) and prove:

* `layer_eq`: the layer `G_j ∩ B-orth(G_{j-1})` is exactly the harmonic piece of bidegree
  `(j, 0)`;
* `flag_nondegenerate`: `B` restricted to every `G_j` is nondegenerate (Beem–Garner Lemma 4.3);
* `layer_pos`: on the layer `j`, `i^j h` is positive definite (Lemma 4.5), and
  `layer_signed_pos`: for `j = 2p` this is `IsPosOn (signedForm h p)`, the exact clause of
  `VOA.LayerPositive`.

These are the clauses (iv) and (vi) of `VOA.GradedUnitaryAt`, stated for the abstract harmonic
model of `H⁰` at one conformal weight. All proved outright from the listed hypotheses.
-/

namespace VOA.GradedUnitaryCohomology

open VOA.LeeYangCosetTransfer
open Module (finrank)

universe u

variable {K : Type u} [AddCommGroup K] [Module ℂ K]

namespace KahlerComplex

variable (C : KahlerComplex K)

/-- The induced flag on the harmonic model of `H⁰`: ghost number zero, `2R ∈ [L, j]`. -/
def flag (L j : ℤ) : Submodule ℂ K :=
  C.harm ⊓ C.degOn (KahlerComplex.rowSet (Finset.Icc L j) 0)

/-- The flag is the span of its harmonic bigraded pieces. -/
theorem flag_eq_iSup (L j : ℤ) :
    C.flag L j = ⨆ i ∈ Finset.Icc L j, C.harmDeg (i, 0) := by
  apply le_antisymm
  · unfold flag
    generalize Finset.Icc L j = S
    induction S using Finset.induction_on with
    | empty =>
      have : KahlerComplex.rowSet (∅ : Finset ℤ) 0 = ∅ := by
        ext a; simp [KahlerComplex.rowSet]
      rw [this, C.degOn_empty, inf_bot_eq]; exact bot_le
    | insert i S hi ih =>
      refine (C.harm_inf_row_insert i S hi 0).trans (sup_le ?_ (ih.trans ?_))
      · exact le_biSup (fun i => C.harmDeg (i, 0)) (Finset.mem_insert_self i S)
      · exact biSup_mono fun k hk => Finset.mem_insert_of_mem hk
  · refine iSup₂_le fun i hi => ?_
    exact inf_le_inf_left _ (C.deg_le_degOn ⟨Finset.mem_coe.mp hi, rfl⟩)

theorem harmDeg_le_flag {L i j : ℤ} (hLi : L ≤ i) (hij : i ≤ j) :
    C.harmDeg (i, 0) ≤ C.flag L j := by
  rw [flag_eq_iSup]
  exact le_biSup (fun i => C.harmDeg (i, 0)) (Finset.mem_Icc.mpr ⟨hLi, hij⟩)

/-- The flag is increasing by one harmonic piece at a time. -/
theorem flag_succ {L j : ℤ} (hLj : L ≤ j) :
    C.flag L j = C.harmDeg (j, 0) ⊔ C.flag L (j - 1) := by
  rw [flag_eq_iSup, flag_eq_iSup]
  have hS : Finset.Icc L j = insert j (Finset.Icc L (j - 1)) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hS, Finset.iSup_insert]

end KahlerComplex

/-- **The form/conjugation datum on a Kähler complex.** See the module docstring. -/
structure GUData (C : KahlerComplex K) where
  /-- The invariant bilinear form `(-,-)` at this conformal weight. -/
  B : LinearMap.BilinForm ℂ K
  /-- The conjugation `ρ` (antilinear). -/
  ρ : K →ₗ⋆[ℂ] K
  /-- The sesquilinear form `h x y = (ρ x, y)`. -/
  h : SesqForm K
  h_eq : ∀ x y, h x y = B (ρ x) y
  /-- `⟨x|y⟩ = i^{2R} (ρ x, y)` on vectors of `ℜ`-degree `R = j/2`. -/
  P_eq : ∀ j g : ℤ, ∀ x ∈ C.deg (j, g), ∀ y, C.P x y = Complex.I ^ j * h x y
  /-- `ρ` maps harmonic vectors of bidegree `(j, 0)` to harmonic vectors of bidegree `(j, 0)`. -/
  ρ_maps : ∀ j : ℤ, ∀ x ∈ C.harmDeg (j, 0), ρ x ∈ C.harmDeg (j, 0)
  /-- ... and onto them. -/
  ρ_onto : ∀ j : ℤ, ∀ y ∈ C.harmDeg (j, 0), ∃ x ∈ C.harmDeg (j, 0), ρ x = y

namespace GUData

variable {C : KahlerComplex K} (G : GUData C)

theorem I_zpow_ne_zero (j : ℤ) : Complex.I ^ j ≠ 0 := zpow_ne_zero _ Complex.I_ne_zero

/-- Harmonic pieces of ghost number zero and distinct `ℜ`-degree are `B`-orthogonal. -/
theorem B_orth {i j : ℤ} (hij : i ≠ j) {x y : K} (hx : x ∈ C.harmDeg (i, 0))
    (hy : y ∈ C.harmDeg (j, 0)) : G.B x y = 0 := by
  obtain ⟨x', hx', rfl⟩ := G.ρ_onto i x hx
  have hP : C.P x' y = 0 :=
    C.orth (i, 0) (j, 0) (by simp [hij]) x' hx'.2 y hy.2
  rw [G.P_eq i 0 x' hx'.2, mul_eq_zero] at hP
  rw [← G.h_eq]
  exact hP.resolve_left (I_zpow_ne_zero i)

/-- A vector of the flag `B`-paired to zero against the whole flag (in the first slot)
vanishes: right-separation of `B` on `G_j`. -/
theorem eq_zero_of_B_flag {L j : ℤ} {m : K} (hm : m ∈ C.flag L j)
    (h0 : ∀ n ∈ C.flag L j, G.B n m = 0) : m = 0 := by
  apply C.eq_zero_of_self
  have hall : ∀ w ∈ C.flag L j, C.P w m = 0 := by
    intro w hw
    rw [C.flag_eq_iSup] at hw
    refine Submodule.iSup_induction (fun i => ⨆ (_ : i ∈ Finset.Icc L j), C.harmDeg (i, 0))
      (motive := fun w => C.P w m = 0) hw ?_ (C.P.zero_left m)
      (fun x x' h h' => by beta_reduce at h h' ⊢; rw [C.P.add_left, h, h', add_zero])
    intro i w hw
    by_cases hi : i ∈ Finset.Icc L j
    · beta_reduce at hw; rw [iSup_pos hi] at hw
      have hρ : G.ρ w ∈ C.flag L j := by
        rw [C.flag_eq_iSup]
        exact le_biSup (fun i => C.harmDeg (i, 0)) hi (G.ρ_maps i w hw)
      rw [G.P_eq i 0 w hw.2, G.h_eq, h0 _ hρ, mul_zero]
    · beta_reduce at hw; rw [iSup_neg hi] at hw
      rw [(Submodule.mem_bot ℂ).mp hw, C.P.zero_left]
  exact hall m hm

/-- **Nondegeneracy of the induced flag** (Beem–Garner Lemma 4.3): `B` restricted to every
step of the flag is nondegenerate. -/
theorem flag_nondegenerate [FiniteDimensional ℂ K] (L j : ℤ) :
    (G.B.restrict (C.flag L j)).Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingRight
  intro y hy
  apply Subtype.ext
  exact G.eq_zero_of_B_flag y.2 fun n hn => hy ⟨n, hn⟩

/-- The layer of the flag at `j`: `G_j ∩ B-orth(G_{j-1})`, as in `VOA.GradedFlag.layer`. -/
def layer (L j : ℤ) : Submodule ℂ K := C.flag L j ⊓ G.B.orthogonal (C.flag L (j - 1))

/-- `B` pairs the flag below `j` trivially with the harmonic piece of degree `j`. -/
theorem B_flag_harmDeg {L j : ℤ} {n x : K} (hn : n ∈ C.flag L (j - 1))
    (hx : x ∈ C.harmDeg (j, 0)) : G.B n x = 0 := by
  rw [C.flag_eq_iSup] at hn
  refine Submodule.iSup_induction (fun i => ⨆ (_ : i ∈ Finset.Icc L (j - 1)), C.harmDeg (i, 0))
    (motive := fun n => G.B n x = 0) hn ?_ (by simp)
    (fun a b ha hb => by beta_reduce at ha hb ⊢; rw [map_add, LinearMap.add_apply, ha, hb,
      add_zero])
  intro i w hw
  by_cases hi : i ∈ Finset.Icc L (j - 1)
  · beta_reduce at hw; rw [iSup_pos hi] at hw
    have : i ≠ j := by rw [Finset.mem_Icc] at hi; omega
    exact G.B_orth this hw hx
  · beta_reduce at hw; rw [iSup_neg hi] at hw
    rw [(Submodule.mem_bot ℂ).mp hw]; simp

/-- **The layers are the harmonic pieces.** -/
theorem layer_eq {L j : ℤ} (hLj : L ≤ j) : G.layer L j = C.harmDeg (j, 0) := by
  apply le_antisymm
  · rintro x ⟨hxG, hxO⟩
    rw [C.flag_succ hLj] at hxG
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hxG
    have hb0 : b = 0 := by
      apply G.eq_zero_of_B_flag hb
      intro n hn
      have h1 : G.B n (a + b) = 0 := hxO n hn
      rwa [map_add, G.B_flag_harmDeg hn ha, zero_add] at h1
    rw [hb0, add_zero]; exact ha
  · intro x hx
    exact ⟨C.harmDeg_le_flag hLj le_rfl hx, fun n hn => G.B_flag_harmDeg hn hx⟩

/-- **Positivity on the layers** (Beem–Garner Lemma 4.5): on the layer `j` (`R = j/2`), the
twisted form `i^j h` is positive definite. -/
theorem layer_pos {L j : ℤ} (hLj : L ≤ j) {x : K} (hx : x ∈ G.layer L j) (hne : x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Complex.I ^ j * G.h x x = (r : ℂ) := by
  rw [G.layer_eq hLj] at hx
  rw [← G.P_eq j 0 x hx.2]
  exact C.pos x Submodule.mem_top hne

/-- **The project's clause (vi)**: for integral `R = p` (`j = 2p`) the layer form is
`signedForm h p = (-1)^p h`, and it is positive on the layer. -/
theorem layer_signed_pos {L : ℤ} (p : ℕ) (hL : L ≤ 2 * (p : ℤ)) :
    IsPosOn (signedForm G.h p) (G.layer L (2 * (p : ℤ))) := by
  intro x hx hne
  obtain ⟨r, hr, hrx⟩ := G.layer_pos hL hx hne
  refine ⟨r, hr, ?_⟩
  have : Complex.I ^ (2 * (p : ℤ)) = (-1 : ℂ) ^ p := by
    rw [zpow_mul, zpow_two, Complex.I_mul_I, zpow_natCast]
  rw [signedForm_apply, ← this, hrx]

end GUData

end VOA.GradedUnitaryCohomology
