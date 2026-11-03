/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLRationalMain
import VOA.Huang.HKLFrobDimSimple
import VOA.Huang.HuangModularityTrace
import VOA.Huang.HuangTierReduced
import VOA.Huang.AndersonMooreMain
import VOA.Classification.COne.MainVerlindeProved

/-!
# `HKLFrobeniusDimInput`: `dim A ≠ 0` for a commutative haploid algebra with trivial twist

Let `V` be nice, `F` any fusion choice, `A` a commutative haploid algebra in `Ordinary V` with
`θ_A = 1`, and `c` a copairing with `Zig₁ c (μ ≫ q)`.  Then `c ≫ μ ≠ 0`:

* `(c, μ ≫ q)` is a symmetric self-duality of `A` (`isCentral_of_frobenius`), so for the twist
  pivotal structure `P = twistPivotal twistIso` (any right duals, `rightRigid_ordinary`)
  `tr_P(𝟙_A) = c ≫ μ ≫ q` (`twistPivotal_trL_id_frobenius`);
* `A ≅ ⨁_j M_{lab j}` (`semisimple_of_modularData`), so by cyclicity and additivity of the trace
  and Huang's dimension theorem on `Ordinary V` (`twistPivotal_trL_module`)
  `tr_P(𝟙_A) = (Σ_j d_{lab j}) • 𝟙`;
* `d ≥ 1` (pseudo-unitarity, `IsModularData.d_ge_one`; the modular data exist by the proved
  `IModData` chain) and `n ≥ 1` (`A` haploid, hence nonzero), so `Σ_j d_{lab j} ≥ 1`, while
  `c ≫ μ = 0` would force the trace to vanish; `𝟙_{𝟙} ≠ 0` since `Hom(𝟙, A) ≠ 0`.

Headlines:
* `hklFrobeniusDimInput_holds : HKLFrobeniusDimInput`;
* `hklRationalInput_holds : HKLRationalInput`;
* `VOA.Classification.COne.gannonRayhaun_hkl_final` — the forward Gannon–Rayhaun theorem
  conditional on `DLNCongruenceInput`, `GaloisSymmetryNontrivialInput`, `QExpPrinciple24Away 2`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Huang.HKLRational

open CategoryTheory MonoidalCategory Limits Module
open VOA VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.FusionUnit
  VOA.Huang.FusionProduct VOA.Huang.TensorCat.BraidRibbon VOA.Huang.HKLExt VOA.Huang.HKLNice
  VOA.Huang.HuangRigid VOA.Huang.HuangModularity VOA.Huang.TensorCat.RepPackaging

universe u

/-- **`IModData` is proved** (no hypothesis; the PBW datum comes from the theorem `VOA.pbw`): PBW
datum, Anderson–Moore, and Huang's Verlinde theorem (`huangVerlindeFusionInput_holds`). -/
theorem iModData_holds : IModData.{u} :=
  VOA.Huang.HuangTierReduced.iModData_of_verlinde_pbw_inputs
    VOA.Huang.AndersonMoore.andersonMooreInput_holds
    (VOA.Huang.VerlindeFusion.verlindeInput_of_fusion huangVerlindeFusionInput_holds)

/-- **`HKLFrobeniusDimInput`** (`dim A ≥ 1` for the twist pivotal structure). -/
theorem hklFrobeniusDimInput_holds : HKLFrobeniusDimInput.{u} := by
  classical
  intro 𝒱 _ _ V hV F
  letI := monoidalCategoryOfStronglyRational_pbw F hV.1
  letI := HexagonClose.braidedCategory_stronglyRational_pbw F hV.1
  intro A _ hcomm htw hhap q c h₁ hzero
  haveI := hcomm
  haveI := monoidalPreadditive_pbw F hV.1
  haveI := monoidalLinear_pbw F hV.1
  obtain ⟨D, hD⟩ := iModData_holds 𝒱 V hV
  obtain ⟨r⟩ := rightRigid_ordinary F hV
  letI := r
  -- `Hom(𝟙, A) ≠ 0`
  have hne : ¬ ∀ f : 𝟙_ (Ordinary V) ⟶ A, f = 0 := by
    intro h0
    haveI : Subsingleton (𝟙_ (Ordinary V) ⟶ A) := ⟨fun x y => by rw [h0 x, h0 y]⟩
    rw [finrank_zero_of_subsingleton] at hhap
    exact zero_ne_one hhap
  have hid : 𝟙 (𝟙_ (Ordinary V)) ≠ 0 := by
    intro h0
    exact hne fun f => by rw [← Category.id_comp f, h0, zero_comp]
  -- the trace through the self-duality
  have hA : (twistPivotal (θ := fun X => twistIso X) (fun f => twist_naturality f)).trL (𝟙 A) =
      c ≫ MonObj.mul ≫ q :=
    twistPivotal_trL_id_frobenius (fun f => twist_naturality f) h₁ htw
  rw [← Category.assoc, hzero, zero_comp] at hA
  -- the trace through the decomposition
  obtain ⟨n, lab, ⟨e⟩⟩ := semisimple_of_modularData D hD hV.1 A
  have hsum : (twistPivotal (θ := fun X => twistIso X) (fun f => twist_naturality f)).trL (𝟙 A) =
      (∑ j, (D.d (lab j) : ℂ)) • 𝟙 _ := by
    have h0 : 𝟙 A = e.hom ≫ 𝟙 _ ≫ e.inv := by simp
    rw [h0, trL_conj, trL_biproduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Category.id_comp, biproduct.ι_π_self]
    exact twistPivotal_trL_module hV F D hD (lab j) r
  rw [hA] at hsum
  have hs : (∑ j, (D.d (lab j) : ℂ)) = 0 := by
    rcases smul_eq_zero.mp hsum.symm with h | h
    · exact h
    · exact absurd h hid
  -- positivity
  have hn : n ≠ 0 := by
    rintro rfl
    apply hne
    intro f
    rw [← Category.comp_id f, ← e.hom_inv_id, ← Category.assoc]
    have : f ≫ e.hom = 0 := biproduct.hom_ext _ _ (fun j => j.elim0)
    rw [this, zero_comp]
  have hge : (n : ℝ) ≤ ∑ j, D.d (lab j) := by
    have := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hD.d_ge_one (lab j))
    simpa using this
  have hpos : (0 : ℝ) < ∑ j, D.d (lab j) :=
    lt_of_lt_of_le (by exact_mod_cast Nat.pos_of_ne_zero hn) hge
  have hs' : ((∑ j, D.d (lab j) : ℝ) : ℂ) = 0 := by push_cast; exact hs
  exact hpos.ne' (by exact_mod_cast hs')

/-- **`HKLRationalInput`.** -/
theorem hklRationalInput_holds : HKLRationalInput.{u} :=
  hklRationalInput_of_dim hklFrobeniusDimInput_holds

end VOA.Huang.HKLRational

namespace VOA.Classification.COne

universe u

/-- **Gannon–Rayhaun Theorem 3.1 (forward), with the whole HKL side proved.**  Conditional
on `DLNCongruenceInput`, `GaloisSymmetryNontrivialInput` and `QExpPrinciple24Away 2`. -/
theorem gannonRayhaun_hkl_final
    (hC : VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u})
    (hG : VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u})
    (hQ : SSHecke.QExpPrinciple24Away 2) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_hkl_dim hC hG hQ VOA.Huang.HKLRational.hklFrobeniusDimInput_holds

end VOA.Classification.COne
