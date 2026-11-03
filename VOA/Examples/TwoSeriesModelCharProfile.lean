/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesModelCharGF

/-!
# Gordon colour profiles and their Feigin–Stoyanovsky functions

A *profile* is a list `P = [r_0, r_1, …, r_k]`: `r_c` blocks of colour `c`, sorted by colour.
The blocks are `Fin (nbL P)`; a block of colour `c` carries `c` *slots* (`Fin (tsL P)` in all);
`rhoL P` sends a slot to its block and `grpL P` to its *copy* `0, 1, …` (the `i`-th slot of a
block lies in copy `i`).  The copies are nested: copy `i` meets exactly the blocks of colour
`> i`.

* `card_rhoL` — the fibre of `rhoL` over a block has the block's colour as size;
* `rhoL_grpL_inj`, `grpL_lt_colL` — the slots of a block lie in distinct copies `< colour`.

The unsymmetrized FS function `gFS P x` is the product over copies `i` of `Π_{u ≠ w ∈ copy i}
(x_u - x_w)` times elementary-symmetric monomials of the copy (`topL`); `FL P x` is its
symmetrization.

* `gFS_vanish` — `gFS` dies under any map identifying two slots of the same copy;
* `gFS_rename_congr` — `gFS` renamed along two maps injective on copies with the same copy
  images agree;
* `FL_collKill` — **`FL P x` is killed by collisions of `length P` variables** (pigeonhole);
* `topL_mul_mainL` — `topL · rename rhoL gFS = VL · FamL` (the main term factorizes).

Everything is proved outright.
-/

namespace VOA.TwoSeries.ModelChar

open MvPolynomial VOA.SymbolModel VOA.TwoSeries.StrictModel VOA.JetProduct
open scoped BigOperators

noncomputable section

/-! ### Profiles, blocks and slots -/

/-- The number of blocks. -/
def nbL : List ℕ → ℕ
  | [] => 0
  | r :: P => r + nbL P

/-- The number of slots (the `T`-degree). -/
def tsL : List ℕ → ℕ
  | [] => 0
  | _ :: P => nbL P + tsL P

/-- The colour of each block. -/
def colL : (P : List ℕ) → Fin (nbL P) → ℕ
  | [] => Fin.elim0
  | r :: P => Fin.append (fun _ : Fin r => 0) (fun b => colL P b + 1)

/-- The block of each slot. -/
def rhoL : (P : List ℕ) → Fin (tsL P) → Fin (nbL P)
  | [] => Fin.elim0
  | r :: P => Fin.append (Fin.natAdd r) (fun v => Fin.natAdd r (rhoL P v))

/-- The copy of each slot. -/
def grpL : (P : List ℕ) → Fin (tsL P) → ℕ
  | [] => Fin.elim0
  | _ :: P => Fin.append (fun _ : Fin (nbL P) => 0) (fun v => grpL P v + 1)

theorem rhoL_cons_castAdd (r : ℕ) (P : List ℕ) (i : Fin (nbL P)) :
    rhoL (r :: P) (Fin.castAdd (tsL P) i) = Fin.natAdd r i := by
  simp [rhoL, Fin.append_left]

theorem rhoL_cons_natAdd (r : ℕ) (P : List ℕ) (v : Fin (tsL P)) :
    rhoL (r :: P) (Fin.natAdd (nbL P) v) = Fin.natAdd r (rhoL P v) := by
  simp [rhoL, Fin.append_right]

theorem grpL_cons_castAdd (r : ℕ) (P : List ℕ) (i : Fin (nbL P)) :
    grpL (r :: P) (Fin.castAdd (tsL P) i) = 0 := by
  simp [grpL, Fin.append_left]

theorem grpL_cons_natAdd (r : ℕ) (P : List ℕ) (v : Fin (tsL P)) :
    grpL (r :: P) (Fin.natAdd (nbL P) v) = grpL P v + 1 := by
  simp [grpL, Fin.append_right]

theorem colL_cons_castAdd (r : ℕ) (P : List ℕ) (i : Fin r) :
    colL (r :: P) (Fin.castAdd (nbL P) i) = 0 := by
  simp [colL, Fin.append_left]

theorem colL_cons_natAdd (r : ℕ) (P : List ℕ) (b : Fin (nbL P)) :
    colL (r :: P) (Fin.natAdd r b) = colL P b + 1 := by
  simp [colL, Fin.append_right]

/-- The slots of a block lie in distinct copies. -/
theorem rhoL_grpL_inj : ∀ (P : List ℕ) (v w : Fin (tsL P)), rhoL P v = rhoL P w →
    grpL P v = grpL P w → v = w
  | [], v, _, _, _ => Fin.elim0 v
  | r :: P, v, w, h1, h2 => by
    revert h1 h2
    refine Fin.addCases (fun i => ?_) (fun v' => ?_) v <;>
      refine Fin.addCases (fun j => ?_) (fun w' => ?_) w
    · intro h1 _
      rw [rhoL_cons_castAdd, rhoL_cons_castAdd] at h1
      rw [Fin.natAdd_injective (nbL P) r h1]
    · intro _ h2
      rw [grpL_cons_castAdd, grpL_cons_natAdd] at h2; omega
    · intro _ h2
      rw [grpL_cons_castAdd, grpL_cons_natAdd] at h2; omega
    · intro h1 h2
      rw [rhoL_cons_natAdd, rhoL_cons_natAdd] at h1
      have h1' := Fin.natAdd_injective (nbL P) r h1
      rw [grpL_cons_natAdd, grpL_cons_natAdd, Nat.add_right_cancel_iff] at h2
      rw [rhoL_grpL_inj P v' w' h1' h2]

/-- A slot's copy is below its block's colour. -/
theorem grpL_lt_colL : ∀ (P : List ℕ) (v : Fin (tsL P)), grpL P v < colL P (rhoL P v)
  | [], v => Fin.elim0 v
  | r :: P, v => by
    refine Fin.addCases (fun i => ?_) (fun v' => ?_) v
    · rw [grpL_cons_castAdd, rhoL_cons_castAdd, colL_cons_natAdd]; omega
    · rw [grpL_cons_natAdd, rhoL_cons_natAdd, colL_cons_natAdd]
      have := grpL_lt_colL P v'
      omega

theorem card_filter_fin_add {m n : ℕ} (p : Fin (m + n) → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = (Finset.univ.filter fun i : Fin m => p (Fin.castAdd n i)).card +
      (Finset.univ.filter fun j : Fin n => p (Fin.natAdd m j)).card := by
  simp only [Finset.card_filter]
  rw [Fin.sum_univ_add]

/-- The fibre of `rhoL` over a block has the block's colour as size. -/
theorem card_rhoL : ∀ (P : List ℕ) (b : Fin (nbL P)),
    (Finset.univ.filter fun v => rhoL P v = b).card = colL P b
  | [], b => Fin.elim0 b
  | r :: P, b => by
    show (Finset.univ.filter fun v : Fin (nbL P + tsL P) => rhoL (r :: P) v = b).card = _
    rw [card_filter_fin_add (m := nbL P) (n := tsL P)]
    revert b
    refine fun b => Fin.addCases (fun i => ?_) (fun b' => ?_) b
    · rw [colL_cons_castAdd]
      have h1 : (Finset.univ.filter fun i' : Fin (nbL P) =>
          rhoL (r :: P) (Fin.castAdd (tsL P) i') = Fin.castAdd (nbL P) i) = ∅ := by
        ext i'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rw [rhoL_cons_castAdd]
        intro h; exact absurd (congrArg Fin.val h) (by simp; omega)
      have h2 : (Finset.univ.filter fun v : Fin (tsL P) =>
          rhoL (r :: P) (Fin.natAdd (nbL P) v) = Fin.castAdd (nbL P) i) = ∅ := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rw [rhoL_cons_natAdd]
        intro h; exact absurd (congrArg Fin.val h) (by simp; omega)
      rw [h1, h2]; rfl
    · rw [colL_cons_natAdd, ← card_rhoL P b']
      have h1 : (Finset.univ.filter fun i' : Fin (nbL P) =>
          rhoL (r :: P) (Fin.castAdd (tsL P) i') = Fin.natAdd r b').card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨b', ?_⟩
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        rw [rhoL_cons_castAdd]
        exact ⟨fun h => Fin.natAdd_injective (nbL P) r h, fun h => h ▸ rfl⟩
      have h2 : (Finset.univ.filter fun v : Fin (tsL P) =>
          rhoL (r :: P) (Fin.natAdd (nbL P) v) = Fin.natAdd r b') =
            (Finset.univ.filter fun v => rhoL P v = b') := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [rhoL_cons_natAdd]
        exact ⟨fun h => Fin.natAdd_injective (nbL P) r h, fun h => h ▸ rfl⟩
      rw [h1, h2, add_comm]

/-! ### Slot assignments: abstract combinatorics -/

section Assign

variable {s K : ℕ}

/-- Two slots in the same block and the same copy coincide. -/
def ValidA (Θ : Fin s → Fin K) (grp : Fin s → ℕ) : Prop :=
  ∀ v w, Θ v = Θ w → grp v = grp w → v = w

instance (Θ : Fin s → Fin K) (grp : Fin s → ℕ) : Decidable (ValidA Θ grp) := by
  unfold ValidA; infer_instance

theorem card_grp_lt_eq_sum (Θ : Fin s → Fin K) (grp : Fin s → ℕ) (j : ℕ) :
    (Finset.univ.filter fun v => grp v < j).card =
      ∑ b, (Finset.univ.filter fun v => Θ v = b ∧ grp v < j).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Θ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

theorem card_block_grp_lt_le {Θ : Fin s → Fin K} {grp : Fin s → ℕ} (hv : ValidA Θ grp)
    (b : Fin K) (j : ℕ) :
    (Finset.univ.filter fun v => Θ v = b ∧ grp v < j).card ≤
      min (Finset.univ.filter fun v => Θ v = b).card j := by
  classical
  refine le_min (Finset.card_le_card fun v hv => ?_) ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢; exact hv.1
  · calc (Finset.univ.filter fun v => Θ v = b ∧ grp v < j).card
        ≤ (Finset.range j).card := by
          apply Finset.card_le_card_of_injOn grp
          · intro v hv
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
            simp [hv.2]
          · intro v hv w hw h
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv hw
            exact hv' v w (hv.1.trans hw.1.symm) h
      _ = j := Finset.card_range j
  where hv' := hv

/-- The copies of a block's slots fill `{0, …, c_b - 1}` when they are all below `c_b`. -/
theorem image_grp_eq_range {Θ : Fin s → Fin K} {grp : Fin s → ℕ} (hv : ValidA Θ grp)
    (hlt : ∀ v, grp v < (Finset.univ.filter fun w => Θ w = Θ v).card) (b : Fin K) :
    (Finset.univ.filter fun v => Θ v = b).image grp =
      Finset.range (Finset.univ.filter fun v => Θ v = b).card := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    obtain ⟨v, hv1, rfl⟩ := Finset.mem_image.mp hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv1
    rw [Finset.mem_range, ← hv1]
    exact hlt v
  · rw [Finset.card_range, Finset.card_image_of_injOn]
    intro v hv1 w hw1 h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv1 hw1
    exact hv v w (hv1.trans hw1.symm) h

theorem card_block_grp_lt_eq {Θ : Fin s → Fin K} {grp : Fin s → ℕ} (hv : ValidA Θ grp)
    (hlt : ∀ v, grp v < (Finset.univ.filter fun w => Θ w = Θ v).card) (b : Fin K) (j : ℕ) :
    (Finset.univ.filter fun v => Θ v = b ∧ grp v < j).card =
      min (Finset.univ.filter fun v => Θ v = b).card j := by
  classical
  have him := image_grp_eq_range hv hlt b
  have h1 : (Finset.univ.filter fun v => Θ v = b ∧ grp v < j).card =
      (((Finset.univ.filter fun v => Θ v = b).image grp).filter (· < j)).card := by
    rw [Finset.filter_image, Finset.card_image_of_injOn]
    · congr 1; ext v; simp
    · intro v hv1 w hw1 h
      have hv2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hv1)).1
      have hw2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hw1)).1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv2 hw2
      exact hv v w (hv2.trans hw2.symm) h
  rw [h1, him]
  have : (Finset.range (Finset.univ.filter fun v => Θ v = b).card).filter (· < j) =
      Finset.range (min (Finset.univ.filter fun v => Θ v = b).card j) := by
    ext i; simp [Finset.mem_filter, Finset.mem_range]
  rw [this, Finset.card_range]

/-- **Equality forces the copies**: if the copy counts below each `j` equal the
`Σ_b min(c_b, j)` of the fibre sizes, then every slot's copy is below its block's size. -/
theorem grp_lt_of_sum_eq {Θ : Fin s → Fin K} {grp : Fin s → ℕ} (hv : ValidA Θ grp)
    (heq : ∀ j, (Finset.univ.filter fun v => grp v < j).card =
      ∑ b, min (Finset.univ.filter fun v => Θ v = b).card j) (v : Fin s) :
    grp v < (Finset.univ.filter fun w => Θ w = Θ v).card := by
  classical
  set c := (Finset.univ.filter fun w => Θ w = Θ v).card
  have hle := fun b => card_block_grp_lt_le hv b c
  have hsum := heq c
  rw [card_grp_lt_eq_sum Θ grp c] at hsum
  have hall := (Finset.sum_eq_sum_iff_of_le (fun b _ => hle b)).mp hsum (Θ v) (Finset.mem_univ _)
  rw [min_self] at hall
  have hsub : (Finset.univ.filter fun w => Θ w = Θ v ∧ grp w < c) =
      (Finset.univ.filter fun w => Θ w = Θ v) := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢; exact hw.1
    · rw [hall]
  have hvmem : v ∈ (Finset.univ.filter fun w => Θ w = Θ v) := by simp
  rw [← hsub] at hvmem
  simpa using hvmem

/-- **Copy images**: under the conclusion of `grp_lt_of_sum_eq`, a block meets copy `i` iff
`i` is below its size. -/
theorem mem_image_copy_iff {Θ : Fin s → Fin K} {grp : Fin s → ℕ} (hv : ValidA Θ grp)
    (hlt : ∀ v, grp v < (Finset.univ.filter fun w => Θ w = Θ v).card) (b : Fin K) (i : ℕ) :
    (∃ v, grp v = i ∧ Θ v = b) ↔ i < (Finset.univ.filter fun v => Θ v = b).card := by
  classical
  constructor
  · rintro ⟨v, rfl, rfl⟩; exact hlt v
  · intro hi
    have him := image_grp_eq_range hv hlt b
    rw [← Finset.mem_range, ← him, Finset.mem_image] at hi
    obtain ⟨v, hv1, rfl⟩ := hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv1
    exact ⟨v, rfl, hv1⟩

end Assign

/-! ### Exponents and the FS functions of a profile -/

/-- The exponent data of a profile: `γ` for colour `0` (the operator `E`) and `β_c` for the copies. -/
def ExpL : List ℕ → Type
  | [] => Unit
  | r :: P => (Fin r → ℕ) × ExpL P

/-- Decidable equality of exponent data. -/
def ExpL.decEq : (P : List ℕ) → DecidableEq (ExpL P)
  | [] => inferInstanceAs (DecidableEq Unit)
  | _ :: P => @instDecidableEqProd _ _ _ (ExpL.decEq P)

instance (P : List ℕ) : DecidableEq (ExpL P) := ExpL.decEq P

/-- The elementary-symmetric monomial of the top level: `e^{(x_0, 0)}` on all blocks. -/
def topL : (P : List ℕ) → ExpL P → MvPolynomial (Fin (nbL P)) ℂ
  | [], _ => 1
  | r :: P, x => (esymmPow (Fin.append x.1 (fun _ : Fin (nbL P) => 0)) :
      MvPolynomial (Fin (r + nbL P)) ℂ)

theorem topL_symm : ∀ (P : List ℕ) (x : ExpL P), Symm (topL P x)
  | [], _ => fun σ => by simp [topL]
  | r :: P, x => esymmPow_symm (s := r + nbL P) _

/-- The unsymmetrized FS function: over the copies, `vdm · topL` of the next level. -/
def gFS : (P : List ℕ) → ExpL P → MvPolynomial (Fin (tsL P)) ℂ
  | [], _ => 1
  | _ :: P, x => (rename (Fin.castAdd (tsL P)) (vdm (nbL P) * topL P x.2) *
      rename (Fin.natAdd (nbL P)) (gFS P x.2) : MvPolynomial (Fin (nbL P + tsL P)) ℂ)

theorem rename_vdm_eq_zero {N K : ℕ} (f : Fin N → Fin K) {i j : Fin N} (hij : i ≠ j)
    (hf : f i = f j) : rename f (vdm N) = 0 := by
  rw [vdm, map_prod]
  apply Finset.prod_eq_zero (i := (i, j)) (by simp [Finset.mem_offDiag, hij])
  simp [hf]

/-- `gFS` dies under any map identifying two slots of the same copy. -/
theorem gFS_vanish : ∀ (P : List ℕ) (x : ExpL P) {K : ℕ} (f : Fin (tsL P) → Fin K)
    (v w : Fin (tsL P)), v ≠ w → grpL P v = grpL P w → f v = f w → rename f (gFS P x) = 0
  | [], _, _, _, v, _, _, _, _ => Fin.elim0 v
  | r :: P, x, K, f, v, w, hvw, hg, hf => by
    revert hvw hg hf
    refine Fin.addCases (fun i => ?_) (fun v' => ?_) v <;>
      refine Fin.addCases (fun j => ?_) (fun w' => ?_) w
    · intro hvw _ hf
      have hij : i ≠ j := fun h => hvw (h ▸ rfl)
      have key : ∀ f' : Fin (nbL P + tsL P) → Fin K, f' (Fin.castAdd (tsL P) i) =
          f' (Fin.castAdd (tsL P) j) →
          rename f' (rename (Fin.castAdd (tsL P)) (vdm (nbL P) * topL P x.2) *
            rename (Fin.natAdd (nbL P)) (gFS P x.2)) = 0 := by
        intro f' hf'
        rw [map_mul, rename_rename, map_mul, rename_vdm_eq_zero _ hij hf', zero_mul, zero_mul]
      exact key f hf
    · intro _ hg _
      rw [grpL_cons_castAdd, grpL_cons_natAdd] at hg; omega
    · intro _ hg _
      rw [grpL_cons_castAdd, grpL_cons_natAdd] at hg; omega
    · intro hvw hg hf
      have hvw' : v' ≠ w' := fun h => hvw (h ▸ rfl)
      rw [grpL_cons_natAdd, grpL_cons_natAdd, Nat.add_right_cancel_iff] at hg
      have key : ∀ f' : Fin (nbL P + tsL P) → Fin K, f' (Fin.natAdd (nbL P) v') =
          f' (Fin.natAdd (nbL P) w') →
          rename f' (rename (Fin.castAdd (tsL P)) (vdm (nbL P) * topL P x.2) *
            rename (Fin.natAdd (nbL P)) (gFS P x.2)) = 0 := by
        intro f' hf'
        rw [map_mul, rename_rename (Fin.natAdd (nbL P)),
          gFS_vanish P x.2 (f' ∘ Fin.natAdd (nbL P)) v' w' hvw' hg hf', mul_zero]
      exact key f hf

theorem exists_perm_of_range_eq {N K : ℕ} {φ ψ : Fin N → Fin K} (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) (h : Set.range φ = Set.range ψ) :
    ∃ π : Equiv.Perm (Fin N), ∀ i, ψ i = φ (π i) := by
  refine ⟨(Equiv.ofInjective ψ hψ).trans ((Equiv.setCongr h.symm).trans
    (Equiv.ofInjective φ hφ).symm), fun i => ?_⟩
  simp only [Equiv.trans_apply]
  rw [Equiv.apply_ofInjective_symm hφ]
  rfl

theorem Symm.mul {N : ℕ} {A B : MvPolynomial (Fin N) ℂ} (hA : Symm A) (hB : Symm B) :
    Symm (A * B) := fun σ => by rw [map_mul, hA σ, hB σ]

theorem rename_symm_congr {N K : ℕ} {A : MvPolynomial (Fin N) ℂ} (hA : Symm A)
    {φ ψ : Fin N → Fin K} (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (h : Set.range φ = Set.range ψ) : rename ψ A = rename φ A := by
  obtain ⟨π, hπ⟩ := exists_perm_of_range_eq hφ hψ h
  have : ψ = φ ∘ π := funext hπ
  rw [this, ← rename_rename, hA π]

/-- `gFS` renamed along two maps that are injective on copies with the same copy images
agree. -/
theorem gFS_rename_congr : ∀ (P : List ℕ) (x : ExpL P) {K : ℕ} (f g : Fin (tsL P) → Fin K),
    ValidA f (grpL P) → ValidA g (grpL P) →
    (∀ (i : ℕ) (b : Fin K), (∃ v, grpL P v = i ∧ f v = b) ↔ (∃ v, grpL P v = i ∧ g v = b)) →
      rename f (gFS P x) = rename g (gFS P x)
  | [], _, _, _, _, _, _, _ => by simp [gFS]
  | r :: P, x, K, f, g, hf, hg, himg => by
    suffices key : ∀ f' g' : Fin (nbL P + tsL P) → Fin K, f = f' → g = g' →
        rename f' (rename (Fin.castAdd (tsL P)) (vdm (nbL P) * topL P x.2) *
          rename (Fin.natAdd (nbL P)) (gFS P x.2)) =
        rename g' (rename (Fin.castAdd (tsL P)) (vdm (nbL P) * topL P x.2) *
          rename (Fin.natAdd (nbL P)) (gFS P x.2)) from key f g rfl rfl
    intro f' g' hf' hg'
    subst hf' hg'
    have hAsymm : Symm (vdm (nbL P) * topL P x.2) := Symm.mul (vdm_symm _) (topL_symm P x.2)
    generalize vdm (nbL P) * topL P x.2 = A at hAsymm ⊢
    rw [map_mul, map_mul, rename_rename, rename_rename, rename_rename, rename_rename]
    congr 1
    · -- the first copy
      have hinj : ∀ h : Fin (tsL (r :: P)) → Fin K, ValidA h (grpL (r :: P)) →
          Function.Injective (h ∘ Fin.castAdd (tsL P)) := by
        intro h hh i j hij
        have := hh _ _ hij (by rw [grpL_cons_castAdd, grpL_cons_castAdd])
        exact Fin.castAdd_injective _ _ this
      have hrange : Set.range (f ∘ Fin.castAdd (tsL P)) = Set.range (g ∘ Fin.castAdd (tsL P)) := by
        ext b
        have key : ∀ h : Fin (tsL (r :: P)) → Fin K,
            b ∈ Set.range (h ∘ Fin.castAdd (tsL P)) ↔ ∃ v, grpL (r :: P) v = 0 ∧ h v = b := by
          intro h
          constructor
          · rintro ⟨i, rfl⟩; exact ⟨_, grpL_cons_castAdd r P i, rfl⟩
          · rintro ⟨v, hv, rfl⟩
            revert hv
            refine Fin.addCases (fun i => ?_) (fun v' => ?_) v
            · intro _; exact ⟨i, rfl⟩
            · intro hv; rw [grpL_cons_natAdd] at hv; omega
        exact (key f).trans ((himg 0 b).trans (key g).symm)
      exact (rename_symm_congr hAsymm (hinj g hg) (hinj f hf) hrange.symm)
    · -- the remaining copies
      refine gFS_rename_congr P x.2 _ _ ?_ ?_ ?_
      · intro v w h1 h2
        exact Fin.natAdd_injective _ _ (hf _ _ h1 (by
          rw [grpL_cons_natAdd, grpL_cons_natAdd, h2]))
      · intro v w h1 h2
        exact Fin.natAdd_injective _ _ (hg _ _ h1 (by
          rw [grpL_cons_natAdd, grpL_cons_natAdd, h2]))
      · intro i b
        have key : ∀ h : Fin (tsL (r :: P)) → Fin K,
            (∃ v, grpL P v = i ∧ (h ∘ Fin.natAdd (nbL P)) v = b) ↔
              ∃ v, grpL (r :: P) v = i + 1 ∧ h v = b := by
          intro h
          constructor
          · rintro ⟨v, hv, rfl⟩; exact ⟨_, by rw [grpL_cons_natAdd, hv], rfl⟩
          · rintro ⟨v, hv, rfl⟩
            revert hv
            refine Fin.addCases (fun j => ?_) (fun v' => ?_) v
            · intro hv; rw [grpL_cons_castAdd] at hv; omega
            · intro hv
              rw [grpL_cons_natAdd, Nat.add_right_cancel_iff] at hv
              exact ⟨v', hv, rfl⟩
        exact (key f).trans ((himg (i + 1) b).trans (key g).symm)

/-- The FS function of a profile: the symmetrization of `gFS`. -/
def fFS (P : List ℕ) (x : ExpL P) : MvPolynomial (Fin (tsL P)) ℂ :=
  ∑ σ : Equiv.Perm (Fin (tsL P)), rename σ (gFS P x)

theorem fFS_symm (P : List ℕ) (x : ExpL P) : Symm (fFS P x) := by
  intro τ
  rw [fFS, map_sum]
  simp_rw [rename_rename]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)

theorem grpL_lt_length : ∀ (P : List ℕ) (v : Fin (tsL P)), grpL P v + 1 < P.length
  | [], v => Fin.elim0 v
  | r :: P, v => by
    refine Fin.addCases (fun i => ?_) (fun v' => ?_) v
    · rw [grpL_cons_castAdd]
      cases P with
      | nil => exact Fin.elim0 i
      | cons _ _ => simp
    · rw [grpL_cons_natAdd]
      have := grpL_lt_length P v'
      simp only [List.length_cons]
      omega

/-- **The FS function of a profile is killed by collisions of `length P` variables.** -/
theorem fFS_collKill (P : List ℕ) (hP : P ≠ []) (x : ExpL P) :
    CollKill P.length (fFS P x) := by
  classical
  intro K ρ b hcard
  rw [fFS, map_sum]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [rename_rename]
  -- the slots sent to `b` meet some copy twice
  set S := Finset.univ.filter fun v => (ρ ∘ σ) v = b
  have hS : P.length ≤ S.card := by
    have : S.card = (Finset.univ.filter fun v => ρ v = b).card := by
      apply Finset.card_bij (fun v _ => σ v)
      · intro v hv; simpa [S] using hv
      · intro v _ w _ h; exact σ.injective h
      · intro w hw; exact ⟨σ.symm w, by simpa [S] using hw, by simp⟩
    rw [this]; exact hcard
  have hmaps : ∀ v ∈ S, grpL P v ∈ Finset.range (P.length - 1) := by
    intro v _
    have := grpL_lt_length P v
    rw [Finset.mem_range]; omega
  have hlt : (Finset.range (P.length - 1)).card < S.card := by
    rw [Finset.card_range]
    have : 0 < P.length := List.length_pos_iff.mpr hP
    omega
  obtain ⟨v, hv, w, hw, hvw, hg⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  exact gFS_vanish P x _ v w hvw hg (by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hv hw; rw [hv, hw])

/-! ### The main term, and its factorization -/

/-- The main term `gFS` at the profile's own slots. -/
def mainL (P : List ℕ) (x : ExpL P) : MvPolynomial (Fin (nbL P)) ℂ := rename (rhoL P) (gFS P x)

theorem mainL_cons (r : ℕ) (P : List ℕ) (x : ExpL (r :: P)) :
    mainL (r :: P) x = (rename (Fin.natAdd r) (vdm (nbL P) * topL P x.2 * mainL P x.2) :
      MvPolynomial (Fin (r + nbL P)) ℂ) := by
  have key : ∀ ρ' : Fin (nbL P + tsL P) → Fin (r + nbL P), ρ' = rhoL (r :: P) →
      rename ρ' (rename (Fin.castAdd (tsL P)) (vdm (nbL P) * topL P x.2) *
        rename (Fin.natAdd (nbL P)) (gFS P x.2)) =
      rename (Fin.natAdd r) (vdm (nbL P) * topL P x.2 * mainL P x.2) := by
    intro ρ' hρ'
    subst hρ'
    generalize vdm (nbL P) * topL P x.2 = A
    rw [map_mul, rename_rename, rename_rename, mainL, map_mul, rename_rename]
    congr 1
    · congr 2; funext i; exact rhoL_cons_castAdd r P i
    · congr 2; funext v; exact rhoL_cons_natAdd r P v
  exact key _ rfl

/-- The product of the Vandermonde factors. -/
def VL : (P : List ℕ) → MvPolynomial (Fin (nbL P)) ℂ
  | [] => 1
  | r :: P => (rename (Fin.natAdd r) (vdm (nbL P) * VL P) : MvPolynomial (Fin (r + nbL P)) ℂ)

/-- The elementary-symmetric family of a profile. -/
def FamL : (P : List ℕ) → ExpL P → MvPolynomial (Fin (nbL P)) ℂ
  | [], _ => 1
  | r :: P, x => (esymmPow (Fin.append x.1 (fun _ : Fin (nbL P) => 0)) *
      rename (Fin.natAdd r) (FamL P x.2) : MvPolynomial (Fin (r + nbL P)) ℂ)

/-- **The main term factorizes**: `topL · mainL = VL · FamL`. -/
theorem topL_mul_mainL : ∀ (P : List ℕ) (x : ExpL P), topL P x * mainL P x = VL P * FamL P x
  | [], x => by simp [topL, mainL, gFS, VL, FamL]
  | r :: P, x => by
    rw [mainL_cons]
    have ih := topL_mul_mainL P x.2
    show (esymmPow (Fin.append x.1 (fun _ : Fin (nbL P) => 0)) : MvPolynomial (Fin (r + nbL P)) ℂ) *
        rename (Fin.natAdd r) (vdm (nbL P) * topL P x.2 * mainL P x.2) =
      rename (Fin.natAdd r) (vdm (nbL P) * VL P) *
        (esymmPow (Fin.append x.1 (fun _ : Fin (nbL P) => 0)) * rename (Fin.natAdd r) (FamL P x.2))
    rw [mul_assoc (vdm (nbL P)), ih]
    simp only [map_mul]
    ring

theorem VL_ne_zero : ∀ P : List ℕ, VL P ≠ 0
  | [] => one_ne_zero
  | r :: P => by
    intro h
    have h' : rename (Fin.natAdd r) (vdm (nbL P) * VL P) = 0 := h
    rw [← map_zero (rename (Fin.natAdd r : Fin (nbL P) → Fin (r + nbL P)))] at h'
    have := rename_injective _ (Fin.natAdd_injective (nbL P) r) h'
    exact mul_ne_zero (vdm_ne_zero _) (VL_ne_zero P) this

/-! ### Evaluating the FS function of a profile at coloured points -/

theorem card_fiber_comp_equiv {s s' K : ℕ} (ρ : Fin s' → Fin K) (e : Fin s ≃ Fin s') (b : Fin K) :
    (Finset.univ.filter fun v => (ρ ∘ e) v = b).card = (Finset.univ.filter fun u => ρ u = b).card := by
  apply Finset.card_bij (fun v _ => e v)
  · intro v hv; simpa using hv
  · intro v _ w _ h; exact e.injective h
  · intro u hu; exact ⟨e.symm u, by simpa using hu, by simp⟩

theorem rhoL_hlt (P : List ℕ) (v : Fin (tsL P)) :
    grpL P v < (Finset.univ.filter fun w => rhoL P w = rhoL P v).card := by
  rw [card_rhoL]; exact grpL_lt_colL P v

/-- The number of slots in copies `< j`. -/
def cntL (P : List ℕ) (j : ℕ) : ℕ := (Finset.univ.filter fun v : Fin (tsL P) => grpL P v < j).card

theorem cntL_eq (P : List ℕ) (j : ℕ) :
    cntL P j = ∑ b, min (Finset.univ.filter fun v => rhoL P v = b).card j := by
  rw [cntL, card_grp_lt_eq_sum (rhoL P) (grpL P) j]
  exact Finset.sum_congr rfl fun b _ =>
    card_block_grp_lt_eq (rhoL_grpL_inj P) (rhoL_hlt P) b j

/-- **At its own colouring**, every valid slot assignment of a profile gives the main term. -/
theorem rename_valid_eq_mainL (P : List ℕ) (x : ExpL P) (σ : Equiv.Perm (Fin (tsL P)))
    (hv : ValidA (rhoL P ∘ σ) (grpL P)) : rename (rhoL P ∘ σ) (gFS P x) = mainL P x := by
  have hcard : ∀ b, (Finset.univ.filter fun v => (rhoL P ∘ σ) v = b).card =
      (Finset.univ.filter fun u => rhoL P u = b).card := card_fiber_comp_equiv (rhoL P) σ
  have heq : ∀ j, (Finset.univ.filter fun v => grpL P v < j).card =
      ∑ b, min (Finset.univ.filter fun v => (rhoL P ∘ σ) v = b).card j := by
    intro j
    rw [← cntL, cntL_eq]
    simp only [hcard]
  have hlt := grp_lt_of_sum_eq hv heq
  rw [mainL]
  apply gFS_rename_congr P x _ _ hv (rhoL_grpL_inj P)
  intro i b
  rw [mem_image_copy_iff hv hlt b i, mem_image_copy_iff (rhoL_grpL_inj P) (rhoL_hlt P) b i, hcard]

/-- **The FS function at its own colouring is a nonzero multiple of the main term.** -/
theorem rename_rhoL_fFS (P : List ℕ) (x : ExpL P) :
    rename (rhoL P) (fFS P x) =
      ((Finset.univ.filter fun σ : Equiv.Perm (Fin (tsL P)) =>
        ValidA (rhoL P ∘ σ) (grpL P)).card : ℂ) • mainL P x := by
  classical
  rw [fFS, map_sum]
  simp_rw [rename_rename]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun σ : Equiv.Perm (Fin (tsL P)) => ValidA (rhoL P ∘ σ) (grpL P))]
  rw [Finset.sum_congr rfl (fun σ hσ => rename_valid_eq_mainL P x σ (Finset.mem_filter.mp hσ).2),
    Finset.sum_const, Finset.sum_eq_zero, add_zero, Nat.cast_smul_eq_nsmul]
  intro σ hσ
  have hnv := (Finset.mem_filter.mp hσ).2
  simp only [ValidA, not_forall] at hnv
  obtain ⟨v, w, h1, h2, hne⟩ := hnv
  exact gFS_vanish P x _ v w hne h2 h1

theorem card_valid_pos (P : List ℕ) :
    0 < (Finset.univ.filter fun σ : Equiv.Perm (Fin (tsL P)) =>
      ValidA (rhoL P ∘ σ) (grpL P)).card :=
  Finset.card_pos.mpr ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    intro v w h1 h2; exact rhoL_grpL_inj P v w h1 h2⟩⟩

/-- A valid assignment of profile `P`'s copies to the colouring of `P0` bounds the copy counts. -/
theorem cntL_le_of_valid (P P0 : List ℕ) (h : tsL P = tsL P0) (σ : Equiv.Perm (Fin (tsL P)))
    (hv : ValidA (rhoL P0 ∘ Fin.cast h ∘ σ) (grpL P)) (j : ℕ) : cntL P j ≤ cntL P0 j := by
  rw [cntL, card_grp_lt_eq_sum (rhoL P0 ∘ Fin.cast h ∘ σ) (grpL P) j, cntL_eq]
  apply Finset.sum_le_sum
  intro b _
  have := card_block_grp_lt_le hv b j
  rwa [show (Finset.univ.filter fun v => (rhoL P0 ∘ Fin.cast h ∘ σ) v = b).card =
    (Finset.univ.filter fun u => rhoL P0 u = b).card from
      card_fiber_comp_equiv (rhoL P0) (σ.trans (finCongr h)) b] at this

/-- The FS function of `P` vanishes at the colouring of `P0` when no assignment is valid. -/
theorem rename_fFS_eq_zero (P P0 : List ℕ) (h : tsL P = tsL P0) (x : ExpL P)
    (hno : ∀ σ : Equiv.Perm (Fin (tsL P)), ¬ ValidA (rhoL P0 ∘ Fin.cast h ∘ σ) (grpL P)) :
    rename (rhoL P0 ∘ Fin.cast h) (fFS P x) = 0 := by
  rw [fFS, map_sum]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [rename_rename]
  have hnv := hno σ
  simp only [ValidA, not_forall] at hnv
  obtain ⟨v, w, h1, h2, hne⟩ := hnv
  exact gFS_vanish P x _ v w hne h2 h1

/-! ### Copy counts determine the profile -/

theorem cntL_cons_zero (r : ℕ) (P : List ℕ) : cntL (r :: P) 0 = 0 := by
  simp [cntL]

theorem cntL_cons_succ (r : ℕ) (P : List ℕ) (j : ℕ) :
    cntL (r :: P) (j + 1) = nbL P + cntL P j := by
  unfold cntL
  show (Finset.univ.filter fun v : Fin (nbL P + tsL P) => grpL (r :: P) v < j + 1).card = _
  rw [card_filter_fin_add (m := nbL P) (n := tsL P)]
  congr 1
  · have : (Finset.univ.filter fun i : Fin (nbL P) =>
        grpL (r :: P) (Fin.castAdd (tsL P) i) < j + 1) = Finset.univ := by
      ext i; simp [grpL_cons_castAdd]
    rw [this, Finset.card_univ, Fintype.card_fin]
  · congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [grpL_cons_natAdd]
    omega

/-- **Profiles of equal length and block count with equal copy counts coincide.** -/
theorem eq_of_cntL : ∀ (P P0 : List ℕ), P.length = P0.length → nbL P = nbL P0 →
    (∀ j, cntL P j = cntL P0 j) → P = P0
  | [], [], _, _, _ => rfl
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl
  | r :: P, r0 :: P0, hl, hnb, hc => by
    have h1 := hc 1
    rw [cntL_cons_succ, cntL_cons_succ] at h1
    have h0 : cntL P 0 = 0 := by simp [cntL]
    have h0' : cntL P0 0 = 0 := by simp [cntL]
    rw [h0, h0'] at h1
    have h1' : nbL P = nbL P0 := by simpa using h1
    have hP : P = P0 := eq_of_cntL P P0 (by simpa using hl) h1' (fun j => by
      have := hc (j + 1)
      rw [cntL_cons_succ, cntL_cons_succ] at this
      omega)
    subst hP
    have : r = r0 := by
      have := hnb
      simp only [nbL] at this
      omega
    rw [this]

theorem cntL_eq_tsL (P : List ℕ) (j : ℕ) (hj : P.length ≤ j + 1) : cntL P j = tsL P := by
  unfold cntL
  rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
  intro v _
  have := grpL_lt_length P v
  omega

/-- The potential `Σ_{j < n} cntL P j`. -/
def potL (n : ℕ) (P : List ℕ) : ℕ := ∑ j ∈ Finset.range n, cntL P j

/-- **Triangularity**: if the copy counts of `P` are below those of `P0` and the potential of
`P0` is minimal, then `P = P0`. -/
theorem eq_of_cntL_le_of_potL (P P0 : List ℕ) (hl : P.length = P0.length)
    (hts : tsL P = tsL P0) (hnb : nbL P = nbL P0) (hle : ∀ j, cntL P j ≤ cntL P0 j)
    (hpot : potL P.length P0 ≤ potL P.length P) : P = P0 := by
  apply eq_of_cntL P P0 hl hnb
  intro j
  by_cases hj : j < P.length
  · have hsum : potL P.length P = potL P.length P0 := le_antisymm
      (Finset.sum_le_sum fun j _ => hle j) hpot
    have := (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp hsum j (Finset.mem_range.mpr hj)
    exact this
  · rw [cntL_eq_tsL P j (by omega), cntL_eq_tsL P0 j (by omega), hts]

end

end VOA.TwoSeries.ModelChar
