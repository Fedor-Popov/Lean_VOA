/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGeneralLocality

/-!
# Lattice reconstruction — STAGE 2 §B/§E of `latticeVOA_A1`

The Dong locality cascade and the `reconstruct` application for the lattice `A₁` VOA, gated on the
one remaining crux — the general charge-pair locality `Yemα_local m m'`:

* `genFieldLat_local_YwordLat` — boson generator local with every word field (NO charge-pair input).
* `Yemα_local_YwordLat`, `YwordLat_local` — full word-field mutual locality, given the hypothesis
  `hYloc : ∀ m m', Local (Yemα m) (Yemα m')`.
* `latYfull_of_locality` — the basis-free all-states vertex map `Yfull` from `reconstruct`, with its
  six properties (word evaluation, `IsField`, mutual locality, the VA3 creation tower, and
  `Trec`-covariance), gated on `hYloc`.  The lattice analogue of `affineYA_of_currentCov`.

All `pbw`-free.  The single open obligation `hYloc` is the general-pairing boson contraction
(`(1-x)^{2mm'}`): finite/commuting for same-sign charges, the infinite cross machinery for
opposite-sign.
-/

open VOA VOA.LatExp VOA.LatticeVOA
open Module (End)
open scoped TensorProduct BigOperators

namespace VOA.LatExp

/-! ## §B  The Dong locality cascade. -/

/-- The boson generator field is local with every word field (Dong cascade over the boson word;
base = `genFieldLat_local_Yemα`, step = `dong_neg` with `genFieldLat_local`). No charge-pair
locality needed. -/
theorem genFieldLat_local_YwordLat :
    ∀ (l : List ℕ) (m : ℤ) (i : ℕ), Local (genFieldLat i) (YwordLat l m)
  | [], m, i => by rw [YwordLat_nil]; exact genFieldLat_local_Yemα i m
  | (j :: rest), m, i => by
      rw [YwordLat_cons]
      have hab : Local (genFieldLat j) (YwordLat rest m) := genFieldLat_local_YwordLat rest m j
      have hac : Local (genFieldLat j) (genFieldLat i) := genFieldLat_local j i
      have hbc : Local (YwordLat rest m) (genFieldLat i) :=
        (genFieldLat_local_YwordLat rest m i).symm
      exact (dong_neg (genFieldLat_isField j) (YwordLat_isField rest m) hab hac hbc).symm

/-- The charge seed `Yemα m₁` is local with every word field, GIVEN the general charge-pair
locality `hYloc`. Cascade over the second word; base = `hYloc`. -/
theorem Yemα_local_YwordLat (hYloc : ∀ m m' : ℤ, Local (Yemα m) (Yemα m')) (m₁ : ℤ) :
    ∀ (l₂ : List ℕ) (m₂ : ℤ), Local (Yemα m₁) (YwordLat l₂ m₂)
  | [], m₂ => by rw [YwordLat_nil]; exact hYloc m₁ m₂
  | (j :: rest), m₂ => by
      rw [YwordLat_cons]
      have hab : Local (genFieldLat j) (YwordLat rest m₂) := genFieldLat_local_YwordLat rest m₂ j
      have hac : Local (genFieldLat j) (Yemα m₁) := genFieldLat_local_Yemα j m₁
      have hbc : Local (YwordLat rest m₂) (Yemα m₁) := (Yemα_local_YwordLat hYloc m₁ rest m₂).symm
      exact (dong_neg (genFieldLat_isField j) (YwordLat_isField rest m₂) hab hac hbc).symm

/-- **Every two word fields are mutually local**, GIVEN the general charge-pair locality `hYloc`.
Cascade over the first word; base = `Yemα_local_YwordLat`, step = `dong_neg`. -/
theorem YwordLat_local (hYloc : ∀ m m' : ℤ, Local (Yemα m) (Yemα m')) :
    ∀ (l₁ : List ℕ) (m₁ : ℤ) (l₂ : List ℕ) (m₂ : ℤ),
      Local (YwordLat l₁ m₁) (YwordLat l₂ m₂)
  | [], m₁, l₂, m₂ => by rw [YwordLat_nil]; exact Yemα_local_YwordLat hYloc m₁ l₂ m₂
  | (i :: rest), m₁, l₂, m₂ => by
      rw [YwordLat_cons]
      have hab : Local (genFieldLat i) (YwordLat rest m₁) := genFieldLat_local_YwordLat rest m₁ i
      have hac : Local (genFieldLat i) (YwordLat l₂ m₂) := genFieldLat_local_YwordLat l₂ m₂ i
      have hbc : Local (YwordLat rest m₁) (YwordLat l₂ m₂) := YwordLat_local hYloc rest m₁ l₂ m₂
      exact dong_neg (genFieldLat_isField i) (YwordLat_isField rest m₁) hab hac hbc

/-! ## §E  The reconstructed all-states vertex map (gated on the charge-pair locality). -/

/-- **The basis-free lattice vertex map** from the reconstruction engine, gated on the general
charge-pair locality `hYloc : ∀ m m', Local (Yemα m) (Yemα m')`.  Yields `Yfull` with
`Yfull (wordStateLat l m) = YwordLat l m`, `IsField`, mutual locality, the VA3 creation tower, and
`Trec`-covariance — the lattice analogue of `affineYA_of_currentCov`. -/
theorem latYfull_of_locality (hYloc : ∀ m m' : ℤ, Local (Yemα m) (Yemα m')) :
    ∃ Yfull : LatModule →ₗ[ℂ] FormalDist (End ℂ LatModule),
      (∀ (lm : List ℕ × ℤ), Yfull (Function.uncurry wordStateLat lm)
        = Function.uncurry (fun l m => YwordLat l m) lm) ∧
      (∀ u : LatModule, IsField (Yfull u)) ∧
      (∀ u v : LatModule, Local (Yfull u) (Yfull v)) ∧
      (∀ u : LatModule, (Yfull u) 0 latVacuum = u) ∧
      (∀ u : LatModule, ∀ q : ℤ, q < 0 → (Yfull u) q latVacuum = 0) ∧
      (∀ u : LatModule, Reconstruction.DCovariant Trec (Yfull u)) :=
  Reconstruction.reconstruct latVacuum (Function.uncurry wordStateLat)
    (Function.uncurry (fun l m => YwordLat l m)) Trec
    wordStateLat_span
    (fun lm => YwordLat_isField lm.1 lm.2)
    (fun lm₁ lm₂ => YwordLat_local hYloc lm₁.1 lm₁.2 lm₂.1 lm₂.2)
    (fun lm => YwordLat_vacuum_base lm.1 lm.2)
    (fun lm _q hq => YwordLat_vacuum_neg lm.1 lm.2 hq)
    Trec_vacuum
    (fun lm => YwordLat_DCovariant lm.1 lm.2)

end VOA.LatExp
