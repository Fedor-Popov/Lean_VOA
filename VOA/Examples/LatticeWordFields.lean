/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeExpVirasoro

/-!
# Lattice word fields — STAGE 2 §A of the `latticeVOA_A1` reconstruction

The generating-field family for the operator-first reconstruction of the lattice `A₁` VOA, the
direct mirror of `Examples.HeisenbergNVertex` / `Examples.AffineSl2VOA` word fields:

* `genFieldLat i := (i!)⁻¹ ∂_z^i αLat(z)` — the scaled boson generator field, with `IsField`,
  mutual locality (`genFieldLat_local`), and `Trec`-covariance (`genFieldLat_DCovariant`, from the
  STAGE 1 `Trec_alphaLat_DCovariant`).
* `Yemα_isField m` — the charge-`m` lattice vertex operator is a field.
* `YwordLat l m` — the iterated normal-ordered boson product **seeded by the charge field**
  `Yemα m` (in place of the affine identity seed), with its field witness.

All `pbw`-free / axiom-clean.
-/

open VOA VOA.LatExp VOA.LatticeVOA
open Module (End)
open scoped TensorProduct BigOperators

namespace VOA.LatExp

/-! ## §A.1  The scaled boson generator field `genFieldLat i = (i!)⁻¹ ∂^i αLat`. -/

/-- The **scaled boson generator field** `genFieldLat i := (i!)⁻¹ · ∂_z^i αLat(z)` — the lattice
analogue of `genFieldN`/`genFieldA`, the field `Y(α₋(i+1)·latVacuum, z)`. -/
noncomputable def genFieldLat (i : ℕ) : FormalDist (End ℂ LatModule) :=
  (i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] alphaLat)

theorem genFieldLat_isField (i : ℕ) : IsField (genFieldLat i) := by
  intro x
  obtain ⟨B, hB⟩ := alphaLat_isField.deriv_iterate i x
  exact ⟨B, fun n hn => by
    change ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] alphaLat) n) x = 0
    rw [LinearMap.smul_apply, hB n hn, smul_zero]⟩

theorem genFieldLat_zero : genFieldLat 0 = alphaLat := by
  rw [genFieldLat, Function.iterate_zero, id, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]

/-- Iterated derivatives of `αLat` are mutually local. -/
theorem dalphaLat_local (i j : ℕ) :
    Local (VOA.deriv^[i] alphaLat) (VOA.deriv^[j] alphaLat) :=
  ((latticeA1_alpha_local).deriv_iterate_left i).deriv_iterate_right j

theorem genFieldLat_local (i j : ℕ) : Local (genFieldLat i) (genFieldLat j) := by
  change Local ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] alphaLat))
    ((j.factorial : ℂ)⁻¹ • (VOA.deriv^[j] alphaLat))
  exact Local.smulR _ (VertexOperatorAlgebra.Local.smul' _ (dalphaLat_local i j))

/-- `genFieldLat i` inherits `Trec`-covariance from `αLat` (STAGE 1 `Trec_alphaLat_DCovariant`). -/
theorem genFieldLat_DCovariant (i : ℕ) :
    Reconstruction.DCovariant Trec (genFieldLat i) := by
  rw [genFieldLat]
  exact Reconstruction.DCovariant.smul ((i.factorial : ℂ)⁻¹)
    (Reconstruction.DCovariant.deriv_iterate Trec_alphaLat_DCovariant i)

/-! ## §A.2  The charge field `Yemα m` is a field. -/

/-- **The charged lattice vertex operator is a field** (`IsField (Yemα m)`): on `p ⊗ e^{nα}` the
sector shift `t ↦ t - 2mn` lower-truncates via `EEC_isField`; the bound is the min over the
finitely many lattice sectors of a tensor. -/
theorem Yemα_isField (m : ℤ) : IsField (Yemα m) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, fun n _ => (Yemα m n).map_zero⟩
  | add x y hx hy =>
      obtain ⟨Bx, hBx⟩ := hx
      obtain ⟨By, hBy⟩ := hy
      refine ⟨min Bx By, fun n hn => ?_⟩
      rw [map_add (Yemα m n) x y, hBx n (lt_of_lt_of_le hn (min_le_left _ _)),
        hBy n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => exact ⟨0, fun n _ => by erw [TensorProduct.tmul_zero]; exact (Yemα m n).map_zero⟩
      | add g1 g2 h1 h2 =>
          obtain ⟨B1, hB1⟩ := h1
          obtain ⟨B2, hB2⟩ := h2
          refine ⟨min B1 B2, fun n hn => ?_⟩
          erw [TensorProduct.tmul_add]
          simp only [map_add]
          rw [hB1 n (lt_of_lt_of_le hn (min_le_left _ _)),
            hB2 n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]
      | single k a =>
          obtain ⟨Bp, hBp⟩ := EEC_isField (m : ℂ) p
          refine ⟨Bp + 2 * m * k, fun n hn => ?_⟩
          rw [(Finsupp.smul_single_one k a).symm,
            show (Finsupp.single k 1 : LatGrp) = eVec k from rfl]
          erw [TensorProduct.tmul_smul, map_smul, Yemα_tmul,
            hBp (n - 2 * m * k) (by omega), TensorProduct.zero_tmul, smul_zero]

/-! ## §A.3  The lattice word fields `YwordLat`. -/

/-- The iterated normal-ordered boson product seeded by the charge field `Yemα m`, paired with its
field witness: `([], m) ↦ Yemα m`; `(i :: rest, m) ↦ :(genFieldLat i)(YwordLat rest m):`. -/
noncomputable def YwordLatF (m : ℤ) :
    List ℕ → { f : FormalDist (End ℂ LatModule) // IsField f }
  | [] => ⟨Yemα m, Yemα_isField m⟩
  | (i :: rest) =>
      let p := YwordLatF m rest
      ⟨nprod (genFieldLat_isField i) p.2, IsField.nprod (genFieldLat_isField i) p.2⟩

/-- The lattice word field `YwordLat l m`. -/
noncomputable def YwordLat (l : List ℕ) (m : ℤ) : FormalDist (End ℂ LatModule) :=
  (YwordLatF m l).1

theorem YwordLat_isField (l : List ℕ) (m : ℤ) : IsField (YwordLat l m) := (YwordLatF m l).2

@[simp] theorem YwordLat_nil (m : ℤ) : YwordLat [] m = Yemα m := rfl

theorem YwordLat_cons (i : ℕ) (rest : List ℕ) (m : ℤ) :
    YwordLat (i :: rest) m = nprod (genFieldLat_isField i) (YwordLat_isField rest m) := rfl

/-! ## §D  `Trec`-covariance propagation. -/

/-- Every lattice word field `YwordLat l m` is `Trec`-covariant: induction over the boson word,
base `Trec_Yemα_DCovariant m` (STAGE 1), step `DCovariant.nprod` (Leibniz). -/
theorem YwordLat_DCovariant :
    ∀ (l : List ℕ) (m : ℤ), Reconstruction.DCovariant Trec (YwordLat l m)
  | [], m => by rw [YwordLat_nil]; exact Trec_Yemα_DCovariant m
  | (i :: rest), m => by
      rw [YwordLat_cons]
      exact Reconstruction.DCovariant.nprod (genFieldLat_isField i) (YwordLat_isField rest m)
        (genFieldLat_DCovariant i) (YwordLat_DCovariant rest m)

/-! ## §D  The creation tower. -/

/-- The boson generator field annihilates the vacuum below degree `0` (a power series on `|0⟩`). -/
theorem genFieldLat_vacuum_neg (i : ℕ) {q : ℤ} (hq : q < 0) :
    genFieldLat i q latVacuum = 0 := by
  change ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] alphaLat) q) latVacuum = 0
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    ← Int.cast_smul_eq_zsmul ℂ (∏ m ∈ Finset.range i, (q + 1 + (m : ℤ)))]
  simp only [LinearMap.smul_apply]
  by_cases hqi : q + (i : ℤ) < 0
  · rw [alphaLat_vacuum_neg (show q + (i : ℤ) < 0 by omega), smul_zero, smul_zero]
  · rw [Finset.prod_eq_zero (i := (-q - 1).toNat) (Finset.mem_range.mpr (by omega))
        (by rw [show ((-q - 1).toNat : ℤ) = -q - 1 from by omega]; ring),
      Int.cast_zero, zero_smul, smul_zero]

/-- The boson generator field's `z⁰`-coefficient is the boson creation `α₋(i+1)` lifted to the
lattice module (`rTensor`, with `eVec` a spectator): `(genFieldLat i)₀ = rTensor (αField i)`. -/
theorem genFieldLat_zero_op (i : ℕ) :
    (genFieldLat i) 0 = LinearMap.rTensor LatGrp (alphaField i) := by
  change (i.factorial : ℂ)⁻¹ • ((VOA.deriv^[i] alphaLat) 0) = _
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    show (∏ m ∈ Finset.range i, ((0 : ℤ) + 1 + (m : ℤ))) = (i.factorial : ℤ) from by
        rw [← VertexOperatorAlgebra.prod_one_add_factorial]
        exact Finset.prod_congr rfl (fun m _ => by ring),
    ← Int.cast_smul_eq_zsmul ℂ (i.factorial : ℤ), Int.cast_natCast, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero i), one_smul,
    show (0 : ℤ) + (i : ℤ) = (i : ℤ) from by ring, alphaLat,
    if_neg (by omega : ¬ (i : ℤ) = -1), add_zero]

/-- The **word-state map**: the boson creation word applied to the charge-`m` vacuum `e^{mα}`. -/
noncomputable def wordStateLat : List ℕ → ℤ → LatModule
  | [], m => latState m
  | (i :: rest), m => LinearMap.rTensor LatGrp (alphaField i) (wordStateLat rest m)

@[simp] theorem wordStateLat_nil (m : ℤ) : wordStateLat [] m = latState m := rfl

theorem wordStateLat_cons (i : ℕ) (rest : List ℕ) (m : ℤ) :
    wordStateLat (i :: rest) m
      = LinearMap.rTensor LatGrp (alphaField i) (wordStateLat rest m) := rfl

/-- **Creation tower (power-series part)**: `(YwordLat l m)_q |0⟩ = 0` for `q < 0`. -/
theorem YwordLat_vacuum_neg :
    ∀ (l : List ℕ) (m : ℤ) {q : ℤ}, q < 0 → (YwordLat l m) q latVacuum = 0
  | [], m, q, hq => by rw [YwordLat_nil, Yemα_vacuum, if_neg (by omega)]
  | (i :: rest), m, q, hq => by
      rw [YwordLat_cons]
      exact nprod_vacuum_neg_gen (genFieldLat_isField i) (YwordLat_isField rest m)
        latVacuum (fun s hs => genFieldLat_vacuum_neg i hs)
        (fun s hs => YwordLat_vacuum_neg rest m hs) hq

/-- **Creation tower (base)**: `(YwordLat l m)_0 |0⟩ = wordStateLat l m`. -/
theorem YwordLat_vacuum_base :
    ∀ (l : List ℕ) (m : ℤ), (YwordLat l m) 0 latVacuum = wordStateLat l m
  | [], m => by rw [YwordLat_nil, wordStateLat_nil, Yemα_creation_z0]
  | (i :: rest), m => by
      rw [YwordLat_cons,
        nprod_vacuum_base_gen (genFieldLat_isField i) (YwordLat_isField rest m)
          latVacuum (fun s hs => genFieldLat_vacuum_neg i hs)
          (fun s hs => YwordLat_vacuum_neg rest m hs),
        genFieldLat_zero_op, YwordLat_vacuum_base rest m, wordStateLat_cons]

/-! ## §C  Spanning of the word states. -/

/-- The boson generator's `z⁰` action creates the boson variable `X_i`: `αField i p = X_{(i,0)}·p`. -/
theorem alphaField_creation (i : ℕ) (p : B) :
    alphaField i p = MvPolynomial.X ((i, 0) : ℕ × Fin 1) * p := by
  rw [alphaField, HeisenbergN.currentN_apply,
    HeisenbergN.oscN_apply_neg 1 2 0 (by omega : -(i : ℤ) - 1 < 0),
    show (-(-(i : ℤ) - 1) - 1).toNat = i from by omega]

/-- The word state is the boson monomial (`HeisenbergN.wordStateN`) tensor the lattice point. -/
theorem wordStateLat_eq (l : List ℕ) (m : ℤ) :
    wordStateLat l m
      = (HeisenbergN.wordStateN (l.map (fun i => ((i, 0) : ℕ × Fin 1)))) ⊗ₜ[ℂ] eVec m := by
  induction l with
  | nil => rw [wordStateLat_nil]; rfl
  | cons i rest ih =>
      rw [wordStateLat_cons, ih, List.map_cons, HeisenbergN.wordStateN_cons,
        LinearMap.rTensor_tmul, alphaField_creation]

/-- **The word states span** `LatModule` (the `hspan` input): every boson monomial tensor lattice
point is a word state, and these span via `TensorProduct.span_tmul_eq_top` + the `FockN 1` monomial
basis + the `eVec`-spanning of `ℂ{ℤ}`. -/
theorem wordStateLat_span :
    Submodule.span ℂ (Set.range (Function.uncurry wordStateLat)) = ⊤ := by
  set S := Submodule.span ℂ (Set.range (Function.uncurry wordStateLat)) with hS
  -- (1) each monomial ⊗ eVec m is a word state
  have hmono : ∀ (a : (ℕ × Fin 1) →₀ ℕ) (m : ℤ),
      (MvPolynomial.monomial a (1 : ℂ)) ⊗ₜ[ℂ] eVec m ∈ S := by
    intro a m
    have hword : wordStateLat ((HeisenbergN.monoWordN a).map Prod.fst) m
        = (MvPolynomial.monomial a (1 : ℂ)) ⊗ₜ[ℂ] eVec m := by
      rw [wordStateLat_eq, List.map_map,
        show (HeisenbergN.monoWordN a).map ((fun i => ((i, 0) : ℕ × Fin 1)) ∘ Prod.fst)
            = HeisenbergN.monoWordN a from by
          rw [List.map_congr_left (g := id) (fun e _ => by
              simp only [Function.comp_apply, id_eq]
              exact Prod.ext rfl (Subsingleton.elim _ _)), List.map_id],
        HeisenbergN.wordStateN_monoWordN]
    rw [← hword]
    exact Submodule.subset_span ⟨((HeisenbergN.monoWordN a).map Prod.fst, m), rfl⟩
  -- (2) each p ⊗ eVec m is in S (p as a sum of monomials)
  have hpe : ∀ (p : B) (m : ℤ), p ⊗ₜ[ℂ] eVec m ∈ S := by
    intro p m
    rw [← MvPolynomial.support_sum_monomial_coeff p, TensorProduct.sum_tmul]
    refine Submodule.sum_mem _ (fun a _ => ?_)
    rw [show (MvPolynomial.monomial a (MvPolynomial.coeff a p))
          = (MvPolynomial.coeff a p) • MvPolynomial.monomial a (1 : ℂ) from by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
      ← TensorProduct.smul_tmul' (MvPolynomial.coeff a p) (MvPolynomial.monomial a (1 : ℂ))
        (eVec m)]
    exact Submodule.smul_mem _ _ (hmono a m)
  -- (3) span via the tensor generators (decompose `g` over the `eVec` basis by `Finsupp` induction)
  rw [hS, eq_top_iff, ← TensorProduct.span_tmul_eq_top ℂ B LatGrp, Submodule.span_le]
  rintro _ ⟨p, g, rfl⟩
  rw [SetLike.mem_coe]
  induction g using Finsupp.induction with
  | zero => erw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
  | single_add n c g' _ _ ih =>
      erw [TensorProduct.tmul_add]
      refine Submodule.add_mem _ ?_ ih
      rw [show (Finsupp.single n c : LatGrp) = c • eVec n from by
          rw [eVec, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]]
      erw [TensorProduct.tmul_smul]
      exact Submodule.smul_mem _ _ (hpe p n)

end VOA.LatExp
