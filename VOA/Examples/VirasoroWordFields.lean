/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroSpanning
import VOA.Core.Reconstruction
import VOA.Core.ReconstructionExistence
import VOA.Examples.HeisenbergVertex

/-!
# The Virasoro word fields

From the single generating field `Y(ω,z)` we build, by `z`-derivatives and iterated normal-ordered
products, the family of **word fields** `YwordVir ws` indexed by `ws : List ℕ` (the tower of
`:∂^{i₁}ω ⋯ ∂^{iₖ}ω:`), each an `IsField`, pairwise local (Dong's lemma), with creation tower
`(YwordVir ws)₀|0⟩ = negWordVir ws` (the creation monomial) and `(YwordVir ws)_q|0⟩ = 0` for `q<0`.

These supply the generating data the `Core` operator-first reconstruction theorem consumes; the
creation states `negWordVir ws` span `VirUniv c` (`negSpanVir_eq_top`).  Mirror of the free-boson /
affine word-field cascade, but for the single Virasoro generator.  `sorry`-free, axiom-clean,
`pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.VirModule

open VOA
open Module (End)
open VOA.Reconstruction

variable (c : ℂ)

/-! ## §1  The generator fields, identity field, and word fields. -/

/-- The **scaled generator field** `genFieldVir i := (i!)⁻¹ · ∂_z^i Y(ω,z)` — in the vertex
indexing exactly `Y(ω₍₋ᵢ₋₁₎|0⟩, z) = Y(L₋ᵢ₋₂|0⟩, z)`. -/
noncomputable def genFieldVir (i : ℕ) : FormalDist (End ℂ (VirUniv c)) :=
  (i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (YomegaVir c))

/-- Differentiating the generating field and dividing by a factorial preserves the field property: on any fixed state, sufficiently high modes still vanish. -/
theorem genFieldVir_isField (i : ℕ) : IsField (genFieldVir c i) := by
  intro x
  obtain ⟨B, hB⟩ := (YomegaVir_isField c).deriv_iterate i x
  exact ⟨B, fun n hn => by
    change ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (YomegaVir c)) n) x = 0
    rw [LinearMap.smul_apply, hB n hn, smul_zero]⟩

/-- The **identity field** `Y(|0⟩,z) = id`. -/
noncomputable def idFieldVir : FormalDist (End ℂ (VirUniv c)) :=
  fun j => if j = 0 then LinearMap.id else 0

/-- The vacuum field is a field because its only nonzero coefficient is the identity operator at index zero. -/
theorem idFieldVir_isField : IsField (idFieldVir c) :=
  fun x => ⟨0, fun n hn => by rw [idFieldVir, if_neg (by omega)]; rfl⟩

/-- The iterated normal-ordered product over a creation word, paired with its field witness. -/
noncomputable def YwordVirF :
    List ℕ → { f : FormalDist (End ℂ (VirUniv c)) // IsField f }
  | [] => ⟨idFieldVir c, idFieldVir_isField c⟩
  | (i :: rest) =>
      let p := YwordVirF rest
      ⟨nprod (genFieldVir_isField c i) p.2, IsField.nprod (genFieldVir_isField c i) p.2⟩

/-- The iterated normal-ordered product `YwordVir [i₁,…] = :(∂^{i₁}ω/i₁!)⋯:`. -/
noncomputable def YwordVir (ws : List ℕ) : FormalDist (End ℂ (VirUniv c)) := (YwordVirF c ws).1

/-- Every recursively normal-ordered word is a field. The construction stores this truncation proof together with the coefficients, so it survives each recursion step. -/
theorem YwordVir_isField (ws : List ℕ) : IsField (YwordVir c ws) := (YwordVirF c ws).2

/-- An empty creation word represents the vacuum, whose field is the identity distribution. -/
@[simp] theorem YwordVir_nil : YwordVir c [] = idFieldVir c := rfl

/-- Adding a creation mode at the front of a word amounts to taking the normal-ordered product of its differentiated generator field with the shorter word field. -/
theorem YwordVir_cons (i : ℕ) (rest : List ℕ) :
    YwordVir c (i :: rest) = nprod (genFieldVir_isField c i) (YwordVir_isField c rest) := rfl

/-! ## §2  The word-field locality cascade (VA4 datum for reconstruction). -/

/-- Iterated derivatives of `Y(ω,z)` are mutually local (from `YomegaVir_self_local`). -/
theorem dYomegaVir_local (i j : ℕ) :
    Local (VOA.deriv^[i] (YomegaVir c)) (VOA.deriv^[j] (YomegaVir c)) :=
  ((YomegaVir_self_local c).deriv_iterate_left i).deriv_iterate_right j

/-- The scaled generator fields are mutually local. -/
theorem genFieldVir_local (i j : ℕ) : Local (genFieldVir c i) (genFieldVir c j) := by
  change Local ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (YomegaVir c)))
    ((j.factorial : ℂ)⁻¹ • (VOA.deriv^[j] (YomegaVir c)))
  exact Local.smulR _ (VertexOperatorAlgebra.Local.smul' _ (dYomegaVir_local c i j))

/-- The identity field commutes with every distribution. -/
theorem bracketDist_idFieldVir_left (b : FormalDist (End ℂ (VirUniv c))) :
    bracketDist (idFieldVir c) b = 0 := by
  apply FormalDist₂.ext; intro m n
  rw [bracketDist_apply, idFieldVir]
  change (if m = 0 then LinearMap.id else 0 : End ℂ (VirUniv c)) * b n
      - b n * (if m = 0 then LinearMap.id else 0) = (0 : FormalDist₂ (End ℂ (VirUniv c))) m n
  by_cases h : m = 0
  · rw [if_pos h, show (LinearMap.id : End ℂ (VirUniv c)) = 1 from rfl, one_mul, mul_one, sub_self]
    rfl
  · rw [if_neg h, zero_mul, mul_zero, sub_zero]; rfl

/-- The identity field is local with every formal distribution because all of its coefficients commute with every operator. No positive locality exponent is needed. -/
theorem Local_idFieldVir_left (b : FormalDist (End ℂ (VirUniv c))) : Local (idFieldVir c) b :=
  local_of_bracketDist_eq_zero (bracketDist_idFieldVir_left c b)

/-- Locality is symmetric, so the identity field may appear on either side of the locality relation. -/
theorem Local_idFieldVir_right (b : FormalDist (End ℂ (VirUniv c))) : Local b (idFieldVir c) :=
  (Local_idFieldVir_left c b).symm

/-- Each generator field is local with every word field (induction on the word). -/
theorem genFieldVir_local_YwordVir :
    ∀ (ws : List ℕ) (i : ℕ), Local (genFieldVir c i) (YwordVir c ws) := by
  intro ws
  induction ws with
  | nil => intro i; rw [YwordVir_nil]; exact Local_idFieldVir_right c _
  | cons j rest ih =>
      intro i
      have hab : Local (genFieldVir c j) (YwordVir c rest) := ih j
      have hac : Local (genFieldVir c j) (genFieldVir c i) := genFieldVir_local c j i
      have hbc : Local (YwordVir c rest) (genFieldVir c i) := (ih i).symm
      have hmain : Local (nprod (genFieldVir_isField c j) (YwordVir_isField c rest))
          (genFieldVir c i) :=
        dong_neg (genFieldVir_isField c j) (YwordVir_isField c rest) hab hac hbc
      rw [YwordVir_cons]
      exact hmain.symm

/-- **VA4 datum**: every two word fields are mutually local. -/
theorem YwordVir_local : ∀ (ws₁ ws₂ : List ℕ), Local (YwordVir c ws₁) (YwordVir c ws₂) := by
  intro ws₁
  induction ws₁ with
  | nil => intro ws₂; rw [YwordVir_nil]; exact Local_idFieldVir_left c _
  | cons i rest ih =>
      intro ws₂
      have hab : Local (genFieldVir c i) (YwordVir c rest) := genFieldVir_local_YwordVir c rest i
      have hac : Local (genFieldVir c i) (YwordVir c ws₂) := genFieldVir_local_YwordVir c ws₂ i
      have hbc : Local (YwordVir c rest) (YwordVir c ws₂) := ih ws₂
      have hmain : Local (nprod (genFieldVir_isField c i) (YwordVir_isField c rest))
          (YwordVir c ws₂) :=
        dong_neg (genFieldVir_isField c i) (YwordVir_isField c rest) hab hac hbc
      rw [YwordVir_cons]
      exact hmain

/-! ## §3  The creation tower of the word fields (VA3 datum for reconstruction). -/

/-- `Y(ω,z)` annihilates the vacuum below degree `0` (`L₋q₋₂|0⟩ = 0` for `q < 0`, since
`-q-2 ≥ -1`). -/
theorem YomegaVir_vacuum_neg {q : ℤ} (hq : q < 0) : (YomegaVir c) q (vacVec c) = 0 := by
  rw [YomegaVir_apply]; exact Lop_vacuum c (by omega)

/-- The generator field annihilates the vacuum below degree `0`. -/
theorem genFieldVir_vacuum_neg (i : ℕ) {q : ℤ} (hq : q < 0) :
    genFieldVir c i q (vacVec c) = 0 := by
  change ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (YomegaVir c)) q) (vacVec c) = 0
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    ← Int.cast_smul_eq_zsmul ℂ (∏ m ∈ Finset.range i, (q + 1 + (m : ℤ)))]
  simp only [LinearMap.smul_apply]
  by_cases hqi : q + (i : ℤ) < 0
  · rw [YomegaVir_vacuum_neg c (show q + (i : ℤ) < 0 by omega), smul_zero, smul_zero]
  · rw [Finset.prod_eq_zero (i := (-q - 1).toNat) (Finset.mem_range.mpr (by omega))
        (by rw [show ((-q - 1).toNat : ℤ) = -q - 1 from by omega]; ring),
      Int.cast_zero, zero_smul, smul_zero]

/-- The generator field's `z⁰`-coefficient is the creation mode `L₋ᵢ₋₂` (matching `negWordVir`). -/
theorem genFieldVir_zero_op (i : ℕ) : (genFieldVir c i) 0 = Lop c (-(i : ℤ) - 2) := by
  change (i.factorial : ℂ)⁻¹ • ((VOA.deriv^[i] (YomegaVir c)) 0) = _
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    show (∏ m ∈ Finset.range i, ((0 : ℤ) + 1 + (m : ℤ))) = (i.factorial : ℤ) from by
        rw [← VertexOperatorAlgebra.prod_one_add_factorial]
        exact Finset.prod_congr rfl (fun m _ => by ring),
    ← Int.cast_smul_eq_zsmul ℂ (i.factorial : ℤ), Int.cast_natCast, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero i), one_smul,
    show (0 : ℤ) + (i : ℤ) = (i : ℤ) from by ring, YomegaVir_apply]

/-- **Creation tower (power-series part)**: `(YwordVir ws)_q |0⟩ = 0` for `q < 0`. -/
theorem YwordVir_vacuum_neg (ws : List ℕ) :
    ∀ {q : ℤ}, q < 0 → (YwordVir c ws) q (vacVec c) = 0 := by
  induction ws with
  | nil =>
      intro q hq
      rw [YwordVir_nil]
      change (if q = 0 then (LinearMap.id : End ℂ (VirUniv c)) else 0) (vacVec c) = 0
      rw [if_neg (by omega : ¬ q = 0)]; rfl
  | cons i rest ih =>
      intro q hq
      rw [YwordVir_cons]
      exact nprod_vacuum_neg_gen (genFieldVir_isField c i) (YwordVir_isField c rest)
        (vacVec c) (fun s hs => genFieldVir_vacuum_neg c i hs) (fun s hs => ih hs) hq

/-- **Creation tower (base)**: `(YwordVir ws)_0 |0⟩ = negWordVir ws` — the field creates its
creation monomial from the vacuum. -/
theorem YwordVir_vacuum_base (ws : List ℕ) :
    (YwordVir c ws) 0 (vacVec c) = negWordVir c ws := by
  induction ws with
  | nil =>
      rw [YwordVir_nil]
      change (if (0 : ℤ) = 0 then (LinearMap.id : End ℂ (VirUniv c)) else 0) (vacVec c)
        = negWordVir c []
      rw [if_pos rfl]; rfl
  | cons i rest ih =>
      rw [YwordVir_cons,
        nprod_vacuum_base_gen (genFieldVir_isField c i) (YwordVir_isField c rest)
          (vacVec c) (fun s hs => genFieldVir_vacuum_neg c i hs)
          (fun s hs => YwordVir_vacuum_neg c rest hs),
        genFieldVir_zero_op, ih, negWordVir_cons]

end VOA.VirModule
