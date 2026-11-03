/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.AffineGeneral.SugawaraField
import VOA.Core.VertexOperatorAlgebra

/-!
# Actual sl3 creation words and their mutually local fields

*General-`𝔤` port* of `VOA/Examples/AffineSl3WordFields.lean` (generated mechanically from that file):
the index type is `ι`, the Lie data is `D : LieData κ ι`, the dual Coxeter number is `D.h`.  Where the
text below says sl₃, `Fin 8`, `6` or `3`, read `𝔤`, `ι`, `2 * D.h` and `D.h`.

Finite derivatives of the eight currents and iterated normal products
supply fields for every creation word. The vacuum creation identities
and pairwise locality are proved before choosing any state-field map.
-/
namespace VOA.AffineGeneral
open VOA VOA.AffineLie Module
noncomputable section

open LieData
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (D : LieData κ ι)
set_option maxHeartbeats 4000000
/-- The **scaled generator field** `genFieldA k a i := (i!)⁻¹ · ∂_z^i J^a(z)` — in the
vertex indexing exactly `Y(J^a_{-i-1}|0⟩, z)` (Gannon 5.2.5). -/
noncomputable def genFieldA (k : ℂ) (a : ι) (i : ℕ) :
    FormalDist (End ℂ (Vacuum D k)) :=
  (i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (Jfield D k a))

/-- Factorial-scaled derivatives preserve current lower truncation. -/
theorem genFieldA_isField (k : ℂ) (a : ι) (i : ℕ) : IsField (genFieldA D k a i) := by
  intro x
  obtain ⟨B, hB⟩ := (Jfield_isField D k a).deriv_iterate i x
  exact ⟨B, fun n hn => by
    show ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (Jfield D k a)) n) x = 0
    rw [LinearMap.smul_apply, hB n hn, smul_zero]⟩

/-- At derivative order zero the generator field is the original current. -/
theorem genFieldA_zero (k : ℂ) (a : ι) : genFieldA D k a 0 = Jfield D k a := by
  rw [genFieldA, Function.iterate_zero, id, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]

/-- The **identity field** `Y(|0⟩,z) = id`. -/
noncomputable def idFieldA (k : ℂ) : FormalDist (End ℂ (Vacuum D k)) :=
  fun j => if j = 0 then LinearMap.id else 0

/-- The identity field has only its degree-zero coefficient. -/
theorem idFieldA_isField (k : ℂ) : IsField (idFieldA D k) :=
  fun x => ⟨0, fun n hn => by rw [idFieldA, if_neg (by omega)]; rfl⟩

/-- The iterated normal-ordered product over a creation word `(a,i) :: …`, paired with its
field witness: `[]` ↦ the identity field; `(a,i) :: rest` ↦ `:(genFieldA a i)(YwordA rest):`. -/
noncomputable def YwordAF (k : ℂ) :
    List (ι × ℕ) → { f : FormalDist (End ℂ (Vacuum D k)) // IsField f }
  | [] => ⟨idFieldA D k, idFieldA_isField D k⟩
  | (ai :: rest) =>
      let p := YwordAF k rest
      ⟨nprod (genFieldA_isField D k ai.1 ai.2) p.2,
        IsField.nprod (genFieldA_isField D k ai.1 ai.2) p.2⟩

/-- The iterated normal-ordered product `YwordA k [(a₁,i₁),…] = :(∂^{i₁}J^{a₁}/i₁!)⋯:`. -/
noncomputable def YwordA (k : ℂ) (l : List (ι × ℕ)) :
    FormalDist (End ℂ (Vacuum D k)) := (YwordAF D k l).1

/-- Every iterated normal product is lower-truncated by its inductive construction. -/
theorem YwordA_isField (k : ℂ) (l : List (ι × ℕ)) : IsField (YwordA D k l) :=
  (YwordAF D k l).2

/-- The empty creation word corresponds to the identity field. -/
@[simp] theorem YwordA_nil (k : ℂ) : YwordA D k [] = idFieldA D k := rfl

/-- Prepending a creation mode corresponds to one further normal product. -/
theorem YwordA_cons (k : ℂ) (ai : ι × ℕ) (rest : List (ι × ℕ)) :
    YwordA D k (ai :: rest)
      = nprod (genFieldA_isField D k ai.1 ai.2) (YwordA_isField D k rest) := rfl

/-! ## §B″  The word-field locality cascade (VA4 reduction toward reconstruction)

Every two iterated word fields are mutually local — the VA4 datum the reconstruction theorem
needs on the generating fields.  Proved by the same iterated `dong_neg` cascade as the free
boson (`Examples.HeisenbergNVertex`): the current-field locality `Jfield_local` lifts to the
scaled generators `genFieldA` (derivative locality + scalar), then to words by induction. -/

/-- Iterated derivatives of the current fields are mutually local. -/
theorem dJfield_local (k : ℂ) (a b : ι) (i j : ℕ) :
    Local (VOA.deriv^[i] (Jfield D k a)) (VOA.deriv^[j] (Jfield D k b)) :=
  ((Jfield_local D k a b).deriv_iterate_left i).deriv_iterate_right j

/-- The scaled generator fields `genFieldA k a i = (i!)⁻¹ ∂_z^i J^a(z)` are mutually local. -/
theorem genFieldA_local (k : ℂ) (a b : ι) (i j : ℕ) :
    Local (genFieldA D k a i) (genFieldA D k b j) := by
  change Local ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (Jfield D k a)))
    ((j.factorial : ℂ)⁻¹ • (VOA.deriv^[j] (Jfield D k b)))
  exact Reconstruction.Local.smulR _ (VertexOperatorAlgebra.Local.smul' _ (dJfield_local D k a b i j))

/-- The identity field commutes with every distribution: `[1(z₁), b(z₂)] = 0`. -/
theorem bracketDist_idFieldA_left (k : ℂ) (b : FormalDist (End ℂ (Vacuum D k))) :
    bracketDist (idFieldA D k) b = 0 := by
  apply FormalDist₂.ext; intro m n
  rw [bracketDist_apply, idFieldA]
  change (if m = 0 then LinearMap.id else 0 : End ℂ (Vacuum D k)) * b n
      - b n * (if m = 0 then LinearMap.id else 0) = (0 : FormalDist₂ (End ℂ (Vacuum D k))) m n
  by_cases h : m = 0
  · rw [if_pos h, show (LinearMap.id : End ℂ (Vacuum D k)) = 1 from rfl, one_mul, mul_one, sub_self]
    rfl
  · rw [if_neg h, zero_mul, mul_zero, sub_zero]; rfl

/-- The identity field has zero commutator with every distribution. -/
theorem Local_idFieldA_left (k : ℂ) (b : FormalDist (End ℂ (Vacuum D k))) :
    Local (idFieldA D k) b :=
  local_of_bracketDist_eq_zero (bracketDist_idFieldA_left D k b)

/-- Locality with the identity also holds in the reversed order. -/
theorem Local_idFieldA_right (k : ℂ) (b : FormalDist (End ℂ (Vacuum D k))) :
    Local b (idFieldA D k) :=
  (Local_idFieldA_left D k b).symm

/-- Each generator field is local with every iterated word field (induction on the word). -/
theorem genFieldA_local_YwordA (k : ℂ) :
    ∀ (l : List (ι × ℕ)) (i : ℕ) (a : ι),
      Local (genFieldA D k a i) (YwordA D k l) := by
  intro l
  induction l with
  | nil => intro i a; rw [YwordA_nil]; exact Local_idFieldA_right D k _
  | cons ai rest ih =>
      intro i a
      have hab : Local (genFieldA D k ai.1 ai.2) (YwordA D k rest) := ih ai.2 ai.1
      have hac : Local (genFieldA D k ai.1 ai.2) (genFieldA D k a i) :=
        genFieldA_local D k ai.1 a ai.2 i
      have hbc : Local (YwordA D k rest) (genFieldA D k a i) := (ih i a).symm
      have hmain : Local (nprod (genFieldA_isField D k ai.1 ai.2) (YwordA_isField D k rest))
          (genFieldA D k a i) :=
        dong_neg (genFieldA_isField D k ai.1 ai.2) (YwordA_isField D k rest) hab hac hbc
      rw [YwordA_cons]
      exact hmain.symm

/-- **VA4 reduction** (Gannon 5.2.5c): every two iterated word fields are mutually local — the
locality datum on the generating fields that the reconstruction theorem consumes. -/
theorem YwordA_local (k : ℂ) :
    ∀ (l₁ l₂ : List (ι × ℕ)), Local (YwordA D k l₁) (YwordA D k l₂) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; rw [YwordA_nil]; exact Local_idFieldA_left D k _
  | cons ai rest ih =>
      intro l₂
      have hab : Local (genFieldA D k ai.1 ai.2) (YwordA D k rest) :=
        genFieldA_local_YwordA D k rest ai.2 ai.1
      have hac : Local (genFieldA D k ai.1 ai.2) (YwordA D k l₂) :=
        genFieldA_local_YwordA D k l₂ ai.2 ai.1
      have hbc : Local (YwordA D k rest) (YwordA D k l₂) := ih l₂
      have hmain : Local (nprod (genFieldA_isField D k ai.1 ai.2) (YwordA_isField D k rest))
          (YwordA D k l₂) :=
        dong_neg (genFieldA_isField D k ai.1 ai.2) (YwordA_isField D k rest) hab hac hbc
      rw [YwordA_cons]
      exact hmain

/-! ## §B‴  The creation tower of the word fields (STEP 2 of reconstruction)

Each iterated word field `YwordA k l` *creates* its word-state from the vacuum as a power series:
`(YwordA k l)_0 |0⟩ = wordStateA l` (the creation word) and `(YwordA k l)_q |0⟩ = 0` for `q < 0`.
Together with `YwordA_local` this pins each word field by its created state (the data the
reconstruction `YA` is defined from).  Built on the generic `nprod_vacuum_{base,neg}_gen`
(`Core.Dong`) + the highest-weight condition `vacuum_pos_annihilate`. -/

/-- Positive current modes annihilate the vacuum: `J^a_m |0⟩ = 0` for `m ≥ 0`. -/
theorem J_vacuum_nonneg (k : ℂ) (a : ι) {m : ℤ} (hm : 0 ≤ m) : J D k a m (vacuumA D k) = 0 :=
  vacuum_pos_annihilate κ D.invariant k (D.generator a) m hm

/-- The generator field annihilates the vacuum below degree `0` (a power series on `|0⟩`). -/
theorem genFieldA_vacuum_neg (k : ℂ) (a : ι) (i : ℕ) {q : ℤ} (hq : q < 0) :
    genFieldA D k a i q (vacuumA D k) = 0 := by
  show ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (Jfield D k a)) q) (vacuumA D k) = 0
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    ← Int.cast_smul_eq_zsmul ℂ (∏ m ∈ Finset.range i, (q + 1 + (m : ℤ)))]
  simp only [LinearMap.smul_apply]
  by_cases hqi : q + (i : ℤ) < 0
  · rw [Jfield_vacuum_neg D k a (show q + (i : ℤ) < 0 by omega), smul_zero, smul_zero]
  · rw [Finset.prod_eq_zero (i := (-q - 1).toNat) (Finset.mem_range.mpr (by omega))
        (by rw [show ((-q - 1).toNat : ℤ) = -q - 1 from by omega]; ring),
      Int.cast_zero, zero_smul, smul_zero]

/-- The generator field's `z⁰`-coefficient is the creation mode: `(genFieldA k a i)₀ = J^a_{-i-1}`. -/
theorem genFieldA_zero_op (k : ℂ) (a : ι) (i : ℕ) :
    (genFieldA D k a i) 0 = J D k a (-(i : ℤ) - 1) := by
  show (i.factorial : ℂ)⁻¹ • ((VOA.deriv^[i] (Jfield D k a)) 0) = _
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    show (∏ m ∈ Finset.range i, ((0 : ℤ) + 1 + (m : ℤ))) = (i.factorial : ℤ) from by
        rw [← VertexOperatorAlgebra.prod_one_add_factorial]
        exact Finset.prod_congr rfl (fun m _ => by ring),
    ← Int.cast_smul_eq_zsmul ℂ (i.factorial : ℤ), Int.cast_natCast, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero i), one_smul,
    show (0 : ℤ) + (i : ℤ) = (i : ℤ) from by ring, Jfield_apply]

/-- The **word-state map**: the creation word applied to the vacuum (matching `negWord`). -/
noncomputable def wordStateA (k : ℂ) : List (ι × ℕ) → Vacuum D k
  | [] => vacuumA D k
  | (ai :: rest) => J D k ai.1 (-(ai.2 : ℤ) - 1) (wordStateA k rest)

/-- The empty current word creates the vacuum. -/
@[simp] theorem wordStateA_nil (k : ℂ) : wordStateA D k [] = vacuumA D k := rfl

/-- A nonempty word acts by its first negative current mode on the remaining word state. -/
theorem wordStateA_cons (k : ℂ) (ai : ι × ℕ) (rest : List (ι × ℕ)) :
    wordStateA D k (ai :: rest) = J D k ai.1 (-(ai.2 : ℤ) - 1) (wordStateA D k rest) := rfl

/-- **Creation tower (power-series part)**: `(YwordA k l)_q |0⟩ = 0` for `q < 0`. -/
theorem YwordA_vacuum_neg (k : ℂ) (l : List (ι × ℕ)) :
    ∀ {q : ℤ}, q < 0 → (YwordA D k l) q (vacuumA D k) = 0 := by
  induction l with
  | nil =>
      intro q hq
      rw [YwordA_nil]
      show (if q = 0 then (LinearMap.id : End ℂ (Vacuum D k)) else 0) (vacuumA D k) = 0
      rw [if_neg (by omega : ¬ q = 0)]; rfl
  | cons ai rest ih =>
      intro q hq
      rw [YwordA_cons]
      exact nprod_vacuum_neg_gen (genFieldA_isField D k ai.1 ai.2) (YwordA_isField D k rest)
        (vacuumA D k) (fun s hs => genFieldA_vacuum_neg D k ai.1 ai.2 hs) (fun s hs => ih hs) hq

/-- **Creation tower (base)**: `(YwordA k l)_0 |0⟩ = wordStateA l` — the field creates the
word-state from the vacuum. -/
theorem YwordA_vacuum_base (k : ℂ) (l : List (ι × ℕ)) :
    (YwordA D k l) 0 (vacuumA D k) = wordStateA D k l := by
  induction l with
  | nil =>
      rw [YwordA_nil]
      show (if (0 : ℤ) = 0 then (LinearMap.id : End ℂ (Vacuum D k)) else 0) (vacuumA D k)
        = wordStateA D k []
      rw [if_pos rfl]; rfl
  | cons ai rest ih =>
      rw [YwordA_cons,
        nprod_vacuum_base_gen (genFieldA_isField D k ai.1 ai.2) (YwordA_isField D k rest)
          (vacuumA D k) (fun s hs => genFieldA_vacuum_neg D k ai.1 ai.2 hs)
          (fun s hs => YwordA_vacuum_neg D k rest hs),
        genFieldA_zero_op, ih, wordStateA_cons]


end
end VOA.AffineGeneral
