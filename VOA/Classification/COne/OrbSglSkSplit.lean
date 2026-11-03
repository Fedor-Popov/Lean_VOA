import VOA.Classification.COne.OrbSglSkew

/-!
# OrbSgl (5c): chunked certification of the skew-symmetry terms

A single certificate `VectorCertificate (uTerm isJ k i) P` for small `k + i` costs the kernel up
to about 11 GB.  The terms are linear in the input state, so the input is cut into chunks
`C` (with `C.flatten` certified equal to the input), each chunk is certified separately, and the
chunk outputs `A` are reassembled (`A.flatten` certified equal to the final data).
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbSgl

open VOA VertexOperatorAlgebra VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational
  OrbC2g OrbC2h OrbC2c OrbC2e OrbC2f PlusC2 PlusC2Eval PlusUnitary

local notation "V8" => V2m 4 four_ge_one

/-- The chunked term `L(-1)ʲ a₍ₙ₎ (Σ chunks)` is the sum of the certified chunk values. -/
theorem evaluate_chunks (isJ : Bool) (n : ℤ) (j : ℕ) :
    ∀ (C A : List SectorVector),
      List.Forall₂ (fun c a => VectorCertificate (Tpow j (aLeft isJ n c)) a) C A →
      evaluate (Tpow j (aLeft isJ n C.flatten)) = evaluate A.flatten := by
  intro C A h
  induction h with
  | nil =>
    simp only [List.flatten_nil, evaluate_Tpow, evaluate_aLeft]
    simp [evaluate]
  | cons hca _ ih =>
    rename_i c a C A
    have h1 := vector_eq_of_certificate _ _ hca
    rw [evaluate_Tpow, evaluate_aLeft] at h1 ih
    rw [List.flatten_cons, List.flatten_cons, evaluate_append, evaluate_Tpow, evaluate_aLeft,
      evaluate_append, PreVertexAlgebra.smul_add_right, map_add, h1, ih]

/-- Stage 1 from chunks of `nineData`. -/
theorem uTerm_of_chunks (isJ : Bool) (k i : ℕ) (n : ℤ) (hn : n = (k : ℤ) + i)
    (C A : List SectorVector) (hC : VectorCertificate C.flatten nineData)
    (hA : List.Forall₂ (fun c a => VectorCertificate (Tpow i (aLeft isJ n c)) a) C A)
    (X : SectorVector) (hX : VectorCertificate A.flatten X) :
    evaluate X = evaluate (uTerm isJ k i) := by
  rw [← vector_eq_of_certificate _ _ hX, ← evaluate_chunks isJ n i C A hA, uTerm, hn,
    evaluate_Tpow, evaluate_Tpow, evaluate_aLeft, evaluate_aLeft,
    vector_eq_of_certificate _ _ hC]

/-- Stage 2 from chunks of `Y`. -/
theorem vTerm_of_chunks (isJ : Bool) (Y : SectorVector) (k j : ℕ) (n : ℤ)
    (hn : n = 6 - (k : ℤ) + j)
    (C A : List SectorVector) (hC : VectorCertificate C.flatten Y)
    (hA : List.Forall₂ (fun c a => VectorCertificate (Tpow j (aLeft isJ n c)) a) C A)
    (X : SectorVector) (hX : VectorCertificate A.flatten X) :
    evaluate X = evaluate (vTerm isJ Y k j) := by
  rw [← vector_eq_of_certificate _ _ hX, ← evaluate_chunks isJ n j C A hA, vTerm, hn,
    evaluate_Tpow, evaluate_Tpow, evaluate_aLeft, evaluate_aLeft,
    vector_eq_of_certificate _ _ hC]

end VOA.Classification.COne.OrbSgl
