import VOA.Examples.AffineSl3Reconstruction
import VOA.Core.BareVA

/-!
# The actual sl3 state-field correspondence

At noncritical level, reconstruction supplies a vertex algebra without
grading, identifies the Sugawara state with its actual normal-ordered
field and proves translation. No Virasoro or rigidity conclusion is
asserted here.
-/
namespace VOA.AffineSl3
open Module (End)
open VOA.AffineLie
open scoped BigOperators

/-- The reconstruction-existence witness, fed the unconditional Sugawara covariance. -/
noncomputable def YAspec (k : ℂ) (hk : k + 3 ≠ 0) :=
  affineYA_exists k hk

/-- **The unconditional affine `𝔰𝔩₃` vertex map** `YA k hk : Vacuum k →ₗ FormalDist`. -/
noncomputable def YA (k : ℂ) (hk : k + 3 ≠ 0) :
    Vacuum k →ₗ[ℂ] FormalDist (End ℂ (Vacuum k)) :=
  (YAspec k hk).choose

/-- The chosen state-field map agrees with each iterated current word field. -/
theorem YA_wordState (k : ℂ) (hk : k + 3 ≠ 0) (l : List (Fin 8 × ℕ)) :
    YA k hk (wordStateA k l) = YwordA k l := (YAspec k hk).choose_spec.1 l

/-- Every reconstructed field is lower truncated on each vacuum-module vector. -/
theorem YA_isField (k : ℂ) (hk : k + 3 ≠ 0) (u : Vacuum k) : IsField (YA k hk u) :=
  (YAspec k hk).choose_spec.2.1 u

/-- The reconstructed fields of any two states are mutually local. -/
theorem YA_local (k : ℂ) (hk : k + 3 ≠ 0) (u v : Vacuum k) : Local (YA k hk u) (YA k hk v) :=
  (YAspec k hk).choose_spec.2.2.1 u v

/-- The constant vacuum coefficient of the reconstructed field recovers its state. -/
theorem YA_creation0 (k : ℂ) (hk : k + 3 ≠ 0) (u : Vacuum k) :
    (YA k hk u) 0 (vacuumA k) = u := (YAspec k hk).choose_spec.2.2.2.1 u

/-- Every negative power in a reconstructed field acting on the vacuum vanishes. -/
theorem YA_creationNeg (k : ℂ) (hk : k + 3 ≠ 0) (u : Vacuum k) {q : ℤ} (hq : q < 0) :
    (YA k hk u) q (vacuumA k) = 0 := (YAspec k hk).choose_spec.2.2.2.2.1 u q hq

/-- Sugawara translation differentiates every reconstructed field through commutators. -/
theorem YA_DCov (k : ℂ) (hk : k + 3 ≠ 0) (u : Vacuum k) :
    Reconstruction.DCovariant (Ltrans k) (YA k hk u) := (YAspec k hk).choose_spec.2.2.2.2.2 u

/-! ## VA2: the vacuum field is the unit -/

/-- The affine identity field is the unit field `1`. -/
theorem idFieldA_eq_one (k : ℂ) :
    idFieldA k = (1 : FormalDist (End ℂ (Vacuum k))) := by
  funext j
  rw [idFieldA, FormalDist.one_apply]
  split_ifs <;> rfl

/-- **VA2** (`hYA_vac`): `YA |0⟩ = 1`. -/
theorem YA_vacuum (k : ℂ) (hk : k + 3 ≠ 0) :
    YA k hk (vacuumA k) = (1 : FormalDist (End ℂ (Vacuum k))) := by
  rw [← wordStateA_nil k, YA_wordState, YwordA_nil, idFieldA_eq_one]

/-! ## VA3 creation, VA5 regularity in `mode` form -/

/-- **VA3** (`hYA_creation`): `u₍₋₁₎|0⟩ = u` and `u₍ₙ₎|0⟩ = 0` for `n ≥ 0`. -/
theorem YA_creation (k : ℂ) (hk : k + 3 ≠ 0) (u : Vacuum k) :
    mode (YA k hk u) (-1) (vacuumA k) = u
      ∧ ∀ n : ℤ, 0 ≤ n → mode (YA k hk u) n (vacuumA k) = 0 := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [mode_apply, show (-(-1) - 1 : ℤ) = 0 from by ring, YA_creation0]
  · rw [mode_apply]; exact YA_creationNeg k hk u (by omega)

/-- **VA5** (`hYA_reg`): for each `u, v` the products `u₍ₙ₎v` vanish for `n` large. -/
theorem YA_regularity (k : ℂ) (hk : k + 3 ≠ 0) (u v : Vacuum k) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (YA k hk u) n v = 0 := by
  obtain ⟨B, hB⟩ := YA_isField k hk u v
  refine ⟨-B, fun n hn => ?_⟩
  rw [mode_apply]
  exact hB (-n - 1) (by omega)

/-! ## VOA `ω ∈ grading 2` -/

/-- **`hYA_omega_mem`**: the Sugawara conformal vector `ω = (T)₀|0⟩` has conformal weight `2`. -/
theorem omegaA_mem (k : ℂ) : omegaA k ∈ gradingZA k 2 := by
  rw [omegaA_eq, sugawaraField]
  show (2 * (k + dualCoxeter))⁻¹ • (Reconstruction.evalAt 0 (vacuumA k)
      (∑ aa : Fin 8, ∑ bb : Fin 8,
        kappaInv aa bb • nprod (Jfield_isField k aa) (Jfield_isField k bb))) ∈ gradingZA k 2
  refine Submodule.smul_mem _ _ ?_
  rw [map_sum]
  refine Submodule.sum_mem _ (fun aa _ => ?_)
  rw [map_sum]
  refine Submodule.sum_mem _ (fun bb _ => ?_)
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  show nprod (Jfield_isField k aa) (Jfield_isField k bb) 0 (vacuumA k) ∈ gradingZA k 2
  rw [nprod_vacuum_base_gen (Jfield_isField k aa) (Jfield_isField k bb) (vacuumA k)
      (fun q hq => Jfield_vacuum_neg k aa hq) (fun q hq => Jfield_vacuum_neg k bb hq),
    Jfield_apply, Jfield_apply, show (-(0 : ℤ) - 1) = -1 from by ring]
  rw [show (2 : ℤ) = 1 - (-1) from by ring]
  refine J_mem_gradingZA k aa (-1) 1 ?_
  rw [show (1 : ℤ) = 0 - (-1) from by ring]
  exact J_mem_gradingZA k bb (-1) 0 (vacuumA_mem_gradingZA_zero k)

/-! ## VOA3 translation: `YA (L₋₁ v) = ∂_z YA(v)` -/

/-- The Sugawara field is `T`-covariant (lift `Jfield_DCovariant` through `nprod`/scaling/sums). -/
theorem sugawaraField_DCovariant (k : ℂ) (hk : k + 3 ≠ 0) :
    Reconstruction.DCovariant (Ltrans k) (sugawaraField k) := by
  rw [sugawaraField]
  refine Reconstruction.DCovariant.smul _ ?_
  refine Reconstruction.DCovariant.finsetSum _ _ (fun aa _ => ?_)
  refine Reconstruction.DCovariant.finsetSum _ _ (fun bb _ => ?_)
  refine Reconstruction.DCovariant.smul _ ?_
  exact Reconstruction.DCovariant.nprod (Jfield_isField k aa) (Jfield_isField k bb)
    (SugawaraCov.Jfield_DCovariant k hk aa) (SugawaraCov.Jfield_DCovariant k hk bb)

/-- The Sugawara field annihilates the vacuum below degree `0`. -/
theorem sugawaraField_vacuum_neg (k : ℂ) (q : ℤ) (hq : q < 0) :
    (sugawaraField k) q (vacuumA k) = 0 := by
  rw [sugawaraField]
  show (2 * (k + dualCoxeter))⁻¹ • (Reconstruction.evalAt q (vacuumA k)
      (∑ aa : Fin 8, ∑ bb : Fin 8,
        kappaInv aa bb • nprod (Jfield_isField k aa) (Jfield_isField k bb))) = 0
  rw [map_sum]
  refine smul_eq_zero_of_right _ (Finset.sum_eq_zero (fun aa _ => ?_))
  rw [map_sum]
  refine Finset.sum_eq_zero (fun bb _ => ?_)
  rw [map_smul]
  show kappaInv aa bb • (nprod (Jfield_isField k aa) (Jfield_isField k bb) q (vacuumA k)) = 0
  rw [nprod_vacuum_neg_gen (Jfield_isField k aa) (Jfield_isField k bb) (vacuumA k)
    (fun s hs => Jfield_vacuum_neg k aa hs) (fun s hs => Jfield_vacuum_neg k bb hs) hq, smul_zero]

/-- The Sugawara field is local with every word field (Dong's lemma on the current generators). -/
theorem sugawaraField_local_YwordA (k : ℂ) (l : List (Fin 8 × ℕ)) :
    Local (sugawaraField k) (YwordA k l) := by
  rw [sugawaraField]
  refine VertexOperatorAlgebra.Local.smul' _ ?_
  refine Reconstruction.Local.sum_left _ _ _ (fun aa _ => ?_)
  refine Reconstruction.Local.sum_left _ _ _ (fun bb _ => ?_)
  refine VertexOperatorAlgebra.Local.smul' _ ?_
  refine dong_neg (Jfield_isField k aa) (Jfield_isField k bb) (Jfield_local k aa bb) ?_ ?_
  · rw [← genFieldA_zero k aa]; exact genFieldA_local_YwordA k l 0 aa
  · rw [← genFieldA_zero k bb]; exact genFieldA_local_YwordA k l 0 bb

/-- `(YA v)₁ |0⟩ = L₋₁ v` (the first creation-tower step). -/
theorem YA_one_vac (k : ℂ) (hk : k + 3 ≠ 0) (v : Vacuum k) :
    (YA k hk v) 1 (vacuumA k) = Ltrans k v := by
  have h := congrArg (fun (R : End ℂ (Vacuum k)) => R (vacuumA k)) (YA_DCov k hk v 0)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
  rw [Ltrans_vacuum, map_zero, sub_zero, YA_creation0, show ((0 : ℤ) + 1) = 1 from by ring,
    one_smul] at h
  exact h.symm

/-- **`YA(ω) = T(z)`**: the field of the conformal vector is the Sugawara field (operator-first
uniqueness: both are local with the word fields, create `ω`, and share the full vacuum tower). -/
theorem YA_omega_eq (k : ℂ) (hk : k + 3 ≠ 0) : YA k hk (omegaA k) = sugawaraField k := by
  have hloc : ∀ l : List (Fin 8 × ℕ),
      Local (YA k hk (omegaA k) - sugawaraField k) (YwordA k l) := by
    intro l
    have h1 : Local (YA k hk (omegaA k)) (YwordA k l) := by
      rw [← YA_wordState k hk l]; exact YA_local k hk (omegaA k) (wordStateA k l)
    have h2 : Local (sugawaraField k) (YwordA k l) := sugawaraField_local_YwordA k l
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (sugawaraField k)]
    exact Reconstruction.Local.add_left h1 (VertexOperatorAlgebra.Local.smul' (-1) h2)
  have hAvac : ∀ p : ℤ, (YA k hk (omegaA k) - sugawaraField k) p (vacuumA k) = 0 := by
    intro p
    show ((YA k hk (omegaA k)) p - (sugawaraField k) p) (vacuumA k) = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact Reconstruction.tower_unique (YA_DCov k hk (omegaA k)) (sugawaraField_DCovariant k hk)
      (Ltrans_vacuum k) (by rw [YA_creation0, ← omegaA_eq])
      (fun q hq => YA_creationNeg k hk (omegaA k) hq)
      (fun q hq => sugawaraField_vacuum_neg k q hq) p
  have hz := Reconstruction.field_eq_zero_of_vacuum (vacuumA k)
    (YA k hk (omegaA k) - sugawaraField k) (wordStateA k) (YwordA k)
    hloc (fun l => YwordA_vacuum_base k l) (fun l q hq => YwordA_vacuum_neg k l hq)
    hAvac (wordStateA_span k)
  rwa [sub_eq_zero] at hz

/-- `mode (YA ω) 0 = L₋₁` (the conformal `L₋₁` is the Sugawara translation). -/
theorem mode_YA_omega_zero (k : ℂ) (hk : k + 3 ≠ 0) :
    mode (YA k hk (omegaA k)) 0 = Ltrans k := by
  rw [mode_apply, show (-(0 : ℤ) - 1) = -1 from by ring, YA_omega_eq, ← Ltrans_eq]

/-- **VOA3 (translation), `L₋₁` form**: `YA(L₋₁ v) = ∂_z YA(v)` (operator-first uniqueness via the
shared vacuum tower of `YA(L₋₁v)` and `∂YA(v)`). -/
theorem YA_translation (k : ℂ) (hk : k + 3 ≠ 0) (v : Vacuum k) :
    YA k hk (Ltrans k v) = deriv (YA k hk v) := by
  have hGcov : Reconstruction.DCovariant (Ltrans k) (deriv (YA k hk v)) :=
    Reconstruction.DCovariant.deriv' (YA_DCov k hk v)
  have hGneg : ∀ q : ℤ, q < 0 → (deriv (YA k hk v)) q (vacuumA k) = 0 := by
    intro q hq
    rw [deriv_apply]
    show ((q + 1 : ℤ) • (YA k hk v) (q + 1)) (vacuumA k) = 0
    rw [← Int.cast_smul_eq_zsmul ℂ (q + 1), LinearMap.smul_apply]
    by_cases hq1 : q + 1 < 0
    · rw [YA_creationNeg k hk v hq1, smul_zero]
    · rw [show q + 1 = (0 : ℤ) from by omega, Int.cast_zero, zero_smul]
  have hbase : (YA k hk (Ltrans k v)) 0 (vacuumA k) = (deriv (YA k hk v)) 0 (vacuumA k) := by
    rw [YA_creation0, deriv_apply]
    show Ltrans k v = ((0 + 1 : ℤ) • (YA k hk v) (0 + 1)) (vacuumA k)
    rw [← Int.cast_smul_eq_zsmul ℂ (0 + 1), LinearMap.smul_apply, show (0 + 1 : ℤ) = 1 from by ring,
      Int.cast_one, one_smul, YA_one_vac]
  have hAvac : ∀ p : ℤ, (YA k hk (Ltrans k v) - deriv (YA k hk v)) p (vacuumA k) = 0 := by
    intro p
    show ((YA k hk (Ltrans k v)) p - (deriv (YA k hk v)) p) (vacuumA k) = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact Reconstruction.tower_unique (YA_DCov k hk (Ltrans k v)) hGcov
      (Ltrans_vacuum k) hbase (fun q hq => YA_creationNeg k hk (Ltrans k v) hq) hGneg p
  have hloc : ∀ l : List (Fin 8 × ℕ),
      Local (YA k hk (Ltrans k v) - deriv (YA k hk v)) (YwordA k l) := by
    intro l
    have h1 : Local (YA k hk (Ltrans k v)) (YwordA k l) := by
      rw [← YA_wordState k hk l]; exact YA_local k hk (Ltrans k v) (wordStateA k l)
    have h2 : Local (deriv (YA k hk v)) (YwordA k l) := by
      have hv : Local (YA k hk v) (YwordA k l) := by
        rw [← YA_wordState k hk l]; exact YA_local k hk v (wordStateA k l)
      exact Local.derivL hv
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (deriv (YA k hk v))]
    exact Reconstruction.Local.add_left h1 (VertexOperatorAlgebra.Local.smul' (-1) h2)
  have hz := Reconstruction.field_eq_zero_of_vacuum (vacuumA k)
    (YA k hk (Ltrans k v) - deriv (YA k hk v)) (wordStateA k) (YwordA k)
    hloc (fun l => YwordA_vacuum_base k l) (fun l q hq => YwordA_vacuum_neg k l hq)
    hAvac (wordStateA_span k)
  rwa [sub_eq_zero] at hz

/-- **VOA3** (`hYA_translation`): `YA(ω₍₀₎ v) = ∂_z YA(v)`. -/
theorem hYA_translation (k : ℂ) (hk : k + 3 ≠ 0) (v : Vacuum k) :
    YA k hk (mode (YA k hk (omegaA k)) 0 v) = deriv (YA k hk v) := by
  rw [mode_YA_omega_zero]
  exact YA_translation k hk v

/-- The actual reconstructed vacuum module is a vertex algebra without grading
at every noncritical level. All locality and creation axioms are discharged. -/
noncomputable def affineBareVA (k : ℂ) (hk : k+3 ≠ 0) : BarePreVA (Vacuum k) where
  Y := YA k hk
  vacuum := vacuumA k
  vacuum_Y := YA_vacuum k hk
  creation := YA_creation k hk
  locality := YA_local k hk
  regularity := YA_regularity k hk

end VOA.AffineSl3
