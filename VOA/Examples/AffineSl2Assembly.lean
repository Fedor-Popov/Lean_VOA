import VOA.Examples.AffineSl2CurrentCovStruct

/-!
# The unconditional affine `𝔰𝔩₂` vertex map `YA` and the VOA assembly

With the Sugawara current covariance `SugawaraCov.Jfield_DCovariant` (the hypothesis `hJ`) proved
unconditionally (at non-critical level `k + 2 ≠ 0`), the reconstruction producer
`affineYA_of_currentCov` yields an unconditional all-states vertex map `YA k hk` with VA3 creation,
VA4 locality, VA5 regularity, and translation covariance.  This file extracts `YA k hk`, proves the
basis-free VOA axioms (VA2 vacuum, VA3 creation, VA4 locality, VA5 regularity) and `ω ∈ grading 2`.
-/

namespace VOA.AffineVOA

open Module (End)
open VOA.AffineLie
open scoped BigOperators

universe u

/-! ## The unconditional vertex map `YA` and its spec -/

/-- The reconstruction-existence witness, fed the unconditional Sugawara covariance. -/
noncomputable def YAspec (k : ℂ) (hk : k + 2 ≠ 0) :=
  affineYA_of_currentCov k (fun a => SugawaraCov.Jfield_DCovariant k hk a)

/-- **The unconditional affine `𝔰𝔩₂` vertex map** `YA k hk : WakModule k →ₗ FormalDist`. -/
noncomputable def YA (k : ℂ) (hk : k + 2 ≠ 0) :
    WakModule k →ₗ[ℂ] FormalDist (End ℂ (WakModule k)) :=
  (YAspec k hk).choose

theorem YA_wordState (k : ℂ) (hk : k + 2 ≠ 0) (l : List (Fin 3 × ℕ)) :
    YA k hk (wordStateA k l) = YwordA k l := (YAspec k hk).choose_spec.1 l

theorem YA_isField (k : ℂ) (hk : k + 2 ≠ 0) (u : WakModule k) : IsField (YA k hk u) :=
  (YAspec k hk).choose_spec.2.1 u

theorem YA_local (k : ℂ) (hk : k + 2 ≠ 0) (u v : WakModule k) : Local (YA k hk u) (YA k hk v) :=
  (YAspec k hk).choose_spec.2.2.1 u v

theorem YA_creation0 (k : ℂ) (hk : k + 2 ≠ 0) (u : WakModule k) :
    (YA k hk u) 0 (vacuumA k) = u := (YAspec k hk).choose_spec.2.2.2.1 u

theorem YA_creationNeg (k : ℂ) (hk : k + 2 ≠ 0) (u : WakModule k) {q : ℤ} (hq : q < 0) :
    (YA k hk u) q (vacuumA k) = 0 := (YAspec k hk).choose_spec.2.2.2.2.1 u q hq

theorem YA_DCov (k : ℂ) (hk : k + 2 ≠ 0) (u : WakModule k) :
    Reconstruction.DCovariant (Ltrans k) (YA k hk u) := (YAspec k hk).choose_spec.2.2.2.2.2 u

/-! ## VA2: the vacuum field is the unit -/

/-- The affine identity field is the unit field `1`. -/
theorem idFieldA_eq_one (k : ℂ) :
    idFieldA k = (1 : FormalDist (End ℂ (WakModule k))) := by
  funext j
  rw [idFieldA, FormalDist.one_apply]
  split_ifs <;> rfl

/-- **VA2** (`hYA_vac`): `YA |0⟩ = 1`. -/
theorem YA_vacuum (k : ℂ) (hk : k + 2 ≠ 0) :
    YA k hk (vacuumA k) = (1 : FormalDist (End ℂ (WakModule k))) := by
  rw [← wordStateA_nil k, YA_wordState, YwordA_nil, idFieldA_eq_one]

/-! ## VA3 creation, VA5 regularity in `mode` form -/

/-- **VA3** (`hYA_creation`): `u₍₋₁₎|0⟩ = u` and `u₍ₙ₎|0⟩ = 0` for `n ≥ 0`. -/
theorem YA_creation (k : ℂ) (hk : k + 2 ≠ 0) (u : WakModule k) :
    mode (YA k hk u) (-1) (vacuumA k) = u
      ∧ ∀ n : ℤ, 0 ≤ n → mode (YA k hk u) n (vacuumA k) = 0 := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [mode_apply, show (-(-1) - 1 : ℤ) = 0 from by ring, YA_creation0]
  · rw [mode_apply]; exact YA_creationNeg k hk u (by omega)

/-- **VA5** (`hYA_reg`): for each `u, v` the products `u₍ₙ₎v` vanish for `n` large. -/
theorem YA_regularity (k : ℂ) (hk : k + 2 ≠ 0) (u v : WakModule k) :
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
      (∑ aa : Fin 3, ∑ bb : Fin 3,
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
theorem sugawaraField_DCovariant (k : ℂ) (hk : k + 2 ≠ 0) :
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
      (∑ aa : Fin 3, ∑ bb : Fin 3,
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
theorem sugawaraField_local_YwordA (k : ℂ) (l : List (Fin 3 × ℕ)) :
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
theorem YA_one_vac (k : ℂ) (hk : k + 2 ≠ 0) (v : WakModule k) :
    (YA k hk v) 1 (vacuumA k) = Ltrans k v := by
  have h := congrArg (fun (R : End ℂ (WakModule k)) => R (vacuumA k)) (YA_DCov k hk v 0)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
  rw [Ltrans_vacuum, map_zero, sub_zero, YA_creation0, show ((0 : ℤ) + 1) = 1 from by ring,
    one_smul] at h
  exact h.symm

/-- **`YA(ω) = T(z)`**: the field of the conformal vector is the Sugawara field (operator-first
uniqueness: both are local with the word fields, create `ω`, and share the full vacuum tower). -/
theorem YA_omega_eq (k : ℂ) (hk : k + 2 ≠ 0) : YA k hk (omegaA k) = sugawaraField k := by
  have hloc : ∀ l : List (Fin 3 × ℕ),
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
theorem mode_YA_omega_zero (k : ℂ) (hk : k + 2 ≠ 0) :
    mode (YA k hk (omegaA k)) 0 = Ltrans k := by
  rw [mode_apply, show (-(0 : ℤ) - 1) = -1 from by ring, YA_omega_eq, ← Ltrans_eq]

/-- **VOA3 (translation), `L₋₁` form**: `YA(L₋₁ v) = ∂_z YA(v)` (operator-first uniqueness via the
shared vacuum tower of `YA(L₋₁v)` and `∂YA(v)`). -/
theorem YA_translation (k : ℂ) (hk : k + 2 ≠ 0) (v : WakModule k) :
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
  have hloc : ∀ l : List (Fin 3 × ℕ),
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
theorem hYA_translation (k : ℂ) (hk : k + 2 ≠ 0) (v : WakModule k) :
    YA k hk (mode (YA k hk (omegaA k)) 0 v) = deriv (YA k hk v) := by
  rw [mode_YA_omega_zero]
  exact YA_translation k hk v

/-! ## VA1 grading: the graded-field machine -/

/-- A **graded field of weight `D`**: each coefficient `a j` shifts the `gradingZA`-degree by `D+j`. -/
def GradedFieldA (k : ℂ) (a : FormalDist (End ℂ (WakModule k))) (D : ℤ) : Prop :=
  ∀ (j w : ℤ) (p : WakModule k), p ∈ gradingZA k w → a j p ∈ gradingZA k (D + w + j)

/-- A finite-support finsum of submodule elements lies in the submodule. -/
theorem finsumA_mem_submodule {k : ℂ} {ι : Type*} (S : Submodule ℂ (WakModule k))
    (g : ι → WakModule k) (hfin : (Function.support g).Finite) (hmem : ∀ i, g i ∈ S) :
    (∑ᶠ i, g i) ∈ S := by
  rw [finsum_eq_finsetSum_of_support_subset g (s := hfin.toFinset) (by rw [hfin.coe_toFinset])]
  exact Submodule.sum_mem _ (fun i _ => hmem i)

/-- The identity field is a graded field of weight `0`. -/
theorem idFieldA_gradedField (k : ℂ) : GradedFieldA k (idFieldA k) 0 := by
  intro j w p hp
  show (if j = 0 then (LinearMap.id : End ℂ (WakModule k)) else 0) p ∈ gradingZA k (0 + w + j)
  by_cases hj : j = 0
  · rw [if_pos hj, LinearMap.id_apply, hj, show (0 : ℤ) + w + 0 = w from by ring]; exact hp
  · rw [if_neg hj, LinearMap.zero_apply]; exact Submodule.zero_mem _

/-- The `zʲ`-coefficient of `genFieldA a i`. -/
theorem genFieldA_coeff (k : ℂ) (a : Fin 3) (i : ℕ) (j : ℤ) :
    (genFieldA k a i) j
      = (i.factorial : ℂ)⁻¹ • ((∏ q ∈ Finset.range i, (j + 1 + (q : ℤ))) • J k a (-j - i - 1)) := by
  have h : (genFieldA k a i) j = (i.factorial : ℂ)⁻¹ • ((VOA.deriv^[i] (Jfield k a)) j) := rfl
  rw [h, VertexOperatorAlgebra.deriv_pow_apply, Jfield_apply,
    show (-(j + (i : ℤ)) - 1 : ℤ) = -j - i - 1 from by ring]

/-- The generator field `genFieldA a i` is a graded field of weight `i+1`. -/
theorem genFieldA_gradedField (k : ℂ) (a : Fin 3) (i : ℕ) :
    GradedFieldA k (genFieldA k a i) ((i : ℤ) + 1) := by
  intro j w p hp
  rw [genFieldA_coeff, LinearMap.smul_apply,
    show ((i : ℤ) + 1 + w + j) = w - (-j - (i : ℤ) - 1) from by ring]
  refine Submodule.smul_mem _ _ ?_
  show ((∏ q ∈ Finset.range i, (j + 1 + (q : ℤ))) • J k a (-j - (i : ℤ) - 1)) p ∈ _
  rw [← Int.cast_smul_eq_zsmul ℂ, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (J_mem_gradingZA k a (-j - (i : ℤ) - 1) w hp)

/-- The normal-ordered product of graded fields is graded, weights adding. -/
theorem GradedFieldA.nprod {k : ℂ} {a b : FormalDist (End ℂ (WakModule k))} (ha : IsField a)
    (hb : IsField b) {Da Db : ℤ} (hga : GradedFieldA k a Da) (hgb : GradedFieldA k b Db) :
    GradedFieldA k (VOA.nprod ha hb) (Da + Db) := by
  intro s w p hp
  rw [nprod_apply]
  refine finsumA_mem_submodule _ _ (normalOrdered_diag_support_finite ha hb s p) (fun m => ?_)
  rw [normalOrdered_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0]
    show a m (b (s - m) p) ∈ gradingZA k (Da + Db + w + s)
    have hb' := hgb (s - m) w p hp
    have ha' := hga m (Db + w + (s - m)) _ hb'
    rwa [show Da + (Db + w + (s - m)) + m = Da + Db + w + s from by ring] at ha'
  · rw [if_neg h0]
    show b (s - m) (a m p) ∈ gradingZA k (Da + Db + w + s)
    have ha' := hga m w p hp
    have hb' := hgb (s - m) (Da + w + m) _ ha'
    rwa [show Db + (Da + w + m) + (s - m) = Da + Db + w + s from by ring] at hb'

/-- The integer weight of a (basis) word `l`: `∑ (iₜ+1)`. -/
def wordDegA : List (Fin 3 × ℕ) → ℤ
  | [] => 0
  | (ai :: rest) => ((ai.2 : ℤ) + 1) + wordDegA rest

@[simp] theorem wordDegA_nil : wordDegA ([] : List (Fin 3 × ℕ)) = 0 := rfl

theorem wordDegA_cons (ai : Fin 3 × ℕ) (rest : List (Fin 3 × ℕ)) :
    wordDegA (ai :: rest) = ((ai.2 : ℤ) + 1) + wordDegA rest := rfl

/-- Each word field `YwordA k l` is a graded field of weight `wordDegA l`. -/
theorem YwordA_gradedField (k : ℂ) :
    ∀ l : List (Fin 3 × ℕ), GradedFieldA k (YwordA k l) (wordDegA l)
  | [] => by rw [YwordA_nil, wordDegA_nil]; exact idFieldA_gradedField k
  | (ai :: rest) => by
      rw [YwordA_cons, wordDegA_cons]
      exact GradedFieldA.nprod (genFieldA_isField k ai.1 ai.2) (YwordA_isField k rest)
        (genFieldA_gradedField k ai.1 ai.2) (YwordA_gradedField k rest)

/-- `GradedFieldA` is closed under addition (same weight). -/
theorem GradedFieldA.add {k : ℂ} {a b : FormalDist (End ℂ (WakModule k))} {D : ℤ}
    (ha : GradedFieldA k a D) (hb : GradedFieldA k b D) : GradedFieldA k (a + b) D := by
  intro j w p hp
  show (a j + b j) p ∈ _
  rw [LinearMap.add_apply]
  exact Submodule.add_mem _ (ha j w p hp) (hb j w p hp)

/-- `GradedFieldA` is closed under scaling. -/
theorem GradedFieldA.smul' {k : ℂ} {a : FormalDist (End ℂ (WakModule k))} {D : ℤ} (c : ℂ)
    (ha : GradedFieldA k a D) : GradedFieldA k (c • a) D := by
  intro j w p hp
  show (c • a j) p ∈ _
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ c (ha j w p hp)

theorem GradedFieldA.zero {k : ℂ} {D : ℤ} :
    GradedFieldA k (0 : FormalDist (End ℂ (WakModule k))) D := by
  intro j w p hp
  show (0 : End ℂ (WakModule k)) p ∈ _
  rw [LinearMap.zero_apply]
  exact Submodule.zero_mem _

/-! ### Homogeneous spanning of `gradingZA` by basis word states -/

/-- The span of the weight-`p` basis word states. -/
noncomputable def HSpan (k : ℂ) (p : ℤ) : Submodule ℂ (WakModule k) :=
  Submodule.span ℂ {x | ∃ l : List (Fin 3 × ℕ), wordDegA l = p ∧ wordStateA k l = x}

/-- `Jᵃ_{-n-1}` maps the weight-`d` span into the weight-`d+(n+1)` span. -/
theorem J_mem_hspan (k : ℂ) (a : Fin 3) (n : ℕ) (d : ℤ) {y : WakModule k}
    (hy : y ∈ HSpan k d) : J k a (-(n : ℤ) - 1) y ∈ HSpan k (d + ((n : ℤ) + 1)) := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hl, rfl⟩ := hz
      refine Submodule.subset_span ⟨(a, n) :: l, ?_, ?_⟩
      · rw [wordDegA_cons, hl]; ring
      · rw [wordStateA_cons]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add p q _ _ ihp ihq => rw [map_add]; exact Submodule.add_mem _ ihp ihq
  | smul c p _ ihp => rw [map_smul]; exact Submodule.smul_mem _ c ihp

/-- Each creation monomial `negWord L` lies in the weight-`wordDeg L` span. -/
theorem negWord_mem_hspan (k : ℂ) (L : List (Sl2 × ℕ)) :
    negWord kappaForm kappaForm_isInvariant k L ∈ HSpan k (wordDeg L : ℤ) := by
  induction L with
  | nil =>
      refine Submodule.subset_span ⟨[], ?_, ?_⟩
      · rw [wordDegA_nil, wordDeg_nil, Nat.cast_zero]
      · rfl
  | cons xn L' ih =>
      obtain ⟨x, n⟩ := xn
      rw [negWord_cons]
      have heq : vacuumRho kappaForm kappaForm_isInvariant k
            (ofLoop kappaForm kappaForm_isInvariant x (-(n : ℤ) - 1))
            (negWord kappaForm kappaForm_isInvariant k L')
          = ∑ c : Fin 3, x c • (J k c (-(n : ℤ) - 1)
              (negWord kappaForm kappaForm_isInvariant k L')) := by
        rw [← loopMul_apply]
        conv_lhs => rw [basis_decomp x]
        rw [map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [map_smul, LinearMap.smul_apply]
        rfl
      rw [heq, show (wordDeg ((x, n) :: L') : ℤ) = (wordDeg L' : ℤ) + ((n : ℤ) + 1) from by
        simp only [wordDeg]; push_cast; ring]
      exact Submodule.sum_mem _ (fun c _ =>
        Submodule.smul_mem _ _ (J_mem_hspan k c n (wordDeg L' : ℤ) ih))

/-- **Homogeneous spanning**: `gradingZA k p ≤ HSpan k p` (each energy eigenspace is spanned by the
weight-`p` basis word states; via `eigenspace_eq_degSpan` + the degree-tracked basis decomposition). -/
theorem gradingZA_le_hspan (k : ℂ) (p : ℤ) : gradingZA k p ≤ HSpan k p := by
  rw [gradingZA_def, ell0OpA, eigenspace_eq_degSpan, degSpan, Submodule.span_le]
  rintro _ ⟨L, hL, rfl⟩
  have hp : (wordDeg L : ℤ) = p := by
    simp only [Set.mem_setOf_eq, neg_inj] at hL
    exact_mod_cast hL
  rw [SetLike.mem_coe, ← hp]
  exact negWord_mem_hspan k L

/-! ### VA1 -/

/-- `YA u` is a graded field of weight `p` whenever `u ∈ HSpan k p`. -/
theorem YA_gradedField_of_hspan (k : ℂ) (hk : k + 2 ≠ 0) (p : ℤ) {u : WakModule k}
    (hu : u ∈ HSpan k p) : GradedFieldA k (YA k hk u) p := by
  induction hu using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hl, rfl⟩ := hz
      rw [YA_wordState, ← hl]; exact YwordA_gradedField k l
  | zero => rw [map_zero]; exact GradedFieldA.zero
  | add x y _ _ ihx ihy => rw [map_add]; exact GradedFieldA.add ihx ihy
  | smul c x _ ihx => rw [map_smul]; exact GradedFieldA.smul' c ihx

/-- `YA u` is a graded field of weight `p` whenever `u ∈ gradingZA k p`. -/
theorem YA_gradedField_of_mem (k : ℂ) (hk : k + 2 ≠ 0) (p : ℤ) {u : WakModule k}
    (hu : u ∈ gradingZA k p) : GradedFieldA k (YA k hk u) p :=
  YA_gradedField_of_hspan k hk p (gradingZA_le_hspan k p hu)

/-- **VA1** (`hYA_grading`): `mode (YA u) n v ∈ gradingZA k (p + q - n - 1)`. -/
theorem hYA_grading (k : ℂ) (hk : k + 2 ≠ 0) {p q : ℤ} (u : WakModule k)
    (hu : u ∈ gradingZA k p) (v : WakModule k) (hv : v ∈ gradingZA k q) (n : ℤ) :
    mode (YA k hk u) n v ∈ gradingZA k (p + q - n - 1) := by
  rw [mode_apply]
  have := YA_gradedField_of_mem k hk p hu (-n - 1) q v hv
  rwa [show p + q + (-n - 1) = p + q - n - 1 from by ring] at this

end VOA.AffineVOA
