/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2BelowCriticalPBWFlag
import VOA.Examples.AffineSl2BelowCriticalRealStructure
import VOA.Examples.AffineSl2BelowCriticalMatrixRigidity

/-!
# Graded unitarity of `V^k(sl₂)` in PBW coordinates

At a fixed conformal weight `E` the ordered PBW monomials of energy `E` (index type `EIdx E`,
independent of the level) are coordinates on `V_E` adapted to the ordinary flag
(`AffineSl2BelowCriticalPBWFlag`).  For a compact real structure `R` the Hermitian Gram matrix
`gram k hk R E` of `h(x,y) = B(ρx, y)` in these coordinates captures both clauses of graded
unitarity:

* `matrixStepNondeg_of_layerNondeg` — clause (iv) gives nondegenerate principal minors on every
  length step;
* `layerPositive_iff_matrixLayerSign` — clause (vi) is exactly the matrix layer-sign condition
  of `AffineSl2BelowCriticalMatrixRigidity`.
-/

namespace VOA

namespace AffineSl2BelowCritical

open AffineVOA AffineVOA.Inst AffineSl2GeneralRigidity AffineSl2PBWWakimotoReduction
open Matrix MatrixRigidity BelowCriticalNoWall

noncomputable section

/-- PBW exponents of a fixed energy. -/
def EIdx (E : ℤ) : Type := {mu : CurrentIndex // currentEnergy mu = E}

variable {k : ℂ} (hk : k + 2 ≠ 0)

theorem currentPBWBasis_mem_grading {E : ℤ} (i : EIdx E) :
    currentPBWBasis k hk i.val ∈ (universal k hk).grading E := by
  rw [currentPBWBasis_apply]
  have h := creation_state_grading k hk (orderedPBWColorWord i.val)
  rwa [show wordDegA (orderedPBWColorWord i.val) = E from i.2] at h

/-- The PBW monomials of energy `E` as vectors of the weight space. -/
def eVec (E : ℤ) (i : EIdx E) : (universal k hk).grading E :=
  ⟨currentPBWBasis k hk i.val, currentPBWBasis_mem_grading hk i⟩

theorem eVec_linearIndependent (E : ℤ) : LinearIndependent ℂ (eVec hk E) := by
  apply LinearIndependent.of_comp ((universal k hk).grading E).subtype
  exact (currentPBWBasis k hk).linearIndependent.comp _ Subtype.val_injective

theorem one_noncritical : (1 : ℂ) + 2 ≠ 0 := by norm_num

instance (E : ℤ) : Finite (EIdx E) := by
  haveI := (universal (1 : ℂ) one_noncritical).finrank E
  exact (eVec_linearIndependent one_noncritical E).finite

noncomputable instance (E : ℤ) : Fintype (EIdx E) := Fintype.ofFinite _

noncomputable instance (E : ℤ) : DecidableEq (EIdx E) := Classical.decEq _

/-- PBW coordinates of a vector, restricted to the energy-`E` exponents. -/
def coords (E : ℤ) (x : WakModule k) : EIdx E → ℂ :=
  fun i => (currentPBWBasis k hk).repr x i.val

/-- Off-energy PBW coordinates of a weight-`E` vector vanish. -/
theorem repr_eq_zero_of_energy_ne {E : ℤ} {x : WakModule k} (hx : x ∈ (universal k hk).grading E)
    (mu : CurrentIndex) (hmu : currentEnergy mu ≠ E) : (currentPBWBasis k hk).repr x mu = 0 := by
  apply basis_eigen_coordinate_zero (currentPBWBasis k hk) ((universal k hk).L 0)
    (fun mu => (currentEnergy mu : ℂ)) (currentPBWBasis_L0 k hk) x _
    ((universal k hk).L_zero_grading x hx) mu
  exact_mod_cast hmu

/-- A finite sum over the energy-`E` exponents. -/
theorem sum_EIdx_eq_finsupp {E : ℤ} (f : CurrentIndex → WakModule k) (s : Finset CurrentIndex)
    (hs : ∀ mu ∈ s, currentEnergy mu = E) (hf : ∀ mu, mu ∉ s → f mu = 0) :
    ∑ i : EIdx E, f i.val = ∑ mu ∈ s, f mu := by
  classical
  let T : Finset CurrentIndex := Finset.univ.map ⟨fun i : EIdx E => i.val, Subtype.val_injective⟩
  have hT : ∑ i : EIdx E, f i.val = ∑ mu ∈ T, f mu := by simp [T, Finset.sum_map]
  rw [hT]
  have hsT : s ⊆ T := by
    intro mu hmu
    let i : EIdx E := ⟨mu, hs mu hmu⟩
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
  exact (Finset.sum_subset hsT (fun mu _ hmu => hf mu hmu)).symm

/-- **Expansion in the energy-`E` PBW monomials.** -/
theorem eq_sum_coords {E : ℤ} {x : WakModule k} (hx : x ∈ (universal k hk).grading E) :
    x = ∑ i : EIdx E, coords hk E x i • currentPBWBasis k hk i.val := by
  conv_lhs => rw [← (currentPBWBasis k hk).linearCombination_repr x]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  symm
  refine sum_EIdx_eq_finsupp (fun mu => (currentPBWBasis k hk).repr x mu • currentPBWBasis k hk mu)
    _ ?_ ?_
  · intro mu hmu
    by_contra hne
    exact (Finsupp.mem_support_iff.mp hmu) (repr_eq_zero_of_energy_ne hk hx mu hne)
  · intro mu hmu
    simp only
    rw [Finsupp.notMem_support_iff.mp hmu, zero_smul]

/-- Coordinates of a finite combination of energy-`E` monomials. -/
theorem coords_sum {E : ℤ} (z : EIdx E → ℂ) :
    coords hk E (∑ i : EIdx E, z i • currentPBWBasis k hk i.val) = z := by
  funext j
  simp only [coords, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [Finsupp.single_apply, if_neg (fun h => hij (Subtype.ext h)), mul_zero]
  · simp

theorem sum_mem_grading {E : ℤ} (z : EIdx E → ℂ) :
    (∑ i : EIdx E, z i • currentPBWBasis k hk i.val) ∈ (universal k hk).grading E :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (currentPBWBasis_mem_grading hk i)

/-- A weight-`E` vector lies in the length-`p` piece iff its coordinates vanish beyond length
`p`. -/
theorem mem_ordinaryPiece_iff_coords {E : ℤ} {x : WakModule k}
    (hx : x ∈ (universal k hk).grading E) (p : ℕ) :
    x ∈ ordinaryPiece k p ↔ ∀ i : EIdx E, p < pbwLength i.val → coords hk E x i = 0 := by
  rw [mem_ordinaryPiece_iff_repr k hk]
  constructor
  · intro h i hi
    exact h i.val hi
  · intro h mu hmu
    by_cases he : currentEnergy mu = E
    · exact h ⟨mu, he⟩ hmu
    · exact repr_eq_zero_of_energy_ne hk hx mu he

/-! ## The Gram matrix of the Hermitian form -/

/-- The Hermitian Gram matrix in the energy-`E` PBW monomials. -/
def gram (R : RealStructure (universal k hk)) (E : ℤ) : Matrix (EIdx E) (EIdx E) ℂ :=
  fun i j => sesqForm (universalForm k hk) R (currentPBWBasis k hk i.val)
    (currentPBWBasis k hk j.val)

variable {R : RealStructure (universal k hk)}

/-- Pairing a monomial against a weight-`E` vector is a row of the Gram matrix. -/
theorem sesq_basis_eq_gram_mulVec {E : ℤ} (i : EIdx E) {x : WakModule k}
    (hx : x ∈ (universal k hk).grading E) :
    sesqForm (universalForm k hk) R (currentPBWBasis k hk i.val) x =
      (gram hk R E *ᵥ coords hk E x) i := by
  conv_lhs => rw [eq_sum_coords hk hx]
  simp only [sesqForm_apply, map_sum, map_smul, smul_eq_mul, mulVec, dotProduct, gram]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The Hermitian form in coordinates.** -/
theorem sesq_eq_dotProduct {E : ℤ} {x y : WakModule k} (hx : x ∈ (universal k hk).grading E)
    (hy : y ∈ (universal k hk).grading E) :
    sesqForm (universalForm k hk) R x y =
      star (coords hk E x) ⬝ᵥ (gram hk R E *ᵥ coords hk E y) := by
  conv_lhs => rw [eq_sum_coords hk hx]
  rw [sesqForm_apply]
  have hrho : R.rho (∑ i : EIdx E, coords hk E x i • currentPBWBasis k hk i.val) =
      ∑ i : EIdx E, (starRingEnd ℂ) (coords hk E x i) • R.rho (currentPBWBasis k hk i.val) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => R.antilinear _ _
  rw [hrho, map_sum, LinearMap.sum_apply, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, Pi.star_apply]
  rw [← sesq_basis_eq_gram_mulVec hk i hy, sesqForm_apply]
  rfl

/-! ## Clauses (iv) and (vi) in coordinates -/

open scoped ComplexOrder

/-- The PBW length on the energy-`E` exponents. -/
def eLen (E : ℤ) (i : EIdx E) : ℕ := pbwLength i.val

variable (hR : IsCompactRealStructure R)
include hR

/-- Orthogonality to a flag piece in coordinates. -/
theorem orth_piece_iff {E : ℤ} {u : WakModule k} (hu : u ∈ (universal k hk).grading E) (p : ℕ) :
    (∀ w ∈ (ordinaryFlag k hk).piece p E, (universalForm k hk).form w u = 0) ↔
      ∀ i : EIdx E, eLen E i ≤ p → (gram hk R E *ᵥ coords hk E u) i = 0 := by
  constructor
  · intro h i hi
    rw [← sesq_basis_eq_gram_mulVec hk i hu, sesqForm_apply]
    apply h
    apply hR.rho_mem_ordinaryFlag
    exact ⟨ordinaryPiece_mono hi (by
      rw [currentPBWBasis_apply]; exact wordStateA_mem_ordinaryPiece le_rfl),
      currentPBWBasis_mem_grading hk i⟩
  · intro h
    refine form_eq_zero_of_sesq (S := ((ordinaryFlag k hk).piece p E : Set (WakModule k)))
      (fun x hx => hR.rho_mem_ordinaryFlag hx) (fun x hx => hx.2) (hR.parity_ne_zero E) ?_
    intro x hx
    rw [sesq_eq_dotProduct hk hx.2 hu, dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : eLen E i ≤ p
    · rw [h i hi, mul_zero]
    · rw [Pi.star_apply, (mem_ordinaryPiece_iff_coords hk hx.2 p).mp hx.1 i (by
        simp only [eLen] at hi; omega), star_zero, zero_mul]

/-- **Clause (iv) gives nondegenerate principal minors on every length step.** -/
theorem matrixStepNondeg_of_layerNondeg {E : ℤ}
    (hnd : LayerNondegenerate (ordinaryFlag k hk) E (LiRadical.gradedForm (universalForm k hk) E)) :
    MatrixStepNondeg (eLen E) (gram hk R E) := by
  intro r
  cases r with
  | zero =>
      haveI : IsEmpty {i : EIdx E // eLen E i < 0} := ⟨fun i => Nat.not_lt_zero _ i.2⟩
      rw [Matrix.det_isEmpty]
      exact one_ne_zero
  | succ q =>
      intro hdet0
      obtain ⟨z, hz, hmz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
      let z' : EIdx E → ℂ := fun i => if h : eLen E i < q + 1 then z ⟨i, h⟩ else 0
      set u := ∑ i : EIdx E, z' i • currentPBWBasis k hk i.val with hu
      have huE : u ∈ (universal k hk).grading E := sum_mem_grading hk z'
      have hcu : coords hk E u = z' := coords_sum hk z'
      have hupiece : u ∈ ordinaryPiece k q := by
        rw [mem_ordinaryPiece_iff_coords hk huE q, hcu]
        intro i hi
        simp only [z', dif_neg (show ¬ eLen E i < q + 1 by simp only [eLen]; omega)]
      have horth : ∀ w ∈ (ordinaryFlag k hk).piece q E, (universalForm k hk).form w u = 0 := by
        rw [orth_piece_iff hk hR huE q, hcu]
        intro i hi
        have := congrFun hmz ⟨i, by omega⟩
        simp only [Pi.zero_apply, stepMatrix, mulVec, dotProduct, submatrix_apply] at this
        rw [← this, mulVec, dotProduct]
        symm
        rw [← sum_subtype_of_vanish (fun j : EIdx E => eLen E j < q + 1)
          (fun j => gram hk R E i j * z' j) (fun j hj => by
            simp only [z', dif_neg (show ¬ eLen E j < q + 1 from hj), mul_zero])]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [z', dif_pos j.2]
      have hu0 : u = 0 := by
        have := hnd q
        have hsep := this.2
        have := hsep ⟨⟨u, huE⟩, hupiece, huE⟩ (fun x => by
          change (universalForm k hk).form ((x : (universal k hk).grading E) : WakModule k) u = 0
          exact horth _ x.2)
        have h2 := congrArg Subtype.val (congrArg Subtype.val this)
        simpa using h2
      apply hz
      funext j
      have := congrFun hcu j.1
      rw [hu0] at this
      simp only [coords, map_zero, Finsupp.coe_zero, Pi.zero_apply, z', dif_pos j.2] at this
      exact this.symm

/-- Layer membership in coordinates. -/
theorem mem_layer_iff {E : ℤ} (p : ℕ) (u : (universal k hk).grading E) :
    u ∈ (ordinaryFlag k hk).layer E (LiRadical.gradedForm (universalForm k hk) E) p ↔
      (∀ i : EIdx E, p < eLen E i → coords hk E u i = 0) ∧
        ∀ i : EIdx E, eLen E i < p → (gram hk R E *ᵥ coords hk E u) i = 0 := by
  rw [GradedFlag.layer, Submodule.mem_inf, GradedFlag.mem_pieceIn]
  have hpiece : (u : WakModule k) ∈ (ordinaryFlag k hk).piece p E ↔
      ∀ i : EIdx E, p < eLen E i → coords hk E u i = 0 := by
    rw [ordinaryFlag_piece, Submodule.mem_inf, mem_ordinaryPiece_iff_coords hk u.2 p]
    exact ⟨fun h => h.1, fun h => ⟨h, u.2⟩⟩
  rw [hpiece]
  apply and_congr_right
  intro _
  cases p with
  | zero =>
      simp only [GradedFlag.pieceLT_zero, LinearMap.BilinForm.orthogonal_bot,
        Submodule.mem_top, true_iff]
      intro i hi
      exact absurd hi (Nat.not_lt_zero _)
  | succ q =>
      rw [GradedFlag.pieceLT_succ]
      have := orth_piece_iff hk hR u.2 q
      constructor
      · intro h
        have h' : ∀ w ∈ (ordinaryFlag k hk).piece q E,
            (universalForm k hk).form w (u : WakModule k) = 0 := by
          intro w hw
          exact h ⟨w, (ordinaryFlag k hk).le_grading q E hw⟩ hw
        intro i hi
        exact this.mp h' i (by omega)
      · intro h w hw
        exact this.mpr (fun i hi => h i (by omega)) _ hw

/-- **Clause (vi) at weight `E` is the matrix layer-sign condition.** -/
theorem layerPositive_iff_matrixLayerSign {E : ℤ} :
    LayerPositive (ordinaryFlag k hk) E (LiRadical.gradedForm (universalForm k hk) E)
        (gradedSesq (universalForm k hk) R E) ↔
      ∀ r : ℕ, MatrixLayerSign (eLen E) (gram hk R E) r := by
  constructor
  · intro hLP r y hsupp horth hy
    set u : (universal k hk).grading E :=
      ⟨∑ i : EIdx E, y i • currentPBWBasis k hk i.val, sum_mem_grading hk y⟩ with hu
    have hcu : coords hk E u = y := coords_sum hk y
    have hmem :
        u ∈ (ordinaryFlag k hk).layer E (LiRadical.gradedForm (universalForm k hk) E) r := by
      rw [mem_layer_iff hk hR, hcu]
      exact ⟨hsupp, horth⟩
    have hne : u ≠ 0 := by
      intro h
      apply hy
      rw [← hcu, h]
      funext i
      simp [coords]
    obtain ⟨s, hs, hsu⟩ := hLP r u hmem hne
    have hval : (signedForm (gradedSesq (universalForm k hk) R E) r) u u =
        (-1 : ℂ) ^ r * (star y ⬝ᵥ (gram hk R E *ᵥ y)) := by
      rw [signedForm_apply, gradedSesq_apply, ← sesqForm_apply,
        sesq_eq_dotProduct hk u.2 u.2, hcu]
    rw [← hval, hsu]
    exact Complex.zero_lt_real.mpr hs
  · intro hM p u hmem hne
    have hc := (mem_layer_iff hk hR p u).mp hmem
    have hcne : coords hk E u ≠ 0 := by
      intro h
      apply hne
      apply Subtype.ext
      rw [eq_sum_coords hk u.2, h]
      simp
    have hpos := hM p (coords hk E u) hc.1 hc.2 hcne
    refine ⟨((-1 : ℂ) ^ p * (star (coords hk E u) ⬝ᵥ (gram hk R E *ᵥ coords hk E u))).re,
      (Complex.pos_iff.mp hpos).1, ?_⟩
    rw [signedForm_apply, gradedSesq_apply, ← sesqForm_apply, sesq_eq_dotProduct hk u.2 u.2]
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]
      exact (Complex.pos_iff.mp hpos).2.symm

end

end AffineSl2BelowCritical

end VOA
