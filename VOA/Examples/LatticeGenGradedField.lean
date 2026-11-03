/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenL0Translation

/-!
# The bigrading-tracking mode-grading machinery (VA1) for the general even-lattice VOA

The graded-field predicate `GradedFieldLatGen`, the base boson-grading chain
(`vSchur → EEVec_memZ`), the charge/current graded fields, the closure lemmas, the word-degree
bookkeeping, homogeneous spanning `gradingLatGen ≤ HSpanLatGen`, and the target VA1 axiom
`YfullGen_grading_mode`.  Cross-charge lift of A₁'s `LatticeVOAInstance` (lines 808-1181) with the
charge weight `n² → halfNorm L α` and `List ℕ → List (ℕ × Fin (rank L))`.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN Reconstruction

variable (L : IntegralLattice)

/-! ## §A  `halfNorm` additivity (evenness + bilinearity). -/

/-- **`halfNorm (α+β) = halfNorm α + halfNorm β + ⟨α,β⟩`** — the charge weight of `e^{α+β}` from
bilinearity and evenness. -/
theorem halfNorm_add (hEven : L.Even) (α β : L.carrier) :
    halfNorm L (α + β) = halfNorm L α + halfNorm L β + L.form α β := by
  have hexp : L.form (α + β) (α + β) = L.form α α + L.form β β + 2 * L.form α β := by
    simp only [map_add, LinearMap.add_apply]
    rw [form_symm L β α]; ring
  have h2ab := two_halfNorm L hEven (α + β)
  have h2a := two_halfNorm L hEven α
  have h2b := two_halfNorm L hEven β
  omega

/-! ## §B  The base boson-grading chain `vSchur → EEVec_memZ`. -/

/-- The charge-weighted creation variable `vVar α m` is weight-`(m+1)` homogeneous. -/
theorem vVar_mem_gradingWN (α : L.carrier) (m : ℕ) :
    vVar L α m ∈ HeisenbergN.gradingWN (rank L) (m + 1) := by
  rw [vVar]
  refine Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ ?_)
  rw [HeisenbergN.mem_gradingWN]
  have := MvPolynomial.isWeightedHomogeneous_X ℂ (HeisenbergN.weightFnN (r := rank L)) (m, a)
  rwa [HeisenbergN.weightFnN_apply] at this

/-- `vSchur α N` is weight-`N` homogeneous (the vector-charge creation Schur polynomial). -/
theorem vSchur_mem_gradingWN (α : L.carrier) (N : ℕ) :
    vSchur L α N ∈ HeisenbergN.gradingWN (rank L) N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [vSchur_zero]; exact HeisenbergN.vacuumN_mem_gradingWN (rank L)
    | (M + 1) =>
      rw [vSchur_succ]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m hm => ?_)
      simp only [Finset.mem_range] at hm
      have hcv : vVar L α m ∈ HeisenbergN.gradingWN (rank L) (m + 1) := vVar_mem_gradingWN L α m
      have hsc : vSchur L α (M - m) ∈ HeisenbergN.gradingWN (rank L) (M - m) := ih (M - m) (by omega)
      rw [HeisenbergN.mem_gradingWN] at hcv hsc ⊢
      have hmul := hcv.mul hsc
      rwa [show (m + 1) + (M - m) = M + 1 from by omega] at hmul

/-- `EminusVec α N` (multiplication by weight-`N` `vSchur α N`) raises `gradingWN` by `N`. -/
theorem EminusVec_mem_gradingWN (α : L.carrier) (N : ℕ) {w : ℕ} {p : FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingWN (rank L) w) :
    EminusVec L α N p ∈ HeisenbergN.gradingWN (rank L) (N + w) := by
  rw [EminusVec, LinearMap.mulLeft_apply]
  have hc : vSchur L α N ∈ HeisenbergN.gradingWN (rank L) N := vSchur_mem_gradingWN L α N
  rw [HeisenbergN.mem_gradingWN] at hc hp ⊢
  exact hc.mul hp

/-- `E⁻(α)_t` raises `gradingZN` by `t` (from `gradingWN`). -/
theorem EminusVecField_mem_gradingZN (α : L.carrier) (t : ℤ) {w : ℕ} {p : FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingWN (rank L) w) :
    EminusVecField L α t p ∈ HeisenbergN.gradingZN (rank L) ((w : ℤ) + t) := by
  rw [EminusVecField_apply]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht]
    have h := HeisenbergN.mem_gradingZN_of_gradingWN (EminusVec_mem_gradingWN L α t.toNat hp)
    rwa [show ((t.toNat + w : ℕ) : ℤ) = (w : ℤ) + t from by
      rw [Nat.cast_add, Int.toNat_of_nonneg ht]; ring] at h
  · rw [if_neg ht, LinearMap.zero_apply]; exact Submodule.zero_mem _

/-- `E⁺(α)_t` raises `gradingZN` by `t` (from `gradingWN`). -/
theorem EplusVecField_mem_gradingZN (α : L.carrier) (t : ℤ) {w : ℕ} {p : FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingWN (rank L) w) :
    EplusVecField L α t p ∈ HeisenbergN.gradingZN (rank L) ((w : ℤ) + t) := by
  rw [EplusVecField_apply]
  by_cases ht : t ≤ 0
  · rw [if_pos ht]
    have := aExpVec_mem_gradingZN L α (-t).toNat hp
    rwa [show (w : ℤ) - ((-t).toNat : ℤ) = (w : ℤ) + t from by
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -t)]; ring] at this
  · rw [if_neg ht, LinearMap.zero_apply]; exact Submodule.zero_mem _

/-- `E⁻(α)_t` raises `gradingZN` by `t` (`gradingZN` version). -/
theorem EminusVecField_memZ (α : L.carrier) (t : ℤ) {d : ℤ} {p : FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingZN (rank L) d) :
    EminusVecField L α t p ∈ HeisenbergN.gradingZN (rank L) (d + t) := by
  by_cases hd : 0 ≤ d
  · rw [HeisenbergN.gradingZN_of_nonneg hd] at hp
    have := EminusVecField_mem_gradingZN L α t hp
    rwa [Int.toNat_of_nonneg hd] at this
  · rw [HeisenbergN.gradingZN_of_neg (by omega), Submodule.mem_bot] at hp
    rw [hp, LinearMap.map_zero]; exact Submodule.zero_mem _

/-- `E⁺(α)_t` raises `gradingZN` by `t` (`gradingZN` version). -/
theorem EplusVecField_memZ (α : L.carrier) (t : ℤ) {d : ℤ} {p : FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingZN (rank L) d) :
    EplusVecField L α t p ∈ HeisenbergN.gradingZN (rank L) (d + t) := by
  by_cases hd : 0 ≤ d
  · rw [HeisenbergN.gradingZN_of_nonneg hd] at hp
    have := EplusVecField_mem_gradingZN L α t hp
    rwa [Int.toNat_of_nonneg hd] at this
  · rw [HeisenbergN.gradingZN_of_neg (by omega), Submodule.mem_bot] at hp
    rw [hp, LinearMap.map_zero]; exact Submodule.zero_mem _

/-- A finite-support finsum of submodule elements lies in the submodule (`FockN` version). -/
theorem finsumFockN_mem_submodule {ι : Type*} (S : Submodule ℂ (FockN (rank L)))
    (g : ι → FockN (rank L)) (hfin : (Function.support g).Finite) (hmem : ∀ i, g i ∈ S) :
    (∑ᶠ i, g i) ∈ S := by
  rw [finsum_eq_finsetSum_of_support_subset g (s := hfin.toFinset) (by rw [hfin.coe_toFinset])]
  exact Submodule.sum_mem _ (fun i _ => hmem i)

/-- **`EE(α)_s` raises `gradingZN` by `s`** (the boson dressing grades by its argument). -/
theorem EEVec_memZ (α : L.carrier) (s : ℤ) {d : ℤ} {p : FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingZN (rank L) d) :
    EEVec L α s p ∈ HeisenbergN.gradingZN (rank L) (d + s) := by
  rw [EEVec, nprod_apply]
  refine finsumFockN_mem_submodule L _ _
    (normalOrdered_diag_support_finite (EminusVecField_isField L α) (EplusVecField_isField L α) s p)
    (fun m => ?_)
  rw [normalOrdered_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0, Module.End.mul_apply]
    have h1 := EplusVecField_memZ L α (s - m) hp
    have h2 := EminusVecField_memZ L α m h1
    rwa [show d + (s - m) + m = d + s from by ring] at h2
  · rw [if_neg h0, Module.End.mul_apply]
    have h1 := EminusVecField_memZ L α m hp
    have h2 := EplusVecField_memZ L α (s - m) h1
    rwa [show d + m + (s - m) = d + s from by ring] at h2

/-! ## §C  The graded-field predicate and its bigraded characterization. -/

/-- `Yeαvec α t (mkEα β p)` lands in conformal grade `halfNorm α + (w + halfNorm β) + t`. -/
theorem Yeαvec_bigrad_mem (hEven : L.Even) (α β : L.carrier) (t w : ℤ) {p : FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingZN (rank L) w) :
    Yeαvec L α t (mkEα L β p) ∈ gradingLatGen L (halfNorm L α + (w + halfNorm L β) + t) := by
  rw [show mkEα L β p = latStateGen L p β from rfl, Yeαvec_tmul]
  refine Submodule.smul_mem _ _ ?_
  have hE : EEVec L α (t - L.form α β) p ∈ HeisenbergN.gradingZN (rank L) (w + (t - L.form α β)) :=
    EEVec_memZ L α (t - L.form α β) hp
  have hle := bigradα_le_gradingLatGen L (w + (t - L.form α β)) (α + β)
    (show latStateGen L (EEVec L α (t - L.form α β) p) (α + β)
        ∈ bigradα L (w + (t - L.form α β), α + β) from ⟨_, hE, rfl⟩)
  rwa [show (w + (t - L.form α β)) + halfNorm L (α + β)
      = halfNorm L α + (w + halfNorm L β) + t from by rw [halfNorm_add L hEven α β]; ring] at hle

/-- A lattice graded field of weight `D`: the `zʲ`-coefficient `a j` shifts conformal grade by
`D + j` (mode `n = a(-n-1)` shifts by `D - n - 1`). -/
def GradedFieldLatGen (a : FormalDist (End ℂ (LatModuleGen L))) (D : ℤ) : Prop :=
  ∀ (j q : ℤ) (x : LatModuleGen L), x ∈ gradingLatGen L q → a j x ∈ gradingLatGen L (D + q + j)

/-- To check `GradedFieldLatGen a D`, it suffices to check it on bigraded basis elements `mkEα β p`
(`p ∈ gradingZN (rank L) w`, conformal weight `w + halfNorm β`). -/
theorem GradedFieldLatGen.of_bigrad (hEven : L.Even) (hPos : L.PosDef)
    {a : FormalDist (End ℂ (LatModuleGen L))} {D : ℤ}
    (h : ∀ (j w : ℤ) (β : L.carrier) (p : FockN (rank L)), p ∈ HeisenbergN.gradingZN (rank L) w →
      a j (mkEα L β p) ∈ gradingLatGen L (D + (w + halfNorm L β) + j)) :
    GradedFieldLatGen L a D := by
  intro j q x hx
  refine (?_ : gradingLatGen L q ≤ (gradingLatGen L (D + q + j)).comap (a j)) hx
  rw [gradingLatGen_eq_biSup_pos L hEven hPos q]
  refine iSup_le (fun p' => iSup_le (fun hp' => ?_))
  rintro y ⟨z, hz, rfl⟩
  rw [Submodule.mem_comap]
  obtain ⟨hfib, hpos⟩ := hp'
  have hgoal := h j p'.1 p'.2 z hz
  rwa [show D + (p'.1 + halfNorm L p'.2) + j = D + q + j from by rw [← hfib]] at hgoal

/-! ## §D  The generator graded fields (charge, current). -/

/-- `Y(e^α)` is a graded field of weight `halfNorm α` (the conformal weight of `e^α`). -/
theorem Yeαvec_gradedField (hEven : L.Even) (hPos : L.PosDef) (α : L.carrier) :
    GradedFieldLatGen L (Yeαvec L α) (halfNorm L α) := by
  refine GradedFieldLatGen.of_bigrad L hEven hPos (fun j w β p hp => ?_)
  have := Yeαvec_bigrad_mem L hEven α β j w hp
  rwa [show halfNorm L α + (w + halfNorm L β) + j = halfNorm L α + (w + halfNorm L β) + j from rfl]

/-- `alphaLatGen a j (mkEα δ p)` lands in conformal grade `(w + halfNorm δ) + (1 + j)`. -/
theorem alphaLatGen_bigrad_mem (a : Fin (rank L)) (j w : ℤ) {δ : L.carrier} {p : FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingZN (rank L) w) :
    alphaLatGen L a j (mkEα L δ p) ∈ gradingLatGen L (1 + (w + halfNorm L δ) + j) := by
  rw [show mkEα L δ p = latStateGen L p δ from rfl, alphaLatGen_tmul]
  refine Submodule.add_mem _ ?_ ?_
  · have hα : currentN (rank L) 1 a j p ∈ HeisenbergN.gradingZN (rank L) (w + j + 1) := by
      rw [currentN_apply]
      by_cases hd : 0 ≤ w
      · rw [HeisenbergN.gradingZN_of_nonneg hd] at hp
        have h := HeisenbergN.oscN_mem_gradingZN (rank L) 1 a (-j - 1) hp
        rw [Int.toNat_of_nonneg hd] at h
        rwa [show w - (-j - 1) = w + j + 1 from by ring] at h
      · rw [HeisenbergN.gradingZN_of_neg (by omega), Submodule.mem_bot] at hp
        rw [hp, map_zero]; exact HeisenbergN.zero_mem_gradingZN (rank L) _
    have hle := bigradα_le_gradingLatGen L (w + j + 1) δ
      (show latStateGen L (currentN (rank L) 1 a j p) δ ∈ bigradα L (w + j + 1, δ) from ⟨_, hα, rfl⟩)
    rwa [show (w + j + 1) + halfNorm L δ = 1 + (w + halfNorm L δ) + j from by ring] at hle
  · by_cases hj : j = -1
    · rw [if_pos hj]
      refine Submodule.smul_mem _ _ ?_
      have hle := bigradα_le_gradingLatGen L w δ
        (show latStateGen L p δ ∈ bigradα L (w, δ) from ⟨p, hp, rfl⟩)
      rwa [show w + halfNorm L δ = 1 + (w + halfNorm L δ) + j from by rw [hj]; ring] at hle
    · rw [if_neg hj]; exact Submodule.zero_mem _

/-- `alphaLatGen a` is a graded field of weight `1` (the boson current has conformal weight `1`). -/
theorem alphaLatGen_gradedField (hEven : L.Even) (hPos : L.PosDef) (a : Fin (rank L)) :
    GradedFieldLatGen L (alphaLatGen L a) 1 := by
  refine GradedFieldLatGen.of_bigrad L hEven hPos (fun j w β p hp => ?_)
  exact alphaLatGen_bigrad_mem L a j w hp

/-! ## §E  Closure of graded fields under `+`, `•`, `deriv`, `nprod`. -/

/-- A finite-support finsum of submodule elements lies in the submodule (`V_L` version). -/
theorem finsumLatGen_mem_submodule {ι : Type*} (S : Submodule ℂ (LatModuleGen L))
    (g : ι → LatModuleGen L) (hfin : (Function.support g).Finite) (hmem : ∀ i, g i ∈ S) :
    (∑ᶠ i, g i) ∈ S := by
  rw [finsum_eq_finsetSum_of_support_subset g (s := hfin.toFinset) (by rw [hfin.coe_toFinset])]
  exact Submodule.sum_mem _ (fun i _ => hmem i)

theorem GradedFieldLatGen.add {a b : FormalDist (End ℂ (LatModuleGen L))} {D : ℤ}
    (ha : GradedFieldLatGen L a D) (hb : GradedFieldLatGen L b D) :
    GradedFieldLatGen L (a + b) D := by
  intro j q x hx
  show (a j + b j) x ∈ _
  rw [LinearMap.add_apply]
  exact Submodule.add_mem _ (ha j q x hx) (hb j q x hx)

theorem GradedFieldLatGen.smul' {a : FormalDist (End ℂ (LatModuleGen L))} {D : ℤ} (c : ℂ)
    (ha : GradedFieldLatGen L a D) : GradedFieldLatGen L (c • a) D := by
  intro j q x hx
  show (c • a j) x ∈ _
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ c (ha j q x hx)

theorem GradedFieldLatGen.zero {D : ℤ} :
    GradedFieldLatGen L (0 : FormalDist (End ℂ (LatModuleGen L))) D := by
  intro j q x hx
  show (0 : End ℂ (LatModuleGen L)) x ∈ _
  rw [LinearMap.zero_apply]; exact Submodule.zero_mem _

theorem GradedFieldLatGen.deriv {a : FormalDist (End ℂ (LatModuleGen L))} {D : ℤ}
    (ha : GradedFieldLatGen L a D) : GradedFieldLatGen L (VOA.deriv a) (D + 1) := by
  intro j q x hx
  rw [deriv_apply, ← Int.cast_smul_eq_zsmul ℂ (j + 1), LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  have := ha (j + 1) q x hx
  rwa [show D + q + (j + 1) = D + 1 + q + j from by ring] at this

theorem GradedFieldLatGen.deriv_iterate {a : FormalDist (End ℂ (LatModuleGen L))} {D : ℤ}
    (ha : GradedFieldLatGen L a D) (i : ℕ) :
    GradedFieldLatGen L (VOA.deriv^[i] a) (D + i) := by
  induction i with
  | zero => rw [Function.iterate_zero, id]; rwa [Nat.cast_zero, add_zero]
  | succ p ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    have := ih.deriv L
    rwa [show D + (p : ℤ) + 1 = D + ((p : ℤ) + 1) from by ring, ← Nat.cast_succ] at this

/-- `genFieldLatGen a i = (i!)⁻¹ ∂^i (alphaLatGen a)` is a graded field of weight `i + 1`. -/
theorem genFieldLatGen_gradedField (hEven : L.Even) (hPos : L.PosDef) (a : Fin (rank L)) (i : ℕ) :
    GradedFieldLatGen L (genFieldLatGen L a i) ((i : ℤ) + 1) := by
  rw [genFieldLatGen]
  have := ((alphaLatGen_gradedField L hEven hPos a).deriv_iterate L i).smul' L ((i.factorial : ℂ)⁻¹)
  rwa [show (1 : ℤ) + (i : ℤ) = (i : ℤ) + 1 from by ring] at this

theorem GradedFieldLatGen.nprod {a b : FormalDist (End ℂ (LatModuleGen L))}
    (haf : IsField a) (hbf : IsField b) {Da Db : ℤ}
    (ha : GradedFieldLatGen L a Da) (hb : GradedFieldLatGen L b Db) :
    GradedFieldLatGen L (VOA.nprod haf hbf) (Da + Db) := by
  intro s q x hx
  rw [nprod_apply]
  refine finsumLatGen_mem_submodule L _ _
    (normalOrdered_diag_support_finite haf hbf s x) (fun m => ?_)
  rw [normalOrdered_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0, Module.End.mul_apply]
    have hb' := hb (s - m) q x hx
    have ha' := ha m (Db + q + (s - m)) _ hb'
    rwa [show Da + (Db + q + (s - m)) + m = Da + Db + q + s from by ring] at ha'
  · rw [if_neg h0, Module.End.mul_apply]
    have ha' := ha m q x hx
    have hb' := hb (s - m) (Da + q + m) _ ha'
    rwa [show Db + (Da + q + m) + (s - m) = Da + Db + q + s from by ring] at hb'

/-! ## §F  Word degree and word-field grading. -/

/-- The conformal weight of a lattice word `(l, α)`: boson degree `∑(i+1)` plus charge weight
`halfNorm α`. -/
noncomputable def wordDegLatGen : List (ℕ × Fin (rank L)) → L.carrier → ℤ
  | [], α => halfNorm L α
  | (ia :: rest), α => ((ia.1 : ℤ) + 1) + wordDegLatGen rest α

@[simp] theorem wordDegLatGen_nil (α : L.carrier) : wordDegLatGen L [] α = halfNorm L α := rfl

theorem wordDegLatGen_cons (ia : ℕ × Fin (rank L)) (rest : List (ℕ × Fin (rank L))) (α : L.carrier) :
    wordDegLatGen L (ia :: rest) α = ((ia.1 : ℤ) + 1) + wordDegLatGen L rest α := rfl

/-- Each lattice word field `YwordLatGen l α` is a graded field of weight `wordDegLatGen l α`. -/
theorem YwordLatGen_gradedField (hEven : L.Even) (hPos : L.PosDef) :
    ∀ (l : List (ℕ × Fin (rank L))) (α : L.carrier),
      GradedFieldLatGen L (YwordLatGen L l α) (wordDegLatGen L l α)
  | [], α => by rw [YwordLatGen_nil, wordDegLatGen_nil]; exact Yeαvec_gradedField L hEven hPos α
  | (ia :: rest), α => by
      rw [YwordLatGen_cons, wordDegLatGen_cons]
      exact GradedFieldLatGen.nprod L (genFieldLatGen_isField L ia.2 ia.1)
        (YwordLatGen_isField L rest α) (genFieldLatGen_gradedField L hEven hPos ia.2 ia.1)
        (YwordLatGen_gradedField hEven hPos rest α)

/-! ## §G  Homogeneous spanning `gradingLatGen q ≤ HSpanLatGen q`. -/

/-- The span of the lattice word states of conformal weight `q`. -/
noncomputable def HSpanLatGen (q : ℤ) : Submodule ℂ (LatModuleGen L) :=
  Submodule.span ℂ {x | ∃ (l : List (ℕ × Fin (rank L))) (α : L.carrier),
    wordDegLatGen L l α = q ∧ wordStateLatGen L l α = x}

/-- `wordDegLatGen l α = (wordWeightNN l : ℤ) + halfNorm α`. -/
theorem wordDegLatGen_eq_sum (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    wordDegLatGen L l α = ((HeisenbergN.wordWeightNN l : ℕ) : ℤ) + halfNorm L α := by
  induction l with
  | nil => rw [wordDegLatGen_nil, HeisenbergN.wordWeightNN]; simp
  | cons ia rest ih =>
      rw [wordDegLatGen_cons, ih]
      simp only [HeisenbergN.wordWeightNN, List.map_cons, List.sum_cons]
      push_cast; ring

/-- `wordDegLatGen (monoWordN a) α = (weight a : ℤ) + halfNorm α`. -/
theorem wordDegLatGen_monoWordN (a : (ℕ × Fin (rank L)) →₀ ℕ) (α : L.carrier) :
    wordDegLatGen L (HeisenbergN.monoWordN a) α
      = ((Finsupp.weight HeisenbergN.weightFnN a : ℕ) : ℤ) + halfNorm L α := by
  rw [wordDegLatGen_eq_sum, HeisenbergN.wordWeightNN_monoWordN_eq_weight]

/-- Each weight-`w` monomial tensor `e^α` is a degree-`(w + halfNorm α)` word state, hence in
`HSpanLatGen`. -/
theorem monomial_tmul_mem_HSpanLatGen (a : (ℕ × Fin (rank L)) →₀ ℕ) (w : ℕ) (α : L.carrier)
    (ha : Finsupp.weight HeisenbergN.weightFnN a = w) :
    (MvPolynomial.monomial a (1 : ℂ)) ⊗ₜ[ℂ] eGen L α ∈ HSpanLatGen L ((w : ℤ) + halfNorm L α) := by
  have hword : wordStateLatGen L (HeisenbergN.monoWordN a) α
      = (MvPolynomial.monomial a (1 : ℂ)) ⊗ₜ[ℂ] eGen L α := by
    rw [wordStateLatGen_eq, HeisenbergN.wordStateN_monoWordN]
  rw [← hword]
  refine Submodule.subset_span ⟨HeisenbergN.monoWordN a, α, ?_, rfl⟩
  rw [wordDegLatGen_monoWordN, ha]

/-- `mkEα α p ∈ HSpanLatGen (w + halfNorm α)` for `p ∈ gradingWN (rank L) w`. -/
theorem mkEα_mem_HSpanLatGen (w : ℕ) (α : L.carrier) {p : FockN (rank L)}
    (hp : p ∈ HeisenbergN.gradingWN (rank L) w) :
    mkEα L α p ∈ HSpanLatGen L ((w : ℤ) + halfNorm L α) := by
  classical
  rw [mkEα_apply, ← MvPolynomial.support_sum_monomial_coeff p, TensorProduct.sum_tmul]
  refine Submodule.sum_mem _ (fun a ha => ?_)
  rw [show (MvPolynomial.monomial a (MvPolynomial.coeff a p))
        = (MvPolynomial.coeff a p) • MvPolynomial.monomial a (1 : ℂ) from by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
    ← TensorProduct.smul_tmul' (MvPolynomial.coeff a p) (MvPolynomial.monomial a (1 : ℂ)) (eGen L α)]
  refine Submodule.smul_mem _ _ ?_
  have hwa : Finsupp.weight HeisenbergN.weightFnN a = w := by
    rw [HeisenbergN.mem_gradingWN] at hp
    exact hp (by rw [MvPolynomial.coeff]; exact Finsupp.mem_support_iff.mp ha)
  exact monomial_tmul_mem_HSpanLatGen L a w α hwa

/-- **Homogeneous spanning**: `gradingLatGen q ≤ HSpanLatGen q`. -/
theorem gradingLatGen_le_HSpanLatGen (hEven : L.Even) (hPos : L.PosDef) (q : ℤ) :
    gradingLatGen L q ≤ HSpanLatGen L q := by
  rw [gradingLatGen_eq_biSup_pos L hEven hPos q]
  refine iSup_le (fun p' => iSup_le (fun hp' => ?_))
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨hfib, hpos⟩ := hp'
  obtain ⟨w, hw⟩ : ∃ w : ℕ, p'.1 = (w : ℤ) := ⟨p'.1.toNat, by omega⟩
  have hzW : z ∈ HeisenbergN.gradingWN (rank L) w := by
    rw [hw, HeisenbergN.gradingZN_of_nonneg (by positivity), Int.toNat_natCast] at hz; exact hz
  have := mkEα_mem_HSpanLatGen L w p'.2 hzW
  rwa [show (w : ℤ) + halfNorm L p'.2 = q from by rw [← hfib, hw]] at this

/-! ## §H  VA1 — `YfullGen_grading_mode`. -/

/-- A graded field assignment `a` of weight `D` is a graded field on each `HSpanLatGen`-spanning
word state (combining `YwordLatGen_gradedField` with the spanning). -/
theorem GradedFieldLatGen.of_HSpan (hEven : L.Even) (hPos : L.PosDef)
    {a : LatModuleGen L → FormalDist (End ℂ (LatModuleGen L))}
    (hgen : ∀ (l : List (ℕ × Fin (rank L))) (α : L.carrier),
      a (wordStateLatGen L l α) = YwordLatGen L l α)
    (hlin : ∀ (x y : LatModuleGen L), a (x + y) = a x + a y)
    (hsmul : ∀ (c : ℂ) (x : LatModuleGen L), a (c • x) = c • a x)
    (hzero : a 0 = 0)
    (p : ℤ) {u : LatModuleGen L} (hu : u ∈ HSpanLatGen L p) :
    GradedFieldLatGen L (a u) p := by
  induction hu using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, α, hl, rfl⟩ := hz
      rw [hgen, ← hl]; exact YwordLatGen_gradedField L hEven hPos l α
  | zero => rw [hzero]; exact GradedFieldLatGen.zero L
  | add x y _ _ ihx ihy => rw [hlin]; exact GradedFieldLatGen.add L ihx ihy
  | smul c x _ ihx => rw [hsmul]; exact GradedFieldLatGen.smul' L c ihx

/-- `YfullGen u` is a graded field of conformal weight `p` whenever `u ∈ gradingLatGen p`. -/
theorem YfullGen_gradedField_of_mem (hEven : L.Even) (hPos : L.PosDef) {p : ℤ} {u : LatModuleGen L}
    (hu : u ∈ gradingLatGen L p) :
    GradedFieldLatGen L (YfullGen L hEven hPos u) p :=
  GradedFieldLatGen.of_HSpan L hEven hPos (YfullGen_word L hEven hPos)
    (fun x y => map_add (YfullGen L hEven hPos) x y)
    (fun c x => map_smul (YfullGen L hEven hPos) c x)
    (map_zero (YfullGen L hEven hPos)) p (gradingLatGen_le_HSpanLatGen L hEven hPos p hu)

/-- **VA1 (grading_mode)**: `mode (YfullGen u) j v ∈ gradingLatGen (p + q - j - 1)`. -/
theorem YfullGen_grading_mode (hEven : L.Even) (hPos : L.PosDef) {p q : ℤ} (u : LatModuleGen L)
    (hu : u ∈ gradingLatGen L p) (v : LatModuleGen L) (hv : v ∈ gradingLatGen L q) (j : ℤ) :
    mode (YfullGen L hEven hPos u) j v ∈ gradingLatGen L (p + q - j - 1) := by
  rw [mode_apply]
  have := YfullGen_gradedField_of_mem L hEven hPos hu (-j - 1) q v hv
  rwa [show p + q + (-j - 1) = p + q - j - 1 from by ring] at this

end VOA.LatGen
