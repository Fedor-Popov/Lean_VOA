/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean v4.35.0-rc3 with the
module system), files:
  CFSG/Monster/Griess/TrialityMatrix/Blocks.lean
  CFSG/Monster/Griess/TrialityMatrix.lean
Original authors (from the `@misc{axiom-cfsg}` citation, "Lean formalization of the
classification of finite simple groups", 2026):
  Cureton, Dean and Ilin, Vasily and Mehta, Bhavik and Voss, Niels and Cabral, Rafael and
  Defant, Colin and Gregory, Erik and Hill, Aaron and Hong, Letong and Hu, Qinheping and Jamner,
  Dustin and Jiang, Albert and Jordan, Tadeusz and Kurghinyan, Andranik and Lau, Kenny and
  Laurent, Jonathan and Liang, David and Limperg, Jannis and Mahns, Simon and Nugent, Brian and
  Olson, Connor and Ono, Ken and Paul, Eric and Rajan, Dhruv and Ram, Karun and Ray, Charlie and
  Siu, Ho Chung and Swaminathan, Ashvin A. and Thorner, Jesse and Tsaplin, Aleksey and Wang,
  Chenkai.
Port to Lean 4.30.0 / Mathlib v4.30.0 for LeanVOA by Fedor K. Popov (with Claude).
Released under the Apache 2.0 license.  Modifications relative to the source are listed in the
"Port notes" section of the module docstring below.
-/
import VOA.Moonshine.MonsterGriess.TrialityBasis
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

/-!
# Axiom's Monster port: the rational triality element `tauB` of `SpaceB`

In the orthogonal basis `tbasis` (`TrialityBasis.lean`) the triality is block diagonal:

* identity on the 24 diagonal matrix units;
* the cyclic permutation `cyc3` on each of the triples indexed by `LtPair × Fin 3` and
  `C₀ × Fin 24 × Fin 3`;
* on the 64 octad vectors of each octad `d`, the matrix `octHD d = H·D` (Fourier matrix of the
  even-subset quadratic space times its sign matrix), of order 3 and trace 1.

⭐ `tauB := Matrix.toLinOfInv tbasis tbasis tauMat_transpose_mul tauMat_mul_transpose :
SpaceB ≃ₗ[ℚ] SpaceB`, with `tauB_pow_three`, `orderOf_tauB = 3`, `bform_tauB` (an isometry of the
form), `map_tauB_BR` (it preserves the dyadic lattice `BR`), `trace_tauB = 783`,
`finrank_ker_tauB_sub_one = 66150`, its values on the basis (`tauB_diag`, `tauB_pair`, `tauB_odd`,
`tauB_oct`, `tauB_Xlift_rOct`), and the summary `rational_triality_matrix`.

This file does **not** prove that `tauB` preserves the Griess product: that is the source's
`Griess/ProductInvariance.lean` (`tauB_gmul`), not ported here.

## Port notes
* Namespace `CFSG.Monster.Griess` ↦ `VOA.Moonshine.MonsterGriess` (as in the earlier ports).
  Module-system syntax, `@[expose]` and the source's `attribute [-instance] …` line dropped.
  Bodies verbatim.
-/

set_option linter.style.longLine false
set_option linter.style.show false

namespace VOA.Moonshine.MonsterGriess

/-! ### From `CFSG/Monster/Griess/TrialityMatrix/Blocks.lean` -/

open Matrix Module
open scoped Kronecker

section Diag2

variable {m n : Type*}

def diag2 (A : Matrix m m ℚ) (D : Matrix n n ℚ) : Matrix (m ⊕ n) (m ⊕ n) ℚ :=
  fromBlocks A 0 0 D

theorem diag2_apply_inl_inl (A : Matrix m m ℚ) (D : Matrix n n ℚ) (i j : m) :
    diag2 A D (.inl i) (.inl j) = A i j := rfl

theorem diag2_apply_inl_inr (A : Matrix m m ℚ) (D : Matrix n n ℚ) (i : m) (j : n) :
    diag2 A D (.inl i) (.inr j) = 0 := rfl

theorem diag2_apply_inr_inl (A : Matrix m m ℚ) (D : Matrix n n ℚ) (i : n) (j : m) :
    diag2 A D (.inr i) (.inl j) = 0 := rfl

theorem diag2_apply_inr_inr (A : Matrix m m ℚ) (D : Matrix n n ℚ) (i j : n) :
    diag2 A D (.inr i) (.inr j) = D i j := rfl

theorem diag2_mul [Fintype m] [Fintype n] (A A' : Matrix m m ℚ) (D D' : Matrix n n ℚ) :
    diag2 A D * diag2 A' D' = diag2 (A * A') (D * D') := by
  simp only [diag2, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem diag2_transpose (A : Matrix m m ℚ) (D : Matrix n n ℚ) :
    (diag2 A D)ᵀ = diag2 Aᵀ Dᵀ := by
  simp only [diag2, fromBlocks_transpose, transpose_zero]

theorem diag2_one [DecidableEq m] [DecidableEq n] :
    diag2 (1 : Matrix m m ℚ) (1 : Matrix n n ℚ) = 1 :=
  fromBlocks_one

theorem diag2_pow [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℚ) (D : Matrix n n ℚ) (k : ℕ) : diag2 A D ^ k = diag2 (A ^ k) (D ^ k) := by
  induction k with
  | zero => simp only [pow_zero, diag2_one]
  | succ k ih => rw [pow_succ, ih, diag2_mul, ← pow_succ, ← pow_succ]

theorem trace_diag2 [Fintype m] [Fintype n] (A : Matrix m m ℚ) (D : Matrix n n ℚ) :
    trace (diag2 A D) = trace A + trace D := by
  simp only [trace, diag, Fintype.sum_sum_type]
  rfl

theorem diag2_diagonal [DecidableEq m] [DecidableEq n] (a : m → ℚ) (b : n → ℚ) :
    diag2 (diagonal a) (diagonal b) = diagonal (Sum.elim a b) :=
  fromBlocks_diagonal a b

theorem diag2_mem_dyadic {A : Matrix m m ℚ} {D : Matrix n n ℚ} (hA : ∀ i j, A i j ∈ dyadic)
    (hD : ∀ i j, D i j ∈ dyadic) : ∀ x y, diag2 A D x y ∈ dyadic
  | .inl i, .inl j => hA i j
  | .inl _, .inr _ => dyadic.zero_mem
  | .inr _, .inl _ => dyadic.zero_mem
  | .inr i, .inr j => hD i j

end Diag2

section Kron1

variable {n : Type*} (ι : Type*) [DecidableEq ι]

def kron1 (A : Matrix n n ℚ) : Matrix (ι × n) (ι × n) ℚ := (1 : Matrix ι ι ℚ) ⊗ₖ A

theorem kron1_apply (A : Matrix n n ℚ) (i j : ι) (k l : n) :
    kron1 ι A (i, k) (j, l) = (1 : Matrix ι ι ℚ) i j * A k l := rfl

theorem kron1_mul [Fintype ι] [Fintype n] (A B : Matrix n n ℚ) :
    kron1 ι A * kron1 ι B = kron1 ι (A * B) := by
  rw [kron1, kron1, kron1, ← mul_kronecker_mul, Matrix.one_mul]

theorem kron1_transpose (A : Matrix n n ℚ) : (kron1 ι A)ᵀ = kron1 ι Aᵀ := by
  rw [kron1, kron1, ← kroneckerMap_transpose, transpose_one]

theorem kron1_one [DecidableEq n] : kron1 ι (1 : Matrix n n ℚ) = 1 := one_kronecker_one

theorem kron1_pow [Fintype ι] [Fintype n] [DecidableEq n] (A : Matrix n n ℚ) (k : ℕ) :
    kron1 ι A ^ k = kron1 ι (A ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, kron1_one]
  | succ k ih => rw [pow_succ, ih, kron1_mul, ← pow_succ]

theorem trace_kron1 [Fintype ι] [Fintype n] (A : Matrix n n ℚ) :
    trace (kron1 ι A) = Fintype.card ι * trace A := by
  rw [kron1, trace_kronecker, trace_one]

theorem kron1_diagonal [DecidableEq n] (s : n → ℚ) :
    kron1 ι (diagonal s) = diagonal fun p : ι × n => s p.2 := by
  rw [kron1, ← diagonal_one, diagonal_kronecker_diagonal]
  simp only [one_mul]

theorem one_apply_mem_dyadic {m : Type*} [DecidableEq m] (i j : m) :
    (1 : Matrix m m ℚ) i j ∈ dyadic := by
  rw [one_apply]
  split_ifs
  · exact dyadic.one_mem
  · exact dyadic.zero_mem

theorem kron1_mem_dyadic {A : Matrix n n ℚ} (hA : ∀ k l, A k l ∈ dyadic) :
    ∀ x y, kron1 ι A x y ∈ dyadic
  | (i, k), (j, l) => dyadic.mul_mem (one_apply_mem_dyadic i j) (hA k l)

end Kron1

def cyc3 : Matrix (Fin 3) (Fin 3) ℚ := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem cyc3_apply (k l : Fin 3) : cyc3 k l = if l = k + 1 then 1 else 0 := by
  fin_cases k <;> fin_cases l <;> simp [cyc3]

theorem cyc3_mul_transpose : cyc3 * cyc3ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc3, Matrix.mul_apply, Fin.sum_univ_three]

theorem cyc3_transpose_mul : cyc3ᵀ * cyc3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc3, Matrix.mul_apply, Fin.sum_univ_three]

theorem cyc3_pow_three : cyc3 ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, cyc3, Matrix.mul_apply, Fin.sum_univ_three]

theorem trace_cyc3 : trace cyc3 = 0 := by
  simp [trace, cyc3, Fin.sum_univ_three]

theorem cyc3_mem_dyadic (k l : Fin 3) : cyc3 k l ∈ dyadic := by
  rw [cyc3_apply]
  split_ifs
  · exact dyadic.one_mem
  · exact dyadic.zero_mem

theorem cyc3_conj_diagonal (s : Fin 3 → ℚ) :
    cyc3ᵀ * diagonal s * cyc3 = diagonal ![s 2, s 0, s 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc3, Matrix.mul_apply, Fin.sum_univ_three, diagonal_apply]

noncomputable def octH (d : OctadWord) :
    Matrix (Octad.EvenQuot (octSupp d)) (Octad.EvenQuot (octSupp d)) ℚ :=
  fourierMatrix (QuadraticMap.polarBilin (Octad.quadForm (octSupp d))) 3

noncomputable def octD (d : OctadWord) :
    Matrix (Octad.EvenQuot (octSupp d)) (Octad.EvenQuot (octSupp d)) ℚ :=
  signMatrix (Octad.quadForm (octSupp d))

noncomputable def octHD (d : OctadWord) :
    Matrix (Octad.EvenQuot (octSupp d)) (Octad.EvenQuot (octSupp d)) ℚ :=
  octH d * octD d

theorem octH_mul_transpose (d : OctadWord) : octH d * (octH d)ᵀ = 1 :=
  (Octad.eight_point_even_subset_quadratic_space (octSupp d) (card_octSupp d)).2.2.2.2.2.1

theorem octD_mul_transpose (d : OctadWord) : octD d * (octD d)ᵀ = 1 :=
  (Octad.eight_point_even_subset_quadratic_space (octSupp d) (card_octSupp d)).2.2.2.2.2.2.2.1

theorem orderOf_octHD (d : OctadWord) : orderOf (octHD d) = 3 :=
  (Octad.eight_point_even_subset_quadratic_space (octSupp d) (card_octSupp d)).2.2.2.2.2.2.2.2.2.1

theorem trace_octHD (d : OctadWord) : trace (octHD d) = 1 :=
  (Octad.eight_point_even_subset_quadratic_space (octSupp d)
    (card_octSupp d)).2.2.2.2.2.2.2.2.2.2.1

theorem octHD_pow_three (d : OctadWord) : octHD d ^ 3 = 1 := by
  rw [← orderOf_octHD d]
  exact pow_orderOf_eq_one _

theorem octHD_mul_transpose (d : OctadWord) : octHD d * (octHD d)ᵀ = 1 := by
  rw [octHD, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (octD d), octD_mul_transpose,
    Matrix.one_mul, octH_mul_transpose]

theorem octHD_transpose_mul (d : OctadWord) : (octHD d)ᵀ * octHD d = 1 :=
  mul_eq_one_comm.1 (octHD_mul_transpose d)

theorem octHD_mem_dyadic (d : OctadWord) (u v : Octad.EvenQuot (octSupp d)) :
    octHD d u v ∈ dyadic :=
  mul_mem_dyadic (fourierMatrix_mem_dyadic _ 3) (signMatrix_mem_dyadic _) u v

theorem octHD_cls (d : OctadWord) {δ ε : Finset (Fin 24)} (hδ : δ ⊆ octSupp d)
    (hδe : Even δ.card) (hε : ε ⊆ octSupp d) (hεe : Even ε.card) :
    octHD d (Octad.cls (octSupp d) δ) (Octad.cls (octSupp d) ε) =
      (8 : ℚ)⁻¹ * (-1) ^ ((δ ∩ ε).card + ε.card / 2) := by
  have h4 : 4 ∣ (octSupp d).card := by rw [card_octSupp]; norm_num
  rw [octHD, octD, signMatrix, mul_diagonal, octH, fourierMatrix,
    Octad.polarBilin_quadForm_cls h4 hδ hδe hε hεe, Octad.quadForm_cls h4 hε hεe,
    Octad.sgn_natCast, Octad.sgn_natCast, pow_add]
  norm_num
  ring

theorem sq_eq_transpose_of_pow_three {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℚ} (h3 : A ^ 3 = 1) (ho : A * Aᵀ = 1) : A ^ 2 = Aᵀ := by
  calc A ^ 2 = A ^ 2 * (A * Aᵀ) := by rw [ho, Matrix.mul_one]
    _ = A ^ 3 * Aᵀ := by rw [← Matrix.mul_assoc, ← pow_succ]
    _ = Aᵀ := by rw [h3, Matrix.one_mul]

theorem three_mul_finrank_ker_sub_one {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (T : Module.End ℚ V) (hT : T ^ 3 = 1) :
    3 * (finrank ℚ (LinearMap.ker (T - 1)) : ℚ) =
      finrank ℚ V + LinearMap.trace ℚ V T + LinearMap.trace ℚ V (T ^ 2) := by
  set P : Module.End ℚ V := (3 : ℚ)⁻¹ • (1 + T + T ^ 2) with hP
  have hT4 : T ^ 4 = T := by rw [pow_succ, hT, one_mul]
  have hPidem : IsIdempotentElem P := by
    show P * P = P
    rw [hP, smul_mul_smul_comm]
    have : (1 + T + T ^ 2) * (1 + T + T ^ 2) = (3 : ℚ) • (1 + T + T ^ 2) := by
      have e : (1 + T + T ^ 2) * (1 + T + T ^ 2) = 1 + 2 • T + 3 • T ^ 2 + 2 • T ^ 3 + T ^ 4 := by
        noncomm_ring
      rw [e, hT, hT4, ← Nat.cast_smul_eq_nsmul ℚ 2, ← Nat.cast_smul_eq_nsmul ℚ 3]
      module
    rw [this, smul_smul]
    norm_num
  have hrange : LinearMap.range P = LinearMap.ker (T - 1) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      show (T * P) y = P y
      rw [hP, mul_smul_comm]
      congr 1
      have e : T * (1 + T + T ^ 2) = T + T ^ 2 + T ^ 3 := by noncomm_ring
      rw [e, hT]
      abel_nf
    · intro hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
      refine ⟨x, ?_⟩
      have hx2 : (T ^ 2) x = x := by rw [pow_two, Module.End.mul_apply, hx, hx]
      rw [hP, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply,
        hx, hx2]
      module
  have htrace : LinearMap.trace ℚ V P = finrank ℚ (LinearMap.range P) :=
    LinearMap.IsProj.trace (LinearMap.IsIdempotentElem.isProj_range P hPidem)
  rw [← hrange, ← htrace, hP, map_smul, map_add, map_add, LinearMap.trace_one, smul_eq_mul]
  ring

theorem bform_toLin_of_gram {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℚ SpaceB)
    {N : ι → ℚ} (hb : ∀ x y, bform (b x) (b y) = if x = y then N x else 0)
    {M : Matrix ι ι ℚ} (hM : M * diagonal N * Mᵀ = diagonal N) (u v : SpaceB) :
    bform (toLin b b Mᵀ u) (toLin b b Mᵀ v) = bform u v := by
  have hG : LinearMap.toMatrix₂ b b bform = diagonal N := by
    ext x y
    rw [LinearMap.toMatrix₂_apply, hb, diagonal_apply]
  have key : LinearMap.toMatrix₂ b b (bform.compl₁₂ (toLin b b Mᵀ) (toLin b b Mᵀ)) =
      LinearMap.toMatrix₂ b b bform := by
    rw [LinearMap.toMatrix₂_compl₁₂ b b, LinearMap.toMatrix_toLin, transpose_transpose, hG, hM]
  exact LinearMap.congr_fun₂ ((LinearMap.toMatrix₂ b b).injective key) u v

theorem map_toLin_BR_le {M : Matrix TIdx TIdx ℚ} (hM : ∀ x y, M x y ∈ dyadic) :
    BR.map ((toLin tbasis tbasis M).restrictScalars dyadic) ≤ BR := by
  rw [← span_tbasis, Submodule.map_span_le]
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.restrictScalars_apply, toLin_self]
  refine Submodule.sum_mem _ fun y _ => ?_
  exact (Submodule.span dyadic (Set.range tbasis)).smul_mem (⟨M y x, hM y x⟩ : dyadic)
    (Submodule.subset_span ⟨y, rfl⟩)

theorem toLin_mem_BR {M : Matrix TIdx TIdx ℚ} (hM : ∀ x y, M x y ∈ dyadic) {u : SpaceB}
    (hu : u ∈ BR) : toLin tbasis tbasis M u ∈ BR :=
  map_toLin_BR_le hM ⟨u, hu, rfl⟩

theorem sum_ite_smul_tbasis (x : TIdx) :
    ∑ y : TIdx, (if y = x then (1 : ℚ) else 0) • tbasis y = tbasis x := by
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem toLin_diagonal_self {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℚ SpaceB)
    (s : ι → ℚ) (x : ι) : toLin b b (diagonal s) (b x) = s x • b x := by
  rw [toLin_self, Finset.sum_eq_single x (fun y _ hy => by rw [diagonal_apply_ne _ hy, zero_smul])
    (fun h => absurd (Finset.mem_univ x) h), diagonal_apply_eq]

/-! ### From `CFSG/Monster/Griess/TrialityMatrix.lean` -/

open VOA.Moonshine.MonsterGriess.Spin

noncomputable instance instDecidableEqOddOctIdx : DecidableEq ((C₀ × Fin 24 × Fin 3) ⊕ OctIdx) :=
  @instDecidableEqSum _ _ inferInstance inferInstance

noncomputable instance instDecidableEqPairOddOctIdx :
    DecidableEq ((LtPair × Fin 3) ⊕ (C₀ × Fin 24 × Fin 3) ⊕ OctIdx) :=
  @instDecidableEqSum _ _ inferInstance inferInstance

noncomputable def pairBlock : Matrix (LtPair × Fin 3) (LtPair × Fin 3) ℚ :=
  kron1 LtPair cyc3

noncomputable def oddBlock : Matrix (C₀ × Fin 24 × Fin 3) (C₀ × Fin 24 × Fin 3) ℚ :=
  kron1 C₀ (kron1 (Fin 24) cyc3)

noncomputable def octBlock : Matrix OctIdx OctIdx ℚ := blockDiagonal' octHD

noncomputable def tauMat : Matrix TIdx TIdx ℚ :=
  diag2 1 (diag2 pairBlock (diag2 oddBlock octBlock))

theorem pairBlock_mul_transpose : pairBlock * pairBlockᵀ = 1 := by
  rw [pairBlock, kron1_transpose, kron1_mul, cyc3_mul_transpose, kron1_one]

theorem pairBlock_transpose_mul : pairBlockᵀ * pairBlock = 1 := by
  rw [pairBlock, kron1_transpose, kron1_mul, cyc3_transpose_mul, kron1_one]

theorem oddBlock_mul_transpose : oddBlock * oddBlockᵀ = 1 := by
  rw [oddBlock, kron1_transpose, kron1_transpose, kron1_mul, kron1_mul, cyc3_mul_transpose,
    kron1_one, kron1_one]

theorem oddBlock_transpose_mul : oddBlockᵀ * oddBlock = 1 := by
  rw [oddBlock, kron1_transpose, kron1_transpose, kron1_mul, kron1_mul, cyc3_transpose_mul,
    kron1_one, kron1_one]

theorem octBlock_mul_transpose : octBlock * octBlockᵀ = 1 := by
  rw [octBlock, blockDiagonal'_transpose, ← blockDiagonal'_mul, ← blockDiagonal'_one]
  congr 1
  funext d
  exact octHD_mul_transpose d

theorem octBlock_transpose_mul : octBlockᵀ * octBlock = 1 := by
  rw [octBlock, blockDiagonal'_transpose, ← blockDiagonal'_mul, ← blockDiagonal'_one]
  congr 1
  funext d
  exact octHD_transpose_mul d

theorem pairBlock_pow_three : pairBlock ^ 3 = 1 := by
  rw [pairBlock, kron1_pow, cyc3_pow_three, kron1_one]

theorem oddBlock_pow_three : oddBlock ^ 3 = 1 := by
  rw [oddBlock, kron1_pow, kron1_pow, cyc3_pow_three, kron1_one, kron1_one]

theorem octBlock_pow_three : octBlock ^ 3 = 1 := by
  rw [octBlock, ← blockDiagonal'_pow, ← blockDiagonal'_one]
  congr 1
  funext d
  exact octHD_pow_three d

theorem trace_pairBlock : trace pairBlock = 0 := by
  rw [pairBlock, trace_kron1, trace_cyc3, mul_zero]

theorem trace_oddBlock : trace oddBlock = 0 := by
  rw [oddBlock, trace_kron1, trace_kron1, trace_cyc3, mul_zero, mul_zero]

theorem trace_octBlock : trace octBlock = 759 := by
  rw [octBlock, trace_blockDiagonal']
  simp only [trace_octHD, Finset.sum_const, Finset.card_univ, card_octadWord, nsmul_eq_mul,
    mul_one]
  norm_num

theorem tauMat_mul_transpose : tauMat * tauMatᵀ = 1 := by
  rw [tauMat, diag2_transpose, diag2_transpose, diag2_transpose, diag2_mul, diag2_mul, diag2_mul,
    transpose_one, Matrix.mul_one, pairBlock_mul_transpose, oddBlock_mul_transpose,
    octBlock_mul_transpose, diag2_one, diag2_one, diag2_one]

theorem tauMat_transpose_mul : tauMatᵀ * tauMat = 1 := by
  rw [tauMat, diag2_transpose, diag2_transpose, diag2_transpose, diag2_mul, diag2_mul, diag2_mul,
    transpose_one, Matrix.mul_one, pairBlock_transpose_mul, oddBlock_transpose_mul,
    octBlock_transpose_mul, diag2_one, diag2_one, diag2_one]

theorem tauMat_pow_three : tauMat ^ 3 = 1 := by
  rw [tauMat, diag2_pow, diag2_pow, diag2_pow, one_pow, pairBlock_pow_three, oddBlock_pow_three,
    octBlock_pow_three, diag2_one, diag2_one, diag2_one]

theorem trace_tauMat : trace tauMat = 783 := by
  rw [tauMat, trace_diag2, trace_diag2, trace_diag2, trace_one, trace_pairBlock, trace_oddBlock,
    trace_octBlock, Fintype.card_fin]
  norm_num

theorem trace_tauMat_sq : trace (tauMat ^ 2) = 783 := by
  rw [sq_eq_transpose_of_pow_three tauMat_pow_three tauMat_mul_transpose, trace_transpose,
    trace_tauMat]

theorem tauMat_mem_dyadic : ∀ x y, tauMat x y ∈ dyadic :=
  diag2_mem_dyadic one_apply_mem_dyadic (diag2_mem_dyadic (kron1_mem_dyadic _ cyc3_mem_dyadic)
    (diag2_mem_dyadic (kron1_mem_dyadic _ (kron1_mem_dyadic _ cyc3_mem_dyadic))
      fun ⟨d, u⟩ ⟨d', v⟩ => by
        rw [octBlock, blockDiagonal'_apply]
        split_ifs with h
        · exact octHD_mem_dyadic _ _ _
        · exact dyadic.zero_mem))

theorem diagonal_tnorm : diagonal tnorm = diag2 1 (diag2 ((2 : ℚ) • 1) (diag2 1 1)) := by
  ext x y
  rcases x with i | q | q | o <;> rcases y with j | q' | q' | o' <;>
    simp [diag2, diagonal_apply, tnorm, one_apply]

theorem tauMat_mul_diagonal_tnorm : tauMat * diagonal tnorm * tauMatᵀ = diagonal tnorm := by
  rw [diagonal_tnorm, tauMat, diag2_transpose, diag2_transpose, diag2_transpose, diag2_mul,
    diag2_mul, diag2_mul, diag2_mul, diag2_mul, diag2_mul, Matrix.mul_one, Matrix.mul_one,
    Matrix.mul_one, transpose_one, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, pairBlock_mul_transpose, oddBlock_mul_transpose, octBlock_mul_transpose]

theorem tauMat_diag_apply (i : Fin 24) (y : TIdx) :
    tauMat (.inl i) y = if y = .inl i then 1 else 0 := by
  rcases y with j | q | q | o
  · simp [tauMat, diag2_apply_inl_inl, one_apply, eq_comm]
  · simp [tauMat, diag2_apply_inl_inr]
  · simp [tauMat, diag2_apply_inl_inr]
  · simp [tauMat, diag2_apply_inl_inr]

theorem tauMat_pair_apply (p : LtPair) (k : Fin 3) (y : TIdx) :
    tauMat (.inr (.inl (p, k))) y = if y = .inr (.inl (p, k + 1)) then 1 else 0 := by
  rcases y with j | ⟨p', k'⟩ | q | o
  · simp [tauMat, diag2_apply_inr_inl]
  · simp only [tauMat, diag2_apply_inr_inr, diag2_apply_inl_inl, pairBlock, kron1_apply, one_apply,
      cyc3_apply, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq]
    by_cases hp : p = p' <;> by_cases hk : k' = k + 1 <;> simp [hp, hk, eq_comm]
  · simp [tauMat, diag2_apply_inr_inr, diag2_apply_inl_inr]
  · simp [tauMat, diag2_apply_inr_inr, diag2_apply_inl_inr]

theorem tauMat_odd_apply (c : C₀) (i : Fin 24) (k : Fin 3) (y : TIdx) :
    tauMat (.inr (.inr (.inl (c, i, k)))) y =
      if y = .inr (.inr (.inl (c, i, k + 1))) then 1 else 0 := by
  rcases y with j | q | ⟨c', i', k'⟩ | o
  · simp [tauMat, diag2_apply_inr_inl]
  · simp [tauMat, diag2_apply_inr_inr, diag2_apply_inr_inl]
  · simp only [tauMat, diag2_apply_inr_inr, diag2_apply_inl_inl, oddBlock, kron1_apply, one_apply,
      cyc3_apply, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq]
    by_cases hc : c = c' <;> by_cases hi : i = i' <;> by_cases hk : k' = k + 1 <;>
      simp [hc, hi, hk, eq_comm]
  · simp [tauMat, diag2_apply_inr_inr, diag2_apply_inl_inr]

theorem tauMat_oct_apply_oct (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) :
    tauMat (.inr (.inr (.inr ⟨d, v⟩))) (.inr (.inr (.inr ⟨d, w⟩))) = octHD d v w := by
  simp only [tauMat, diag2_apply_inr_inr, octBlock, blockDiagonal'_apply_eq]

theorem tauMat_oct_apply_of_notMem (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) (y : TIdx)
    (hy : y ∉ Set.range fun w : Octad.EvenQuot (octSupp d) => (.inr (.inr (.inr ⟨d, w⟩)) : TIdx)) :
    tauMat (.inr (.inr (.inr ⟨d, v⟩))) y = 0 := by
  rcases y with j | q | q | ⟨d', w⟩
  · rfl
  · rfl
  · rfl
  · have hd : d ≠ d' := by
      rintro rfl
      exact hy ⟨w, rfl⟩
    simp only [tauMat, diag2_apply_inr_inr, octBlock]
    exact blockDiagonal'_apply_ne _ _ _ hd

/-- ⭐ **The rational triality element** `tauB : SpaceB ≃ₗ[ℚ] SpaceB` (the source's `tauB`):
the linear automorphism with matrix `tauMatᵀ` in the orthogonal basis `tbasis`. -/
noncomputable def tauB : SpaceB ≃ₗ[ℚ] SpaceB :=
  Matrix.toLinOfInv tbasis tbasis tauMat_transpose_mul tauMat_mul_transpose

theorem coe_tauB : (tauB : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis tauMatᵀ := rfl

theorem coe_tauB_symm : (tauB.symm : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis tauMat := rfl

theorem tauB_apply (u : SpaceB) : tauB u = toLin tbasis tbasis tauMatᵀ u := rfl

theorem tauB_symm_apply (u : SpaceB) : tauB.symm u = toLin tbasis tbasis tauMat u := rfl

theorem tauB_tbasis (x : TIdx) : tauB (tbasis x) = ∑ y, tauMat x y • tbasis y := by
  rw [tauB_apply, toLin_self]
  rfl

theorem tauB_diag (i : Fin 24) : tauB (tbasis (.inl i)) = tbasis (.inl i) := by
  rw [tauB_tbasis]
  simp only [tauMat_diag_apply, sum_ite_smul_tbasis]

theorem tauB_pair (p : LtPair) (k : Fin 3) :
    tauB (tbasis (.inr (.inl (p, k)))) = tbasis (.inr (.inl (p, k + 1))) := by
  rw [tauB_tbasis]
  simp only [tauMat_pair_apply, sum_ite_smul_tbasis]

theorem tauB_odd (c : C₀) (i : Fin 24) (k : Fin 3) :
    tauB (tbasis (.inr (.inr (.inl (c, i, k))))) = tbasis (.inr (.inr (.inl (c, i, k + 1)))) := by
  rw [tauB_tbasis]
  simp only [tauMat_odd_apply, sum_ite_smul_tbasis]

theorem tauB_oct (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    tauB (tbasis (.inr (.inr (.inr ⟨d, v⟩)))) =
      ∑ w, octHD d v w • tbasis (.inr (.inr (.inr ⟨d, w⟩))) := by
  rw [tauB_tbasis]
  refine (Fintype.sum_of_injective (fun w : Octad.EvenQuot (octSupp d) =>
    (.inr (.inr (.inr ⟨d, w⟩)) : TIdx)) ?_ _ _ ?_ ?_).symm
  · intro w w' h
    simpa using h
  · intro y hy
    rw [tauMat_oct_apply_of_notMem d v y hy, zero_smul]
  · intro w
    rw [tauMat_oct_apply_oct]

theorem tauB_Xlift_rOct {d : OctadWord} {δ : Finset (Fin 24)} (hδ : δ ⊆ octSupp d)
    (he : Even δ.card) :
    tauB ((0 : symMat), Xlift (rOct d δ), (0 : SpaceW)) =
      ∑ v : Octad.EvenQuot (octSupp d),
        ((8 : ℚ)⁻¹ * (-1) ^ ((δ ∩ octRep d v).card + (octRep d v).card / 2)) •
          ((0 : symMat), Xlift (rOct d (octRep d v)), (0 : SpaceW)) := by
  rw [← tbasis_oct_cls hδ he, tauB_oct]
  refine Finset.sum_congr rfl fun v _ => ?_
  obtain ⟨h1, h2, h3⟩ := octRep_spec d v
  rw [tbasis_oct]
  refine congrArg₂ (· • ·) ?_ rfl
  calc octHD d (Octad.cls (octSupp d) δ) v =
        octHD d (Octad.cls (octSupp d) δ) (Octad.cls (octSupp d) (octRep d v)) := by rw [h3]
    _ = _ := octHD_cls d hδ he h1 h2

theorem bform_tauB (u v : SpaceB) : bform (tauB u) (tauB v) = bform u v :=
  bform_toLin_of_gram tbasis bform_tbasis tauMat_mul_diagonal_tnorm u v

theorem bform_tauB_symm (u v : SpaceB) : bform (tauB.symm u) (tauB.symm v) = bform u v := by
  rw [← bform_tauB, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem tauB_mem_BR {u : SpaceB} (hu : u ∈ BR) : tauB u ∈ BR := by
  rw [tauB_apply]
  exact toLin_mem_BR (fun x y => tauMat_mem_dyadic y x) hu

theorem tauB_symm_mem_BR {u : SpaceB} (hu : u ∈ BR) : tauB.symm u ∈ BR := by
  rw [tauB_symm_apply]
  exact toLin_mem_BR tauMat_mem_dyadic hu

theorem tauB_mem_BR_iff {u : SpaceB} : tauB u ∈ BR ↔ u ∈ BR :=
  ⟨fun h => by simpa using tauB_symm_mem_BR h, tauB_mem_BR⟩

theorem tauB_symm_mem_BR_iff {u : SpaceB} : tauB.symm u ∈ BR ↔ u ∈ BR :=
  ⟨fun h => by simpa using tauB_mem_BR h, tauB_symm_mem_BR⟩

theorem map_tauB_BR : BR.map ((tauB : SpaceB →ₗ[ℚ] SpaceB).restrictScalars dyadic) = BR := by
  ext u
  refine ⟨?_, fun h => ⟨tauB.symm u, tauB_symm_mem_BR h, tauB.apply_symm_apply u⟩⟩
  rintro ⟨v, hv, rfl⟩
  exact tauB_mem_BR hv

theorem coe_pow_linearEquiv (e : SpaceB ≃ₗ[ℚ] SpaceB) (n : ℕ) :
    ((e ^ n : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) = (e : SpaceB →ₗ[ℚ] SpaceB) ^ n :=
  map_pow LinearEquiv.automorphismGroup.toLinearMapMonoidHom e n

theorem coe_tauB_pow (n : ℕ) :
    (tauB : SpaceB →ₗ[ℚ] SpaceB) ^ n = toLin tbasis tbasis (tauMat ^ n)ᵀ := by
  rw [coe_tauB, transpose_pow, Matrix.toLin_pow]

/-- ⭐ `tauB ^ 3 = 1`. -/
theorem tauB_pow_three : tauB ^ 3 = 1 := by
  apply LinearEquiv.toLinearMap_injective
  rw [coe_pow_linearEquiv, coe_tauB_pow, tauMat_pow_three, transpose_one, Matrix.toLin_one]
  rfl

theorem trace_tauB : LinearMap.trace ℚ SpaceB tauB = 783 := by
  rw [LinearMap.trace_eq_matrix_trace ℚ tbasis, coe_tauB, LinearMap.toMatrix_toLin,
    trace_transpose, trace_tauMat]

theorem trace_tauB_sq : LinearMap.trace ℚ SpaceB ((tauB : SpaceB →ₗ[ℚ] SpaceB) ^ 2) = 783 := by
  rw [coe_tauB_pow, LinearMap.trace_eq_matrix_trace ℚ tbasis, LinearMap.toMatrix_toLin,
    trace_transpose, trace_tauMat_sq]

theorem tauB_ne_one : tauB ≠ 1 := by
  intro h
  have htr := trace_tauB
  rw [h, LinearEquiv.coe_toLinearMap_one, LinearMap.trace_id, finrank_B] at htr
  norm_num at htr

/-- ⭐ `tauB` has order exactly 3. -/
theorem orderOf_tauB : orderOf tauB = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime tauB_pow_three tauB_ne_one

theorem finrank_ker_tauB_sub_one :
    finrank ℚ (LinearMap.ker ((tauB : SpaceB →ₗ[ℚ] SpaceB) - 1)) = 66150 := by
  have h3 : (tauB : SpaceB →ₗ[ℚ] SpaceB) ^ 3 = 1 := by
    rw [← coe_pow_linearEquiv, tauB_pow_three]
    rfl
  have key := three_mul_finrank_ker_sub_one _ h3
  rw [trace_tauB, trace_tauB_sq, finrank_B] at key
  have h' : ((3 * finrank ℚ (LinearMap.ker ((tauB : SpaceB →ₗ[ℚ] SpaceB) - 1)) : ℕ) : ℚ) =
      ((3 * 66150 : ℕ) : ℚ) := by
    push_cast
    rw [key]
    norm_num
  have h'' := Nat.cast_injective h'
  omega

theorem rational_triality_matrix :
    (∀ i : Fin 24, tauB (tbasis (.inl i)) = tbasis (.inl i)) ∧
    (∀ (p : LtPair) (k : Fin 3),
      tauB (tbasis (.inr (.inl (p, k)))) = tbasis (.inr (.inl (p, k + 1)))) ∧
    (∀ (c : C₀) (i : Fin 24) (k : Fin 3),
      tauB (tbasis (.inr (.inr (.inl (c, i, k))))) = tbasis (.inr (.inr (.inl (c, i, k + 1))))) ∧
    (∀ (d : OctadWord) (v : Octad.EvenQuot (octSupp d)),
      tauB (tbasis (.inr (.inr (.inr ⟨d, v⟩)))) =
        ∑ w, (fourierMatrix (QuadraticMap.polarBilin (Octad.quadForm (octSupp d))) 3 *
          signMatrix (Octad.quadForm (octSupp d))) v w • tbasis (.inr (.inr (.inr ⟨d, w⟩)))) ∧
    (∀ (d : OctadWord) (δ ε : Finset (Fin 24)), δ ⊆ octSupp d → Even δ.card →
      ε ⊆ octSupp d → Even ε.card →
      (fourierMatrix (QuadraticMap.polarBilin (Octad.quadForm (octSupp d))) 3 *
          signMatrix (Octad.quadForm (octSupp d))) (Octad.cls (octSupp d) δ)
            (Octad.cls (octSupp d) ε) =
        (8 : ℚ)⁻¹ * (-1) ^ ((δ ∩ ε).card + ε.card / 2)) ∧
    (∀ (d : OctadWord) (δ : Finset (Fin 24)), δ ⊆ octSupp d → Even δ.card →
      tauB ((0 : symMat), Xlift (rOct d δ), (0 : SpaceW)) =
        ∑ v : Octad.EvenQuot (octSupp d),
          ((8 : ℚ)⁻¹ * (-1) ^ ((δ ∩ octRep d v).card + (octRep d v).card / 2)) •
            ((0 : symMat), Xlift (rOct d (octRep d v)), (0 : SpaceW))) ∧
    (∀ u v : SpaceB, bform (tauB u) (tauB v) = bform u v) ∧
    BR.map ((tauB : SpaceB →ₗ[ℚ] SpaceB).restrictScalars dyadic) = BR ∧
    orderOf tauB = 3 ∧
    LinearMap.trace ℚ SpaceB tauB = 783 ∧
    finrank ℚ (LinearMap.ker ((tauB : SpaceB →ₗ[ℚ] SpaceB) - 1)) = 66150 :=
  ⟨tauB_diag, tauB_pair, tauB_odd, tauB_oct,
    fun d _ _ hδ hδe hε hεe => octHD_cls d hδ hδe hε hεe, fun _ _ hδ he => tauB_Xlift_rOct hδ he,
    bform_tauB, map_tauB_BR, orderOf_tauB, trace_tauB, finrank_ker_tauB_sub_one⟩

end VOA.Moonshine.MonsterGriess
