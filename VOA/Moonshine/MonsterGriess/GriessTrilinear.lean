/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean v4.35.0-rc3 with the
module system), files:
  CFSG/Monster/Griess/Short.lean
  CFSG/Monster/Griess/Space.lean
  CFSG/Monster/Griess/Trilinear.lean
  CFSG/Monster/Griess/TrilinearData.lean
  CFSG/Monster/Griess/Parity.lean
  CFSG/Monster/Griess/Product.lean
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
import VOA.Moonshine.MonsterGriess.SpinExtraspecial
import VOA.Moonshine.MonsterGriess.AutO
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Axiom's Monster port (parity-centralizer closure): the Griess trilinear form, its uniqueness, `xB`

* `coordOf r`, `centralCoord r`, `rep p` — coordinates of `r ∈ Q` and the section
  `C × Cocode → Q`; `eq_zQ_pow_mul_rep`; `Xlift r ∈ SpaceX` (`± e_c` for short `r`);
* the bases `basisA` (of `symMat`, indexed by `Sym2 (Fin 24)`) and `basisB` (of `SpaceB`);
  `bform_self_pos` — `bform` is positive definite;
* `T u v w = bform (gmul u v) w` — the trilinear form; its explicit formula `Tex` (`T_eq_Tex`),
  full symmetry (`T_swap12`, `T_cycle`, `T_swap23`) and block values (`T_AAA`, …, `T_WWW`);
* ⭐ `T_unique` — a symmetric trilinear form with the block values of `IsGriessForm` equals `T`
  (the block values on `inA`, `inX (Xlift r)`, `inW (tensor q v)` determine it);
* ⭐ `xB : SpaceB ≃ₗ[ℚ] SpaceB`, `(A, x, N) ↦ (A, x, -N)` — the parity involution;
  its eigenspaces `mem_eigenspace_xB_one`, `mem_eigenspace_xB_neg_one`;
* `eq_of_bform_eq`, `bform_gmul`, `uQ_dotProduct_self`.

## Port notes
* Namespaces `CFSG.Monster.Griess` ↦ `VOA.Moonshine.MonsterGriess` (as in the earlier ports).
  Module-system syntax and the source's `attribute [-instance] …` line dropped.  Bodies verbatim
  except as listed.
* **Renamed:** the source's `CFSG.Monster.Griess.qf_zero` ↦ `qf_zero_mat`, because
  `VOA.Moonshine.MonsterGriess.qf_zero` (same statement) already exists in
  `MoonshineCNGriessTable.lean`.
* Drift: `ite_eq_left h`/`ite_eq_right h` (absent in Mathlib v4.30) ↦ `if_pos h`/`if_neg h`;
  `Basis` ↦ `Module.Basis` where Mathlib v4.30 requires it.
* Already ported and used: `symMat`, `SpaceX`, `SpaceW`, `SpaceB`, `bform`, `bform_apply`, `uQ`,
  `Umat`, `Rmat`, `qf`, `tau`, `Umat_symm`, `Am`, `xs`, `Nm`, `Am_symm`, `gmulA`, `gmulX`,
  `gmulWHalf`, `gmulW`, `gmulFun`, `gmul`, `gmul_apply` (`Algebra.lean`), `IsShortCoord`,
  `ShortIdx`, `uvec`, `LexLE` (`Short.lean`), `pair_eq_zero_of_isShortCoord`
  (`LatticeQuadratic.lean`).
* Omitted (not reached): `card_pairIdx`, `coe_basisA`, `gramDiag`, `BR`, `gmulFun_comm`,
  `gmul_comm`, `bform_comm`, `bform_gmul_assoc`, the unit `oneB`, the dyadic-coordinate
  layer (`DyadicCoords.lean`, `IsDyM`), the projections of `Parity.lean` other than `projW`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.MonsterGriess

open VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin
  VOA.Moonshine.MonsterGriess.SpinLattice Matrix Module Subgroup

/-! ### From `CFSG/Monster/Griess/Short.lean` -/

def IsShort (c : Q ⧸ center Q) : Prop :=
  ∃ u ∈ minVecs, classOf u = Multiplicative.toAdd (phi c)

noncomputable def coordOf (r : Q) : C × Cocode :=
  ((spinEquiv.symm r).a, (spinEquiv.symm r).δ)

noncomputable def centralCoord (r : Q) : ZMod 2 := (spinEquiv.symm r).s

theorem toAdd_phi_mk (r : Q) :
    Multiplicative.toAdd (phi (QuotientGroup.mk r)) = phi0 (coordOf r) :=
  have hx : spinEquiv (spinEquiv.symm r) = r := spinEquiv.apply_symm_apply r
  (congrArg (fun g => Multiplicative.toAdd (phi (QuotientGroup.mk g))) hx.symm).trans
    (congrArg Multiplicative.toAdd (phi_mk_spinEquiv (spinEquiv.symm r)))

theorem isShort_mk_iff (r : Q) : IsShort (QuotientGroup.mk r) ↔ IsShortCoord (coordOf r) := by
  unfold IsShort IsShortCoord
  rw [toAdd_phi_mk]

noncomputable def rep (p : C × Cocode) : Q := spinEquiv ⟨0, p.1, p.2⟩

theorem coordOf_rep (p : C × Cocode) : coordOf (rep p) = p := by
  rw [coordOf, rep, MulEquiv.symm_apply_apply]

theorem centralCoord_rep (p : C × Cocode) : centralCoord (rep p) = 0 := by
  rw [centralCoord, rep, MulEquiv.symm_apply_apply]

theorem eq_zQ_pow_mul_rep (r : Q) : r = zQ ^ (centralCoord r).val * rep (coordOf r) := by
  have hx : spinEquiv (spinEquiv.symm r) = r := spinEquiv.apply_symm_apply r
  have h : spinEquiv.symm r = ⟨centralCoord r, 0, 0⟩ * ⟨0, (coordOf r).1, (coordOf r).2⟩ := by
    ext <;> simp [centralCoord, coordOf, SpinCoord.mul_s]
  calc r = spinEquiv (spinEquiv.symm r) := hx.symm
    _ = spinEquiv (⟨centralCoord r, 0, 0⟩ * ⟨0, (coordOf r).1, (coordOf r).2⟩) :=
        congrArg spinEquiv h
    _ = zQ ^ (centralCoord r).val * rep (coordOf r) := by
        rw [map_mul, ← zQ_pow_val]
        rfl

theorem uvec_spec (c : ShortIdx) :
    uvec c ∈ minVecs ∧ classOf (uvec c) = phi0 c.1 ∧ LexLE (uvec c) (-uvec c) := by
  obtain ⟨hu, hcl⟩ := c.2.choose_spec
  unfold uvec
  split_ifs with h
  · exact ⟨hu, hcl, h⟩
  · refine ⟨neg_mem_minVecs hu, ?_, ?_⟩
    · exact ((classOf_eq_iff hu (neg_mem_minVecs hu)).2 (Or.inr rfl)).symm.trans hcl
    · rw [neg_neg]
      exact le_of_lt (lt_of_not_ge h)

theorem uvec_mem (c : ShortIdx) : uvec c ∈ minVecs := (uvec_spec c).1

theorem classOf_uvec (c : ShortIdx) : classOf (uvec c) = phi0 c.1 := (uvec_spec c).2.1

/-! ### From `CFSG/Monster/Griess/Space.lean` -/

abbrev PairIdx : Type := Sym2 (Fin 24)

def symEntry (A : symMat) : PairIdx → ℚ :=
  Sym2.lift ⟨fun i j => (A : Matrix (Fin 24) (Fin 24) ℚ) i j,
    fun i j => (congrFun (congrFun A.2 i) j).symm⟩

theorem symEntry_mk (A : symMat) (i j : Fin 24) :
    symEntry A s(i, j) = (A : Matrix (Fin 24) (Fin 24) ℚ) i j := Sym2.lift_mk _ _ _

def symCoord : symMat ≃ₗ[ℚ] (PairIdx → ℚ) where
  toFun := symEntry
  map_add' A B := by
    funext z
    induction z using Sym2.ind with | h i j => simp [symEntry_mk]
  map_smul' c A := by
    funext z
    induction z using Sym2.ind with | h i j => simp [symEntry_mk]
  invFun f := ⟨Matrix.of fun i j => f s(i, j), by
      ext i j
      simp only [transpose_apply, of_apply, Sym2.eq_swap]⟩
  left_inv A := by
    apply Subtype.ext
    ext i j
    simp only [of_apply, symEntry_mk]
  right_inv f := by
    funext z
    induction z using Sym2.ind with | h i j => simp only [symEntry_mk, of_apply]

noncomputable def basisA : Basis PairIdx ℚ symMat := Basis.ofEquivFun symCoord

theorem basisA_apply (z : PairIdx) (k l : Fin 24) :
    (basisA z : Matrix (Fin 24) (Fin 24) ℚ) k l = if s(k, l) = z then 1 else 0 := by
  rw [basisA, Basis.coe_ofEquivFun]
  change (Pi.single z 1 : PairIdx → ℚ) s(k, l) = _
  rw [Pi.single_apply]

def tensor (q : SpinIdx → ℚ) (v : Fin 24 → ℚ) : SpaceW := vecMulVec q v

noncomputable def Xlift (r : Q) : SpaceX :=
  open Classical in
  if h : IsShortCoord (coordOf r) then sgn (centralCoord r) • Pi.single ⟨coordOf r, h⟩ 1 else 0

abbrev BIdx : Type := PairIdx ⊕ ShortIdx ⊕ (SpinIdx × Fin 24)

noncomputable def basisB : Basis BIdx ℚ SpaceB :=
  basisA.prod ((Pi.basisFun ℚ ShortIdx).prod (Matrix.stdBasis ℚ SpinIdx (Fin 24)))

theorem basisB_inl (z : PairIdx) : basisB (Sum.inl z) = (basisA z, 0, 0) := by
  rw [basisB, Basis.prod_apply]
  rfl

theorem basisB_inr_inl (c : ShortIdx) : basisB (Sum.inr (Sum.inl c)) = (0, Pi.single c 1, 0) := by
  rw [basisB, Basis.prod_apply]
  simp [Basis.prod_apply]

theorem basisB_inr_inr (k : SpinIdx × Fin 24) :
    basisB (Sum.inr (Sum.inr k)) = (0, 0, tensor (Pi.single k.1 1) (Pi.single k.2 1)) := by
  obtain ⟨k₁, k₂⟩ := k
  rw [basisB, Basis.prod_apply]
  simp only [Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply, Basis.prod_apply, tensor]
  rw [Matrix.stdBasis_eq_single]
  congr 2
  ext i j
  simp only [Matrix.single_apply, vecMulVec_apply, Pi.single_apply]
  split_ifs <;> simp_all

theorem single_dotProduct_single {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    (Pi.single i (1 : ℚ) : ι → ℚ) ⬝ᵥ Pi.single j 1 = if i = j then 1 else 0 := by
  rw [single_dotProduct, one_mul, Pi.single_apply]

theorem bform_self (v : SpaceB) :
    bform v v = ∑ k, ∑ l, (v.1 : Matrix (Fin 24) (Fin 24) ℚ) k l ^ 2 + ∑ c, v.2.1 c ^ 2 +
      ∑ j, ∑ i, v.2.2 j i ^ 2 := by
  rw [bform_apply]
  congr 1
  · congr 1
    · simp only [trace, diag, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [show (v.1 : Matrix (Fin 24) (Fin 24) ℚ) l k = (v.1 : Matrix (Fin 24) (Fin 24) ℚ) k l from
        congrFun (congrFun v.1.2 k) l]
      ring
    · exact Finset.sum_congr rfl fun c _ => by ring
  · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem bform_self_pos {v : SpaceB} (hv : v ≠ 0) : 0 < bform v v := by
  rw [bform_self]
  have h1 : 0 ≤ ∑ k, ∑ l, (v.1 : Matrix (Fin 24) (Fin 24) ℚ) k l ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : 0 ≤ ∑ c, v.2.1 c ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3 : 0 ≤ ∑ j, ∑ i, v.2.2 j i ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_contra hle
  have hsum : ∑ k, ∑ l, (v.1 : Matrix (Fin 24) (Fin 24) ℚ) k l ^ 2 + ∑ c, v.2.1 c ^ 2 +
      ∑ j, ∑ i, v.2.2 j i ^ 2 = 0 := by linarith
  have e1 : ∑ k, ∑ l, (v.1 : Matrix (Fin 24) (Fin 24) ℚ) k l ^ 2 = 0 := by linarith
  have e2 : ∑ c, v.2.1 c ^ 2 = 0 := by linarith
  have e3 : ∑ j, ∑ i, v.2.2 j i ^ 2 = 0 := by linarith
  apply hv
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  · ext k l
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _).1 e1 k (Finset.mem_univ _)
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 this l (Finset.mem_univ _)
    simpa using this
  · funext c
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 e2 c (Finset.mem_univ _)
    simpa using this
  · ext j i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _).1 e3 j (Finset.mem_univ _)
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 this i (Finset.mem_univ _)
    simpa using this

theorem Xlift_eq {r : Q} (h : IsShortCoord (coordOf r)) :
    Xlift r = sgn (centralCoord r) • Pi.single ⟨coordOf r, h⟩ 1 := by
  unfold Xlift
  exact dif_pos h

/-! ### From `CFSG/Monster/Griess/Trilinear.lean` -/

theorem Rmat_symm (c : ShortIdx) : (Rmat c)ᵀ = Rmat c := by
  rw [Rmat, qmatR_transpose, zero_add, pair_eq_zero_of_isShortCoord c.2]

theorem pair_symm_of_short (d e c : ShortIdx) (h : c.1 = d.1 + e.1) :
    pair e.1.1 d.1.2 = pair d.1.1 e.1.2 := by
  have hc := pair_eq_zero_of_isShortCoord c.2
  have hd := pair_eq_zero_of_isShortCoord d.2
  have he := pair_eq_zero_of_isShortCoord e.2
  rw [h, Prod.fst_add, Prod.snd_add, pair_add_left, pair_add_right, pair_add_right, hd, he,
    zero_add, add_zero] at hc
  have h2 : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide
  exact h2 _ _ hc

theorem tau_comm (d e c : ShortIdx) : tau d e c = tau e d c := by
  unfold tau
  by_cases h : c.1 = d.1 + e.1
  · rw [if_pos h, if_pos (h.trans (add_comm _ _)), pair_symm_of_short d e c h]
  · rw [if_neg h, if_neg (fun h' => h (h'.trans (add_comm _ _)))]

theorem trace_transpose_mul_comm (N N' : SpaceW) : trace (Nᵀ * N') = trace (N'ᵀ * N) := by
  rw [← trace_transpose, transpose_mul, transpose_transpose]

theorem trace_transpose_R_mul_comm (c : ShortIdx) (N N' : SpaceW) :
    trace (Nᵀ * Rmat c * N') = trace (N'ᵀ * Rmat c * N) := by
  rw [← trace_transpose, transpose_mul, transpose_mul, transpose_transpose, Rmat_symm,
    Matrix.mul_assoc]

theorem qf_transpose_R_mul_comm (c : ShortIdx) (N N' : SpaceW) :
    qf c (Nᵀ * Rmat c * N') = qf c (N'ᵀ * Rmat c * N) := by
  unfold qf
  rw [dotProduct_mulVec, ← mulVec_transpose, transpose_mul, transpose_mul, transpose_transpose,
    Rmat_symm, Matrix.mul_assoc, dotProduct_comm]

/-- The Griess trilinear form `T u v w = bform (u * v) w`. -/
noncomputable def T : SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] ℚ := gmul.compr₂ bform

theorem T_apply (u v w : SpaceB) : T u v w = bform (gmulFun u v) w := rfl

noncomputable def fAWW (A : Matrix (Fin 24) (Fin 24) ℚ) (N N' : SpaceW) : ℚ :=
  trace A * trace (Nᵀ * N') / 8 + trace (A * (Nᵀ * N'))

noncomputable def gWWX (c : ShortIdx) (N N' : SpaceW) : ℚ :=
  (trace (Nᵀ * Rmat c * N') - qf c (Nᵀ * Rmat c * N') / 4) / 8

noncomputable def Tex (u v w : SpaceB) : ℚ :=
  4 * trace (Am u * Am v * Am w) +
    (8 : ℚ)⁻¹ * ∑ c, xs u c * xs v c * qf c (Am w) +
    (8 : ℚ)⁻¹ * ∑ c, xs v c * xs w c * qf c (Am u) +
    (8 : ℚ)⁻¹ * ∑ c, xs u c * xs w c * qf c (Am v) +
    ∑ c, ∑ d, ∑ e, xs u d * xs v e * xs w c * tau d e c +
    fAWW (Am w) (Nm u) (Nm v) + fAWW (Am u) (Nm v) (Nm w) + fAWW (Am v) (Nm u) (Nm w) +
    ∑ c, xs w c * gWWX c (Nm u) (Nm v) + ∑ c, xs u c * gWWX c (Nm v) (Nm w) +
    ∑ c, xs v c * gWWX c (Nm u) (Nm w)

theorem trace_mul_mul_symm {A B D : Matrix (Fin 24) (Fin 24) ℚ} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (hD : Dᵀ = D) : trace (B * A * D) = trace (A * B * D) := by
  rw [← trace_transpose, transpose_mul, transpose_mul, hA, hB, hD, ← Matrix.mul_assoc,
    ← trace_mul_cycle]

theorem trace_Umat_mul (c : ShortIdx) (M : Matrix (Fin 24) (Fin 24) ℚ) :
    trace (Umat c * M) = qf c M := by
  rw [Umat, vecMulVec_mul, trace_vecMulVec, qf, dotProduct_mulVec, dotProduct_comm]

theorem trace_transpose_mul_mul_symm {A : Matrix (Fin 24) (Fin 24) ℚ} (hA : Aᵀ = A)
    (N N' : SpaceW) : trace (N'ᵀ * N * A) = trace (A * (Nᵀ * N')) := by
  rw [← trace_transpose, transpose_mul, transpose_mul, transpose_transpose, hA]

theorem sum_sum_mul_eq_trace (N N' : SpaceW) : ∑ j, ∑ i, N j i * N' j i = trace (Nᵀ * N') := by
  simp only [trace, diag, mul_apply, transpose_apply]
  exact Finset.sum_comm

theorem fAWW_comm (A : Matrix (Fin 24) (Fin 24) ℚ) (hA : Aᵀ = A) (N N' : SpaceW) :
    fAWW A N N' = fAWW A N' N := by
  unfold fAWW
  rw [trace_transpose_mul_comm N, ← trace_transpose_mul_mul_symm hA N N',
    trace_mul_comm (N'ᵀ * N) A]

theorem gWWX_comm (c : ShortIdx) (N N' : SpaceW) : gWWX c N N' = gWWX c N' N := by
  unfold gWWX
  rw [trace_transpose_R_mul_comm, qf_transpose_R_mul_comm]

theorem trace_gmulA_mul (u v w : SpaceB) :
    trace (gmulA u v * Am w) = 4 * trace (Am u * Am v * Am w) +
      (8 : ℚ)⁻¹ * ∑ c, xs u c * xs v c * qf c (Am w) + fAWW (Am w) (Nm u) (Nm v) := by
  have h1 : trace (Am v * Am u * Am w) = trace (Am u * Am v * Am w) :=
    trace_mul_mul_symm (Am_symm u) (Am_symm v) (Am_symm w)
  have h2 : trace ((Nm v)ᵀ * Nm u * Am w) = trace (Am w * ((Nm u)ᵀ * Nm v)) :=
    trace_transpose_mul_mul_symm (Am_symm w) _ _
  have h3 : trace ((Nm u)ᵀ * Nm v * Am w) = trace (Am w * ((Nm u)ᵀ * Nm v)) := trace_mul_comm _ _
  have h4 : trace ((∑ c, (xs u c * xs v c) • Umat c) * Am w) =
      ∑ c, xs u c * xs v c * qf c (Am w) := by
    rw [Matrix.sum_mul, trace_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.smul_mul, trace_smul, trace_Umat_mul, smul_eq_mul]
  simp only [gmulA, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, trace_add, trace_smul,
    smul_eq_mul, h1, h2, h3, h4, fAWW]
  ring

theorem sum_gmulX_mul (u v w : SpaceB) :
    ∑ c, gmulX u v c * xs w c = (8 : ℚ)⁻¹ * ∑ c, xs v c * xs w c * qf c (Am u) +
      (8 : ℚ)⁻¹ * ∑ c, xs u c * xs w c * qf c (Am v) +
      ∑ c, ∑ d, ∑ e, xs u d * xs v e * xs w c * tau d e c +
      ∑ c, xs w c * gWWX c (Nm u) (Nm v) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h : (∑ d, ∑ e, xs u d * xs v e * tau d e c) * xs w c =
      ∑ d, ∑ e, xs u d * xs v e * xs w c * tau d e c := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [gmulX, add_mul, add_mul, h, gWWX]
  ring

theorem trace_gmulWHalf_mul (u v : SpaceB) (N' : SpaceW) :
    trace ((gmulWHalf u v)ᵀ * N') = trace (Am u) * trace ((Nm v)ᵀ * N') / 8 +
      trace (Am u * ((Nm v)ᵀ * N')) + ∑ c, xs u c * gWWX c (Nm v) N' := by
  have h : ∀ c, trace ((Rmat c * Nm v - (4 : ℚ)⁻¹ • (Rmat c * Nm v * Umat c))ᵀ * N') =
      8 * gWWX c (Nm v) N' := by
    intro c
    rw [transpose_sub, transpose_smul, transpose_mul, transpose_mul, transpose_mul, Rmat_symm,
      Umat_symm, Matrix.sub_mul, Matrix.smul_mul, trace_sub, trace_smul, smul_eq_mul,
      Matrix.mul_assoc, Matrix.mul_assoc, trace_Umat_mul, gWWX, ← Matrix.mul_assoc]
    ring
  rw [gmulWHalf, transpose_add, transpose_add, transpose_smul, transpose_smul, transpose_mul,
    Am_symm, transpose_sum, Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.sum_mul, trace_add, trace_add, trace_smul, trace_smul, trace_sum, smul_eq_mul,
    smul_eq_mul, Matrix.mul_assoc, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [transpose_smul, Matrix.smul_mul, trace_smul, smul_eq_mul, h]
    ring

theorem T_eq_Tex (u v w : SpaceB) : T u v w = Tex u v w := by
  rw [T_apply, bform_apply, sum_sum_mul_eq_trace]
  have hA : ((gmulFun u v).1 : Matrix (Fin 24) (Fin 24) ℚ) = gmulA u v := rfl
  have hX : (gmulFun u v).2.1 = gmulX u v := rfl
  have hW : (gmulFun u v).2.2 = gmulWHalf u v + gmulWHalf v u := rfl
  rw [hA, hX, hW, transpose_add, Matrix.add_mul, trace_add, trace_gmulA_mul, sum_gmulX_mul,
    trace_gmulWHalf_mul, trace_gmulWHalf_mul]
  unfold Tex fAWW
  ring

theorem add_self_coord (x : C × Cocode) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem tau_cycle (d e c : ShortIdx) : tau d e c = tau c d e := by
  unfold tau
  by_cases h : c.1 = d.1 + e.1
  · have h' : e.1 = c.1 + d.1 := by rw [h, add_comm d.1 e.1, add_assoc, add_self_coord, add_zero]
    rw [if_pos h, if_pos h', pair_symm_of_short d e c h, h, Prod.snd_add, pair_add_right,
      pair_eq_zero_of_isShortCoord d.2, zero_add]
  · have h' : ¬ e.1 = c.1 + d.1 := fun h' =>
      h (by rw [h', add_comm c.1 d.1, ← add_assoc, add_self_coord, zero_add])
    rw [if_neg h, if_neg h']

theorem sum3_tau_swap (x y z : SpaceX) :
    ∑ c, ∑ d, ∑ e, y d * x e * z c * tau d e c = ∑ c, ∑ d, ∑ e, x d * y e * z c * tau d e c := by
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
  rw [tau_comm e d c]
  ring

theorem sum3_tau_cycle (x y z : SpaceX) :
    ∑ c, ∑ d, ∑ e, y d * z e * x c * tau d e c = ∑ c, ∑ d, ∑ e, x d * y e * z c * tau d e c := by
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => ?_
  rw [tau_cycle e c d]
  ring

theorem Tex_swap (u v w : SpaceB) : Tex v u w = Tex u v w := by
  have e1 : ∑ c, xs v c * xs u c * qf c (Am w) = ∑ c, xs u c * xs v c * qf c (Am w) :=
    Finset.sum_congr rfl fun c _ => by ring
  have e2 : ∑ c, xs w c * gWWX c (Nm v) (Nm u) = ∑ c, xs w c * gWWX c (Nm u) (Nm v) :=
    Finset.sum_congr rfl fun c _ => by rw [gWWX_comm]
  unfold Tex
  rw [trace_mul_mul_symm (Am_symm u) (Am_symm v) (Am_symm w), e1, e2,
    sum3_tau_swap (xs u) (xs v) (xs w), fAWW_comm (Am w) (Am_symm w) (Nm v)]
  ring

theorem Tex_cycle (u v w : SpaceB) : Tex v w u = Tex u v w := by
  have e1 : ∑ c, xs w c * xs u c * qf c (Am v) = ∑ c, xs u c * xs w c * qf c (Am v) :=
    Finset.sum_congr rfl fun c _ => by ring
  have e2 : ∑ c, xs v c * xs u c * qf c (Am w) = ∑ c, xs u c * xs v c * qf c (Am w) :=
    Finset.sum_congr rfl fun c _ => by ring
  have e3 : ∑ c, xs v c * gWWX c (Nm w) (Nm u) = ∑ c, xs v c * gWWX c (Nm u) (Nm w) :=
    Finset.sum_congr rfl fun c _ => by rw [gWWX_comm]
  have e4 : ∑ c, xs w c * gWWX c (Nm v) (Nm u) = ∑ c, xs w c * gWWX c (Nm u) (Nm v) :=
    Finset.sum_congr rfl fun c _ => by rw [gWWX_comm]
  unfold Tex
  rw [trace_mul_cycle (Am v), e1, e2, e3, e4, sum3_tau_cycle (xs u) (xs v) (xs w),
    fAWW_comm (Am v) (Am_symm v) (Nm w), fAWW_comm (Am w) (Am_symm w) (Nm v)]
  ring

theorem T_swap12 (u v w : SpaceB) : T u v w = T v u w := by
  rw [T_eq_Tex, T_eq_Tex, Tex_swap u v w]

theorem T_cycle (u v w : SpaceB) : T u v w = T v w u := by
  rw [T_eq_Tex, T_eq_Tex, Tex_cycle u v w]

theorem T_swap23 (u v w : SpaceB) : T u v w = T u w v := by
  rw [T_cycle u w v, T_swap12 w v u, ← T_cycle u v w]

theorem fAWW_zero_left (N N' : SpaceW) : fAWW 0 N N' = 0 := by simp [fAWW]

theorem fAWW_zero_mid (A : Matrix (Fin 24) (Fin 24) ℚ) (N' : SpaceW) : fAWW A 0 N' = 0 := by
  simp [fAWW]

theorem fAWW_zero_right (A : Matrix (Fin 24) (Fin 24) ℚ) (N : SpaceW) : fAWW A N 0 = 0 := by
  simp [fAWW]

/-- The source's `qf_zero` (renamed: `VOA.Moonshine.MonsterGriess.qf_zero` exists in
`MoonshineCNGriessTable.lean`). -/
theorem qf_zero_mat (c : ShortIdx) : qf c 0 = 0 := by simp [qf]

theorem gWWX_zero_left (c : ShortIdx) (N' : SpaceW) : gWWX c 0 N' = 0 := by
  simp [gWWX, qf_zero_mat]

theorem gWWX_zero_right (c : ShortIdx) (N : SpaceW) : gWWX c N 0 = 0 := by
  simp [gWWX, qf_zero_mat]

abbrev inA (A : symMat) : SpaceB := (A, 0, 0)

abbrev inX (x : SpaceX) : SpaceB := (0, x, 0)

abbrev inW (N : SpaceW) : SpaceB := (0, 0, N)

@[simp] theorem Am_inA (A : symMat) : Am (inA A) = A := rfl
@[simp] theorem xs_inA (A : symMat) : xs (inA A) = 0 := rfl
@[simp] theorem Nm_inA (A : symMat) : Nm (inA A) = 0 := rfl
@[simp] theorem Am_inX (x : SpaceX) : Am (inX x) = 0 := rfl
@[simp] theorem xs_inX (x : SpaceX) : xs (inX x) = x := rfl
@[simp] theorem Nm_inX (x : SpaceX) : Nm (inX x) = 0 := rfl
@[simp] theorem Am_inW (N : SpaceW) : Am (inW N) = 0 := rfl
@[simp] theorem xs_inW (N : SpaceW) : xs (inW N) = 0 := rfl
@[simp] theorem Nm_inW (N : SpaceW) : Nm (inW N) = N := rfl

theorem T_AAA (A A' A'' : symMat) :
    T (inA A) (inA A') (inA A'') = 4 * trace ((A : Matrix (Fin 24) (Fin 24) ℚ) *
      (A' : Matrix (Fin 24) (Fin 24) ℚ) * (A'' : Matrix (Fin 24) (Fin 24) ℚ)) := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_right]

theorem T_XXA (x x' : SpaceX) (A : symMat) :
    T (inX x) (inX x') (inA A) = (8 : ℚ)⁻¹ * ∑ c, x c * x' c * qf c A := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_right, qf_zero_mat, gWWX_zero_left]

theorem T_XXX (x x' x'' : SpaceX) :
    T (inX x) (inX x') (inX x'') = ∑ c, ∑ d, ∑ e, x d * x' e * x'' c * tau d e c := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_left, qf_zero_mat, gWWX_zero_left]

theorem T_WWA (N N' : SpaceW) (A : symMat) : T (inW N) (inW N') (inA A) = fAWW A N N' := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_right, qf_zero_mat]

theorem T_WWX (N N' : SpaceW) (x : SpaceX) :
    T (inW N) (inW N') (inX x) = ∑ c, x c * gWWX c N N' := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_left, qf_zero_mat, gWWX_zero_right]

theorem T_AAX (A A' : symMat) (x : SpaceX) : T (inA A) (inA A') (inX x) = 0 := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_right, gWWX_zero_left]

theorem T_AAW (A A' : symMat) (N : SpaceW) : T (inA A) (inA A') (inW N) = 0 := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_mid, gWWX_zero_left]

theorem T_AXW (A : symMat) (x : SpaceX) (N : SpaceW) : T (inA A) (inX x) (inW N) = 0 := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_mid, fAWW_zero_right, qf_zero_mat, gWWX_zero_left]

theorem T_XXW (x x' : SpaceX) (N : SpaceW) : T (inX x) (inX x') (inW N) = 0 := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_mid, qf_zero_mat, gWWX_zero_left]

theorem T_WWW (N N' N'' : SpaceW) : T (inW N) (inW N') (inW N'') = 0 := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_left, qf_zero_mat]

/-! ### From `CFSG/Monster/Griess/TrilinearData.lean` -/

theorem coordOf_mul (r s : Q) : coordOf (r * s) = coordOf r + coordOf s := by
  simp only [coordOf, map_mul, SpinCoord.mul_a, SpinCoord.mul_δ, Prod.mk_add_mk]

theorem centralCoord_mul (r s : Q) :
    centralCoord (r * s) = centralCoord r + centralCoord s + pair (coordOf s).1 (coordOf r).2 := by
  simp only [centralCoord, coordOf, map_mul, SpinCoord.mul_s]

theorem mem_zpowers_zQ_iff (g : Q) : g ∈ zpowers zQ ↔ coordOf g = 0 := by
  rw [← center_Q, ← ker_projQ, MonoidHom.mem_ker]
  show Multiplicative.ofAdd (coordOf g) = 1 ↔ _
  exact ofAdd_eq_one

theorem eq_zQ_pow_iff (g : Q) (e : ZMod 2) : g = zQ ^ e.val ↔ coordOf g = 0 ∧ centralCoord g = e := by
  constructor
  · intro h
    have h' : spinEquiv.symm g = ⟨e, 0, 0⟩ :=
      (congrArg spinEquiv.symm (h.trans (zQ_pow_val e))).trans (spinEquiv.symm_apply_apply _)
    exact ⟨Prod.ext (congrArg SpinCoord.a h') (congrArg SpinCoord.δ h'), congrArg SpinCoord.s h'⟩
  · rintro ⟨h1, h2⟩
    have h' : spinEquiv.symm g = ⟨e, 0, 0⟩ :=
      SpinCoord.ext h2 (congrArg Prod.fst h1) (congrArg Prod.snd h1)
    exact (spinEquiv.apply_symm_apply g).symm.trans
      ((congrArg spinEquiv h').trans (zQ_pow_val e).symm)

theorem exists_eq_zQ_pow {g : Q} (h : g ∈ zpowers zQ) : ∃ e : ZMod 2, g = zQ ^ e.val :=
  ⟨centralCoord g, (eq_zQ_pow_iff g _).2 ⟨(mem_zpowers_zQ_iff g).1 h, rfl⟩⟩

theorem eq_of_add_eq_zero' {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {x y : M}
    (h : x + y = 0) : y = x := by
  have hx : x + x = 0 := by
    rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  calc y = (x + x) + y := by rw [hx, zero_add]
    _ = x + (x + y) := add_assoc _ _ _
    _ = x := by rw [h, add_zero]

theorem add_eq_zero_iff' {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {x y : M} :
    x + y = 0 ↔ y = x := by
  refine ⟨eq_of_add_eq_zero', fun h => ?_⟩
  rw [h, ← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem coe_Q_eq (r : Q) :
    ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      qmatR ℚ (centralCoord r) (coordOf r).1 (coordOf r).2 :=
  congrArg (fun g : Q => ((g : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ))
    (spinEquiv.apply_symm_apply r).symm

theorem qmatR_eq_sgn_smul (s : ZMod 2) (a : C) (δ : Cocode) :
    qmatR ℚ s a δ = sgn s • qmatR ℚ 0 a δ := by
  have h := sgnR_smul_qmatR (R := ℚ) s 0 a δ
  rw [add_zero] at h
  exact h.symm

theorem coe_Q_eq_sgn_smul_Rmat {r : Q} (hr : IsShortCoord (coordOf r)) :
    ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      sgn (centralCoord r) • Rmat ⟨coordOf r, hr⟩ := by
  rw [coe_Q_eq, qmatR_eq_sgn_smul]
  rfl

theorem sum_single_mul_single (cr cs : ShortIdx) (a b : ℚ) (f : ShortIdx → ℚ) :
    ∑ c, (a • (Pi.single cr 1 : SpaceX)) c * (b • (Pi.single cs 1 : SpaceX)) c * f c =
      if cs = cr then a * b * f cr else 0 := by
  rw [Finset.sum_eq_single cr]
  · by_cases h : cs = cr
    · subst h
      simp
    · simp [h, Ne.symm h]
  · intro c _ hc
    simp [hc]
  · simp

theorem sum_single_mul (cr : ShortIdx) (a : ℚ) (f : ShortIdx → ℚ) :
    ∑ c, (a • (Pi.single cr 1 : SpaceX)) c * f c = a * f cr := by
  rw [Finset.sum_eq_single cr]
  · simp
  · intro c _ hc
    simp [hc]
  · simp

theorem sum3_single (cr cs ct : ShortIdx) (a b e : ℚ) :
    ∑ c, ∑ d, ∑ f, (a • (Pi.single cr 1 : SpaceX)) d * (b • (Pi.single cs 1 : SpaceX)) f *
      (e • (Pi.single ct 1 : SpaceX)) c * tau d f c = a * b * e * tau cr cs ct := by
  rw [Finset.sum_eq_single ct]
  · rw [Finset.sum_eq_single cr]
    · rw [Finset.sum_eq_single cs]
      · simp
      · intro f _ hf
        simp [hf]
      · simp
    · intro d _ hd
      simp [hd]
    · simp
  · intro c _ hc
    simp [hc]
  · simp

theorem T_Xlift_Xlift_A {r s : Q} (hr : IsShortCoord (coordOf r)) (hs : IsShortCoord (coordOf s))
    (A : symMat) :
    (∀ e : ZMod 2, r * s = zQ ^ e.val →
      T (inX (Xlift r)) (inX (Xlift s)) (inA A) = sgn e * qf ⟨coordOf r, hr⟩ A / 8) ∧
    (r * s ∉ zpowers zQ → T (inX (Xlift r)) (inX (Xlift s)) (inA A) = 0) := by
  simp only [T_XXA, Xlift_eq hr, Xlift_eq hs, sum_single_mul_single]
  constructor
  · intro e he
    obtain ⟨h1, h2⟩ := (eq_zQ_pow_iff _ e).1 he
    have hcs : coordOf s = coordOf r := eq_of_add_eq_zero' ((coordOf_mul r s).symm.trans h1)
    have hcs' : (⟨coordOf s, hs⟩ : ShortIdx) = ⟨coordOf r, hr⟩ := Subtype.ext hcs
    have he' : e = centralCoord r + centralCoord s := by
      have h3 := (centralCoord_mul r s).symm.trans h2
      simp only [hcs, pair_eq_zero_of_isShortCoord hr, add_zero] at h3
      exact h3.symm
    simp only [if_pos hcs', he', sgn_add]
    ring
  · intro hn
    have hne : (⟨coordOf s, hs⟩ : ShortIdx) ≠ ⟨coordOf r, hr⟩ := fun h => hn
      ((mem_zpowers_zQ_iff _).2 ((coordOf_mul r s).trans
        (add_eq_zero_iff'.2 (congrArg Subtype.val h))))
    simp only [if_neg hne, mul_zero]

theorem T_Xlift3 {r s t : Q} (hr : IsShortCoord (coordOf r)) (hs : IsShortCoord (coordOf s))
    (ht : IsShortCoord (coordOf t)) :
    (∀ e : ZMod 2, r * s * t = zQ ^ e.val →
      T (inX (Xlift r)) (inX (Xlift s)) (inX (Xlift t)) = sgn e) ∧
    (r * s * t ∉ zpowers zQ → T (inX (Xlift r)) (inX (Xlift s)) (inX (Xlift t)) = 0) := by
  simp only [T_XXX, Xlift_eq hr, Xlift_eq hs, Xlift_eq ht, sum3_single]
  constructor
  · intro e he
    obtain ⟨h1, h2⟩ := (eq_zQ_pow_iff _ e).1 he
    have h1' : coordOf r + coordOf s + coordOf t = 0 := by
      have := h1
      simp only [coordOf_mul] at this
      exact this
    have hct : coordOf t = coordOf r + coordOf s := eq_of_add_eq_zero' h1'
    have he' : e = centralCoord r + centralCoord s + centralCoord t +
        pair (coordOf s).1 (coordOf r).2 := by
      have h3 := h2
      simp only [centralCoord_mul, coordOf_mul] at h3
      rw [← hct, pair_eq_zero_of_isShortCoord ht, add_zero] at h3
      rw [← h3]
      ring
    have htau : tau ⟨coordOf r, hr⟩ ⟨coordOf s, hs⟩ ⟨coordOf t, ht⟩ =
        sgn (pair (coordOf s).1 (coordOf r).2) := by
      unfold tau
      exact if_pos hct
    rw [htau, he', sgn_add, sgn_add, sgn_add]
  · intro hn
    have hne : ¬ coordOf t = coordOf r + coordOf s := fun h => hn
      ((mem_zpowers_zQ_iff _).2 (((coordOf_mul _ _).trans
        (congrArg (· + coordOf t) (coordOf_mul r s))).trans (add_eq_zero_iff'.2 h)))
    have htau : tau ⟨coordOf r, hr⟩ ⟨coordOf s, hs⟩ ⟨coordOf t, ht⟩ = 0 := by
      unfold tau
      exact if_neg hne
    rw [htau, mul_zero]

theorem transpose_tensor (q : SpinIdx → ℚ) (v : Fin 24 → ℚ) :
    (tensor q v)ᵀ = vecMulVec v q := transpose_vecMulVec q v

theorem tensor_transpose_mul_tensor (q q' : SpinIdx → ℚ) (v w : Fin 24 → ℚ) :
    (tensor q v)ᵀ * tensor q' w = (q ⬝ᵥ q') • vecMulVec v w := by
  rw [transpose_tensor, tensor, vecMulVec_mul_vecMulVec, vecMulVec_smul]

theorem tensor_transpose_mul_R_mul_tensor (c : ShortIdx) (q q' : SpinIdx → ℚ) (v w : Fin 24 → ℚ) :
    (tensor q v)ᵀ * Rmat c * tensor q' w = ((q ᵥ* Rmat c) ⬝ᵥ q') • vecMulVec v w := by
  rw [transpose_tensor, vecMulVec_mul, tensor, vecMulVec_mul_vecMulVec, vecMulVec_smul]

theorem qf_vecMulVec (c : ShortIdx) (v w : Fin 24 → ℚ) :
    qf c (vecMulVec v w) = (v ⬝ᵥ uQ c) * (w ⬝ᵥ uQ c) := by
  rw [qf, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul,
    dotProduct_comm (uQ c) v]
  ring

theorem qf_smul (c : ShortIdx) (k : ℚ) (M : Matrix (Fin 24) (Fin 24) ℚ) :
    qf c (k • M) = k * qf c M := by
  simp only [qf, smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem mulVec_dotProduct_symm {A : Matrix (Fin 24) (Fin 24) ℚ} (hA : Aᵀ = A) (v w : Fin 24 → ℚ) :
    (A *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (A *ᵥ w) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hA]

theorem T_tensor_tensor_A (q q' : SpinIdx → ℚ) (v w : Fin 24 → ℚ) (A : symMat) :
    T (inW (tensor q v)) (inW (tensor q' w)) (inA A) =
      (q ⬝ᵥ q') * ((v ⬝ᵥ w) * trace (A : Matrix (Fin 24) (Fin 24) ℚ) / 8 +
        v ⬝ᵥ ((A : Matrix (Fin 24) (Fin 24) ℚ) *ᵥ w)) := by
  have hA : (A : Matrix (Fin 24) (Fin 24) ℚ)ᵀ = A := A.2
  rw [T_WWA, fAWW, tensor_transpose_mul_tensor, trace_smul, trace_vecMulVec, Matrix.mul_smul,
    trace_smul, mul_vecMulVec, trace_vecMulVec, smul_eq_mul, smul_eq_mul,
    mulVec_dotProduct_symm hA]
  ring

theorem gWWX_tensor (c : ShortIdx) (q q' : SpinIdx → ℚ) (v w : Fin 24 → ℚ) :
    gWWX c (tensor q v) (tensor q' w) =
      ((q ᵥ* Rmat c) ⬝ᵥ q') * ((v ⬝ᵥ w) - (v ⬝ᵥ uQ c) * (w ⬝ᵥ uQ c) / 4) / 8 := by
  rw [gWWX, tensor_transpose_mul_R_mul_tensor, trace_smul, trace_vecMulVec, qf_smul, qf_vecMulVec,
    smul_eq_mul]
  ring

theorem T_tensor_tensor_Xlift (q q' : SpinIdx → ℚ) (v w : Fin 24 → ℚ) {r : Q}
    (hr : IsShortCoord (coordOf r)) :
    T (inW (tensor q v)) (inW (tensor q' w)) (inX (Xlift r)) =
      ((q ᵥ* ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)) ⬝ᵥ q') *
        ((v ⬝ᵥ w) - (v ⬝ᵥ uQ ⟨coordOf r, hr⟩) * (w ⬝ᵥ uQ ⟨coordOf r, hr⟩) / 4) / 8 := by
  rw [T_WWX, Xlift_eq hr, sum_single_mul, gWWX_tensor, coe_Q_eq_sgn_smul_Rmat hr, vecMul_smul,
    smul_dotProduct, smul_eq_mul]
  ring

theorem isShortCoord_rep (c : ShortIdx) : IsShortCoord (coordOf (rep c.1)) :=
  (coordOf_rep c.1).symm ▸ c.2

theorem Xlift_rep_eq (c : ShortIdx) : Xlift (rep c.1) = Pi.single c 1 := by
  rw [Xlift_eq (isShortCoord_rep c), centralCoord_rep, sgn_zero, one_smul]
  congr 1
  exact Subtype.ext (coordOf_rep c.1)

/-- The block values that characterise the Griess trilinear form. -/
def IsGriessForm (T' : SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] ℚ) : Prop :=
  (∀ A A' A'' : symMat, T' (inA A) (inA A') (inA A'') =
    4 * trace ((A : Matrix (Fin 24) (Fin 24) ℚ) * (A' : Matrix (Fin 24) (Fin 24) ℚ) *
      (A'' : Matrix (Fin 24) (Fin 24) ℚ))) ∧
  (∀ (r s : Q) (hr : IsShortCoord (coordOf r)) (_ : IsShortCoord (coordOf s)) (A : symMat),
    (∀ e : ZMod 2, r * s = zQ ^ e.val →
      T' (inX (Xlift r)) (inX (Xlift s)) (inA A) = sgn e * qf ⟨coordOf r, hr⟩ A / 8) ∧
    (r * s ∉ zpowers zQ → T' (inX (Xlift r)) (inX (Xlift s)) (inA A) = 0)) ∧
  (∀ r s t : Q, IsShortCoord (coordOf r) → IsShortCoord (coordOf s) →
    IsShortCoord (coordOf t) →
    (∀ e : ZMod 2, r * s * t = zQ ^ e.val →
      T' (inX (Xlift r)) (inX (Xlift s)) (inX (Xlift t)) = sgn e) ∧
    (r * s * t ∉ zpowers zQ → T' (inX (Xlift r)) (inX (Xlift s)) (inX (Xlift t)) = 0)) ∧
  (∀ (q q' : SpinIdx → ℚ) (v w : Fin 24 → ℚ) (A : symMat),
    T' (inW (tensor q v)) (inW (tensor q' w)) (inA A) =
      (q ⬝ᵥ q') * ((v ⬝ᵥ w) * trace (A : Matrix (Fin 24) (Fin 24) ℚ) / 8 +
        v ⬝ᵥ ((A : Matrix (Fin 24) (Fin 24) ℚ) *ᵥ w))) ∧
  (∀ (q q' : SpinIdx → ℚ) (v w : Fin 24 → ℚ) (r : Q) (hr : IsShortCoord (coordOf r)),
    T' (inW (tensor q v)) (inW (tensor q' w)) (inX (Xlift r)) =
      ((q ᵥ* ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)) ⬝ᵥ q') *
        ((v ⬝ᵥ w) - (v ⬝ᵥ uQ ⟨coordOf r, hr⟩) * (w ⬝ᵥ uQ ⟨coordOf r, hr⟩) / 4) / 8) ∧
  (∀ (A A' : symMat) (x : SpaceX), T' (inA A) (inA A') (inX x) = 0) ∧
  (∀ (A A' : symMat) (N : SpaceW), T' (inA A) (inA A') (inW N) = 0) ∧
  (∀ (A : symMat) (x : SpaceX) (N : SpaceW), T' (inA A) (inX x) (inW N) = 0) ∧
  (∀ (x x' : SpaceX) (N : SpaceW), T' (inX x) (inX x') (inW N) = 0) ∧
  (∀ N N' N'' : SpaceW, T' (inW N) (inW N') (inW N'') = 0)

theorem isGriessForm_T : IsGriessForm T :=
  ⟨T_AAA, fun _ _ hr hs A => T_Xlift_Xlift_A hr hs A, fun _ _ _ hr hs ht => T_Xlift3 hr hs ht,
    T_tensor_tensor_A, fun q q' v w _ hr => T_tensor_tensor_Xlift q q' v w hr, T_AAX, T_AAW,
    T_AXW, T_XXW, T_WWW⟩

def IsKA (u : SpaceB) : Prop := ∃ A, u = inA A

def IsKX (u : SpaceB) : Prop := ∃ r : Q, IsShortCoord (coordOf r) ∧ u = inX (Xlift r)

def IsKW (u : SpaceB) : Prop := ∃ q v, u = inW (tensor q v)

theorem eq_zero_of_kinds (D : SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] ℚ)
    (h12 : ∀ u v w, D u v w = D v u w) (h23 : ∀ u v w, D u v w = D u w v)
    (hAAA : ∀ u v w, IsKA u → IsKA v → IsKA w → D u v w = 0)
    (hXXA : ∀ u v w, IsKX u → IsKX v → IsKA w → D u v w = 0)
    (hXXX : ∀ u v w, IsKX u → IsKX v → IsKX w → D u v w = 0)
    (hWWA : ∀ u v w, IsKW u → IsKW v → IsKA w → D u v w = 0)
    (hWWX : ∀ u v w, IsKW u → IsKW v → IsKX w → D u v w = 0)
    (hAAX : ∀ u v w, IsKA u → IsKA v → IsKX w → D u v w = 0)
    (hAAW : ∀ u v w, IsKA u → IsKA v → IsKW w → D u v w = 0)
    (hAXW : ∀ u v w, IsKA u → IsKX v → IsKW w → D u v w = 0)
    (hXXW : ∀ u v w, IsKX u → IsKX v → IsKW w → D u v w = 0)
    (hWWW : ∀ u v w, IsKW u → IsKW v → IsKW w → D u v w = 0)
    (u v w : SpaceB) (hu : IsKA u ∨ IsKX u ∨ IsKW u) (hv : IsKA v ∨ IsKX v ∨ IsKW v)
    (hw : IsKA w ∨ IsKX w ∨ IsKW w) : D u v w = 0 := by
  rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> rcases hw with hw | hw | hw
  · exact hAAA u v w hu hv hw
  · exact hAAX u v w hu hv hw
  · exact hAAW u v w hu hv hw
  · rw [h23]; exact hAAX u w v hu hw hv
  · rw [h12, h23]; exact hXXA v w u hv hw hu
  · exact hAXW u v w hu hv hw
  · rw [h23]; exact hAAW u w v hu hw hv
  · rw [h23]; exact hAXW u w v hu hw hv
  · rw [h12, h23]; exact hWWA v w u hv hw hu
  · rw [h12, h23]; exact hAAX v w u hv hw hu
  · rw [h23]; exact hXXA u w v hu hw hv
  · rw [h12]; exact hAXW v u w hv hu hw
  · exact hXXA u v w hu hv hw
  · exact hXXX u v w hu hv hw
  · exact hXXW u v w hu hv hw
  · rw [h23, h12]; exact hAXW w u v hw hu hv
  · rw [h23]; exact hXXW u w v hu hw hv
  · rw [h12, h23]; exact hWWX v w u hv hw hu
  · rw [h12, h23]; exact hAAW v w u hv hw hu
  · rw [h12, h23]; exact hAXW v w u hv hw hu
  · rw [h23]; exact hWWA u w v hu hw hv
  · rw [h23, h12, h23]; exact hAXW w v u hw hv hu
  · rw [h12, h23]; exact hXXW v w u hv hw hu
  · rw [h23]; exact hWWX u w v hu hw hv
  · exact hWWA u v w hu hv hw
  · exact hWWX u v w hu hv hw
  · exact hWWW u v w hu hv hw

theorem kind_basisB (k : BIdx) : IsKA (basisB k) ∨ IsKX (basisB k) ∨ IsKW (basisB k) := by
  rcases k with z | c | k
  · exact Or.inl ⟨basisA z, basisB_inl z⟩
  · refine Or.inr (Or.inl ⟨rep c.1, isShortCoord_rep c, ?_⟩)
    rw [basisB_inr_inl, Xlift_rep_eq]
  · exact Or.inr (Or.inr ⟨Pi.single k.1 1, Pi.single k.2 1, basisB_inr_inr k⟩)

/-- ⭐ **Uniqueness of the Griess trilinear form**: a fully symmetric trilinear form with the
block values `IsGriessForm` is `T`. -/
theorem T_unique (T' : SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] ℚ)
    (h12 : ∀ u v w, T' u v w = T' v u w) (h23 : ∀ u v w, T' u v w = T' u w v)
    (hT' : IsGriessForm T') : T' = T := by
  have hDapp : ∀ u v w, (T' - T) u v w = T' u v w - T u v w := fun _ _ _ => rfl
  obtain ⟨tA, tXXA, tXXX, tWWA, tWWX, tAAX, tAAW, tAXW, tXXW, tWWW⟩ := hT'
  obtain ⟨sA, sXXA, sXXX, sWWA, sWWX, sAAX, sAAW, sAXW, sXXW, sWWW⟩ := isGriessForm_T
  have key := eq_zero_of_kinds (T' - T)
    (fun u v w => by rw [hDapp, hDapp, h12, T_swap12])
    (fun u v w => by rw [hDapp, hDapp, h23, T_swap23])
    (by
      rintro _ _ _ ⟨A, rfl⟩ ⟨A', rfl⟩ ⟨A'', rfl⟩
      rw [hDapp, tA, sA, sub_self])
    (by
      rintro _ _ _ ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩ ⟨A, rfl⟩
      rw [hDapp]
      by_cases h : r * s ∈ zpowers zQ
      · obtain ⟨e, he⟩ := exists_eq_zQ_pow h
        rw [(tXXA r s hr hs A).1 e he, (sXXA r s hr hs A).1 e he, sub_self]
      · rw [(tXXA r s hr hs A).2 h, (sXXA r s hr hs A).2 h, sub_self])
    (by
      rintro _ _ _ ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
      rw [hDapp]
      by_cases h : r * s * t ∈ zpowers zQ
      · obtain ⟨e, he⟩ := exists_eq_zQ_pow h
        rw [(tXXX r s t hr hs ht).1 e he, (sXXX r s t hr hs ht).1 e he, sub_self]
      · rw [(tXXX r s t hr hs ht).2 h, (sXXX r s t hr hs ht).2 h, sub_self])
    (by
      rintro _ _ _ ⟨q, v, rfl⟩ ⟨q', w, rfl⟩ ⟨A, rfl⟩
      rw [hDapp, tWWA, sWWA, sub_self])
    (by
      rintro _ _ _ ⟨q, v, rfl⟩ ⟨q', w, rfl⟩ ⟨r, hr, rfl⟩
      rw [hDapp, tWWX q q' v w r hr, sWWX q q' v w r hr, sub_self])
    (by
      rintro _ _ _ ⟨A, rfl⟩ ⟨A', rfl⟩ ⟨r, hr, rfl⟩
      rw [hDapp, tAAX, sAAX, sub_self])
    (by
      rintro _ _ _ ⟨A, rfl⟩ ⟨A', rfl⟩ ⟨q, v, rfl⟩
      rw [hDapp, tAAW, sAAW, sub_self])
    (by
      rintro _ _ _ ⟨A, rfl⟩ ⟨r, hr, rfl⟩ ⟨q, v, rfl⟩
      rw [hDapp, tAXW, sAXW, sub_self])
    (by
      rintro _ _ _ ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩ ⟨q, v, rfl⟩
      rw [hDapp, tXXW, sXXW, sub_self])
    (by
      rintro _ _ _ ⟨q, v, rfl⟩ ⟨q', w, rfl⟩ ⟨q'', w', rfl⟩
      rw [hDapp, tWWW, sWWW, sub_self])
  have hD : T' - T = 0 := basisB.ext fun i => basisB.ext fun j => basisB.ext fun k => by
    simp only [LinearMap.zero_apply]
    exact key _ _ _ (kind_basisB i) (kind_basisB j) (kind_basisB k)
  exact sub_eq_zero.1 hD

/-! ### From `CFSG/Monster/Griess/Parity.lean` -/

noncomputable def parityMap : SpaceB →ₗ[ℚ] SpaceB :=
  LinearMap.prodMap LinearMap.id (LinearMap.prodMap LinearMap.id (-LinearMap.id))

theorem parityMap_apply (u : SpaceB) : parityMap u = (u.1, u.2.1, -u.2.2) := rfl

/-- ⭐ **The parity involution** `xB (A, x, N) = (A, x, -N)` of the rational Griess algebra. -/
noncomputable def xB : SpaceB ≃ₗ[ℚ] SpaceB :=
  LinearEquiv.ofInvolutive parityMap fun u => by simp [parityMap_apply]

theorem xB_apply (u : SpaceB) : xB u = (u.1, u.2.1, -u.2.2) := rfl

theorem mem_eigenspace_xB_one {u : SpaceB} :
    u ∈ End.eigenspace (xB : End ℚ SpaceB) 1 ↔ u.2.2 = 0 := by
  rw [End.mem_eigenspace_iff, one_smul]
  change xB u = u ↔ _
  rw [xB_apply]
  constructor
  · intro h
    have h' := congrArg (fun v : SpaceB => v.2.2) h
    simp only at h'
    have : (2 : ℚ) • u.2.2 = 0 := by rw [two_smul]; nth_rw 1 [← h']; exact neg_add_cancel _
    exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  · intro h
    ext <;> simp [h]

theorem mem_eigenspace_xB_neg_one {u : SpaceB} :
    u ∈ End.eigenspace (xB : End ℚ SpaceB) (-1) ↔ u.1 = 0 ∧ u.2.1 = 0 := by
  rw [End.mem_eigenspace_iff, neg_one_smul]
  change xB u = -u ↔ _
  rw [xB_apply]
  constructor
  · intro h
    have h1 := congrArg (fun v : SpaceB => v.1) h
    have h2 := congrArg (fun v : SpaceB => v.2.1) h
    simp only [Prod.fst_neg, Prod.snd_neg] at h1 h2
    refine ⟨?_, ?_⟩
    · have : (2 : ℚ) • u.1 = 0 := by rw [two_smul]; nth_rw 1 [h1]; exact neg_add_cancel _
      exact (smul_eq_zero.1 this).resolve_left two_ne_zero
    · have : (2 : ℚ) • u.2.1 = 0 := by rw [two_smul]; nth_rw 1 [h2]; exact neg_add_cancel _
      exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  · rintro ⟨h1, h2⟩
    ext <;> simp [h1, h2]

noncomputable def projW : SpaceB →ₗ[ℚ] SpaceW :=
  LinearMap.snd ℚ SpaceX SpaceW ∘ₗ LinearMap.snd ℚ symMat (SpaceX × SpaceW)

/-! ### From `CFSG/Monster/Griess/Product.lean` -/

theorem eq_of_bform_eq {x y : SpaceB} (h : ∀ w, bform x w = bform y w) : x = y := by
  by_contra hne
  have hz : x - y ≠ 0 := sub_ne_zero.2 hne
  have h0 : bform (x - y) (x - y) = 0 := by
    rw [map_sub bform x y, LinearMap.sub_apply, h, sub_self]
  exact lt_irrefl _ (h0 ▸ bform_self_pos hz)

theorem bform_gmul (u v w : SpaceB) : bform (gmul u v) w = T u v w := rfl

theorem uQ_dotProduct_self (c : ShortIdx) : uQ c ⬝ᵥ uQ c = 32 := by
  have h : normSq (uvec c) = 32 := (mem_minVecs_iff.1 (uvec_mem c)).2
  unfold uQ dotProduct
  have h' : ((∑ i, uvec c i * uvec c i : ℤ) : ℚ) = 32 := by
    rw [show (∑ i, uvec c i * uvec c i) = normSq (uvec c) from rfl, h]
    norm_num
  push_cast at h'
  exact h'

end VOA.Moonshine.MonsterGriess
