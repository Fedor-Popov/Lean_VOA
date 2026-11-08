/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean
v4.35.0-rc3 with the module system), files:
  CFSG/Monster/Code/F4.lean
  CFSG/Monster/Code/Defs.lean
  CFSG/Monster/Code/Bits.lean
  CFSG/Monster/Code/Basis.lean
  CFSG/Monster/Code/Weights.lean
  CFSG/Monster/Code/Loop.lean
  CFSG/Monster/Code/Cocycle.lean
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
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic.Ring.RingNF

/-!
# Axiom's Monster port, part 1: the hexacode Golay code `C` and its theta cocycle

Definitional closure (Aut(V♮) campaign, step 4; `Notes/MONSTER_AUT_PLAN.md`) of Axiom Math's
`CFSG.Monster.Griess.AutO`, the first layer: the binary Golay code
`C : Submodule (ZMod 2) (Fin 24 → ZMod 2)` in its MOG/hexacode description, the basis `B`,
the coordinate map `ψ`, the basis `basisC`, the doubly-even property `four_dvd_wt` (a
`decide +kernel` evaluation over the 4096 codewords, `badCount_eq`), self-orthogonality
`dotProduct_eq_zero`,
and the Parker-loop cocycle `θ` with its linearity in the second argument.

Only what the later definitions need is ported: lemma bodies are verbatim, declarations that
no definition in the closure uses are omitted.

## Port notes
* Namespace `CFSG.Monster.Code` ↦ `VOA.Moonshine.MonsterGriess.Code`.
* Module-system syntax (`module`, `public import`, `@[expose]`, `public section`) dropped.
* Omitted (not needed to state `AutO`): the `F4` identities `α_sq … mem_cases`, the
  `CharP F4 2` instance, `algebraMap_apply`, `smul_def`, `eq_re_add_im`; `G`, `H`, `γ`, `wtCount`
  and the weight enumerators, `Umask`/`dotB` (self-duality), `Parker`, and all cocycle identities
  except `θ_add_right`/`θ_smul_right` (with `θc_eq`, `θc_add_right`, `θc_smul_right`).
-/

namespace VOA.Moonshine.MonsterGriess.Code

open scoped Finset

/-! ### From `CFSG/Monster/Code/F4.lean` -/
structure F4 where
  re : ZMod 2
  im : ZMod 2

namespace F4

@[ext] theorem ext' {x y : F4} (h₁ : x.re = y.re) (h₂ : x.im = y.im) : x = y := by
  cases x; cases y; simp_all

theorem ext_iff' {x y : F4} : x = y ↔ x.re = y.re ∧ x.im = y.im :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => ext' h.1 h.2⟩

instance : DecidableEq F4 := fun _ _ => decidable_of_iff _ ext_iff'.symm

private theorem ZMod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

instance : Fintype F4 where
  elems := ⟨↑[(⟨0, 0⟩ : F4), ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], by decide⟩
  complete := by
    rintro ⟨a, b⟩
    rcases ZMod2_cases a with rfl | rfl <;> rcases ZMod2_cases b with rfl | rfl <;> decide

instance : Zero F4 := ⟨⟨0, 0⟩⟩

instance : One F4 := ⟨⟨1, 0⟩⟩

instance : Add F4 := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩

instance : Neg F4 := ⟨id⟩

instance : Sub F4 := ⟨fun x y => x + y⟩

instance : Mul F4 :=
  ⟨fun x y => ⟨x.re * y.re + x.im * y.im, x.re * y.im + x.im * y.re + x.im * y.im⟩⟩

instance : Inv F4 := ⟨fun x => x * x⟩

instance : Div F4 := ⟨fun x y => x * (y * y)⟩

theorem zero_def : (0 : F4) = ⟨0, 0⟩ := rfl

theorem one_def : (1 : F4) = ⟨1, 0⟩ := rfl

theorem add_def (x y : F4) : x + y = ⟨x.re + y.re, x.im + y.im⟩ := rfl

theorem mul_def (x y : F4) :
    x * y = ⟨x.re * y.re + x.im * y.im, x.re * y.im + x.im * y.re + x.im * y.im⟩ := rfl

instance : CommRing F4 where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  left_distrib := by decide
  right_distrib := by decide
  neg_add_cancel := by decide
  mul_comm := by decide
  sub_eq_add_neg := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := npowRec

instance : Field F4 where
  mul_inv_cancel := by decide
  inv_zero := by decide
  exists_pair_ne := ⟨0, 1, by decide⟩
  div_eq_mul_inv := by decide
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

def α : F4 := ⟨0, 1⟩

def ᾱ : F4 := ⟨1, 1⟩

def ofF2 : ZMod 2 →+* F4 where
  toFun a := ⟨a, 0⟩
  map_one' := rfl
  map_mul' := by decide
  map_zero' := rfl
  map_add' := by decide

instance : Algebra (ZMod 2) F4 := ofF2.toAlgebra

end F4

open F4

/-! ### From `CFSG/Monster/Code/Defs.lean` -/
def coord (r : Fin 4) (j : Fin 6) : Fin 24 := ⟨r + 4 * j, by omega⟩

def row (i : Fin 24) : Fin 4 := ⟨i % 4, by omega⟩

def col (i : Fin 24) : Fin 6 := ⟨i / 4, by omega⟩

@[simp] theorem coord_row_col (i : Fin 24) : coord (row i) (col i) = i := by
  ext; simp only [row, col, coord]; omega

def v₁ : Fin 6 → F4 := ![1, 0, 0, 1, ᾱ, α]

def v₂ : Fin 6 → F4 := ![0, 1, 0, 1, α, ᾱ]

def v₃ : Fin 6 → F4 := ![0, 0, 1, 1, 1, 1]

def H₆ : Submodule F4 (Fin 6 → F4) := Submodule.span F4 {v₁, v₂, v₃}

private theorem systematic : ∀ a b c : F4,
    a • v₁ + b • v₂ + c • v₃ = (a • v₁ + b • v₂ + c • v₃) 0 • v₁ +
      (a • v₁ + b • v₂ + c • v₃) 1 • v₂ + (a • v₁ + b • v₂ + c • v₃) 2 • v₃ := by
  decide

theorem mem_H₆_iff (y : Fin 6 → F4) : y ∈ H₆ ↔ y = y 0 • v₁ + y 1 • v₂ + y 2 • v₃ := by
  constructor
  · intro hy
    obtain ⟨a, z, hz, rfl⟩ := Submodule.mem_span_insert.1 hy
    obtain ⟨b, c, rfl⟩ := Submodule.mem_span_pair.1 hz
    simpa only [add_assoc] using systematic a b c
  · intro hy
    rw [hy, H₆]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_) <;> simp

instance : DecidablePred (· ∈ H₆) := fun y => decidable_of_iff _ (mem_H₆_iff y).symm

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

def hexProj (x : Fin 24 → ZMod 2) : Fin 6 → F4 := fun j =>
  algebraMap (ZMod 2) F4 (x (coord 1 j)) + α * algebraMap (ZMod 2) F4 (x (coord 2 j)) +
    ᾱ * algebraMap (ZMod 2) F4 (x (coord 3 j))

def topParity (x : Fin 24 → ZMod 2) : ZMod 2 := ∑ j, x (coord 0 j)

theorem hexProj_add (x y : Fin 24 → ZMod 2) : hexProj (x + y) = hexProj x + hexProj y := by
  funext j; simp only [hexProj, Pi.add_apply, map_add]; ring

theorem hexProj_zero : hexProj 0 = 0 := by
  funext j; simp [hexProj]

theorem topParity_add (x y : Fin 24 → ZMod 2) :
    topParity (x + y) = topParity x + topParity y := by
  simp [topParity, Finset.sum_add_distrib]

def C : Submodule (ZMod 2) (Fin 24 → ZMod 2) where
  carrier := {x | hexProj x ∈ H₆ ∧ ∀ j, ∑ r, x (coord r j) = topParity x}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by rw [hexProj_add]; exact H₆.add_mem hx hy, fun j => ?_⟩
    simp only [Pi.add_apply, Finset.sum_add_distrib, topParity_add, hx' j, hy' j]
  zero_mem' := ⟨by rw [hexProj_zero]; exact H₆.zero_mem, fun j => by simp [topParity]⟩
  smul_mem' := by
    intro c x hx
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul]
      exact ⟨by rw [hexProj_zero]; exact H₆.zero_mem, fun j => by simp [topParity]⟩
    · rwa [one_smul]

theorem mem_C_iff (x : Fin 24 → ZMod 2) :
    x ∈ C ↔ hexProj x ∈ H₆ ∧ ∀ j, ∑ r, x (coord r j) = topParity x := Iff.rfl

instance : DecidablePred (· ∈ C) := fun x => decidable_of_iff _ (mem_C_iff x).symm

def Ω : Fin 24 → ZMod 2 := fun _ => 1

def ωInf : Fin 24 → ZMod 2 := fun i => if row i = 0 then 1 else 0

def ω (j : Fin 6) : Fin 24 → ZMod 2 := fun i => if col i = j then 1 else 0

def g (j : Fin 6) : Fin 24 → ZMod 2 := ω j + ωInf

def lCol (z : F4) : Fin 4 → ZMod 2 :=
  if z = 0 then ![0, 0, 0, 0] else if z = 1 then ![0, 0, 1, 1]
  else if z = α then ![0, 1, 0, 1] else ![0, 1, 1, 0]

theorem lCol_add : ∀ z w : F4, lCol (z + w) = lCol z + lCol w := by decide

theorem lCol_zero : lCol 0 = 0 := by decide

def l : (Fin 6 → F4) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun y i := lCol (y (col i)) (row i)
  map_add' y y' := by funext i; simp [lCol_add]
  map_smul' c y := by
    rcases zmod2_cases c with rfl | rfl
    · funext i; simp [lCol_zero]
    · simp

def B : Fin 12 → Fin 24 → ZMod 2 :=
  ![g 0, g 1, g 2, g 3, g 4, g 5, l v₁, l (α • v₁), l v₂, l (α • v₂), l v₃, l (α • v₃)]

/-! ### From `CFSG/Monster/Code/Bits.lean` -/
def bvec (n a : ℕ) : Fin n → ZMod 2 := fun i => if a.testBit i then 1 else 0

def popc : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, a => a % 2 + popc k (a / 2)

def treeSumN {M : Type*} [Add M] (F : ℕ → M) (m : ℕ → ℕ) : ℕ → ℕ → M
  | 0, a => F a
  | k + 1, a => treeSumN F m k a + treeSumN F m k (a ^^^ m k)

theorem bvec_zero (n : ℕ) : bvec n 0 = 0 := by
  funext i; simp [bvec]

theorem bvec_xor (n a b : ℕ) : bvec n (a ^^^ b) = bvec n a + bvec n b := by
  funext i
  simp only [bvec, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem bvec_and (n a b : ℕ) : bvec n (a &&& b) = bvec n a * bvec n b := by
  funext i
  simp only [bvec, Nat.testBit_and, Pi.mul_apply]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem bvec_ne_zero_iff (n a : ℕ) (i : Fin n) : bvec n a i ≠ 0 ↔ a.testBit i = true := by
  simp only [bvec]; cases a.testBit i <;> decide

theorem hammingNorm_bvec : ∀ (n a : ℕ), hammingNorm (bvec n a) = popc n a
  | 0, a => by simp [hammingNorm, popc]
  | n + 1, a => by
    have ih := hammingNorm_bvec n (a / 2)
    simp only [hammingNorm, Finset.card_filter, bvec_ne_zero_iff] at ih ⊢
    rw [Fin.sum_univ_succ, popc, ← ih]
    congr 1
    · simp only [Fin.val_zero, Nat.testBit_zero, decide_eq_true_eq]
      split_ifs with h <;> omega
    · simp only [Fin.val_succ, Nat.testBit_succ]

private theorem val_eq_ite : ∀ a : ZMod 2, a.val = if a ≠ 0 then 1 else 0 := by decide

theorem hammingNorm_eq_sum_val {ι : Type*} [Fintype ι] (v : ι → ZMod 2) :
    hammingNorm v = ∑ i, (v i).val := by
  rw [hammingNorm, Finset.card_filter]
  exact Finset.sum_congr rfl fun i _ => (val_eq_ite _).symm

theorem sum_eq_hammingNorm {ι : Type*} [Fintype ι] (v : ι → ZMod 2) :
    ∑ i, v i = (hammingNorm v : ZMod 2) := by
  have h : ∀ x : ZMod 2, x = if x ≠ 0 then 1 else 0 := by decide
  rw [hammingNorm, Finset.natCast_card_filter]
  exact Finset.sum_congr rfl fun i _ => h (v i)

theorem dotProduct_eq_hammingNorm {ι : Type*} [Fintype ι] (v w : ι → ZMod 2) :
    v ⬝ᵥ w = (hammingNorm (v * w) : ZMod 2) := by
  rw [dotProduct, ← sum_eq_hammingNorm]; rfl

theorem bvec_dotProduct (n a b : ℕ) : bvec n a ⬝ᵥ bvec n b = (popc n (a &&& b) : ZMod 2) := by
  rw [dotProduct_eq_hammingNorm, ← bvec_and, hammingNorm_bvec]

private theorem sum_zmod2 {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ c, f c = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide, Finset.sum_pair (by decide)]

theorem sum_comb_bvec {M : Type*} [AddCommMonoid M] (n : ℕ) (F : (Fin n → ZMod 2) → M)
    (m : ℕ → ℕ) : ∀ k a : ℕ,
    ∑ μ : Fin k → ZMod 2, F (bvec n a + ∑ i, μ i • bvec n (m i)) =
      treeSumN (fun a => F (bvec n a)) m k a
  | 0, a => by simp [treeSumN]
  | k + 1, a => by
    rw [treeSumN, ← sum_comb_bvec n F m k a, ← sum_comb_bvec n F m k (a ^^^ m k),
      ← (Fin.snocEquiv fun _ => ZMod 2).sum_comp, Fintype.sum_prod_type, sum_zmod2]
    congr 1 <;> refine Finset.sum_congr rfl fun μ _ => ?_ <;>
      simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_last, Fin.val_castSucc, Fin.val_last, zero_smul, add_zero, one_smul, bvec_xor]
    congr 1
    abel

/-! ### From `CFSG/Monster/Code/Basis.lean` -/
def Bmask (i : ℕ) : ℕ :=
  [0x11111e, 0x1111e1, 0x111e11, 0x11e111, 0x1e1111, 0xe11111, 0xa6c00c, 0x6ca00a, 0x6ac0c0,
    0xc6a0a0, 0xcccc00, 0xaaaa00].getD i 0

theorem B_eq_bvec : ∀ i : Fin 12, B i = bvec 24 (Bmask i) := by decide

theorem B_mem_C : ∀ i, B i ∈ C := by decide

theorem Ω_mem_C : Ω ∈ C := by decide

def ev (r : Fin 4) (j : Fin 6) : (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.proj (coord r j)

def ψ : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 12 → ZMod 2) :=
  LinearMap.pi ![ev 1 0 + ev 2 0 + ev 3 0, ev 1 1 + ev 2 1 + ev 3 1, ev 1 2 + ev 2 2 + ev 3 2,
    ev 1 3 + ev 2 3 + ev 3 3, ev 1 4 + ev 2 4 + ev 3 4, ev 1 5 + ev 2 5 + ev 3 5,
    ev 1 0 + ev 3 0, ev 2 0 + ev 3 0, ev 1 1 + ev 3 1, ev 2 1 + ev 3 1, ev 1 2 + ev 3 2,
    ev 2 2 + ev 3 2]

theorem ψ_B : ∀ i, ψ (B i) = Pi.single i 1 := by decide

theorem ψ_grey (x : Fin 24 → ZMod 2) (j : Fin 6) :
    ψ x (Fin.castAdd 6 j) = x (coord 1 j) + x (coord 2 j) + x (coord 3 j) := by
  fin_cases j <;> rfl

theorem ψ_six (x : Fin 24 → ZMod 2) : ψ x 6 = x (coord 1 0) + x (coord 3 0) := rfl

theorem ψ_seven (x : Fin 24 → ZMod 2) : ψ x 7 = x (coord 2 0) + x (coord 3 0) := rfl

theorem ψ_eight (x : Fin 24 → ZMod 2) : ψ x 8 = x (coord 1 1) + x (coord 3 1) := rfl

theorem ψ_nine (x : Fin 24 → ZMod 2) : ψ x 9 = x (coord 2 1) + x (coord 3 1) := rfl

theorem ψ_ten (x : Fin 24 → ZMod 2) : ψ x 10 = x (coord 1 2) + x (coord 3 2) := rfl

theorem ψ_eleven (x : Fin 24 → ZMod 2) : ψ x 11 = x (coord 2 2) + x (coord 3 2) := rfl

private theorem hex_formula : ∀ a b c : ZMod 2,
    algebraMap (ZMod 2) F4 a + α * algebraMap (ZMod 2) F4 b + ᾱ * algebraMap (ZMod 2) F4 c =
      ⟨a + c, b + c⟩ := by
  decide

theorem hexProj_apply (x : Fin 24 → ZMod 2) (j : Fin 6) :
    hexProj x j = ⟨x (coord 1 j) + x (coord 3 j), x (coord 2 j) + x (coord 3 j)⟩ :=
  hex_formula _ _ _

private theorem col_zero : ∀ a b c : ZMod 2,
    a + c = 0 → b + c = 0 → a + b + c = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  decide

private theorem six_smul (t : ZMod 2) : (6 : ℕ) • t = 0 := by
  rw [nsmul_eq_mul]; revert t; decide

theorem eq_zero_of_mem_C_of_ψ_eq_zero {x : Fin 24 → ZMod 2} (hx : x ∈ C) (hψ : ψ x = 0) :
    x = 0 := by
  obtain ⟨hH, hcol⟩ := hx
  have e : ∀ k, ψ x k = 0 := fun k => congrFun hψ k
  have h0 : hexProj x 0 = 0 := by
    rw [hexProj_apply, ← ψ_six, ← ψ_seven, e, e]; rfl
  have h1 : hexProj x 1 = 0 := by
    rw [hexProj_apply, ← ψ_eight, ← ψ_nine, e, e]; rfl
  have h2 : hexProj x 2 = 0 := by
    rw [hexProj_apply, ← ψ_ten, ← ψ_eleven, e, e]; rfl
  have hz : hexProj x = 0 := by
    rw [mem_H₆_iff, h0, h1, h2] at hH
    simpa using hH
  have hlow : ∀ j, x (coord 1 j) = 0 ∧ x (coord 2 j) = 0 ∧ x (coord 3 j) = 0 := by
    intro j
    have h := congrFun hz j
    rw [hexProj_apply] at h
    exact col_zero _ _ _ (congrArg F4.re h) (congrArg F4.im h) (by rw [← ψ_grey]; exact e _)
  have htop : ∀ j, x (coord 0 j) = topParity x := by
    intro j
    have := hcol j
    rwa [Fin.sum_univ_four, (hlow j).1, (hlow j).2.1, (hlow j).2.2, add_zero, add_zero,
      add_zero] at this
  have ht : topParity x = 0 := by
    have : topParity x = ∑ _j : Fin 6, topParity x :=
      Finset.sum_congr rfl fun j _ => htop j
    rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, six_smul]
  have hall : ∀ r j, x (coord r j) = 0 := by
    intro r j
    fin_cases r
    · exact (htop j).trans ht
    · exact (hlow j).1
    · exact (hlow j).2.1
    · exact (hlow j).2.2
  funext i
  rw [← coord_row_col i]
  exact hall _ _

theorem ψ_comb (μ : Fin 12 → ZMod 2) : ψ (∑ i, μ i • B i) = μ := by
  simp only [map_sum, map_smul, ψ_B]
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem comb_injective : Function.Injective fun μ : Fin 12 → ZMod 2 => ∑ i, μ i • B i :=
  Function.LeftInverse.injective ψ_comb

theorem linearIndependent_B : LinearIndependent (ZMod 2) B := by
  refine LinearIndependent.of_comp ψ ?_
  have : ψ ∘ B = ⇑(Pi.basisFun (ZMod 2) (Fin 12)) := by
    funext i; simp [ψ_B, Pi.basisFun_apply]
  rw [this]
  exact (Pi.basisFun (ZMod 2) (Fin 12)).linearIndependent

theorem eq_comb_of_mem_C {x : Fin 24 → ZMod 2} (hx : x ∈ C) : x = ∑ i, ψ x i • B i := by
  have hy : x - ∑ i, ψ x i • B i ∈ C :=
    C.sub_mem hx (C.sum_mem fun i _ => C.smul_mem _ (B_mem_C i))
  have hψ : ψ (x - ∑ i, ψ x i • B i) = 0 := by rw [map_sub, ψ_comb, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_mem_C_of_ψ_eq_zero hy hψ)

theorem span_B : Submodule.span (ZMod 2) (Set.range B) = C := by
  refine le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 B_mem_C)) fun x hx => ?_
  rw [eq_comb_of_mem_C hx]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_C_iff_exists_comb (x : Fin 24 → ZMod 2) :
    x ∈ C ↔ ∃ μ : Fin 12 → ZMod 2, ∑ i, μ i • B i = x := by
  rw [← span_B, Submodule.mem_span_range_iff_exists_fun]

noncomputable def basisC : Module.Basis (Fin 12) (ZMod 2) C :=
  (Module.Basis.span linearIndependent_B).map (LinearEquiv.ofEq _ _ span_B)

@[simp] theorem basisC_apply (i : Fin 12) : (basisC i : Fin 24 → ZMod 2) = B i := by
  simp [basisC, Module.Basis.span_apply]

/-! ### From `CFSG/Monster/Code/Weights.lean` -/
theorem filter_C : Finset.univ.filter (· ∈ C) =
    Finset.univ.image fun μ : Fin 12 → ZMod 2 => ∑ i, μ i • B i := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    mem_C_iff_exists_comb]

theorem sum_C {M : Type*} [AddCommMonoid M] (F : (Fin 24 → ZMod 2) → M) :
    ∑ x ∈ Finset.univ.filter (· ∈ C), F x = ∑ μ : Fin 12 → ZMod 2, F (∑ i, μ i • B i) := by
  rw [filter_C, Finset.sum_image fun μ _ ν _ h => comb_injective h]

theorem sum_C_eq_treeSumN {M : Type*} [AddCommMonoid M] (F : (Fin 24 → ZMod 2) → M) :
    ∑ x ∈ Finset.univ.filter (· ∈ C), F x = treeSumN (fun a => F (bvec 24 a)) Bmask 12 0 := by
  rw [sum_C, ← sum_comb_bvec 24 F Bmask 12 0, bvec_zero]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [zero_add, B_eq_bvec]

def goodWt (w : ℕ) : Bool := w == 0 || w == 8 || w == 12 || w == 16 || w == 24

def badCount : ℕ := treeSumN (fun a => if goodWt (popc 24 a) then 0 else 1) Bmask 12 0

theorem badCount_eq : badCount = 0 := by decide +kernel

theorem wt_mem {x : Fin 24 → ZMod 2} (hx : x ∈ C) :
    hammingNorm x ∈ ({0, 8, 12, 16, 24} : Finset ℕ) := by
  have h := badCount_eq
  rw [badCount, ← funext fun a => congrArg (fun w => if goodWt w then 0 else 1)
    (hammingNorm_bvec 24 a), ← sum_C_eq_treeSumN (fun x => if goodWt (hammingNorm x) then 0 else 1),
    Finset.sum_eq_zero_iff] at h
  have := h x (Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩)
  simp only [goodWt, Bool.or_eq_true, beq_iff_eq, ite_eq_left_iff, one_ne_zero, imp_false,
    not_not] at this
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem four_dvd_wt {x : Fin 24 → ZMod 2} (hx : x ∈ C) : 4 ∣ hammingNorm x := by
  have := wt_mem hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

theorem B_dot_B : ∀ i j, B i ⬝ᵥ B j = 0 := by
  intro i j
  rw [B_eq_bvec, B_eq_bvec, bvec_dotProduct]
  revert i j; decide

theorem dotProduct_eq_zero {x y : Fin 24 → ZMod 2} (hx : x ∈ C) (hy : y ∈ C) : x ⬝ᵥ y = 0 := by
  rw [eq_comb_of_mem_C hx, eq_comb_of_mem_C hy]
  simp [sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, B_dot_B]

/-! ### From `CFSG/Monster/Code/Loop.lean` -/
def supp (d : Fin 24 → ZMod 2) : Finset (Fin 24) := Finset.univ.filter (d · ≠ 0)

def P (d : Fin 24 → ZMod 2) : ZMod 2 := ((hammingNorm d / 4 : ℕ) : ZMod 2)

def K (d e : Fin 24 → ZMod 2) : ZMod 2 := (((supp d ∩ supp e).card / 2 : ℕ) : ZMod 2)

def A (d e f : Fin 24 → ZMod 2) : ZMod 2 := ((supp d ∩ supp e ∩ supp f).card : ZMod 2)

def β (i j : Fin 12) : ZMod 2 :=
  if i < j then 0 else if i = j then P (B i) else K (B i) (B j)

def θc (μ ν : Fin 12 → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, μ i * ν j * β i j +
    ∑ i, ∑ j, ∑ k, if i < j then μ i * μ j * ν k * A (B i) (B j) (B k) else 0

noncomputable def θ (d e : C) : ZMod 2 := θc (basisC.repr d) (basisC.repr e)

/-! ### From `CFSG/Monster/Code/Cocycle.lean` -/
private theorem val_add_add : ∀ a b : ZMod 2, (a + b).val + 2 * (a * b).val = a.val + b.val := by
  decide

theorem hammingNorm_add_add (x y : Fin 24 → ZMod 2) :
    hammingNorm (x + y) + 2 * hammingNorm (x * y) = hammingNorm x + hammingNorm y := by
  simp only [hammingNorm_eq_sum_val, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply,
    Pi.mul_apply, val_add_add]

def lt01 (i j : Fin 12) : ZMod 2 := if i < j then 1 else 0

def Ab (i j k : Fin 12) : ZMod 2 := A (B i) (B j) (B k)

theorem θc_eq (μ ν : Fin 12 → ZMod 2) : θc μ ν =
    ∑ i, ∑ j, μ i * ν j * β i j + ∑ i, ∑ j, ∑ k, lt01 i j * μ i * μ j * ν k * Ab i j k := by
  rw [θc]
  refine congrArg (HAdd.hAdd _) (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_)
  simp only [lt01, Ab]
  split_ifs <;> ring

theorem θc_add_right (μ ν ν' : Fin 12 → ZMod 2) : θc μ (ν + ν') = θc μ ν + θc μ ν' := by
  simp only [θc_eq, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  ring

theorem θc_smul_right (μ ν : Fin 12 → ZMod 2) (c : ZMod 2) : θc μ (c • ν) = c * θc μ ν := by
  simp only [θc_eq, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
  exact congrArg₂ (· + ·)
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring)

theorem θ_add_right (d e f : C) : θ d (e + f) = θ d e + θ d f := by
  rw [θ, θ, θ, map_add, Finsupp.coe_add, θc_add_right]

theorem θ_smul_right (d e : C) (c : ZMod 2) : θ d (c • e) = c * θ d e := by
  rw [θ, θ, map_smul, Finsupp.coe_smul, θc_smul_right]

end VOA.Moonshine.MonsterGriess.Code
