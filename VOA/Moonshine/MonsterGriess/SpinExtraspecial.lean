/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean v4.35.0-rc3 with the
module system), files:
  CFSG/Monster/Spin/SpinCoord.lean
  CFSG/Monster/Spin/Extraspecial.lean
  CFSG/Monster/Spin/OperatorBasis.lean
  CFSG/Monster/Dyadic.lean
  CFSG/Monster/Spin/DyadicNormalizer.lean
  CFSG/Monster/SpinLattice/Isometry.lean
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
import VOA.Moonshine.MonsterGriess.SpinGroupQ
import Mathlib.GroupTheory.Frattini
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Axiom's Monster port (parity-centralizer closure): `Q ≅ 2^{1+24}`, its Frattini subgroup, dyadic normalizers

* `SpinCoord` — the coordinate group `ZMod 2 × C × Cocode` with
  `(s,a,δ)(t,b,ε) = (s + t + ⟨b,δ⟩, a + b, δ + ε)`; `SpinCoord.center_eq`,
  `SpinCoord.frattini_eq` (both `= ⟨z⟩`);
* `toGL : SpinCoord →* GL SpinIdx ℚ`, `x ↦ qmatR ℚ x.s x.a x.δ`, injective, with range `Q`
  (`range_toGL`); ⭐ `spinEquiv : SpinCoord ≃* Q`; `zQ = -1 ∈ Q`; `center_Q`, ⭐ `frattini_Q`
  (`= ⟨zQ⟩`), `natCard_Q = 2^25`; `projQ : Q →* C × Cocode`, `quotCenterEquiv : Q/Z(Q) ≃ C × Cocode`;
* the operator basis `TDbasis` of `Matrix SpinIdx SpinIdx k` (`trace_qmatR`,
  `linearIndependent_TDR`);
* `dyadic` — the ring `ℤ[1/2] ⊂ ℚ`; `dyadic_of_conj_Q` — an orthogonal matrix normalising
  `Q` has dyadic entries;
* `SpinLattice.phi : Q/Z(Q) ≃* Λ/2Λ`, `phi_mk_spinEquiv`, `zQ_pow_val`.

## Port notes
* Namespaces `CFSG.Monster`, `CFSG.Monster.Spin`, `CFSG.Monster.SpinLattice` ↦
  `VOA.Moonshine.MonsterGriess`, `….Spin`, `….SpinLattice`.  Module-system syntax and the source's
  `attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent …` (instances of Axiom's own
  library, absent here) dropped.  The source's `public noncomputable section` becomes
  `noncomputable section`.  Bodies verbatim except as listed.
* **`CFSG.Foundations.Basic` is not imported** (it pulls a Feit–Thompson prelude):
  the statements using `IsExtraspecialPGroup`/`IsElementaryAbelian` (`SpinCoord.isExtraspecialPGroup`,
  `isExtraspecialPGroup_Q`, `isElementaryAbelian_quot`, `TransQ`) are not reached from the target
  and are omitted; `frattini` and `frattini_le_coatom` are Mathlib's.
* Drift: `Set.mem_ofPred_eq` (absent in Mathlib v4.30) ↦ `Set.mem_setOf_eq`;
  `ite_eq_left h`/`ite_eq_right h` ↦ `if_pos h`/`if_neg h` (`trace_transpose_TDR_mul`).
* `phi` is built from our `phi0Equiv` (`LatticeQuadratic.lean`), whose underlying function is
  `phi0`; `phi_mk` remains `rfl`.
* Omitted (not reached): `SpinCoord.sq_eq`, `z_sq`, `orderOf_z`, `commutator_eq`, the
  transversal `TransQ`, `orderOf_zQ`, the commutator subgroup of `Q`, the `rPlus`/`rMinus`
  isometry layer of `SpinLattice/Isometry.lean`.
-/

set_option linter.style.longLine false
set_option linter.style.show false

namespace VOA.Moonshine.MonsterGriess.Spin

open VOA.Moonshine.MonsterGriess.Code Subgroup
open scoped commutatorElement

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

/-! ### From `CFSG/Monster/Spin/SpinCoord.lean` -/

private theorem eq_one_of_ne_zero : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide

private theorem add_self_C'' (a : C) : a + a = 0 := add_self_C a

private theorem add_self_cocode' (δ : Cocode) : δ + δ = 0 := by
  rw [← two_smul (ZMod 2) δ, two_eq_zero', zero_smul]

@[ext] structure SpinCoord where
  s : ZMod 2
  a : C
  δ : Cocode

namespace SpinCoord

instance : Mul SpinCoord := ⟨fun x y => ⟨x.s + y.s + pair y.a x.δ, x.a + y.a, x.δ + y.δ⟩⟩

instance : One SpinCoord := ⟨⟨0, 0, 0⟩⟩

instance : Inv SpinCoord := ⟨fun x => ⟨x.s + pair x.a x.δ, x.a, x.δ⟩⟩

@[simp] theorem mul_s (x y : SpinCoord) : (x * y).s = x.s + y.s + pair y.a x.δ := rfl

@[simp] theorem mul_a (x y : SpinCoord) : (x * y).a = x.a + y.a := rfl

@[simp] theorem mul_δ (x y : SpinCoord) : (x * y).δ = x.δ + y.δ := rfl

@[simp] theorem one_s : (1 : SpinCoord).s = 0 := rfl

@[simp] theorem one_a : (1 : SpinCoord).a = 0 := rfl

@[simp] theorem one_δ : (1 : SpinCoord).δ = 0 := rfl

@[simp] theorem inv_s (x : SpinCoord) : x⁻¹.s = x.s + pair x.a x.δ := rfl

@[simp] theorem inv_a (x : SpinCoord) : x⁻¹.a = x.a := rfl

@[simp] theorem inv_δ (x : SpinCoord) : x⁻¹.δ = x.δ := rfl

instance : Group SpinCoord where
  mul_assoc x y z := by
    ext
    · simp only [mul_s, mul_a, mul_δ, pair_add_left, pair_add_right]
      ring
    · simp only [mul_a, add_assoc]
    · simp only [mul_δ, add_assoc]
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  inv_mul_cancel x := by
    ext
    · simp only [mul_s, inv_s, inv_δ, one_s]
      linear_combination (x.s + pair x.a x.δ) * two_eq_zero'
    · simp only [mul_a, inv_a, one_a, add_self_C'']
    · simp only [mul_δ, inv_δ, one_δ, add_self_cocode']

def equivProd : SpinCoord ≃ ZMod 2 × C × Cocode where
  toFun x := (x.s, x.a, x.δ)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem natCard : Nat.card SpinCoord = 2 ^ 25 := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_prod, Nat.card_zmod, natCard_C,
    natCard_cocode]
  norm_num

def z : SpinCoord := ⟨1, 0, 0⟩

theorem commutatorElement_eq (x y : SpinCoord) :
    ⁅x, y⁆ = ⟨pair x.a y.δ + pair y.a x.δ, 0, 0⟩ := by
  rw [commutatorElement_def]
  ext
  · simp only [mul_s, mul_δ, inv_s, inv_a, inv_δ, pair_add_right]
    linear_combination (x.s + y.s + pair y.a x.δ + pair x.a x.δ + pair y.a y.δ) * two_eq_zero'
  · simp only [mul_a, inv_a]
    rw [show x.a + y.a + x.a + y.a = (x.a + x.a) + (y.a + y.a) by abel, add_self_C'',
      add_self_C'', add_zero]
  · simp only [mul_δ, inv_δ]
    rw [show x.δ + y.δ + x.δ + y.δ = (x.δ + x.δ) + (y.δ + y.δ) by abel, add_self_cocode',
      add_self_cocode', add_zero]

theorem mem_zpowers_z {x : SpinCoord} : x ∈ zpowers z ↔ x.a = 0 ∧ x.δ = 0 := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    let K : Subgroup SpinCoord :=
      { carrier := {x | x.a = 0 ∧ x.δ = 0}
        mul_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq, mul_a, mul_δ] at *
          rw [hx.1, hx.2, hy.1, hy.2, add_zero, add_zero]
          exact ⟨rfl, rfl⟩
        one_mem' := ⟨rfl, rfl⟩
        inv_mem' := fun {x} hx => hx }
    have : z ^ k ∈ K := K.zpow_mem ⟨rfl, rfl⟩ k
    exact this
  · rintro ⟨ha, hδ⟩
    rcases zmod2_cases x.s with h | h
    · have : x = 1 := SpinCoord.ext h ha hδ
      rw [this]
      exact one_mem _
    · have : x = z := SpinCoord.ext h ha hδ
      rw [this]
      exact mem_zpowers z

theorem mem_center_iff' {x : SpinCoord} : x ∈ center SpinCoord ↔ x.a = 0 ∧ x.δ = 0 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    refine ⟨eq_zero_of_forall_pair_left fun ε => ?_, eq_zero_of_forall_pair fun b => ?_⟩
    · have := congrArg SpinCoord.s (h ⟨0, 0, ε⟩)
      simp only [mul_s, pair_zero_left, add_zero, zero_add] at this
      linear_combination this
    · have := congrArg SpinCoord.s (h ⟨0, b, 0⟩)
      simp only [mul_s, pair_zero_right, add_zero, zero_add] at this
      linear_combination -this
  · rintro ⟨ha, hδ⟩ g
    ext
    · simp only [mul_s, ha, hδ, pair_zero_left, pair_zero_right, add_zero]
      exact add_comm _ _
    · simp only [mul_a, ha, add_zero, zero_add]
    · simp only [mul_δ, hδ, add_zero, zero_add]

theorem center_eq : center SpinCoord = zpowers z := by
  ext x
  rw [mem_center_iff', mem_zpowers_z]

def hyp (φ : Module.Dual (ZMod 2) (C × Cocode)) : Subgroup SpinCoord where
  carrier := {x | φ (x.a, x.δ) = 0}
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, mul_a, mul_δ] at *
    rw [← Prod.mk_add_mk, map_add, hx, hy, add_zero]
  one_mem' := by
    show φ (0, 0) = 0
    rw [Prod.mk_zero_zero, map_zero]
  inv_mem' := fun {x} hx => hx

theorem mem_hyp {φ : Module.Dual (ZMod 2) (C × Cocode)} {x : SpinCoord} :
    x ∈ hyp φ ↔ φ (x.a, x.δ) = 0 := Iff.rfl

theorem isCoatom_hyp {φ : Module.Dual (ZMod 2) (C × Cocode)} (hφ : φ ≠ 0) :
    IsCoatom (hyp φ) := by
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra h
    exact hφ (LinearMap.ext fun v => by
      by_contra hv
      exact h ⟨v, hv⟩)
  rw [SetLike.isCoatom_iff]
  refine ⟨fun h => hv ?_, fun H g hle hg hgH => eq_top_iff.2 fun y _ => ?_⟩
  · have : (⟨0, v.1, v.2⟩ : SpinCoord) ∈ hyp φ := h ▸ mem_top _
    exact this
  · by_cases hy : φ (y.a, y.δ) = 0
    · exact hle hy
    · have hg1 : φ (g.a, g.δ) = 1 := eq_one_of_ne_zero _ hg
      have hy1 : φ (y.a, y.δ) = 1 := eq_one_of_ne_zero _ hy
      have hyg : y * g⁻¹ ∈ hyp φ := by
        rw [mem_hyp, mul_a, mul_δ, inv_a, inv_δ, ← Prod.mk_add_mk, map_add, hg1, hy1]
        rfl
      have := H.mul_mem (hle hyg) hgH
      rwa [inv_mul_cancel_right] at this

theorem frattini_eq : frattini SpinCoord = zpowers z := by
  apply le_antisymm
  · intro x hx
    rw [mem_zpowers_z]
    by_contra hne
    have hv : ((x.a, x.δ) : C × Cocode) ≠ 0 := fun h =>
      hne ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (ZMod 2) (C × Cocode), φ (x.a, x.δ) ≠ 0 := by
      by_contra h
      exact hv ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).1 fun φ => by
        by_contra hφ
        exact h ⟨φ, hφ⟩)
    have hφ0 : φ ≠ 0 := fun h => hφ (by rw [h, LinearMap.zero_apply])
    exact hφ (frattini_le_coatom (isCoatom_hyp hφ0) hx)
  · rw [zpowers_le]
    show z ∈ Order.radical (Subgroup SpinCoord)
    rw [Order.radical]
    simp only [Subgroup.mem_iInf, Set.mem_setOf_eq]
    intro M hM
    by_contra hz
    have hsup : M ⊔ zpowers z = ⊤ :=
      hM.2 _ (lt_of_le_of_ne le_sup_left fun h => hz (h ▸ mem_sup_right (mem_zpowers z)))
    have : (zpowers z).Normal := by rw [← center_eq]; infer_instance
    have hrep : ∀ g : SpinCoord, ∃ m ∈ M, m.a = g.a ∧ m.δ = g.δ := by
      intro g
      have hg : g ∈ (↑(M ⊔ zpowers z) : Set SpinCoord) := by
        rw [hsup]
        exact mem_top g
      rw [mul_normal, Set.mem_mul] at hg
      obtain ⟨m, hm, n, hn, rfl⟩ := hg
      rw [SetLike.mem_coe, mem_zpowers_z] at hn
      exact ⟨m, hm, by simp [hn.1], by simp [hn.2]⟩
    obtain ⟨m₁, hm₁, ha₁, hδ₁⟩ := hrep ⟨0, ΩC, 0⟩
    obtain ⟨m₂, hm₂, ha₂, hδ₂⟩ := hrep ⟨0, 0, Submodule.Quotient.mk (Pi.single 0 1)⟩
    have hcomm : ⁅m₁, m₂⁆ = z := by
      rw [commutatorElement_eq]
      ext <;> simp [ha₁, hδ₁, ha₂, hδ₂, pair_ΩC_mk_single, z]
    apply hz
    rw [← hcomm, commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)

end SpinCoord

/-! ### From `CFSG/Monster/Spin/Extraspecial.lean` -/

noncomputable section Extraspecial

open Matrix

section Transport

variable {G H : Type*} [Group G] [Group H] (e : G ≃* H)

theorem mem_zpowers_map_iff {g x : G} : e x ∈ zpowers (e g) ↔ x ∈ zpowers g := by
  simp only [mem_zpowers_iff, ← map_zpow]
  exact exists_congr fun k => e.injective.eq_iff

theorem center_eq_zpowers_of_mulEquiv {g : G} (h : center G = zpowers g) :
    center H = zpowers (e g) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [mem_zpowers_map_iff, ← h, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro hx g'
    apply e.injective
    rw [map_mul, map_mul, hx]
  · intro hx g'
    obtain ⟨g', rfl⟩ := e.surjective g'
    rw [← map_mul, ← map_mul, hx]

theorem frattini_eq_zpowers_of_mulEquiv {g : G} (h : frattini G = zpowers g) :
    frattini H = zpowers (e g) := by
  have h1 : (frattini G).map e.toMonoidHom = frattini H :=
    OrderIso.map_radical (MulEquiv.mapSubgroup e)
  rw [← h1, h, MonoidHom.map_zpowers]
  rfl

end Transport

def zU : GL SpinIdx ℚ := -1

def TU (a : C) : GL SpinIdx ℚ := XU ⟨a, 0⟩ * DU (thetaD a)

@[simp] theorem coe_zU : (zU : Matrix SpinIdx SpinIdx ℚ) = zmat := by
  rw [zU, Units.val_neg, Units.val_one, zmat]

@[simp] theorem coe_TU (a : C) : (TU a : Matrix SpinIdx SpinIdx ℚ) = Tmat a := rfl

def toGL : SpinCoord →* GL SpinIdx ℚ where
  toFun x := ⟨qmatR ℚ x.s x.a x.δ, (qmatR ℚ x.s x.a x.δ)ᵀ, qmatR_mul_transpose_self _ _ _,
    qmatR_transpose_mul_self _ _ _⟩
  map_one' := Units.ext qmatR_zero
  map_mul' _ _ := Units.ext (qmatR_mul _ _ _ _ _ _).symm

theorem coe_toGL (x : SpinCoord) :
    (toGL x : Matrix SpinIdx SpinIdx ℚ) = qmatR ℚ x.s x.a x.δ := rfl

theorem toGL_injective : Function.Injective toGL := fun x y h => by
  obtain ⟨h1, h2, h3⟩ := qmatR_injective (R := ℚ) two_ne_zero (congrArg Units.val h)
  exact SpinCoord.ext h1 h2 h3

theorem XU_eq_toGL (e : Parker) : XU e = toGL ⟨e.sign, e.code, thetaD e.code⟩ :=
  Units.ext (Xmat_eq_qmatR e)

theorem DU_eq_toGL (δ : Cocode) : DU δ = toGL ⟨0, 0, δ⟩ := Units.ext (Dmat_eq_qmatR δ)

theorem TU_eq_toGL (a : C) : TU a = toGL ⟨0, a, 0⟩ := Units.ext (Tmat_eq_qmatR a)

theorem zU_eq_toGL : zU = toGL SpinCoord.z := Units.ext (by rw [coe_zU, coe_toGL]; exact zmat_eq_qmatR)

@[simp] theorem TU_zero : TU 0 = 1 := by
  rw [TU_eq_toGL]
  exact toGL.map_one

@[simp] theorem DU_zero : DU 0 = 1 := by
  rw [DU_eq_toGL]
  exact toGL.map_one

theorem XU_mul_DU (e : Parker) (δ : Cocode) :
    XU e * DU δ = toGL ⟨e.sign, e.code, thetaD e.code + δ⟩ := by
  rw [XU_eq_toGL, DU_eq_toGL, ← map_mul]
  congr 1
  ext <;> simp

theorem toGL_eq_XU_mul_DU (x : SpinCoord) : toGL x = XU ⟨x.a, x.s⟩ * DU (thetaD x.a + x.δ) := by
  rw [XU_mul_DU, ← add_assoc, add_self_cocode, zero_add]

theorem range_toGL : toGL.range = Q := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [toGL_eq_XU_mul_DU]
    exact Q.mul_mem (XU_mem_Q _) (DU_mem_Q _)
  · rw [Q, Subgroup.closure_le]
    rintro _ (⟨e, rfl⟩ | ⟨δ, rfl⟩)
    · exact ⟨_, (XU_eq_toGL e).symm⟩
    · exact ⟨_, (DU_eq_toGL δ).symm⟩

/-- ⭐ **The coordinates of `Q`**: `SpinCoord ≃* Q`, `x ↦ qmatR ℚ x.s x.a x.δ`. -/
def spinEquiv : SpinCoord ≃* Q :=
  (MonoidHom.ofInjective toGL_injective).trans (MulEquiv.subgroupCongr range_toGL)

def zQ : Q := spinEquiv SpinCoord.z

theorem coe_zQ : (zQ : GL SpinIdx ℚ) = zU := zU_eq_toGL.symm

theorem TU_mem_Q (a : C) : TU a ∈ Q := by
  rw [TU_eq_toGL, ← range_toGL]
  exact ⟨_, rfl⟩

theorem natCard_Q : Nat.card Q = 2 ^ 25 := by
  rw [← Nat.card_congr spinEquiv.toEquiv, SpinCoord.natCard]

theorem center_Q : center Q = zpowers zQ :=
  center_eq_zpowers_of_mulEquiv spinEquiv SpinCoord.center_eq

/-- ⭐ **The Frattini subgroup of `Q` is its centre `{±1}`.** -/
theorem frattini_Q : frattini Q = zpowers zQ :=
  frattini_eq_zpowers_of_mulEquiv spinEquiv SpinCoord.frattini_eq

def SpinCoord.proj : SpinCoord →* Multiplicative (C × Cocode) where
  toFun x := Multiplicative.ofAdd (x.a, x.δ)
  map_one' := rfl
  map_mul' _ _ := rfl

def projQ : Q →* Multiplicative (C × Cocode) :=
  SpinCoord.proj.comp spinEquiv.symm.toMonoidHom

theorem projQ_spinEquiv (x : SpinCoord) : projQ (spinEquiv x) = Multiplicative.ofAdd (x.a, x.δ) := by
  simp only [projQ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.symm_apply_apply]
  rfl

theorem ker_projQ : projQ.ker = center Q := by
  ext g
  obtain ⟨x, rfl⟩ := spinEquiv.surjective g
  have hz : zQ = spinEquiv SpinCoord.z := rfl
  rw [MonoidHom.mem_ker, projQ_spinEquiv, center_Q, hz, mem_zpowers_map_iff spinEquiv,
    SpinCoord.mem_zpowers_z, ofAdd_eq_one, Prod.mk_eq_zero]

theorem projQ_surjective : Function.Surjective projQ := fun v =>
  ⟨spinEquiv ⟨0, (Multiplicative.toAdd v).1, (Multiplicative.toAdd v).2⟩, by
    rw [projQ_spinEquiv]
    rfl⟩

def quotCenterEquiv : (Q ⧸ center Q) ≃* Multiplicative (C × Cocode) :=
  (QuotientGroup.quotientMulEquivOfEq ker_projQ.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective projQ projQ_surjective)

/-! ### From `CFSG/Monster/Spin/OperatorBasis.lean` -/

private theorem eq_one_of_ne_zero' : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide

theorem eq_of_add_eq_zero_C {a b : C} (h : a + b = 0) : a = b := by
  calc a = a + (b + b) := by rw [add_self_C', add_zero]
    _ = (a + b) + b := (add_assoc _ _ _).symm
    _ = b := by rw [h, zero_add]

theorem eq_of_add_eq_zero_cocode {δ ε : Cocode} (h : δ + ε = 0) : δ = ε := by
  calc δ = δ + (ε + ε) := by rw [add_self_cocode, add_zero]
    _ = (δ + ε) + ε := (add_assoc _ _ _).symm
    _ = ε := by rw [h, zero_add]

section Field

variable {k : Type*} [Field k]

theorem sum_sgnR_pair_eq_zero (h2 : (2 : k) ≠ 0) {δ : Cocode} {x₀ : C₀}
    (hx₀ : pair x₀ δ ≠ 0) : ∑ x : C₀, sgnR k (pair x δ) = 0 := by
  have h1 : pair x₀ δ = 1 := eq_one_of_ne_zero' _ hx₀
  have hS : ∑ x : C₀, sgnR k (pair x δ) = -∑ x : C₀, sgnR k (pair x δ) := by
    calc ∑ x : C₀, sgnR k (pair x δ)
        = ∑ x : C₀, sgnR k (pair ((x + x₀ : C₀) : C) δ) :=
          (Fintype.sum_equiv (Equiv.addRight x₀) _ (fun y : C₀ => sgnR k (pair y δ))
            (fun _ => rfl)).symm
      _ = ∑ x : C₀, -sgnR k (pair x δ) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Submodule.coe_add, pair_add_left, h1, sgnR_add_one]
      _ = -∑ x : C₀, sgnR k (pair x δ) := Finset.sum_neg_distrib _
  have h2S : (2 : k) * ∑ x : C₀, sgnR k (pair x δ) = 0 := by
    rw [two_mul]
    nth_rewrite 2 [hS]
    exact add_neg_cancel _
  exact (mul_eq_zero.1 h2S).resolve_left h2

theorem sum_sgnR_pair (h2 : (2 : k) ≠ 0) (δ : Cocode) :
    ∑ x : C₀, sgnR k (pair x δ) = if ∀ x : C₀, pair x δ = 0 then 2048 else 0 := by
  split_ifs with h
  · simp only [h, sgnR_zero, Finset.sum_const, Finset.card_univ, card_C₀, nsmul_eq_mul,
      mul_one]
    norm_num
  · obtain ⟨x₀, hx₀⟩ := not_forall.1 h
    exact sum_sgnR_pair_eq_zero h2 hx₀

theorem trace_qmatR (h2 : (2 : k) ≠ 0) (s : ZMod 2) (a : C) (δ : Cocode) :
    trace (qmatR k s a δ) = if a = 0 ∧ δ = 0 then sgnR k s * 4096 else 0 := by
  rw [qmatR, trace_spm]
  by_cases hfix : pair ΩC δ = 0 ∧ π₀ a = 0
  · obtain ⟨hΩ, hπ⟩ := hfix
    have hsh : ∀ x : C₀, shift a x = x := fun x => (shift_eq_self_iff a x).2 hπ
    have hperm : ∀ i, qPerm a δ i = i := fun i => by
      rw [qPerm, hΩ, add_zero, hsh]
    simp only [hperm, ite_true]
    rw [Fintype.sum_prod_type]
    simp only [qSign, hsh]
    rcases zmod2_cases (μ₀ a) with hμ | hμ
    · have ha : a = 0 := eq_of_π₀_μ₀ (by rw [hπ, map_zero]) (by rw [hμ, map_zero])
      simp only [hμ, mul_zero, add_zero, sgnR_add, ← Finset.mul_sum, sum_sgnR_pair h2,
        Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      by_cases hall : ∀ x : C₀, pair x δ = 0
      · have hδ : δ = 0 := eq_zero_of_forall_pair fun u => by
          rw [← π₀_add_μ₀ u, pair_add_left, pair_smul_left, hall, hΩ, mul_zero, add_zero]
        simp only [ite_true, ha, hδ, and_self]
        norm_num
      · have hδ : δ ≠ 0 := fun h => hall fun x => by rw [h, pair_zero_right]
        simp only [hall, ite_false, mul_zero, hδ, and_false]
    · have ha : a ≠ 0 := fun h => by
        rw [h, map_zero] at hμ
        exact zero_ne_one hμ
      rw [Finset.sum_comm]
      have hη : ∀ x : C₀, ∑ η : ZMod 2, sgnR k (s + η * μ₀ a + pair x δ) = 0 := fun x => by
        rw [← sum_sgnR_add (R := k) (s + pair x δ)]
        refine Finset.sum_congr rfl fun η _ => ?_
        rw [hμ, mul_one]
        congr 1
        ring
      simp only [hη, Finset.sum_const_zero, ha, false_and, ite_false]
  · have hperm : ∀ i, ¬qPerm a δ i = i := by
      intro i h
      apply hfix
      have h1 := congrArg Prod.fst h
      have h2' := congrArg Prod.snd h
      simp only [qPerm, add_eq_left] at h1 h2'
      exact ⟨h1, (shift_eq_self_iff a i.2).1 h2'⟩
    have hne : ¬(a = 0 ∧ δ = 0) := fun ⟨ha, hδ⟩ =>
      hfix ⟨by rw [hδ, pair_zero_right], by rw [ha, map_zero]⟩
    simp only [hperm, ite_false, Finset.sum_const_zero, hne]

end Field

def TDR (R : Type*) [CommRing R] (p : C × Cocode) : Matrix SpinIdx SpinIdx R :=
  TmatR R p.1 * DmatR R p.2

theorem TDR_eq_qmatR {R : Type*} [CommRing R] (p : C × Cocode) : TDR R p = qmatR R 0 p.1 p.2 := by
  rw [TDR, TmatR_eq_qmatR, DmatR_eq_qmatR, qmatR_mul, pair_zero_right]
  simp only [add_zero, zero_add]

section Field

variable {k : Type*} [Field k]

theorem trace_transpose_TDR_mul (h2 : (2 : k) ≠ 0) (p q : C × Cocode) :
    trace ((TDR k p)ᵀ * TDR k q) = if p = q then 4096 else 0 := by
  rw [TDR_eq_qmatR, TDR_eq_qmatR, qmatR_transpose, qmatR_mul, trace_qmatR h2]
  by_cases hpq : p = q
  · subst hpq
    rw [add_self_C', add_self_cocode, if_pos ⟨rfl, rfl⟩, if_pos rfl, zero_add,
      add_zero, zmod2_add_self, sgnR_zero, one_mul]
  · have h : ¬(p.1 + q.1 = 0 ∧ p.2 + q.2 = 0) := fun h =>
      hpq (Prod.ext (eq_of_add_eq_zero_C h.1) (eq_of_add_eq_zero_cocode h.2))
    rw [if_neg h, if_neg hpq]

theorem four_thousand_ninety_six_ne_zero (h2 : (2 : k) ≠ 0) : (4096 : k) ≠ 0 := by
  have := pow_ne_zero 12 h2
  norm_num at this
  exact this

theorem linearIndependent_TDR (h2 : (2 : k) ≠ 0) : LinearIndependent k (TDR k) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have h := congrArg (fun M => trace ((TDR k q)ᵀ * M)) hg
  simp only [Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul,
    trace_transpose_TDR_mul h2, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, trace_zero] at h
  exact (mul_eq_zero.1 h).resolve_right (four_thousand_ninety_six_ne_zero h2)

theorem card_eq_finrank_matrix :
    Fintype.card (C × Cocode) = Module.finrank k (Matrix SpinIdx SpinIdx k) := by
  rw [Fintype.card_prod, card_C, card_cocode, Module.finrank_matrix, Module.finrank_self,
    card_spinIdx]

def TDbasis (h2 : (2 : k) ≠ 0) : Module.Basis (C × Cocode) k (Matrix SpinIdx SpinIdx k) :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_TDR h2) card_eq_finrank_matrix

@[simp] theorem coe_TDbasis (h2 : (2 : k) ≠ 0) : ⇑(TDbasis h2) = TDR k :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

end Field

end Extraspecial

end VOA.Moonshine.MonsterGriess.Spin

/-! ### From `CFSG/Monster/Dyadic.lean` -/

namespace VOA.Moonshine.MonsterGriess

open Matrix

/-- The dyadic rationals `ℤ[1/2] ⊂ ℚ`. -/
def dyadic : Subring ℚ where
  carrier := {q | ∃ k : ℕ, q.den ∣ 2 ^ k}
  mul_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨k + l, (Rat.mul_den_dvd a b).trans (pow_add 2 k l ▸ mul_dvd_mul hk hl)⟩
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨k + l, (Rat.add_den_dvd a b).trans (pow_add 2 k l ▸ mul_dvd_mul hk hl)⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro a ⟨k, hk⟩
    exact ⟨k, by rwa [Rat.neg_den]⟩

theorem mem_dyadic {q : ℚ} : q ∈ dyadic ↔ ∃ k : ℕ, q.den ∣ 2 ^ k := Iff.rfl

theorem mem_dyadic_of_sq_mem {q : ℚ} (h : q * q ∈ dyadic) : q ∈ dyadic := by
  obtain ⟨k, hk⟩ := h
  have hden : (q * q).den = q.den * q.den := by rw [← sq, ← sq, Rat.den_pow]
  rw [hden] at hk
  exact ⟨k, (Dvd.intro q.den rfl).trans hk⟩

theorem dyadic_entries_of_conj_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Set (Matrix ι ι ℚ)) (hH : ∀ g ∈ H, ∀ i j, g i j ∈ dyadic)
    (hspan : ∀ M : Matrix ι ι ℚ, (∀ i j, M i j ∈ dyadic) → M ∈ Submodule.span dyadic H)
    (s : Matrix ι ι ℚ) (hs : sᵀ * s = 1) (hconj : ∀ g ∈ H, sᵀ * g * s ∈ H) :
    ∀ i j, s i j ∈ dyadic ∧ s⁻¹ i j ∈ dyadic := by
  rw [Matrix.inv_eq_left_inv hs]
  have hspan_le : ∀ M ∈ Submodule.span dyadic H, ∀ i j, M i j ∈ dyadic := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx => exact hH x hx
    | zero => intro i j; simp
    | add x y _ _ hx hy => intro i j; simpa using dyadic.add_mem (hx i j) (hy i j)
    | smul c x _ hx =>
      intro i j
      have : (c • x) i j = (c : ℚ) * x i j := rfl
      rw [this]
      exact dyadic.mul_mem c.2 (hx i j)
  have hconj_span : ∀ M ∈ Submodule.span dyadic H, sᵀ * M * s ∈ Submodule.span dyadic H := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hconj x hx)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Matrix.mul_add, Matrix.add_mul]
      exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      have : sᵀ * (c • x) * s = c • (sᵀ * x * s) := by
        change sᵀ * ((c : ℚ) • x) * s = (c : ℚ) • (sᵀ * x * s)
        rw [Matrix.mul_smul, Matrix.smul_mul]
      rw [this]
      exact Submodule.smul_mem _ c hx
  have hentry : ∀ i j, s i j ∈ dyadic := by
    intro i j
    let E : Matrix ι ι ℚ := Matrix.single i i 1
    have hE : E ∈ Submodule.span dyadic H := by
      refine hspan E fun a b => ?_
      by_cases hab : a = i ∧ b = i
      · obtain ⟨rfl, rfl⟩ := hab
        simp [E]
      · have : E a b = 0 := by
          simp only [E, Matrix.single_apply]
          split_ifs with h
          · exact absurd ⟨h.1.symm, h.2.symm⟩ hab
          · rfl
        rw [this]
        exact dyadic.zero_mem
    have hd := hspan_le _ (hconj_span E hE) j j
    have hjj : (sᵀ * E * s) j j = s i j * s i j := by
      simp [E, Matrix.mul_apply, Matrix.single_apply, Matrix.transpose_apply, ite_and,
        Finset.sum_ite_eq, ite_mul]
    rw [hjj] at hd
    exact mem_dyadic_of_sq_mem hd
  exact fun i j => ⟨hentry i j, hentry j i⟩

end VOA.Moonshine.MonsterGriess

/-! ### From `CFSG/Monster/Spin/DyadicNormalizer.lean` -/

namespace VOA.Moonshine.MonsterGriess.Spin

open VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess Matrix

noncomputable section DyadicNormalizer

def Qmats : Set (Matrix SpinIdx SpinIdx ℚ) :=
  (fun g : GL SpinIdx ℚ => (g : Matrix SpinIdx SpinIdx ℚ)) '' (Q : Set (GL SpinIdx ℚ))

def dyadicMatrices : Submodule dyadic (Matrix SpinIdx SpinIdx ℚ) where
  carrier := {M | ∀ i j, M i j ∈ dyadic}
  add_mem' := fun hM hN i j => dyadic.add_mem (hM i j) (hN i j)
  zero_mem' := fun _ _ => dyadic.zero_mem
  smul_mem' := fun c _ hM i j => dyadic.mul_mem c.2 (hM i j)

theorem mem_dyadicMatrices {M : Matrix SpinIdx SpinIdx ℚ} :
    M ∈ dyadicMatrices ↔ ∀ i j, M i j ∈ dyadic := Iff.rfl

theorem qmatR_mem_dyadic (s : ZMod 2) (a : C) (δ : Cocode) (i j : SpinIdx) :
    qmatR ℚ s a δ i j ∈ dyadic := by
  rcases qmatR_apply_mem (R := ℚ) s a δ i j with h | h | h <;> rw [h]
  · exact dyadic.zero_mem
  · exact dyadic.one_mem
  · exact dyadic.neg_mem dyadic.one_mem

theorem Qmats_mem_dyadic {g : Matrix SpinIdx SpinIdx ℚ} (hg : g ∈ Qmats) (i j : SpinIdx) :
    g i j ∈ dyadic := by
  obtain ⟨u, hu, rfl⟩ := hg
  rw [← range_toGL] at hu
  obtain ⟨x, rfl⟩ := hu
  show (toGL x : Matrix SpinIdx SpinIdx ℚ) i j ∈ dyadic
  rw [coe_toGL]
  exact qmatR_mem_dyadic _ _ _ i j

theorem TDR_mem_Qmats (p : C × Cocode) : TDR ℚ p ∈ Qmats :=
  ⟨TU p.1 * DU p.2, Q.mul_mem (TU_mem_Q _) (DU_mem_Q _), rfl⟩

private theorem two_ne_zero_rat' : (2 : ℚ) ≠ 0 := two_ne_zero

theorem eq_sum_trace_smul_TDR (M : Matrix SpinIdx SpinIdx ℚ) :
    M = ∑ p : C × Cocode, (trace ((TDR ℚ p)ᵀ * M) / 4096) • TDR ℚ p := by
  have hb := (TDbasis two_ne_zero_rat').sum_repr M
  rw [coe_TDbasis] at hb
  have hc : ∀ q, trace ((TDR ℚ q)ᵀ * M) = (TDbasis two_ne_zero_rat').repr M q * 4096 := by
    intro q
    conv_lhs => rw [← hb]
    simp only [Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul,
      trace_transpose_TDR_mul two_ne_zero_rat', smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  conv_lhs => rw [← hb]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hc q, mul_div_assoc, div_self (four_thousand_ninety_six_ne_zero two_ne_zero_rat'), mul_one]

theorem trace_transpose_mul_mem_dyadic {M N : Matrix SpinIdx SpinIdx ℚ}
    (hM : ∀ i j, M i j ∈ dyadic) (hN : ∀ i j, N i j ∈ dyadic) : trace (Mᵀ * N) ∈ dyadic := by
  rw [trace]
  refine dyadic.sum_mem fun i _ => ?_
  rw [diag_apply, mul_apply]
  exact dyadic.sum_mem fun j _ => dyadic.mul_mem (hM j i) (hN j i)

theorem inv_4096_mem_dyadic : (4096 : ℚ)⁻¹ ∈ dyadic :=
  ⟨12, by norm_num⟩

theorem span_dyadic_Qmats : Submodule.span dyadic Qmats = dyadicMatrices := by
  apply le_antisymm
  · rw [Submodule.span_le]
    exact fun g hg => Qmats_mem_dyadic hg
  · intro M hM
    have hcoef : ∀ p : C × Cocode, trace ((TDR ℚ p)ᵀ * M) / 4096 ∈ dyadic := fun p => by
      rw [div_eq_mul_inv]
      refine dyadic.mul_mem (trace_transpose_mul_mem_dyadic ?_ hM) inv_4096_mem_dyadic
      intro i j
      rw [TDR_eq_qmatR]
      exact qmatR_mem_dyadic _ _ _ i j
    have hM' : M = ∑ p : C × Cocode, (⟨_, hcoef p⟩ : dyadic) • TDR ℚ p :=
      eq_sum_trace_smul_TDR M
    rw [hM']
    exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (TDR_mem_Qmats p))

theorem mem_span_dyadic_Qmats_iff (M : Matrix SpinIdx SpinIdx ℚ) :
    M ∈ Submodule.span dyadic Qmats ↔ ∀ i j, M i j ∈ dyadic := by
  rw [span_dyadic_Qmats, mem_dyadicMatrices]

theorem dyadic_of_conj_Q_subset (s : Matrix SpinIdx SpinIdx ℚ) (hs : sᵀ * s = 1)
    (hconj : ∀ g ∈ Qmats, s⁻¹ * g * s ∈ Qmats) : ∀ i j, s i j ∈ dyadic ∧ s⁻¹ i j ∈ dyadic := by
  have hinv : s⁻¹ = sᵀ := Matrix.inv_eq_left_inv hs
  refine dyadic_entries_of_conj_mem Qmats (fun g hg => Qmats_mem_dyadic hg)
    (fun M hM => (mem_span_dyadic_Qmats_iff M).2 hM) s hs fun g hg => ?_
  rw [← hinv]
  exact hconj g hg

/-- ⭐ **An orthogonal matrix normalising `Q` has dyadic entries.** -/
theorem dyadic_of_conj_Q (s : Matrix SpinIdx SpinIdx ℚ) (hs : sᵀ * s = 1)
    (hconj : (fun g => s⁻¹ * g * s) '' Qmats = Qmats) (i j : SpinIdx) : s i j ∈ dyadic :=
  (dyadic_of_conj_Q_subset s hs (fun _ hg => hconj ▸ Set.mem_image_of_mem _ hg) i j).1

end DyadicNormalizer

end VOA.Moonshine.MonsterGriess.Spin

/-! ### From `CFSG/Monster/SpinLattice/Isometry.lean` -/

namespace VOA.Moonshine.MonsterGriess.SpinLattice

open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin
  Subgroup

/-- `Q / Z(Q) ≃* Λ/2Λ`, through the coordinates `C × Cocode` and `phi0Equiv`. -/
noncomputable def phi : (Q ⧸ center Q) ≃* Multiplicative L2 :=
  quotCenterEquiv.trans (AddEquiv.toMultiplicative phi0Equiv.toAddEquiv)

theorem phi_mk (g : Q) :
    phi (QuotientGroup.mk g) = Multiplicative.ofAdd (phi0 (Multiplicative.toAdd (projQ g))) := rfl

theorem phi_mk_spinEquiv (x : SpinCoord) :
    phi (QuotientGroup.mk (spinEquiv x)) = Multiplicative.ofAdd (phi0 (x.a, x.δ)) := by
  rw [phi_mk, projQ_spinEquiv]
  rfl

theorem z_pow_val (e : ZMod 2) : SpinCoord.z ^ e.val = ⟨e, 0, 0⟩ := by
  have : ∀ e : ZMod 2, e = 0 ∨ e = 1 := by decide
  rcases this e with rfl | rfl
  · rfl
  · rw [ZMod.val_one, pow_one]
    rfl

theorem zQ_pow_val (e : ZMod 2) : zQ ^ e.val = spinEquiv ⟨e, 0, 0⟩ := by
  rw [zQ, ← map_pow, z_pow_val]

end VOA.Moonshine.MonsterGriess.SpinLattice
