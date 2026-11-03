import VOA.DeligneAudit.DeligneSectorData
import VOA.DeligneAudit.A2SectorWeyl
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# An explicit coadjoint-plus-trivial current site

The underlying space is g* plus one trivial line. Mode zero is the coadjoint
action, mode one evaluates a covector on the current basis vector and maps
to the trivial line, and higher modes vanish. Jacobi and skew symmetry prove
all current brackets directly. No invariant form, Demazure realization, total
dimension bound, or fusion identification is assumed.

For the highest-root generator this is the explicit site corresponding to
Ravinder, arXiv:1409.0274, section 3.2 equation (3.5), whose classical module
is the adjoint representation plus a trivial line. The current action and
all subsequent relations here are proved, not imported from that statement.
-/

namespace VOA.DeligneAudit.D1SiteG

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.SectorLoop
open VOA.DeligneAudit.DeligneSector

noncomputable section

abbrev Co (n : ℕ) := Fin n → ℂ
abbrev Space (n : ℕ) := Co n × ℂ

variable {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ)

/-- The actual coadjoint coefficient matrix. -/
def coMatrix (c : Fin n) : Matrix (Fin n) (Fin n) ℂ := fun i j => -f c i j

def coOp (c : Fin n) : Module.End ℂ (Co n) := Matrix.toLin' (coMatrix f c)

theorem coOp_apply (c : Fin n) (v : Co n) : coOp f c v = slotA f c v := by
  funext i
  simp [coOp, coMatrix, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, slotA,
    Finset.sum_neg_distrib]

theorem coMatrix_comm (hJ : JacobiCoord f) (a b : Fin n) :
    coMatrix f a * coMatrix f b - coMatrix f b * coMatrix f a =
      ∑ e, f a b e • coMatrix f e := by
  ext i j
  simpa only [Matrix.sub_apply, Matrix.mul_apply, coMatrix, neg_mul_neg,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_neg, neg_mul,
    Finset.sum_neg_distrib, neg_neg]
    using hJ a b i j

theorem coOp_comm (hJ : JacobiCoord f) (a b : Fin n) :
    coOp f a * coOp f b - coOp f b * coOp f a = ∑ e, f a b e • coOp f e := by
  have h := congrArg Matrix.toLin' (coMatrix_comm f hJ a b)
  simpa only [map_sub, map_sum, map_smul, Matrix.toLin'_mul, Module.End.mul_eq_comp, coOp]
    using h

/-- Mode zero acts on the coadjoint summand and kills the trivial line. -/
def zeroOp (c : Fin n) : Module.End ℂ (Space n) where
  toFun u := (coOp f c u.1, 0)
  map_add' u v := by simp
  map_smul' z u := by simp

/-- Mode one is the canonical evaluation pairing into the trivial line. -/
def oneOp (c : Fin n) : Module.End ℂ (Space n) where
  toFun u := (0, u.1 c)
  map_add' u v := by simp
  map_smul' z u := by simp

@[simp] theorem zeroOp_apply (c : Fin n) (u : Space n) :
    zeroOp f c u = (coOp f c u.1, 0) := rfl

@[simp] theorem oneOp_apply (c : Fin n) (u : Space n) : oneOp c u = (0, u.1 c) := rfl

theorem zero_zero (hJ : JacobiCoord f) (a b : Fin n) :
    zeroOp f a * zeroOp f b - zeroOp f b * zeroOp f a =
      ∑ e, f a b e • zeroOp f e := by
  apply LinearMap.ext
  intro u
  apply Prod.ext
  · have hh := congrArg (fun T : Module.End ℂ (Co n) => T u.1) (coOp_comm f hJ a b)
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, zeroOp_apply, Prod.fst_sub, Prod.fst_sum, Prod.smul_fst] using hh
  · simp [Prod.snd_sum]

theorem zero_one (a b : Fin n) :
    zeroOp f a * oneOp b - oneOp b * zeroOp f a = ∑ e, f a b e • oneOp e := by
  apply LinearMap.ext
  intro u
  apply Prod.ext
  · simp [Prod.fst_sum]
  · simp [coOp_apply, slotA, Prod.snd_sum]

theorem one_zero (hskew : ∀ a b c, f a b c = -f b a c) (a b : Fin n) :
    oneOp a * zeroOp f b - zeroOp f b * oneOp a = ∑ e, f a b e • oneOp e := by
  apply LinearMap.ext
  intro u
  apply Prod.ext
  · simp [Prod.fst_sum]
  · simp [coOp_apply, slotA, hskew b a, Prod.snd_sum]

theorem one_one (a b : Fin n) : oneOp a * oneOp b - oneOp b * oneOp a = 0 := by
  apply LinearMap.ext
  intro u
  simp

def op (c : Fin n) : ℕ → Module.End ℂ (Space n)
  | 0 => zeroOp f c
  | 1 => oneOp c
  | _ + 2 => 0

theorem op_comm (hJ : JacobiCoord f) (hskew : ∀ a b c, f a b c = -f b a c)
    (a b : Fin n) (r s : ℕ) :
    op f a r * op f b s - op f b s * op f a r = ∑ e, f a b e • op f e (r + s) := by
  rcases r with _ | r
  · rcases s with _ | s
    · exact zero_zero f hJ a b
    · rcases s with _ | s
      · exact zero_one f a b
      · simp [op]
  · rcases r with _ | r
    · rcases s with _ | s
      · exact one_zero f hskew a b
      · rcases s with _ | s
        · simpa only [op, smul_zero, Finset.sum_const_zero] using one_one a b
        · simp [op]
    · have he : r + 1 + 1 + s = (r + s) + 2 := by omega
      change (0 : Module.End ℂ (Space n)) * op f b s - op f b s * 0 =
        ∑ e, f a b e • op f e (r + 1 + 1 + s)
      rw [he]
      simp only [op, zero_mul, mul_zero, sub_self, smul_zero, Finset.sum_const_zero]

/-- The explicit current site, with every current bracket proved. -/
def rep (hJ : JacobiCoord f) (hskew : ∀ a b c, f a b c = -f b a c) :
    CurrentModule f (Space n) where
  op := op f
  comm a b r s v := by
    have hh := congrArg (fun T : Module.End ℂ (Space n) => T v) (op_comm f hJ hskew a b r s)
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
      LinearMap.smul_apply] using hh

def w (c₀ : Fin n) : Space n := (Pi.single c₀ 1, 0)
def vac (n : ℕ) : Space n := (0, 1)

theorem oneOp_w (c₀ : Fin n) : oneOp c₀ (w c₀) = vac n := by simp [w, vac]

theorem finrank_space : Module.finrank ℂ (Space n) = n + 1 := by
  simp [Space, Co, Module.finrank_prod, Module.finrank_fintype_fun_eq_card]

end

end VOA.DeligneAudit.D1SiteG

#print axioms VOA.DeligneAudit.D1SiteG.rep
#print axioms VOA.DeligneAudit.D1SiteG.finrank_space
