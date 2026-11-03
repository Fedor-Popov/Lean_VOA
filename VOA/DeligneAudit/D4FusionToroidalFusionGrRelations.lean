import VOA.DeligneAudit.D4FusionToroidalFusionGrGenerator
import VOA.DeligneAudit.D4FusionToroidalFusionGrPower
import VOA.DeligneAudit.D4FusionToroidalFusionRelations

/-!
# Highest-vector relations in the toroidal fusion associated graded

The one-letter source relations are exact in the graded model. The positive
`t`-Cartan relation uses the scalar site moment, which has lower degree.
-/

namespace VOA.DeligneAudit.Toroidal.FusionGr

open VOA.DeligneAudit.Toroidal VOA.DeligneAudit.D1TensorG
open VOA.DeligneAudit.DeligneSector

noncomputable section

variable (S : DeligneSectorData)
variable (hskew : ∀ a b c, S.f a b c = -S.f b a c)
variable {N : ℕ} (z : Fin N → ℂ)

private def siteAction : ToroidalAction S.f (D1TensorG.Space S.n N) :=
  d1EvalAction S.f S.jacobi hskew z

def highest : Gr (siteAction S hskew z) (D1TensorG.generator S.c₀) :=
  grGenerator (siteAction S hskew z) (D1TensorG.generator S.c₀)

/-- Raising letters of all `u` and `t` degrees kill the graded generator. -/
theorem highest_raising (e : Fin S.n) (he : S.raising e) (i s : ℕ) :
    grOp (siteAction S hskew z) (D1TensorG.generator S.c₀) N e i s
      (highest S hskew z) = 0 :=
  grGenerator_zero_of_raw _ _ N e i s (eval_generator_raising S hskew z e he i s)

/-- Positive `u`-degree Cartan letters kill the graded generator. -/
theorem highest_cartan_u (h : Fin S.n) (hh : S.cartan h) (i s : ℕ)
    (hi : 1 ≤ i) :
    grOp (siteAction S hskew z) (D1TensorG.generator S.c₀) N h i s
      (highest S hskew z) = 0 :=
  grGenerator_zero_of_raw _ _ N h i s
    (eval_generator_cartan_u S hskew z h hh i s hi)

/-- Positive `t`-degree Cartan letters kill the graded generator. -/
theorem highest_cartan_t (h : Fin S.n) (hh : S.cartan h) (s : ℕ)
    (hs : 1 ≤ s) :
    grOp (siteAction S hskew z) (D1TensorG.generator S.c₀) N h 0 s
      (highest S hskew z) = 0 :=
  grGenerator_zero_of_scalar _ _ N h 0 s hs
    ⟨((∑ q : Fin N, z q ^ s) * (S.thetaH h : ℂ)),
      eval_generator_cartan_moment S hskew z h hh s⟩

/-- The zero-mode Cartan eigenvalue is the sum of the site weights. -/
theorem highest_cartan_zero (h : Fin S.n) (hh : S.cartan h) (hm : 0 < N) :
    grOp (siteAction S hskew z) (D1TensorG.generator S.c₀) N h 0 0
      (highest S hskew z) =
        ((N * S.thetaH h : ℕ) : ℂ) • highest S hskew z :=
  grGenerator_eigen _ _ N h _ hm (eval_generator_cartan_zero S hskew z h hh)

theorem highest_cartanN_u (h : Fin S.n) (hh : S.cartanN h) (i s : ℕ)
    (hi : 1 ≤ i) :
    grOp (siteAction S hskew z) (D1TensorG.generator S.c₀) N h i s
      (highest S hskew z) = 0 :=
  grGenerator_zero_of_raw _ _ N h i s
    (eval_generator_cartanN_u S hskew z h hh i s hi)

theorem highest_cartanN_t (h : Fin S.n) (hh : S.cartanN h) (s : ℕ)
    (hs : 1 ≤ s) :
    grOp (siteAction S hskew z) (D1TensorG.generator S.c₀) N h 0 s
      (highest S hskew z) = 0 :=
  grGenerator_zero_of_scalar _ _ N h 0 s hs
    ⟨-((∑ q : Fin N, z q ^ s) * (S.thetaN h : ℂ)),
      eval_generator_cartanN_moment S hskew z h hh s⟩

theorem highest_cartanN_zero (h : Fin S.n) (hh : S.cartanN h) (hm : 0 < N) :
    grOp (siteAction S hskew z) (D1TensorG.generator S.c₀) N h 0 0
      (highest S hskew z) =
        -((N * S.thetaN h : ℕ) : ℂ) • highest S hskew z :=
  grGenerator_eigen _ _ N h _ hm (eval_generator_cartanN_zero S hskew z h hh)

/-- Non-theta fusion letters at `u` degree one vanish. -/
theorem highest_fusion_one (x : Fin S.n) (hx : x ≠ S.c₀) (s : ℕ) :
    grOp (siteAction S hskew z) (D1TensorG.generator S.c₀) N x 1 s
      (highest S hskew z) = 0 :=
  grGenerator_zero_of_raw _ _ N x 1 s (eval_generator_fusion_one S hskew z x hx s)

/-- Every `u`-degree-two letter vanishes, in particular the theta one. -/
theorem highest_u_two (x : Fin S.n) (s : ℕ) :
    grOp (siteAction S hskew z) (D1TensorG.generator S.c₀) N x 2 s
      (highest S hskew z) = 0 := by
  apply grGenerator_zero_of_raw
  change (d1EvalAction S.f S.jacobi hskew z).op x 2 s
    (D1TensorG.generator S.c₀) = 0
  rw [eval_u_two_zero S hskew z x s]
  rfl

/-- The sharp lowering power also kills the graded highest vector. -/
theorem highest_lowering (x : Fin S.n) (hx : S.lowering x) (hm : 0 < N) :
    ((grOp (siteAction S hskew z) (D1TensorG.generator S.c₀) N x 0 0) ^
      (N * S.lowExp x + 1)) (highest S hskew z) = 0 :=
  grZeroMode_pow_zero _ _ N x 0 (N * S.lowExp x + 1) hm
    (eval_generator_lowering S hskew z x hx)

end

end VOA.DeligneAudit.Toroidal.FusionGr

#print axioms VOA.DeligneAudit.Toroidal.FusionGr.highest_raising
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.highest_cartan_t
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.highest_cartan_zero
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.highest_cartanN_zero
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.highest_fusion_one
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.highest_u_two
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.highest_lowering
