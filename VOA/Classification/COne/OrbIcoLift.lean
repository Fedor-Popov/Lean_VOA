import VOA.Classification.COne.OrbIcoGroup

/-! # OrbIco: spin lifts of `ico` to binary forms

The `sl₂`-identification `psi : ℂ[x,y,z] → ℂ[s,t]` intertwines the action of `Aut V₂` on
`(V₂)₁ ≅ ℂ³` with a linear substitution of `(s, t)` (the double cover `SL₂ → SO₃`). We only need
this for `ico`: explicit lifts of the generators (`lift_rotC`, `lift_rotR`), closed under products.

`ico_lift`: every `g ∈ ico` has an algebra endomorphism `β` of `ℂ[s,t]` with
`psi (φ_g F) = β (psi F)` for all `F`.
-/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIco
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice MvPolynomial Equiv OrbPrim OrbOcta
  Complex

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

/-- The linear substitution `s ↦ a s + b t`, `t ↦ c s + d t`. -/
def binSub (a b c d : ℂ) : P2 →ₐ[ℂ] P2 :=
  aeval ![MvPolynomial.C a * X 0 + MvPolynomial.C b * X 1,
    MvPolynomial.C c * X 0 + MvPolynomial.C d * X 1]

/-- `g` lifts to binary forms, by a linear substitution. -/
def Lifts (g : Aut V1) : Prop :=
  ∃ a b c d : ℂ, ∀ F : P3, psi (phiE g F) = binSub a b c d (psi F)

theorem binSub_X0 (a b c d : ℂ) :
    binSub a b c d (X 0) = MvPolynomial.C a * X 0 + MvPolynomial.C b * X 1 := by
  simp [binSub]

theorem binSub_X1 (a b c d : ℂ) :
    binSub a b c d (X 1) = MvPolynomial.C c * X 0 + MvPolynomial.C d * X 1 := by
  simp [binSub]

theorem binSub_comp (a b c d a' b' c' d' : ℂ) :
    (binSub a b c d).comp (binSub a' b' c' d') =
      binSub (a' * a + b' * c) (a' * b + b' * d) (c' * a + d' * c) (c' * b + d' * d) := by
  apply MvPolynomial.algHom_ext
  intro k
  fin_cases k <;> simp [binSub] <;> ring

theorem Lifts.mul {g h : Aut V1} (hg : Lifts g) (hh : Lifts h) : Lifts (g * h) := by
  obtain ⟨a, b, c, d, hβ⟩ := hg
  obtain ⟨a', b', c', d', hγ⟩ := hh
  refine ⟨a' * a + b' * c, a' * b + b' * d, c' * a + d' * c, c' * b + d' * d, fun F => ?_⟩
  rw [phiE_mul, hβ, hγ, ← binSub_comp]
  rfl

theorem binSub_id : binSub 1 0 0 1 = AlgHom.id ℂ P2 := by
  apply MvPolynomial.algHom_ext
  intro k
  fin_cases k <;> simp [binSub]

theorem Lifts.one : Lifts 1 := ⟨1, 0, 0, 1, fun F => by
  rw [binSub_id]; change psi (phiHom 1 F) = _; rw [map_one]; rfl⟩

theorem lifts_of_gen {g : Aut V1} (a b c d : ℂ)
    (h : ∀ k : Fin 3, psi (phiE g (X k)) = binSub a b c d (psi (X k))) : Lifts g := by
  refine ⟨a, b, c, d, fun F => ?_⟩
  have : psi.comp (phiE g).toAlgHom = (binSub a b c d).comp psi := by
    apply MvPolynomial.algHom_ext
    intro k
    exact h k
  exact congrArg (fun φ : P3 →ₐ[ℂ] P2 => φ F) this

theorem eval_psi_X (x : Fin 2 → ℂ) (k : Fin 3) :
    eval x (psi (X k)) = ![x 0 ^ 2 - x 1 ^ 2, I * (x 0 ^ 2 + x 1 ^ 2), -2 * eps1 * (x 0 * x 1)] k := by
  fin_cases k <;> simp [psi]

theorem eval_psi_lin (x : Fin 2 → ℂ) (v : Fin 3 → ℂ) :
    eval x (psi (lin v)) = v 0 * (x 0 ^ 2 - x 1 ^ 2) + v 1 * (I * (x 0 ^ 2 + x 1 ^ 2)) +
      v 2 * (-2 * eps1 * (x 0 * x 1)) := by
  rw [lin_apply]
  simp only [map_add, map_mul, eval_C, eval_psi_X]
  simp [psi]

theorem eval_binSub_psi_X (a b c d : ℂ) (x : Fin 2 → ℂ) (k : Fin 3) :
    eval x (binSub a b c d (psi (X k))) =
      ![(a * x 0 + b * x 1) ^ 2 - (c * x 0 + d * x 1) ^ 2,
        I * ((a * x 0 + b * x 1) ^ 2 + (c * x 0 + d * x 1) ^ 2),
        -2 * eps1 * ((a * x 0 + b * x 1) * (c * x 0 + d * x 1))] k := by
  fin_cases k <;> simp [psi, binSub]


theorem lifts_rotC : Lifts rotC := by
  refine lifts_of_gen ((1 - I) / 2) (-eps1 * (1 + I) / 2) (eps1 * (1 - I) / 2) ((1 + I) / 2)
    fun k => ?_
  apply MvPolynomial.funext
  intro x
  rw [phiE_X, eval_psi_lin, eval_binSub_psi_X, autL_rotC]
  rcases eps1_cases with h | h <;> rw [h] <;> fin_cases k <;>
    simp [Pi.single_apply] <;> ring_nf <;> simp only [I_sq, I_pow_three, I_pow_four] <;> ring_nf

theorem gp_sq' : gp ^ 2 = gp + 1 := by
  rw [gp]; ring_nf; rw [s5_sq]; ring

theorem gq_eq : gq = gp - 1 := by rw [gq, gp]; ring

theorem lifts_rotR : Lifts rotR := by
  refine lifts_of_gen (I * gq / 2) (eps1 * (1 / 2 + I * gp / 2)) (eps1 * (-1 / 2 + I * gp / 2))
    (-(I * gq / 2)) fun k => ?_
  apply MvPolynomial.funext
  intro x
  rw [phiE_X, eval_psi_lin, eval_binSub_psi_X, autL_rotR]
  rcases eps1_cases with h | h <;> rw [h] <;> fin_cases k <;>
    simp [Pi.single_apply, gq_eq] <;> ring_nf <;>
    simp only [I_sq, I_pow_three, I_pow_four, gp_sq'] <;> ring_nf

theorem rotC_cube : rotC * rotC * rotC = 1 := by
  rw [← icoHom_sigC, ← map_mul, ← map_mul,
    show (⟨sigC, sigC_alt⟩ : alternatingGroup (Fin 5)) * ⟨sigC, sigC_alt⟩ * ⟨sigC, sigC_alt⟩ = 1
      by decide, map_one]

theorem rotR_sq : rotR * rotR = 1 := by
  rw [← icoHom_sigR, ← map_mul,
    show (⟨sigR, sigR_alt⟩ : alternatingGroup (Fin 5)) * ⟨sigR, sigR_alt⟩ = 1 by decide, map_one]

theorem rotC_inv : rotC⁻¹ = rotC * rotC := by
  rw [inv_eq_iff_mul_eq_one, ← mul_assoc, rotC_cube]

theorem rotR_inv : rotR⁻¹ = rotR := by
  rw [inv_eq_iff_mul_eq_one, rotR_sq]

/-- Every element of `ico` lifts to binary forms. -/
theorem ico_lift : ∀ g ∈ ico, Lifts g :=
  ico_induction Lifts.one (fun _ _ hx hy => hx.mul hy) lifts_rotC
    (by rw [rotC_inv]; exact lifts_rotC.mul lifts_rotC) lifts_rotR
    (by rw [rotR_inv]; exact lifts_rotR)

/-- The consequence used below: `psi ∘ φ_g` factors through `psi`. -/
theorem psi_phiE_congr {g : Aut V1} (hg : g ∈ ico) {F G : P3} (h : psi F = psi G) :
    psi (phiE g F) = psi (phiE g G) := by
  obtain ⟨a, b, c, d, hβ⟩ := ico_lift g hg
  rw [hβ, hβ, h]

end VOA.Classification.COne.OrbIco
