import VOA.Moonshine.MoonshineCNTensorLightCone
import VOA.Moonshine.MoonshineCNHyperbolicSwap

/-! # Both longitudinal common kernels in the tensor sector -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial
open scoped TensorProduct BigOperators

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

theorem hypTensorOneFamily_eq_commonKernel (a : Fin 2) (charge : ℂ) :
    hypTensorOneFamily (V := V) a =
      ⨅ j : ℕ, LinearMap.ker ((hypOscillator a charge (j + 1 : ℤ)).lTensor V) := by
  classical
  apply le_antisymm
  · apply le_iInf
    intro j
    apply hypTensorSupported_induction
    intro e he v
    change v ⊗ₜ[ℂ] hypOscillator a charge (j + 1 : ℤ) (monomial e 1) = 0
    rw [(hypOneFamily_iff_oscillator a charge _).mp he j, TensorProduct.tmul_zero]
  · intro x hx
    have hx' : ∀ j : ℕ, (hypOscillator a charge (j + 1 : ℤ)).lTensor V x = 0 := by
      simpa only [Submodule.mem_iInf, LinearMap.mem_ker] using hx
    let b := Module.Free.chooseBasis ℂ V
    let c := TensorProduct.equivFinsuppOfBasisLeft (N := hypFock) b
    have hc (f : Module.End ℂ hypFock) (x : V ⊗[ℂ] hypFock)
        (i : Module.Free.ChooseBasisIndex ℂ V) : c (f.lTensor V x) i = f (c x i) := by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v p =>
        simp only [LinearMap.lTensor_tmul, c,
          TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, map_smul]
      | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
    have hp (i : Module.Free.ChooseBasisIndex ℂ V) : c x i ∈ hypOneFamily a := by
      rw [hypOneFamily_iff_oscillator a charge]
      intro j
      rw [← hc]
      rw [hx' j, map_zero, Finsupp.zero_apply]
    have he : x = (c x).sum fun i p => b i ⊗ₜ[ℂ] p := by
      rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
      exact (c.symm_apply_apply x).symm
    rw [he, Finsupp.sum]
    apply Submodule.sum_mem
    intro i _
    exact hypTensorOneFamily_tmul a (b i) (c x i) (hp i)

theorem hypTensor_lightConeSplit_oscillator (D : ℕ → Module.End ℂ V)
    (hD : ∀ i j, D i * D j - D j * D i = ((j : ℂ) - i) • D (i + j + 1))
    (κ ell : ℂ) (hκ : κ ≠ 0) :
    IsCompl (⨆ j : ℕ, LinearMap.range (hypTensorNegative D κ ell j))
      (⨅ j : ℕ, LinearMap.ker ((hypOscA κ (j + 1 : ℤ)).lTensor V)) := by
  rw [← hypTensorOneFamily_eq_commonKernel]
  exact hypTensor_lightConeSplit D hD κ ell hκ

def hypTensorSwap : (V ⊗[ℂ] hypFock) ≃ₗ[ℂ] (V ⊗[ℂ] hypFock) :=
  hypSwapPolynomial.toLinearEquiv.lTensor V

@[simp] theorem hypTensorSwap_tmul (v : V) (p : hypFock) :
    hypTensorSwap (v ⊗ₜ[ℂ] p) = v ⊗ₜ[ℂ] hypSwapPolynomial p := rfl

theorem hypTensorSwap_involutive (x : V ⊗[ℂ] hypFock) :
    hypTensorSwap (hypTensorSwap x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v p => simp [hypSwapPolynomial_involutive]
  | add x y hx hy => simp [hx, hy]

theorem hypTensorSwap_negative (D : ℕ → Module.End ℂ V) (κ ell : ℂ)
    (j : ℕ) (x : V ⊗[ℂ] hypFock) :
    hypTensorSwap (hypTensorNegative D κ ell j x) =
      hypTensorNegative D ell κ j (hypTensorSwap x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v p =>
    simp only [hypTensorNegative_tmul, hypTensorSwap_tmul, map_add,
      hypSwapPolynomial_negativeMode]
  | add x y hx hy => simp [hx, hy]

theorem hypTensorSwap_oneFamily (a : Fin 2) (x : V ⊗[ℂ] hypFock)
    (hx : x ∈ hypTensorOneFamily a) : hypTensorSwap x ∈ hypTensorOneFamily a.rev := by
  apply hypTensorSupported_induction _
    ((hypTensorOneFamily a.rev).comap hypTensorSwap.toLinearMap) ?_ hx
  intro e he v
  exact hypTensorOneFamily_tmul a.rev v _ (hypSwapPolynomial_oneFamily a _ he)

theorem hypTensorSwap_spurious (D : ℕ → Module.End ℂ V) (κ ell : ℂ)
    (x : V ⊗[ℂ] hypFock) (hx : x ∈ hypTensorNegativeSpurious D κ ell) :
    hypTensorSwap x ∈ hypTensorNegativeSpurious D ell κ := by
  have h : hypTensorNegativeSpurious D κ ell ≤
      (hypTensorNegativeSpurious D ell κ).comap hypTensorSwap.toLinearMap := by
    apply iSup_le
    rintro j _ ⟨y, rfl⟩
    change hypTensorSwap (hypTensorNegative D κ ell j y) ∈ hypTensorNegativeSpurious D ell κ
    rw [hypTensorSwap_negative]
    exact (le_iSup (fun j => LinearMap.range (hypTensorNegative D ell κ j)) j)
      (LinearMap.mem_range_self _ _)
  exact h hx

theorem hypTensor_lightConeSplit_swapped (D : ℕ → Module.End ℂ V)
    (hD : ∀ i j, D i * D j - D j * D i = ((j : ℂ) - i) • D (i + j + 1))
    (κ ell : ℂ) (hell : ell ≠ 0) :
    IsCompl (hypTensorNegativeSpurious D κ ell) (hypTensorOneFamily 1) := by
  have hbase := hypTensor_lightConeSplit D hD ell κ hell
  constructor
  · apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro x hx
    have hS := hypTensorSwap_spurious D κ ell x hx.1
    have hK : hypTensorSwap x ∈ hypTensorOneFamily 0 := hypTensorSwap_oneFamily 1 x hx.2
    have hz : hypTensorSwap x = 0 := hbase.disjoint.le_bot ⟨hS, hK⟩
    have he := congrArg hypTensorSwap hz
    simpa only [hypTensorSwap_involutive, map_zero] using he
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : hypTensorSwap x ∈ hypTensorNegativeSpurious D ell κ ⊔ hypTensorOneFamily 0 := by
      rw [hbase.sup_eq_top]
      trivial
    obtain ⟨s, hs, k, hk, he⟩ := Submodule.mem_sup.mp hx
    have he' := congrArg hypTensorSwap he
    rw [map_add, hypTensorSwap_involutive] at he'
    exact Submodule.mem_sup.mpr ⟨_, hypTensorSwap_spurious D ell κ s hs,
      _, hypTensorSwap_oneFamily 0 k hk, he'⟩

/-- For every nonzero momentum, the genuine negative tensor ranges complement
one of the actual longitudinal common kernels. -/
theorem hypTensor_lightConeSplit_nonzero (D : ℕ → Module.End ℂ V)
    (hD : ∀ i j, D i * D j - D j * D i = ((j : ℂ) - i) • D (i + j + 1))
    (κ ell : ℂ) (h : κ ≠ 0 ∨ ell ≠ 0) :
    ∃ a : Fin 2, IsCompl (hypTensorNegativeSpurious D κ ell)
      (⨅ j : ℕ, LinearMap.ker
        ((hypOscillator a (if a = 0 then κ else ell) (j + 1 : ℤ)).lTensor V)) := by
  rcases h with hκ | hell
  · refine ⟨0, ?_⟩
    rw [← hypTensorOneFamily_eq_commonKernel]
    exact hypTensor_lightConeSplit D hD κ ell hκ
  · refine ⟨1, ?_⟩
    rw [← hypTensorOneFamily_eq_commonKernel]
    exact hypTensor_lightConeSplit_swapped D hD κ ell hell

end VOA.Moonshine.ConwayNorton
