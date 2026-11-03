import VOA.Huang.LogAssocFivePointSpectrum
import VOA.Huang.HuangODEThreeConvergence

/-! Genuine summability and Fubini for the literal two-weight logarithmic
pentagon arrays. Actual finite generalized spectra reduce full complex
weight sums to natural progression rows without duplicate counting. -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 2000000
namespace VOA.Huang.LogAssocFivePoint
open VOA.LogTensor VOA.LogTensor.LogModuleCat VOA.Huang.HuangODEThree
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
variable (N P Q R : LogModuleCat W) (tree : FiveTree)
  (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
  (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ)
  (f : fivePointObject hC2 N P Q R tree →ₗ[ℂ] ℂ)

/-- Genuine absolute progression-row convergence implies absolute convergence
of every actual complex internal weight in the same literal expansion. -/
theorem fivePoint_summable_norm_of_rows
    (hs : ∀ h h' : ℂ,Summable (fun p : ℕ × ℕ =>
      ‖fivePointTerm hC2 N P Q R tree a b c d β x y z w r s f (h+p.1) (h'+p.2)‖)) :
    Summable (fun p : ℂ × ℂ =>
      ‖fivePointTerm hC2 N P Q R tree a b c d β x y z w r s f p.1 p.2‖) := by
  classical
  obtain ⟨S,T,hST⟩ := fivePoint_finite_spectral_cover hC2 N P Q R tree a b c d β x y z w r s f
  apply summable_norm_of_finite_cover
    (fun p : ℂ × ℂ => fivePointTerm hC2 N P Q R tree a b c d β x y z w r s f p.1 p.2)
    (S ×ˢ T) (fun h (p : ℕ × ℕ) => (h.1+p.1,h.2+p.2))
  · intro h hh p q he
    apply Prod.ext
    · have hc : (p.1 : ℂ)=(q.1 : ℂ) := add_left_cancel (congrArg Prod.fst he)
      exact_mod_cast hc
    · have hc : (p.2 : ℂ)=(q.2 : ℂ) := add_left_cancel (congrArg Prod.snd he)
      exact_mod_cast hc
  · intro p hp
    obtain ⟨h,hh,h',hh',m,n,hm,hn⟩ := hST p.1 p.2 hp
    exact ⟨(h,h'),Finset.mem_product.mpr ⟨hh,hh'⟩,(m,n),Prod.ext hm.symm hn.symm⟩
  · intro h hh
    exact hs h.1 h.2

/-- The literal jointly convergent completed pentagon expansion may be
summed first over the second actual internal generalized weight. -/
theorem fivePointEvaluation_eq_tsum_first
    (hs : Summable (fun p : ℂ × ℂ =>
      ‖fivePointTerm hC2 N P Q R tree a b c d β x y z w r s f p.1 p.2‖)) :
    fivePointEvaluation hC2 N P Q R tree a b c d β x y z w r s f=
      ∑' γ : ℂ,∑' δ : ℂ,fivePointTerm hC2 N P Q R tree a b c d β x y z w r s f γ δ :=
  hs.of_norm.tsum_prod

/-- True absolute convergence allows the two actual generalized weights
to be summed in the opposite order as well. -/
theorem fivePointEvaluation_eq_tsum_second
    (hs : Summable (fun p : ℂ × ℂ =>
      ‖fivePointTerm hC2 N P Q R tree a b c d β x y z w r s f p.1 p.2‖)) :
    fivePointEvaluation hC2 N P Q R tree a b c d β x y z w r s f=
      ∑' δ : ℂ,∑' γ : ℂ,fivePointTerm hC2 N P Q R tree a b c d β x y z w r s f γ δ :=
  hs.of_norm.tsum_prod.trans hs.of_norm.tsum_comm.symm

end VOA.Huang.LogAssocFivePoint
