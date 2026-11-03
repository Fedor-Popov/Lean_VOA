import VOA.Huang.HuangODEThreeSepMidRing

/-! Coupled logarithmic inner Euler chains over the actual regular bidisc
coefficient ring. The successor log component remains present at every step;
finite generation eliminates it together with the other components. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocFivePointGraded
open VOA.Huang.FivePointSep

/-- Every inner Euler iterate remains in the common regular coefficient
module for an actual coupled logarithmic derivative family. -/
theorem thetaY_iter_mem_mid_coupled {ι : Type*}
    (NN : Submodule midRing PS2) (Q : ι → ℕ → PS2)
    (next : ι → ι) (d : ι → ℂ) (lam : ℕ → ℂ)
    (hQ : ∀ p j, Q p (j+1) = thetaY (lam j) (Q p j) + d p • Q (next p) j)
    (hmem : ∀ p j, Q p j ∈ NN) (μ : ℂ) :
    ∀ i p j, (thetaY μ)^[i] (Q p j) ∈ NN := by
  intro i
  induction i with
  | zero => intro p j; simpa using hmem p j
  | succ i ih =>
    intro p j
    rw [Function.iterate_succ_apply]
    have he : thetaY μ (Q p j) =
        Q p (j+1)+(μ-lam j) • Q p j-d p • Q (next p) j := by
      rw [hQ]
      have ht : thetaY μ (Q p j) = thetaY (lam j) (Q p j)+(μ-lam j) • Q p j := by
        rw [← thetaY_add_const, add_sub_cancel]
      rw [ht]
      module
    rw [he]
    have hsub (x y : PS2) : (thetaY μ)^[i] (x-y) =
        (thetaY μ)^[i] x-(thetaY μ)^[i] y := by
      simp only [← Module.End.pow_apply, map_sub]
    rw [hsub, thetaY_iterate_add, thetaY_iterate_smul, thetaY_iterate_smul]
    exact NN.sub_mem (NN.add_mem (ih p (j+1))
      (smul_mem_of_midRing NN _ (ih p j)))
      (smul_mem_of_midRing NN _ (ih (next p) j))

/-- The genuine coupled chain has a scalar monic inner regular equation
for every component, with no log-free derivative assumption. -/
theorem innerRegularMid_of_coupled_fg {ι : Type*}
    (NN : Submodule midRing PS2) (hfg : NN.FG)
    (Q : ι → ℕ → PS2) (next : ι → ι) (d : ι → ℂ) (lam : ℕ → ℂ)
    (hQ : ∀ p j, Q p (j+1) = thetaY (lam j) (Q p j) + d p • Q (next p) j)
    (hmem : ∀ p j, Q p j ∈ NN) (p : ι) (v : ℂ) :
    InnerRegularMid v (c2 (Q p 0)) :=
  innerRegularMid_of_fg NN hfg (μ := 0)
    (fun i => thetaY_iter_mem_mid_coupled NN Q next d lam hQ hmem 0 i p 0) v

end VOA.Huang.LogAssocFivePointGraded
