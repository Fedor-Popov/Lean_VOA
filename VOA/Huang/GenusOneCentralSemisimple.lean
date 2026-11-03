import VOA.Huang.GenusOneCuspTermination

/-! # Central semisimplicity on the insertion Zhu quotient

For a complete top-algebra bimodule, the conformal central element is diagonal
with the actual lowest weights. Thus generalized central eigenfunctionals are
ordinary eigenfunctionals. This is the algebraic log-elimination mechanism in
Miyamoto, math/0010180, Lemma 4.10 and Proposition 4.14. Applying it to analytic
blocks still requires extraction of their logarithmic coefficient functionals.
-/
namespace VOA.Huang.GenusOne.BimoduleTrace
open scoped BigOperators
variable {ι : Type*} [Finite ι] {U : ι → Type*}
  [∀ i, AddCommGroup (U i)] [∀ i, Module ℂ (U i)]
  {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Scalar central elements have no size-two generalized eigenfunctionals on
any bimodule, including infinite-dimensional bimodules. -/
theorem central_square_elimination
    (B : Actions (∀ i, Module.End ℂ (U i)) E) (h : ι → ℂ) (r : ℂ)
    (f : E →ₗ[ℂ] ℂ)
    (hf : ∀ x, f (B.left (fun i => (h i - r) • (1 : Module.End ℂ (U i)))
      (B.left (fun i => (h i - r) • (1 : Module.End ℂ (U i))) x)) = 0) :
    ∀ x, f (B.left (fun i => (h i - r) • (1 : Module.End ℂ (U i))) x) = 0 := by
  classical
  letI := Fintype.ofFinite ι
  let a : ∀ i, Module.End ℂ (U i) := fun i => (h i - r) • 1
  let e (i : ι) : ∀ j, Module.End ℂ (U j) := Pi.single i 1
  have hae (i : ι) : a * e i = (h i - r) • e i := by
    funext j
    by_cases hj : j = i
    · subst j; simp [a, e]
    · simp [a, e, Pi.single_eq_of_ne hj]
  have heval (i : ι) (x : E) : B.left a (B.left (e i) x) =
      (h i - r) • B.left (e i) x := by
    rw [← B.left_mul, hae, map_smul, LinearMap.smul_apply]
  have hpieces (i : ι) (x : E) : (h i - r) * f (B.left (e i) x) = 0 := by
    have hv := hf (B.left (e i) x)
    change f (B.left a (B.left a (B.left (e i) x))) = 0 at hv
    rw [heval, map_smul, heval, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hv
    by_cases hz : h i - r = 0
    · rw [hz, zero_mul]
    · exact (mul_eq_zero.mp hv).resolve_left hz
  have he : ∑ i, e i = (1 : ∀ i, Module.End ℂ (U i)) := by
    ext j x
    simp [e]
  have hx (x : E) : x = ∑ i, B.left (e i) x := by
    have hv := congrArg (fun b => B.left b x) he
    simpa only [map_sum, LinearMap.sum_apply, B.left_one] using hv.symm
  intro x
  change f (B.left a x) = 0
  conv_lhs => rw [hx x]
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [heval, map_smul, smul_eq_mul, hpieces]

/-- A finite logarithmic chain for a scalar central element has no positive
log coefficients. The recurrence is the leading-coefficient omega recursion. -/
theorem central_log_chain_vanish
    (B : Actions (∀ i, Module.End ℂ (U i)) E) (h : ι → ℂ) (r : ℂ)
    (f : ℕ → E →ₗ[ℂ] ℂ) (K : ℕ) (hK : ∀ k, K ≤ k → f k = 0)
    (hrec : ∀ k x, f k (B.left (fun i => (h i - r) • (1 : Module.End ℂ (U i))) x) =
      (k + 1 : ℂ) * f (k + 1) x) : ∀ k, 1 ≤ k → f k = 0 := by
  have step (j : ℕ) (hj : 1 ≤ j) (hj1 : f (j + 1) = 0) : f j = 0 := by
    have hs := central_square_elimination B h r (f (j - 1)) (fun x => by
      rw [hrec, hrec, show j - 1 + 1 = j by omega, hj1]
      simp)
    ext x
    have hv := hs x
    rw [hrec, show j - 1 + 1 = j by omega] at hv
    have hnz : ((j - 1 : ℕ) : ℂ) + 1 ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (j - 1)
    exact (mul_eq_zero.mp hv).resolve_left hnz
  have hd : ∀ d, ∀ j, 1 ≤ j → K ≤ j + d → f j = 0 := by
    intro d
    induction d with
    | zero => intro j _ hjd; exact hK j (by omega)
    | succ d ih =>
      intro j hj hjd
      exact step j hj (ih (j + 1) (by omega) (by omega))
  exact fun k hk => hd K k hk (by omega)

end VOA.Huang.GenusOne.BimoduleTrace

namespace VOA.Huang.GenusOne
open VOA VOA.FZ FusionTop
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M} {ι : Type u}

/-- The conformal vector acts on each top by its actual lowest weight. -/
theorem insertionTopRep_conformal (P : ι → LWModule W) :
    insertionTopRep P W.conformalVector = fun i => (P i).h • (1 : Module.End ℂ (bot (P i))) := by
  funext i
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((rhoLW (P i).isMod (P i).h W.conformalVector x : bot (P i)) : (P i).carrier) = _
  rw [rhoLW_apply_coe, oMod_homogeneous _ W.conformalVector_mem_grading_two]
  exact (P i).isMod.L0_weight _ _ x.property

/-- Shifted conformal central action on the actual insertion Zhu quotient. -/
noncomputable def insertionCuspOmega (P : ι → LWModule W)
    (B : InsertionTopBimodule A P) (r : ℂ) :
    Module.End ℂ (M ⧸ fzO A.toWeakModule) :=
  B.actions.left (insertionTopRep P W.conformalVector) - r • LinearMap.id

/-- The shifted action agrees with the raw homogeneous Zhu operation. -/
theorem insertionCuspOmega_mk (P : ι → LWModule W)
    (B : InsertionTopBimodule A P) (r : ℂ) (w : M) :
    insertionCuspOmega P B r ((fzO A.toWeakModule).mkQ w) =
      (fzO A.toWeakModule).mkQ (fzLeft A.toWeakModule 2 W.conformalVector w - r • w) := by
  simp only [insertionCuspOmega, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_sub, map_smul,
    B.left_mk 2 W.conformalVector W.conformalVector_mem_grading_two]

theorem insertionCuspOmega_eq_diagonal (P : ι → LWModule W)
    (B : InsertionTopBimodule A P) (r : ℂ) :
    insertionCuspOmega P B r =
      B.actions.left (fun i => ((P i).h - r) • (1 : Module.End ℂ (bot (P i)))) := by
  have hd : (fun i => ((P i).h - r) • (1 : Module.End ℂ (bot (P i)))) =
      insertionTopRep P W.conformalVector - r • 1 := by
    rw [insertionTopRep_conformal]
    ext i x
    simp [sub_smul]
  rw [hd, map_sub, map_smul]
  unfold insertionCuspOmega
  congr 1
  apply congrArg (fun f => r • f)
  exact (LinearMap.ext B.actions.left_one).symm

/-- Algebraic central-character log elimination on `A(M)`, conditional only
on the explicit quotient bimodule bridge. No analytic expansion is assumed here. -/
theorem insertionCuspOmega_square_elimination [Finite ι] (P : ι → LWModule W)
    (B : InsertionTopBimodule A P) (r : ℂ) (f : (M ⧸ fzO A.toWeakModule) →ₗ[ℂ] ℂ)
    (hf : ∀ x, f (insertionCuspOmega P B r (insertionCuspOmega P B r x)) = 0) :
    ∀ x, f (insertionCuspOmega P B r x) = 0 := by
  simp only [insertionCuspOmega_eq_diagonal] at hf ⊢
  exact BimoduleTrace.central_square_elimination B.actions (fun i => (P i).h) r f hf

/-- Once logarithmic leading functionals on the Zhu quotient are extracted,
their finite omega chain contains no positive logarithmic coefficient. -/
theorem insertionCusp_log_chain_vanish [Finite ι] (P : ι → LWModule W)
    (B : InsertionTopBimodule A P) (r : ℂ)
    (f : ℕ → (M ⧸ fzO A.toWeakModule) →ₗ[ℂ] ℂ)
    (K : ℕ) (hK : ∀ k, K ≤ k → f k = 0)
    (hrec : ∀ k x, f k (insertionCuspOmega P B r x) = (k + 1 : ℂ) * f (k + 1) x) :
    ∀ k, 1 ≤ k → f k = 0 := by
  simp only [insertionCuspOmega_eq_diagonal] at hrec
  exact BimoduleTrace.central_log_chain_vanish B.actions (fun i => (P i).h) r f K hK hrec

end VOA.Huang.GenusOne
