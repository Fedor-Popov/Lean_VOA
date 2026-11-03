import VOA.Huang.GenusOneG1bRows
import VOA.Huang.GenusOneG1bWardVector
import VOA.Huang.GenusOneG1bKernelBound

/-!
# The iterate Euler system: VOA input

For the product channels `(Y₁ʲ, Y₂ʲ)` attached to an iterate `(Y₃, Y₄)` by converse
associativity, this file builds

* the vector `phiVec Y₁ Y₂ : P₁ → P₂ → (ι → ℂ⟦u⟧⟦t⟧)` and its Ward property
  (`wardBilinearV_phiVec`);
* a finite family of WEIGHT-homogeneous insertion pairs containing a prescribed pair and one
  Euler system `Θ S(f) = Σ_g C_{fg} S(g)` with `C_{fg} ∈ RatSub` common to all channels
  (`exists_homog_euler`; the C₂ generators are only `lev`-homogeneous, so they are first
  refined into weight components, `exists_homog_cover`);
* uniform pole order / numerator degree for the finitely many kernels (`exists_uniform_rat`)
  and the row form `H1` of the system (`rows_euler`).
-/
noncomputable section
namespace VOA.Huang.GenusOneG1b
open VOA VOA.Huang
open scoped BigOperators
open VOA.Huang.GenusOneWard (Phi c2 R2 RatSub RatRows pc omt thetaR2 thetaV compV
  WardBilinearV wardBilinear_Phi eis_mem_RatSub piK_mem_RatSub wardV_exists_generators
  wardV_theta_mem mem_RatSub)
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N : LWModule W}

/-! ## Weight-homogeneous refinement -/

theorem exists_homog_span (P : LWModule W) (x : P.carrier) :
    ∃ F : Finset P.carrier, (∀ u ∈ F, ∃ n : ℕ, u ∈ P.isMod.weight (P.h + n)) ∧
      x ∈ Submodule.span ℂ (F : Set P.carrier) := by
  classical
  refine FusionTop.induction_weight P.isMod x ?_ ?_ ?_
  · exact ⟨∅, by simp, Submodule.zero_mem _⟩
  · rintro x y ⟨F, hF, hx⟩ ⟨G, hG, hy⟩
    refine ⟨F ∪ G, fun u hu => ?_, ?_⟩
    · rcases Finset.mem_union.mp hu with h | h
      · exact hF u h
      · exact hG u h
    · refine Submodule.add_mem _ (Submodule.span_mono ?_ hx) (Submodule.span_mono ?_ hy)
      · intro u hu; exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_coe.mp hu))
      · intro u hu; exact Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_coe.mp hu))
  · intro α x hx
    rcases FusionTop.eq_zero_or_level P hx with h | ⟨n, hn⟩
    · subst h; exact ⟨∅, by simp, Submodule.zero_mem _⟩
    · refine ⟨{x}, fun u hu => ?_, Submodule.subset_span (by simp)⟩
      rw [Finset.mem_singleton] at hu
      subst hu
      exact ⟨n, hn ▸ hx⟩

theorem exists_homog_cover (P : LWModule W) (U : Finset P.carrier) :
    ∃ U' : Finset P.carrier, (∀ u ∈ U', ∃ n : ℕ, u ∈ P.isMod.weight (P.h + n)) ∧
      ∀ u ∈ U, u ∈ Submodule.span ℂ (U' : Set P.carrier) := by
  classical
  choose F hF hx using fun x : P.carrier => exists_homog_span P x
  refine ⟨U.biUnion F, fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp hu
    exact hF v u hv
  · refine Submodule.span_mono (fun w hw => ?_) (hx u)
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_coe.mp hw⟩)

/-! ## The vector of product channels -/

section Vec
variable {ι : Type*} [Fintype ι] {R : ι → LWModule W}

/-- The vector of two-point series of a family of product channels. -/
def phiVec (Y₁ : ∀ j, IntertwiningOperator P₁.isMod (R j).isMod N.isMod)
    (Y₂ : ∀ j, IntertwiningOperator P₂.isMod N.isMod (R j).isMod) :
    P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] (ι → R2) :=
  LinearMap.mk₂ ℂ (fun x y j => Phi (Y₁ j) (Y₂ j) x y)
    (fun x x' y => by funext j; simp [map_add])
    (fun c x y => by funext j; simp)
    (fun x y y' => by funext j; simp)
    (fun c x y => by funext j; simp)

@[simp] theorem phiVec_apply (Y₁ : ∀ j, IntertwiningOperator P₁.isMod (R j).isMod N.isMod)
    (Y₂ : ∀ j, IntertwiningOperator P₂.isMod N.isMod (R j).isMod) (x : P₁.carrier)
    (y : P₂.carrier) (j : ι) : phiVec Y₁ Y₂ x y j = Phi (Y₁ j) (Y₂ j) x y := rfl

theorem wardBilinearV_phiVec (Y₁ : ∀ j, IntertwiningOperator P₁.isMod (R j).isMod N.isMod)
    (Y₂ : ∀ j, IntertwiningOperator P₂.isMod N.isMod (R j).isMod) :
    WardBilinearV (phiVec Y₁ Y₂) (N.h - W.centralCharge / 24) := by
  intro j
  have h : compV (phiVec Y₁ Y₂) j = Phi (Y₁ j) (Y₂ j) :=
    LinearMap.ext fun x => LinearMap.ext fun y => rfl
  rw [h]
  exact wardBilinear_Phi (Y₁ j) (Y₂ j)

end Vec

/-! ## A homogeneous family with one Euler system -/

section Family
variable {ι : Type*} [Fintype ι]

theorem mem_of_span {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Submodule (↥RatSub) (ι → R2)) (φ : M →ₗ[ℂ] (ι → R2)) {G : Set M}
    (hG : ∀ m ∈ G, φ m ∈ T) {m : M} (hm : m ∈ Submodule.span ℂ G) : φ m ∈ T := by
  have hle : Submodule.span ℂ G ≤ (T.restrictScalars ℂ).comap φ :=
    Submodule.span_le.mpr fun m hm' => hG m hm'
  exact hle hm

/-- **One Euler system with `RatSub` kernels on a weight-homogeneous family** containing a
prescribed homogeneous pair, common to all components. -/
theorem exists_homog_euler (S : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] (ι → R2)) {lam : ℂ}
    (hS : WardBilinearV S lam) (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (x : P₁.carrier) (y : P₂.carrier) (a₀ b₀ : ℕ)
    (hx : x ∈ P₁.isMod.weight (P₁.h + a₀)) (hy : y ∈ P₂.isMod.weight (P₂.h + b₀)) :
    ∃ (κ : Type u) (_ : Fintype κ) (xs : κ → P₁.carrier) (ys : κ → P₂.carrier)
      (a b : κ → ℕ) (f₀ : κ) (Cc : κ → κ → R2),
      (∀ f, xs f ∈ P₁.isMod.weight (P₁.h + a f)) ∧
      (∀ f, ys f ∈ P₂.isMod.weight (P₂.h + b f)) ∧
      xs f₀ = x ∧ ys f₀ = y ∧ a f₀ = a₀ ∧ b f₀ = b₀ ∧
      (∀ f g, Cc f g ∈ RatSub) ∧
      ∀ f j, thetaR2 lam (S (xs f) (ys f) j) = ∑ g, Cc f g * S (xs g) (ys g) j := by
  classical
  obtain ⟨U, Z, hUZ⟩ := wardV_exists_generators RatSub eis_mem_RatSub piK_mem_RatSub S hS
    hV i₁ i₂
  obtain ⟨U', hU'h, hU'⟩ := exists_homog_cover P₁ U
  obtain ⟨Z', hZ'h, hZ'⟩ := exists_homog_cover P₂ Z
  choose la hla using hU'h
  choose lb hlb using hZ'h
  let κ := Option (↥U' × ↥Z')
  let xs : κ → P₁.carrier := fun f => f.elim x fun k => k.1.val
  let ys : κ → P₂.carrier := fun f => f.elim y fun k => k.2.val
  let a : κ → ℕ := fun f => f.elim a₀ fun k => la k.1.val k.1.property
  let b : κ → ℕ := fun f => f.elim b₀ fun k => lb k.2.val k.2.property
  set T : Submodule (↥RatSub) (ι → R2) :=
    Submodule.span (↥RatSub) (Set.range fun f : κ => S (xs f) (ys f)) with hT
  -- every value lies in `T`
  have hgen : ∀ u ∈ (U' : Set P₁.carrier), ∀ z ∈ (Z' : Set P₂.carrier), S u z ∈ T := by
    intro u hu z hz
    exact Submodule.subset_span ⟨some (⟨u, hu⟩, ⟨z, hz⟩), rfl⟩
  have hUZT : ∀ u ∈ (U : Set P₁.carrier), ∀ z ∈ (Z : Set P₂.carrier), S u z ∈ T := by
    intro u hu z hz
    refine mem_of_span T (S.flip z) (fun u' hu' => ?_) (hU' u hu)
    exact mem_of_span T (S u') (fun z' hz' => hgen u' hu' z' hz') (hZ' z hz)
  have hall : ∀ x' y', S x' y' ∈ T := by
    intro x' y'
    have h := hUZ x' y'
    refine (Submodule.span_le.mpr ?_) h
    rintro v ⟨u, hu, z, hz, rfl⟩
    exact hUZT u hu z hz
  have hθ : ∀ f : κ, ∃ C : κ → ↥RatSub, ∑ g, C g • S (xs g) (ys g) =
      thetaV lam (S (xs f) (ys f)) := fun f =>
    (Submodule.mem_span_range_iff_exists_fun (↥RatSub)).mp
      (wardV_theta_mem RatSub eis_mem_RatSub piK_mem_RatSub S hS T hall (xs f) (ys f))
  choose C hC using hθ
  refine ⟨κ, inferInstance, xs, ys, a, b, none, fun f g => (C f g : R2), ?_, ?_, rfl, rfl, rfl,
    rfl, fun f g => (C f g).property, ?_⟩
  · intro f
    cases f with
    | none => exact hx
    | some k => exact hla k.1.val k.1.property
  · intro f
    cases f with
    | none => exact hy
    | some k => exact hlb k.2.val k.2.property
  · intro f j
    have h := congrFun (hC f) j
    simp only [thetaV] at h
    rw [← h, Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]

end Family

/-! ## Uniform rationality and the row form -/

section Rows
variable {κ : Type*} [Fintype κ]

theorem exists_uniform_rat {Cc : κ → κ → R2} (hC : ∀ f g, Cc f g ∈ RatSub) :
    ∃ E c d : ℕ, ∀ f g, RatRows E c d (Cc f g) := by
  classical
  choose E c d h using fun fg : κ × κ => (mem_RatSub.mp (hC fg.1 fg.2)).2
  set Et := ∑ fg : κ × κ, E fg with hEt
  refine ⟨Et, ∑ fg : κ × κ, c fg, ∑ fg : κ × κ, (d fg + Et), fun f g => ?_⟩
  have hle : E (f, g) ≤ Et :=
    Finset.single_le_sum (f := E) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (f, g))
  have h1 := (h (f, g)).raise (Et - E (f, g))
  rw [Nat.add_sub_cancel' hle] at h1
  refine h1.mono ?_ ?_
  · exact Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (f, g))
  · have := Finset.single_le_sum (f := fun fg : κ × κ => d fg + Et) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (f, g))
    simp only at this
    omega

theorem coeff_thetaR2 (lam : ℂ) (F : R2) (n : ℕ) :
    PowerSeries.coeff n (thetaR2 lam F) = (lam + n) • PowerSeries.coeff n F := by
  ext k
  simp [thetaR2, VOA.Huang.GenusOneWard.mk2, PowerSeries.coeff_smul, c2]

/-- The Euler system in row form with polynomial numerators. -/
theorem rows_euler {lam : ℂ} {E : ℕ} {F : κ → R2} {Cc : κ → κ → R2}
    {Pol : κ → κ → ℕ → Polynomial ℂ}
    (hsys : ∀ f, thetaR2 lam (F f) = ∑ g, Cc f g * F g)
    (hnum : ∀ f g p, omt ^ E * PowerSeries.coeff p (Cc f g) = pc (Pol f g p))
    (f : κ) (n : ℕ) :
    (lam + n) • (omt ^ E * PowerSeries.coeff n (F f)) =
      ∑ g, ∑ p ∈ Finset.range (n + 1), pc (Pol f g p) * PowerSeries.coeff (n - p) (F g) := by
  have h := congrArg (PowerSeries.coeff n) (hsys f)
  rw [coeff_thetaR2, map_sum] at h
  rw [← mul_smul_comm, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← hnum]
  ring

end Rows

end VOA.Huang.GenusOneG1b
