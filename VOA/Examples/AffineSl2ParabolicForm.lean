import VOA.Examples.AffineSl2ParabolicExact
import VOA.Examples.AffineSl2HorizontalPowerRadical
import VOA.Examples.AffineSl2ParabolicAdaptedBasis

/-! # The actual descended contravariant form on finite-horizontal modules -/
namespace VOA.AffineVOA.HighestModule
noncomputable section

/-- Choose a linear lift along the actual surjective Verma projection. -/
def parabolicSection (k : ℂ) (d : ℕ) : Parabolic k d →ₗ[ℂ] Verma k d :=
  Classical.choose ((parabolicProjection k d).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (parabolicProjection_surjective k d)))

theorem parabolicSection_rightInverse (k : ℂ) (d : ℕ) :
    (parabolicProjection k d).comp (parabolicSection k d) = LinearMap.id :=
  Classical.choose_spec ((parabolicProjection k d).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (parabolicProjection_surjective k d)))

@[simp] theorem parabolicProjection_section (k : ℂ) (d : ℕ) (v : Parabolic k d) :
    parabolicProjection k d (parabolicSection k d v)=v :=
  LinearMap.congr_fun (parabolicSection_rightInverse k d) v

/-- The complete kernel of the quotient projection lies in the actual Verma radical. -/
theorem parabolicProjection_kernel_radical (k : ℂ) (d : ℕ)
    (v : Verma k d) (hv : parabolicProjection k d v=0) :
    contravariant k d v=0 := by
  have hmem : v ∈ LinearMap.ker (parabolicProjection k d) := hv
  rw [← horizontalReflection_range_eq_kernel] at hmem
  obtain ⟨w,rfl⟩ := hmem
  exact horizontalReflection_radical k d w

/-- The form on the literal parabolic quotient, obtained by descending the
actual normalized Verma contravariant form. -/
def parabolicForm (k : ℂ) (d : ℕ) :
    Parabolic k d →ₗ[ℂ] Module.Dual ℂ (Parabolic k d) :=
  (contravariant k d).compl₁₂ (parabolicSection k d) (parabolicSection k d)

theorem parabolicSection_pairing (k : ℂ) (d : ℕ) (u v : Verma k d) :
    contravariant k d (parabolicSection k d (parabolicProjection k d u)) v =
      contravariant k d u v := by
  have h := parabolicProjection_kernel_radical k d
    (parabolicSection k d (parabolicProjection k d u)-u) (by simp)
  have hh := LinearMap.congr_fun h v
  simpa using sub_eq_zero.mp (by simpa using hh)

/-- On representatives the descended form is exactly the original pairing. -/
@[simp] theorem parabolicForm_projection (k : ℂ) (d : ℕ) (u v : Verma k d) :
    parabolicForm k d (parabolicProjection k d u) (parabolicProjection k d v) =
      contravariant k d u v := by
  change contravariant k d (parabolicSection k d (parabolicProjection k d u))
    (parabolicSection k d (parabolicProjection k d v)) = _
  rw [parabolicSection_pairing,contravariant_symm,parabolicSection_pairing,contravariant_symm]

theorem parabolicForm_symm (k : ℂ) (d : ℕ) (u v : Parabolic k d) :
    parabolicForm k d u v=parabolicForm k d v u := by
  obtain ⟨u,rfl⟩ := parabolicProjection_surjective k d u
  obtain ⟨v,rfl⟩ := parabolicProjection_surjective k d v
  simpa using contravariant_symm k d u v

theorem parabolicProjection_rho (k : ℂ) (d : ℕ) (x : AffSl2) (v : Verma k d) :
    parabolicProjection k d (rho k d x v) =
      parabolicRho k d x (parabolicProjection k d v) := by
  obtain ⟨u,rfl⟩ := Submodule.Quotient.mk_surjective (highestIdeal k d) v
  rfl

theorem parabolicProjection_mode (k : ℂ) (d : ℕ) (a : Fin 3) (n : ℤ) (v : Verma k d) :
    parabolicProjection k d (mode k d a n v) =
      parabolicMode k d a n (parabolicProjection k d v) :=
  parabolicProjection_rho k d (modeElement a n) v

/-- Every actual current has its required adjoint after taking the quotient. -/
theorem parabolicForm_adj (k : ℂ) (d : ℕ) (a : Fin 3) (n : ℤ) (u v : Parabolic k d) :
    parabolicForm k d (parabolicMode k d a n u) v =
      parabolicForm k d u (parabolicMode k d (adjointColour a) (-n) v) := by
  obtain ⟨u,rfl⟩ := parabolicProjection_surjective k d u
  obtain ⟨v,rfl⟩ := parabolicProjection_surjective k d v
  rw [← parabolicProjection_mode,← parabolicProjection_mode,
    parabolicForm_projection,parabolicForm_projection,contravariant_adj]

theorem parabolicForm_degree_adj (k : ℂ) (d : ℕ) (u v : Parabolic k d) :
    parabolicForm k d (parabolicRho k d (AffineLie.ell0 kappaForm kappaForm_isInvariant) u) v =
      parabolicForm k d u (parabolicRho k d (AffineLie.ell0 kappaForm kappaForm_isInvariant) v) := by
  obtain ⟨u,rfl⟩ := parabolicProjection_surjective k d u
  obtain ⟨v,rfl⟩ := parabolicProjection_surjective k d v
  rw [← parabolicProjection_rho,← parabolicProjection_rho,
    parabolicForm_projection,parabolicForm_projection,contravariant_degree_adj]

set_option maxHeartbeats 800000 in
theorem parabolicForm_normalized (k : ℂ) (d : ℕ) :
    parabolicForm k d (parabolicHighest k d) (parabolicHighest k d)=1 := by
  change parabolicForm k d (parabolicProjection k d (highestVector k d))
    (parabolicProjection k d (highestVector k d))=1
  rw [parabolicForm_projection,contravariant_normalized]

/-- The radical is stable under every actual current operator. -/
theorem parabolicForm_radical_mode (k : ℂ) (d : ℕ) (a : Fin 3) (n : ℤ)
    (u : Parabolic k d) (hu : parabolicForm k d u=0) :
    parabolicForm k d (parabolicMode k d a n u)=0 := by
  apply LinearMap.ext
  intro v
  rw [parabolicForm_adj,hu]
  rfl

/-- Distinct actual joint spaces remain orthogonal in the quotient. -/
theorem parabolic_joint_orthogonal (k : ℂ) (d n m : ℕ) (c e : ℤ)
    (u v : Parabolic k d) (hu : u∈parabolicJointSpace k d n c)
    (hv : v∈parabolicJointSpace k d m e) (hne : n≠m ∨ c≠e) :
    parabolicForm k d u v=0 := by
  obtain ⟨u,hu,rfl⟩ := hu
  obtain ⟨v,hv,rfl⟩ := hv
  rw [parabolicForm_projection]
  exact joint_orthogonal k d n m c e u v hu hv hne

/-- Tests in a single joint space detect the full radical for a state in
that space; all other PBW tests vanish by actual orthogonality. -/
theorem parabolic_joint_radical_iff (k : ℂ) (d n : ℕ) (c : ℤ)
    (u : Parabolic k d) (hu : u∈parabolicJointSpace k d n c) :
    parabolicForm k d u=0 ↔
      ∀ v∈parabolicJointSpace k d n c, parabolicForm k d u v=0 := by
  constructor
  · intro h v hv
    rw [h]
    rfl
  · intro h
    have hz : (parabolicForm k d u).comp (parabolicProjection k d)=0 := by
      apply (occupationBasis k d).ext
      intro e
      change parabolicForm k d u (parabolicProjection k d (occupationBasis k d e))=0
      have he : parabolicProjection k d (occupationBasis k d e)∈
          parabolicJointSpace k d (Wak.Charged.occupationEnergy e)
            (Wak.Charged.occupationCharge e) := by
        exact ⟨_,Submodule.subset_span ⟨⟨e,rfl,rfl⟩,rfl⟩,rfl⟩
      by_cases hh : Wak.Charged.occupationEnergy e=n ∧ Wak.Charged.occupationCharge e=c
      · exact h _ (by simpa [hh.1,hh.2] using he)
      · exact parabolic_joint_orthogonal k d n _ c _ u _ hu he
          (by rcases not_and_or.mp hh with hn|hc
              · exact Or.inl (Ne.symm hn)
              · exact Or.inr (Ne.symm hc))
    apply LinearMap.ext
    intro v
    obtain ⟨v,rfl⟩ := parabolicProjection_surjective k d v
    exact LinearMap.congr_fun hz v

end
end VOA.AffineVOA.HighestModule
