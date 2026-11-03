import VOA.DeligneAudit.SL4TThomTransport

/-! # Spanning ideal flags and their transport through Thom multiplication -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra ℂ R] [Algebra ℂ T]

/-- An ordered spanning flag, allowing zero cells and recording one cutoff per cell. -/
inductive SpanningChain (A : Ideal R[X]) : Ideal R → Ideal R → List ℕ → Prop
  | nil (I) : SpanningChain A I I []
  | cons {I K J ns} (x : R) (n : ℕ)
      (step : K.restrictScalars ℂ = I.restrictScalars ℂ ⊔ ℂ ∙ x)
      (relation : Polynomial.C x * X ^ n ∈ I.map Polynomial.C ⊔ A)
      (tail : SpanningChain A K J ns) : SpanningChain A I J (n :: ns)

theorem SpanningChain.append {A : Ideal R[X]} {I J K : Ideal R} {ns ms : List ℕ}
    (h : SpanningChain A I J ns) (h' : SpanningChain A J K ms) :
    SpanningChain A I K (ns ++ ms) := by
  induction h with
  | nil => exact h'
  | cons x n hs hr ht ih => exact .cons x n hs hr (ih h')

/-- Preimage of a source ideal under multiplication, modulo a preceding ideal. -/
def thomFlagIdeal (ρ : R →ₐ[ℂ] T) (t : R) (I : Ideal R) (K : Ideal T) : Ideal R where
  carrier := {y | ∃ x, ρ x ∈ K ∧ y - t * x ∈ I}
  zero_mem' := ⟨0, by simp, by simp⟩
  add_mem' := by
    rintro y z ⟨x, hx, hy⟩ ⟨w, hw, hz⟩
    refine ⟨x + w, by simpa using K.add_mem hx hw, ?_⟩
    convert I.add_mem hy hz using 1
    ring
  smul_mem' := by
    rintro c y ⟨x, hx, hy⟩
    refine ⟨c * x, by simpa using K.mul_mem_left (ρ c) hx, ?_⟩
    convert I.mul_mem_left c hy using 1
    simp only [smul_eq_mul]
    ring

theorem thomFlagIdeal_lower (ρ : R →ₐ[ℂ] T) (t : R) (I : Ideal R) (K : Ideal T) :
    I ≤ thomFlagIdeal ρ t I K := by
  intro y hy
  exact ⟨0, by simp, by simpa using hy⟩

theorem thomFlagIdeal_mul (ρ : R →ₐ[ℂ] T) (t : R) (I : Ideal R)
    (K : Ideal T) {x : R} (hx : ρ x ∈ K) : t * x ∈ thomFlagIdeal ρ t I K :=
  ⟨x, hx, by simp⟩

theorem thomFlagIdeal_mono (ρ : R →ₐ[ℂ] T) (t : R) (I : Ideal R)
    {K L : Ideal T} (h : K ≤ L) : thomFlagIdeal ρ t I K ≤ thomFlagIdeal ρ t I L := by
  rintro y ⟨x, hx, hy⟩
  exact ⟨x, h hx, hy⟩

theorem thomFlagIdeal_bot (ρ : R →ₐ[ℂ] T) (t : R) (I : Ideal R)
    (hker : ∀ x, ρ x = 0 → t * x ∈ I) : thomFlagIdeal ρ t I ⊥ = I := by
  apply le_antisymm _ (thomFlagIdeal_lower ρ t I ⊥)
  rintro y ⟨x, hx, hy⟩
  simpa using I.add_mem hy (hker x hx)

theorem thomFlagIdeal_top (ρ : R →ₐ[ℂ] T) (t : R) (I : Ideal R) :
    thomFlagIdeal ρ t I ⊤ = I ⊔ Ideal.span {t} := by
  apply le_antisymm
  · rintro y ⟨x, _, hy⟩
    exact Submodule.mem_sup.mpr
      ⟨y - t * x, hy, t * x, Ideal.mem_span_singleton.mpr ⟨x, rfl⟩, sub_add_cancel _ _⟩
  · rintro y hy
    obtain ⟨z, hz, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton.mp hw
    exact ⟨x, trivial, by simpa using hz⟩

theorem thomFlagIdeal_step (ρ : R →ₐ[ℂ] T) (t : R) (I : Ideal R)
    {K L : Ideal T} {x : R}
    (h : L.restrictScalars ℂ = K.restrictScalars ℂ ⊔ ℂ ∙ ρ x) :
    (thomFlagIdeal ρ t I L).restrictScalars ℂ =
      (thomFlagIdeal ρ t I K).restrictScalars ℂ ⊔ ℂ ∙ (t * x) := by
  apply le_antisymm
  · rintro y ⟨z, hz, hy⟩
    change ρ z ∈ L.restrictScalars ℂ at hz
    rw [h] at hz
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    have hz' : ρ (z - c • x) ∈ K := by
      rw [map_sub, map_smul, ← huv, add_sub_cancel_right]
      exact hu
    refine Submodule.mem_sup.mpr ⟨y - c • (t * x), ?_, c • (t * x), ?_, ?_⟩
    · refine ⟨z - c • x, hz', ?_⟩
      convert hy using 1
      simp only [Algebra.smul_def]
      ring
    · exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
    · exact sub_add_cancel _ _
  · apply sup_le
    · apply thomFlagIdeal_mono
      intro y hy
      change y ∈ L.restrictScalars ℂ
      rw [h]
      exact Submodule.mem_sup_left hy
    · apply Submodule.span_le.mpr
      rintro y rfl
      apply thomFlagIdeal_mul
      change ρ x ∈ L.restrictScalars ℂ
      rw [h]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

/-- A transport interface separating linear spans from polynomial relation lifting. -/
theorem SpanningChain.thom (ρ : R →ₐ[ℂ] T) (hρ : Function.Surjective ρ)
    (t : R) (I : Ideal R) (A : Ideal R[X]) (B : Ideal T[X]) (s : ℕ)
    (hrel : ∀ (K : Ideal T) (x : R) (n : ℕ),
      Polynomial.C (ρ x) * X ^ n ∈ K.map Polynomial.C ⊔ B →
      Polynomial.C (t * x) * X ^ (n + s) ∈
        (thomFlagIdeal ρ t I K).map Polynomial.C ⊔ A)
    {K L : Ideal T} {ns : List ℕ} (h : SpanningChain B K L ns) :
    SpanningChain A (thomFlagIdeal ρ t I K) (thomFlagIdeal ρ t I L)
      (ns.map (fun n => n + s)) := by
  induction h with
  | nil => exact .nil _
  | @cons K J L ns y n hs hr ht ih =>
      obtain ⟨x, rfl⟩ := hρ y
      exact .cons (t * x) (n + s) (thomFlagIdeal_step ρ t I hs) (hrel K x n hr) ih

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.SpanningChain.append
#print axioms VOA.DeligneAudit.SL4T.thomFlagIdeal_bot
#print axioms VOA.DeligneAudit.SL4T.thomFlagIdeal_top
#print axioms VOA.DeligneAudit.SL4T.thomFlagIdeal_step
#print axioms VOA.DeligneAudit.SL4T.SpanningChain.thom
