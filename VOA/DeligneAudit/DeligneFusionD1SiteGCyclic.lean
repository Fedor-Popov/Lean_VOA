import VOA.DeligneAudit.DeligneFusionD1SiteG

/-!
# Actual cyclicity of the explicit coadjoint-plus-trivial current site

The existing bounded coadjoint word certificate spans the first summand.
The mode-one lowest-root operator produces the trivial-line generator.
Together these prove cyclicity of the entire n+1-dimensional site.
-/

namespace VOA.DeligneAudit.D1SiteG

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.SectorLoop
open VOA.DeligneAudit.DeligneSector

noncomputable section

variable {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ)
variable (hJ : JacobiCoord f) (hskew : ∀ a b c, f a b c = -f b a c)

def inCo : Co n →ₗ[ℂ] Space n where
  toFun v := (v, 0)
  map_add' u v := by simp
  map_smul' z u := by simp

theorem word_zero (l : List (Fin n)) (v : Co n) :
    wordOp (rep f hJ hskew) (l.map fun c => (c, 0)) (inCo v) = inCo (wordA f l v) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
      change zeroOp f c (wordOp (rep f hJ hskew) (l.map fun c => (c, 0)) (inCo v)) = _
      rw [ih]
      change (coOp f c (wordA f l v), 0) = _
      rw [coOp_apply]
      rfl

def coCyclic (c₀ : Fin n) : Submodule ℂ (Co n) :=
  Submodule.span ℂ (Set.range fun l : List (Fin n) => wordA f l (Pi.single c₀ 1))

def cyclic (c₀ : Fin n) : Submodule ℂ (Space n) :=
  Submodule.span ℂ (Set.range fun l : List (Fin n × ℕ) => wordOp (rep f hJ hskew) l (w c₀))

theorem coCyclic_top (c₀ : Fin n) (depth : ℕ)
    (hcyc : ∀ c, (Pi.single c 1 : Co n) ∈ slotWords f c₀ depth) :
    coCyclic f c₀ = ⊤ := by
  have hslot : slotWords f c₀ depth ≤ coCyclic f c₀ :=
    Submodule.span_mono (by rintro _ ⟨l, _, rfl⟩; exact ⟨l, rfl⟩)
  apply top_unique
  intro v _
  have he : v = ∑ c : Fin n, v c • (Pi.single c 1 : Co n) := by
    funext i
    simp [Pi.single_apply]
  rw [he]
  exact Submodule.sum_mem _ (fun c _ => Submodule.smul_mem _ _ (hslot (hcyc c)))

theorem inCo_coCyclic_le (c₀ : Fin n) :
    (coCyclic f c₀).map inCo ≤ cyclic f hJ hskew c₀ := by
  rw [coCyclic, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨v, ⟨l, rfl⟩, rfl⟩
  exact Submodule.subset_span
    ⟨l.map (fun c => (c, 0)), word_zero f hJ hskew l (Pi.single c₀ 1)⟩

/-- Actual cyclicity from the existing finite coadjoint word certificate. -/
theorem cyclic_top (c₀ : Fin n) (depth : ℕ)
    (hcyc : ∀ c, (Pi.single c 1 : Co n) ∈ slotWords f c₀ depth) :
    cyclic f hJ hskew c₀ = ⊤ := by
  have hco : ∀ v : Co n, inCo v ∈ cyclic f hJ hskew c₀ := by
    intro v
    apply inCo_coCyclic_le f hJ hskew c₀
    exact ⟨v, by rw [coCyclic_top f c₀ depth hcyc]; exact Submodule.mem_top, rfl⟩
  have hv : vac n ∈ cyclic f hJ hskew c₀ := by
    apply Submodule.subset_span
    refine ⟨[(c₀, 1)], ?_⟩
    exact oneOp_w c₀
  apply top_unique
  intro u _
  have he : u = inCo u.1 + u.2 • vac n := by
    ext <;> simp [inCo, vac]
  rw [he]
  exact Submodule.add_mem _ (hco u.1) (Submodule.smul_mem _ _ hv)

/-- Every existing Deligne sector's coadjoint cyclic certificate supplies the
new site's cyclicity; no dimension or realization statement is an input. -/
theorem sector_cyclic_top (S : DeligneSectorData)
    (hskew : ∀ a b c, S.f a b c = -S.f b a c) :
    cyclic S.f S.jacobi hskew S.c₀ = ⊤ :=
  cyclic_top S.f S.jacobi hskew S.c₀ S.depth S.cyclic

end

end VOA.DeligneAudit.D1SiteG

#print axioms VOA.DeligneAudit.D1SiteG.cyclic_top
#print axioms VOA.DeligneAudit.D1SiteG.sector_cyclic_top
