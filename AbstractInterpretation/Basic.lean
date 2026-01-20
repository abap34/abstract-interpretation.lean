import AbstractInterpretation.Order.Poset
import AbstractInterpretation.Order.CompleteLattice
import AbstractInterpretation.GaloisConnection
open AbstractInterpretation.Order
import AbstractInterpretation.GaloisConnection

-- Thm1
-- Let (L, ≤), (M, ≤) be complete lattices, and (α, γ) be a Galois connection between them.
-- F: L → L and G: M → M are monotone functions
-- such that for all x ∈ M, α(F(γ(x))) ≤ G(x).
-- Then
--     α(lfp F) ≤ lfp G.
theorem thm1 {L M : Type*} [CompleteLattice L] [CompleteLattice M]
  {alpha : L → M} {gamma : M → L}
  (gc : GaloisConnection alpha gamma)
  {F : L → L} {G : M → M}
  (_F_mon : monotone F) (G_mon : monotone G)
  (h : ∀ x : M, alpha (F (gamma x)) ≤[M] G x) :
  alpha (lfp F) ≤[M] lfp G := by
    have adj: Adjunction alpha gamma := galois_to_adjunction gc
    have h1: G (lfp G) = lfp G := Tarskis_fixed_point_theorem_lfp G G_mon
    have h2: alpha (F (gamma (lfp G))) ≤[M] lfp G := by
      have h2a: alpha (F (gamma (lfp G))) ≤[M] G (lfp G) := h (lfp G)
      rw [h1] at h2a
      exact h2a
    have h3: F (gamma (lfp G)) ≤[L] gamma (lfp G) := by
      exact (adj.adj (F (gamma (lfp G))) (lfp G)).mpr h2
    have h4: lfp F ≤[L] gamma (lfp G) := by
      exact prefixed_point_ge_lfp F (gamma (lfp G)) h3
    have: alpha (lfp F) ≤[M] lfp G := by
      exact (adj.adj (lfp F) (lfp G)).mp h4
    exact this

-- Thm2
-- Let (L, ≤), (M, ≤) be complete lattices, and (α, γ) be a Galois connection between them.
-- F: L → L and G: M → M are monotone functions
-- such that for all x ∈ M, α(F(γ(x))) ≥ G(x)
-- Then
--     α(gfp F) ≥ gfp G.
theorem thm2 {L M : Type*} [instL : CompleteLattice L] [instM : CompleteLattice M]
  {alpha : L → M} {gamma : M → L}
  (gc : GaloisConnection alpha gamma)
  {F : L → L} {G : M → M}
  (F_mon : monotone F) (G_mon : monotone G)
  (h : ∀ x : M, G x ≤[M] alpha (F (gamma x))) :
  gfp G ≤[M] alpha (gfp F) := by
    let instL' : CompleteLattice L := @dual_complete_lattice L instL
    let instM' : CompleteLattice M := @dual_complete_lattice M instM
    have gc' : @GaloisConnection M L instM'.toPoset instL'.toPoset gamma alpha :=
      galois_connection_dual gc
    have gfp_G_eq : @gfp M instM G = @lfp M instM' G := gfp_eq_lfp_dual G G_mon
    have gfp_F_eq : @gfp L instL F = @lfp L instL' F := gfp_eq_lfp_dual F F_mon
    have h' : ∀ x : L, @Poset.le L instL'.toPoset (gamma (G (alpha x))) (F x) := by
      intro x
      -- instL' では y ≤' x ↔ x ≤ y
      -- gamma (G (alpha x)) ≤[L'] F x は F x ≤[L] gamma (G (alpha x))
      show F x ≤[L] gamma (G (alpha x))
      have h1 : G (alpha x) ≤[M] alpha (F (gamma (alpha x))) := h (alpha x)
      have adj : Adjunction alpha gamma := galois_to_adjunction gc
      have h2 : gamma (G (alpha x)) ≤[L] gamma (alpha (F (gamma (alpha x)))) :=
        gc.gamma_mon (G (alpha x)) (alpha (F (gamma (alpha x)))) h1
      have h3 : gamma (alpha (F (gamma (alpha x)))) = F (gamma (alpha x)) := by
        exact galois_gamma_idem gc (F (gamma (alpha x)))
      rw [h3] at h2
      have h4 : gamma (alpha x) ≤[L] gamma (alpha x) := Poset.le_refl (gamma (alpha x))
      have h5 : F (gamma (alpha x)) ≤[L] F x := by
        apply F_mon
        exact (adj.adj (gamma (alpha x)) (alpha x)).mpr (Poset.le_refl (alpha x))
      exact Poset.le_trans h5 h2
