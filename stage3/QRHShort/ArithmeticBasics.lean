import QRHShort.Arithmetic

/-!
Elementary properties of the actual complex embedding and sixth root used in
the residue-symbol definitions. These do not assert residue reciprocity or the
existence of a primary generator.
-/

noncomputable section

namespace QRHShort

/-- Bundle the selected embedding so that its ring laws are available explicitly. -/
def embeddingHom : O →+* ℂ :=
  if 0 < (rawEmbedding (omega : K)).im then
    rawEmbedding.toRingHom.comp (algebraMap O K)
  else
    (starRingEnd ℂ).comp (rawEmbedding.toRingHom.comp (algebraMap O K))

@[simp] theorem embeddingHom_apply (z : O) : embeddingHom z = embedding z := by
  unfold embeddingHom embedding
  split_ifs <;> rfl

@[simp] theorem embedding_zero : embedding 0 = 0 := by
  simpa only [embeddingHom_apply] using map_zero embeddingHom

@[simp] theorem embedding_one : embedding 1 = 1 := by
  simpa only [embeddingHom_apply] using map_one embeddingHom

@[simp] theorem embedding_add (x y : O) :
    embedding (x + y) = embedding x + embedding y := by
  simpa only [embeddingHom_apply] using map_add embeddingHom x y

@[simp] theorem embedding_mul (x y : O) :
    embedding (x * y) = embedding x * embedding y := by
  simpa only [embeddingHom_apply] using map_mul embeddingHom x y

@[simp] theorem embedding_neg (x : O) : embedding (-x) = -embedding x := by
  simpa only [embeddingHom_apply] using map_neg embeddingHom x

@[simp] theorem embedding_sub (x y : O) :
    embedding (x - y) = embedding x - embedding y := by
  simpa only [embeddingHom_apply] using map_sub embeddingHom x y

@[simp] theorem embedding_pow (x : O) (n : ℕ) :
    embedding (x ^ n) = embedding x ^ n := by
  simpa only [embeddingHom_apply] using map_pow embeddingHom x n

theorem embedding_injective : Function.Injective embedding := by
  intro x y h
  apply NumberField.RingOfIntegers.coe_injective
  apply rawEmbedding.injective
  unfold embedding at h
  split_ifs at h with hpos
  · exact h
  · exact star_injective h

@[simp] theorem embedding_eq_zero {x : O} : embedding x = 0 ↔ x = 0 := by
  rw [← embedding_zero]
  exact embedding_injective.eq_iff

@[simp] theorem omega_cube : omega ^ 3 = 1 :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_cube_eq_one

@[simp] theorem rootSix_pow_six : rootSix ^ 6 = 1 := by
  calc
    rootSix ^ 6 = (omega ^ 3) ^ 4 := by unfold rootSix; ring
    _ = 1 := by rw [omega_cube, one_pow]

@[simp] theorem norm_embedding_omega : ‖embedding omega‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := 3)
  · rw [← embedding_pow, omega_cube, embedding_one]
  · decide

@[simp] theorem norm_embedding_rootSix : ‖embedding rootSix‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := 6)
  · rw [← embedding_pow, rootSix_pow_six, embedding_one]
  · decide

@[simp] theorem norm_embedding_rootSix_pow (n : ℕ) :
    ‖embedding (rootSix ^ n)‖ = 1 := by
  rw [embedding_pow, norm_pow, norm_embedding_rootSix, one_pow]

end QRHShort
