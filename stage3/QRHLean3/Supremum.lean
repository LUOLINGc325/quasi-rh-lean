import QRHLean3.Definitions

namespace QRHLean3

/-- S1: the empty-supremum convention. -/
theorem supZero_empty : supZero ∅ = 0 := by
  simp [supZero]

/-- S2: a nonnegative uniform bound controls even an empty family. -/
theorem supZero_le {s : Set ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hs : ∀ x ∈ s, x ≤ B) : supZero s ≤ B := by
  apply csSup_le (show (insert 0 s).Nonempty from ⟨0, by simp⟩)
  intro x hx
  rcases Set.mem_insert_iff.mp hx with hx | hx
  · simpa only [hx] using hB
  · exact hs x hx

/-- S3: every member is below the bounded supremum. -/
theorem le_supZero {s : Set ℝ} (hs : BddAbove s) {x : ℝ} (hx : x ∈ s) :
    x ≤ supZero s := by
  exact le_csSup (hs.insert 0) (Set.mem_insert_of_mem 0 hx)

/-- S4: a bounded supremum containing zero is nonnegative. -/
theorem supZero_nonneg {s : Set ℝ} (hs : BddAbove s) : 0 ≤ supZero s := by
  exact le_csSup (hs.insert 0) (by simp)

end QRHLean3
