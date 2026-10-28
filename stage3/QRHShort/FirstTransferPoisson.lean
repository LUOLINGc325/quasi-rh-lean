import QRHShort.FirstTransferPoissonPreMobius
import QRHShort.FirstTransferPoissonPreMobiusZeroBoundSum
import QRHShort.FirstTransferPreMobiusBilinear
import QRHShort.FirstTransferPoissonNormBound

/-! First Poisson bound for the literal off-diagonal sum. The actual energy
identity, exact Möbius reindexing, and zero-frequency estimate are combined
with a ray expansion whose coefficients precede all weights and scales. -/

namespace QRHShort

open FirstTransferRayFourier

theorem first_transfer_poisson_bound (_ha : ArithmeticStatement) (_hp : PoissonStatement)
    (_hz : PoissonZeroStatement) :
    FirstTransferPoissonBound := by
  classical
  intro c I Φ hc
  obtain ⟨B, hB, hexp⟩ := first_transfer_preMobius_energy_uniform_expansion _hp c hc
  obtain ⟨Kz, hKz, hzero⟩ := first_transfer_preMobius_zero_bound_of_one_le c I Φ hc
  refine ⟨max Kz B, hKz.trans (le_max_left _ _), ?_⟩
  intro ξ W H L F hW hH hL hF
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hF0 : 0 < F := zero_lt_one.trans_le hF
  obtain ⟨l, hl, hidentity⟩ := hexp ξ
  have heq := hidentity I Φ W H L F hW hH0 hL0 hF0
  simp_rw [first_transfer_preMobius_bilinear_eq c I Φ _ hW H F hL0] at heq
  exact first_transfer_poisson_norm_bound c I Φ ξ (rayFourierCharacter c) l W H L F B Kz
    (firstTransferPreMobiusZero c I Φ ξ W H L F) hB hKz hH0.le hl
    (hzero _hz ξ W H L F hW hH hL hF) heq

end QRHShort
