import N27

namespace KakeyaMultiplicativity

set_option maxHeartbeats 0 in
theorem natB9 : classCountN 511 ≤ 9 := by decide +kernel

/-- Case B, `u = 9`. -/
theorem endgame_caseB_nine :
    ∀ extras ∈ ((Finset.univ : Finset (Fin 27)) \ zPlaneIdx).powersetCard 0,
      classCountIdx (zPlaneIdx ∪ extras) ≤ 9 := by
  intro extras hmem
  rw [Finset.powersetCard_zero, Finset.mem_singleton] at hmem
  subst hmem
  rw [Finset.union_empty, classCountN_eq zplane_bit]
  exact natB9

end KakeyaMultiplicativity
