import N16B

namespace KakeyaMultiplicativity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fc2n_s12 :
    ∀ j : Fin 4096,
      countN2 (49152 + j.val) * 6 ≤
        popcountN2 (49152 + j.val) * 15 := by
  decide +kernel

end KakeyaMultiplicativity
