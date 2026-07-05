import N16B

namespace KakeyaMultiplicativity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fc2n_s14 :
    ∀ j : Fin 4096,
      countN2 (57344 + j.val) * 6 ≤
        popcountN2 (57344 + j.val) * 15 := by
  decide +kernel

end KakeyaMultiplicativity
