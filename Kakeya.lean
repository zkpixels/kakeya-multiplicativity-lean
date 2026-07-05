import P12Schema
import P31AFc
import P50BFc

/-!
Root module: building this target builds the entire verification tree
(all theorems of the paper) in dependency order.

The `#guard_msgs`-wrapped `#print axioms` commands below are CHECKED
ASSERTIONS: the build FAILS unless every headline theorem depends on
exactly `[propext, Classical.choice, Quot.sound]` — the standard
classical trio.  No `sorry`, no extra axioms, no `Lean.ofReduceBool`
(i.e. no `native_decide`): every enumeration is checked by the Lean
kernel itself, and this file enforces that mechanically.
-/

/--
info: 'KakeyaMultiplicativity.minKakeyaSize_three_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KakeyaMultiplicativity.minKakeyaSize_three_three

/--
info: 'KakeyaMultiplicativity.minKakeyaSize_six_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KakeyaMultiplicativity.minKakeyaSize_six_three

/--
info: 'KakeyaMultiplicativity.minKakeyaSize_six_three_eq_product' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KakeyaMultiplicativity.minKakeyaSize_six_three_eq_product

/--
info: 'KakeyaMultiplicativity.minKakeyaSize_squarefree_dim_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KakeyaMultiplicativity.minKakeyaSize_squarefree_dim_two

/--
info: 'KakeyaMultiplicativity.minKakeyaSize_four_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KakeyaMultiplicativity.minKakeyaSize_four_two

/--
info: 'KakeyaMultiplicativity.minKakeyaSize_twelve_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KakeyaMultiplicativity.minKakeyaSize_twelve_two

/--
info: 'KakeyaMultiplicativity.minKakeyaSize_two_four'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KakeyaMultiplicativity.minKakeyaSize_two_four'

/--
info: 'KakeyaMultiplicativity.minKakeyaSize_two_mul_dim_four' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KakeyaMultiplicativity.minKakeyaSize_two_mul_dim_four
