import P11Tail
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Squarefree

namespace KakeyaMultiplicativity

/-! ## The plane schema: the certificate holds at the true price for
every prime `q`

The theorem: for every prime `q`,
`FractionalCostAt q 2 (nonzeroDirections q 2) (minKakeyaSize q 2)`.
Combined with the transfer theorem this makes the plane Kakeya minimum
fully multiplicative over squarefree moduli:
`K(N,2) = ∏_{p ∣ N} K(p,2)`.

Proof shape.  The carried directions of a subset `S` organize into
direction classes with canonical representatives; choosing one witness
line per carried representative produces `k ≤ q+1` pairwise
non-parallel full lines inside `S`.  Two regimes:

* `k ≤ q`: non-parallel lines meet in at most one point, so a
  truncated inclusion–exclusion gives `|S| ≥ kq − C(k,2)`, and the
  certificate inequality follows from the single arithmetic input
  `2·K(q,2) ≤ q² + 2q − 1` — an upper-bound CONSTRUCTION; no lower
  bound on `K(q,2)` enters anywhere.
* `k = q+1`: every class is carried, so `S` is itself a Kakeya set and
  `|S| ≥ K(q,2)` holds by definition of the minimum.

The construction supplying `2·K(q,2) ≤ q² + 2q − 1` for odd `q` is the
classical parabola-tangent example in closed form:
`W = {(x,y) : x² − y is a square} ∪ {(0,y)}`, whose nonzero columns
have `(q+1)/2` points each. -/

section PlaneSchema

variable {q : ℕ} [Fact (Nat.Prime q)]

private instance neZero_of_fact_prime : NeZero q :=
  ⟨(Fact.out : q.Prime).ne_zero⟩

/-- `2 ≠ 0` in `ZMod q` for odd prime `q`. -/
theorem two_ne_zero_zmod (hq2 : q ≠ 2) : (2 : ZMod q) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
  have hdvd : q ∣ 2 := (CharP.cast_eq_zero_iff (ZMod q) q 2).mp h2
  exact hq2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime)
    Nat.prime_two).mp hdvd)

/-- Two-coordinate extensionality for plane points. -/
theorem plane_point_ext {b c : ResiduePoint q 2}
    (h0 : b 0 = c 0) (h1 : b 1 = c 1) : b = c := by
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem plane_point_ne_zero_iff {b : ResiduePoint q 2} :
    b ≠ 0 ↔ b 0 ≠ 0 ∨ b 1 ≠ 0 := by
  constructor
  · intro hb
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    exact hb (plane_point_ext hc.1 hc.2)
  · rintro (h | h) rfl <;> simp at h

/-! ### Direction classes and canonical representatives -/

/-- Line-carrying is invariant under unit rescaling of the direction:
the parametrized point sets coincide up to reparametrization. -/
theorem carriesLine_smul_iff {S : Finset (ResiduePoint q 2)}
    {b : ResiduePoint q 2} {u : ZMod q} (hu : u ≠ 0) :
    CarriesLine S (u • b) ↔ CarriesLine S b := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun t => ?_⟩
    have h := ha (t * u⁻¹)
    have he : residueLine a (u • b) (t * u⁻¹) = residueLine a b t := by
      funext i
      simp only [residueLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [show t * u⁻¹ * (u * b i) = t * (u⁻¹ * u) * b i by ring,
        inv_mul_cancel₀ hu, mul_one]
    rwa [he] at h
  · rintro ⟨a, ha⟩
    refine ⟨a, fun t => ?_⟩
    have h := ha (t * u)
    have he : residueLine a b (t * u) = residueLine a (u • b) t := by
      funext i
      simp only [residueLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rwa [he] at h

/-- Canonical class representative: rescale so the first nonzero
coordinate is `1`. -/
def dirRep (b : ResiduePoint q 2) : ResiduePoint q 2 :=
  if b 0 ≠ 0 then ![1, b 1 * (b 0)⁻¹] else ![0, 1]

theorem dirRep_ne_zero (b : ResiduePoint q 2) : dirRep b ≠ 0 := by
  unfold dirRep
  split
  · intro h
    have := congrFun h 0
    simp at this
  · intro h
    have := congrFun h 1
    simp at this

/-- Every nonzero direction is a unit multiple of its representative. -/
theorem dirRep_smul_self {b : ResiduePoint q 2} (hb : b ≠ 0) :
    ∃ u : ZMod q, u ≠ 0 ∧ u • dirRep b = b := by
  by_cases h0 : b 0 ≠ 0
  · refine ⟨b 0, h0, ?_⟩
    have : dirRep b = ![1, b 1 * (b 0)⁻¹] := if_pos h0
    rw [this]
    refine plane_point_ext ?_ ?_
    · simp
    · show b 0 * (![1, b 1 * (b 0)⁻¹] 1) = b 1
      show b 0 * (b 1 * (b 0)⁻¹) = b 1
      rw [show b 0 * (b 1 * (b 0)⁻¹) = b 1 * (b 0 * (b 0)⁻¹) by ring,
        mul_inv_cancel₀ h0, mul_one]
  · have h0eq : b 0 = 0 := not_not.mp h0
    have h1 : b 1 ≠ 0 := by
      rcases plane_point_ne_zero_iff.mp hb with h | h
      · exact absurd h0eq h
      · exact h
    refine ⟨b 1, h1, ?_⟩
    have : dirRep b = ![0, 1] := if_neg h0
    rw [this]
    refine plane_point_ext ?_ ?_
    · show b 1 * (0 : ZMod q) = b 0
      rw [mul_zero, h0eq]
    · show b 1 * (1 : ZMod q) = b 1
      rw [mul_one]

/-- The representative is scale invariant. -/
theorem dirRep_smul (b : ResiduePoint q 2) {u : ZMod q} (hu : u ≠ 0) :
    dirRep (u • b) = dirRep b := by
  have hcoord : ∀ i, (u • b) i = u * b i := fun i => rfl
  by_cases h0 : b 0 ≠ 0
  · have h0' : (u • b) 0 ≠ 0 := by
      rw [hcoord]
      exact mul_ne_zero hu h0
    unfold dirRep
    rw [if_pos h0', if_pos h0]
    refine plane_point_ext rfl ?_
    show u * b 1 * (u * b 0)⁻¹ = b 1 * (b 0)⁻¹
    rw [mul_inv, show u * b 1 * (u⁻¹ * (b 0)⁻¹) =
      (u * u⁻¹) * (b 1 * (b 0)⁻¹) by ring, mul_inv_cancel₀ hu, one_mul]
  · have h0eq : b 0 = 0 := not_not.mp h0
    have h0' : ¬ (u • b) 0 ≠ 0 := by
      rw [hcoord, h0eq, mul_zero]
      simp
    unfold dirRep
    rw [if_neg h0', if_neg h0]

theorem dirRep_idem (b : ResiduePoint q 2) :
    dirRep (dirRep b) = dirRep b := by
  by_cases h0 : b 0 ≠ 0
  · have hb : dirRep b = ![1, b 1 * (b 0)⁻¹] := if_pos h0
    rw [hb]
    have h1 : (![1, b 1 * (b 0)⁻¹] : ResiduePoint q 2) 0 ≠ 0 := by
      show (1 : ZMod q) ≠ 0
      exact one_ne_zero
    have hstep : dirRep (![1, b 1 * (b 0)⁻¹] : ResiduePoint q 2) =
        ![1, (![1, b 1 * (b 0)⁻¹] : ResiduePoint q 2) 1 *
          ((![1, b 1 * (b 0)⁻¹] : ResiduePoint q 2) 0)⁻¹] := if_pos h1
    rw [hstep]
    refine plane_point_ext rfl ?_
    show (b 1 * (b 0)⁻¹) * ((1 : ZMod q))⁻¹ = b 1 * (b 0)⁻¹
    rw [inv_one, mul_one]
  · have hb : dirRep b = ![0, 1] := if_neg h0
    rw [hb]
    have h1 : ¬ (![0, 1] : ResiduePoint q 2) 0 ≠ 0 := by
      show ¬ (0 : ZMod q) ≠ 0
      simp
    exact if_neg h1

/-- Carrying transfers between a direction and its representative. -/
theorem carriesLine_dirRep_iff {S : Finset (ResiduePoint q 2)}
    {b : ResiduePoint q 2} (hb : b ≠ 0) :
    CarriesLine S (dirRep b) ↔ CarriesLine S b := by
  obtain ⟨u, hu, hub⟩ := dirRep_smul_self hb
  conv_rhs => rw [← hub]
  exact (carriesLine_smul_iff hu).symm

/-- The slope injection: representatives embed into `Option (ZMod q)`,
bounding the number of classes by `q + 1`. -/
def slopeOf (b : ResiduePoint q 2) : Option (ZMod q) :=
  if b 0 ≠ 0 then some (b 1 * (b 0)⁻¹) else none

theorem dirRep_eq_of_slopeOf_eq {b c : ResiduePoint q 2}
    (h : slopeOf b = slopeOf c) : dirRep b = dirRep c := by
  unfold slopeOf at h
  unfold dirRep
  by_cases hb : b 0 ≠ 0 <;> by_cases hc : c 0 ≠ 0
  · rw [if_pos hb, if_pos hc]
    rw [if_pos hb, if_pos hc] at h
    exact congrArg (fun s => ![1, s]) (Option.some.inj h)
  · rw [if_pos hb, if_neg hc] at h
    exact absurd h (by simp)
  · rw [if_neg hb, if_pos hc] at h
    exact absurd h (by simp)
  · rw [if_neg hb, if_neg hc]

/-- At most `q + 1` distinct representatives exist. -/
theorem card_reps_le {R : Finset (ResiduePoint q 2)}
    (hR : ∀ r ∈ R, dirRep r = r) : R.card ≤ q + 1 := by
  have hinj : Set.InjOn slopeOf (R : Set (ResiduePoint q 2)) := by
    intro r hr r' hr' h
    have := dirRep_eq_of_slopeOf_eq h
    rwa [hR r hr, hR r' hr'] at this
  calc R.card = (R.image slopeOf).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (Option (ZMod q))).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = q + 1 := by
        rw [Finset.card_univ, Fintype.card_option, ZMod.card]

/-! ### Lines in the plane: size and pairwise intersections -/

/-- Injective parametrization over the prime modulus. -/
theorem residueLine_injective_prime {n : ℕ} {a b : ResiduePoint q n}
    (hb : b ≠ 0) : Function.Injective (residueLine a b) := by
  intro t t' h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
  have h1 := congrFun h i
  simp only [residueLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
  exact mul_right_cancel₀ hi (add_left_cancel h1)

/-- A full line as a finset. -/
def lineFinset (a b : ResiduePoint q 2) : Finset (ResiduePoint q 2) :=
  (Finset.univ : Finset (ZMod q)).image (residueLine a b)

theorem lineFinset_card {a b : ResiduePoint q 2} (hb : b ≠ 0) :
    (lineFinset a b).card = q := by
  unfold lineFinset
  rw [Finset.card_image_of_injective _ (residueLine_injective_prime hb),
    Finset.card_univ, ZMod.card]

theorem lineFinset_subset_iff {a b : ResiduePoint q 2}
    {S : Finset (ResiduePoint q 2)} :
    lineFinset a b ⊆ S ↔ ∀ t : ZMod q, residueLine a b t ∈ S := by
  unfold lineFinset
  constructor
  · intro h t
    exact h (Finset.mem_image_of_mem _ (Finset.mem_univ t))
  · intro h x hx
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hx
    exact h t

/-- Two points of a line differ by a scalar multiple of the direction. -/
theorem sub_smul_of_mem_lineFinset {a b x y : ResiduePoint q 2}
    (hx : x ∈ lineFinset a b) (hy : y ∈ lineFinset a b) :
    ∃ t : ZMod q, y = x + t • b := by
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨s', -, rfl⟩ := Finset.mem_image.mp hy
  refine ⟨s' - s, ?_⟩
  funext i
  simp only [residueLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Lines in distinct classes meet in at most one point. -/
theorem lineFinset_inter_card_le_one {a b a' b' : ResiduePoint q 2}
    (hb : b ≠ 0) (hb' : b' ≠ 0) (hne : dirRep b ≠ dirRep b') :
    (lineFinset a b ∩ lineFinset a' b').card ≤ 1 := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hlt
  obtain ⟨t, ht⟩ := sub_smul_of_mem_lineFinset
    (Finset.mem_of_mem_inter_left hx) (Finset.mem_of_mem_inter_left hy)
  obtain ⟨s, hs⟩ := sub_smul_of_mem_lineFinset
    (Finset.mem_of_mem_inter_right hx) (Finset.mem_of_mem_inter_right hy)
  have hts : t • b = s • b' := by
    have := ht.symm.trans hs
    exact add_left_cancel (by rw [this])
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at ht
    exact hxy (ht ▸ rfl)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hts
    exact hb (smul_eq_zero.mp hts |>.resolve_left ht0)
  have hbb' : b = (t⁻¹ * s) • b' := by
    have := congrArg (fun v => t⁻¹ • v) hts
    simp only [smul_smul, inv_mul_cancel₀ ht0, one_smul] at this
    exact this
  have : dirRep b = dirRep b' := by
    rw [hbb', dirRep_smul _ (mul_ne_zero (inv_ne_zero ht0) hs0)]
  exact hne this

/-! ### Truncated inclusion–exclusion -/

/-- Bonferroni for families with pairwise intersections of size at most
one, in subtraction-free form:
`Σ|f i| ≤ |⋃ f i| + C(|s|, 2)`. -/
theorem sum_card_le_card_biUnion_add_choose {ι : Type*} [DecidableEq ι]
    {X : Type*} [DecidableEq X] (s : Finset ι) (f : ι → Finset X)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (f i ∩ f j).card ≤ 1) :
    ∑ i ∈ s, (f i).card ≤ (s.biUnion f).card + Nat.choose s.card 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hpair' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (f i ∩ f j).card ≤ 1 :=
        fun i hi j hj => hpair i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj)
      have hcross : (f a ∩ s.biUnion f).card ≤ s.card := by
        have hsub : f a ∩ s.biUnion f ⊆
            s.biUnion (fun i => f a ∩ f i) := by
          intro x hx
          obtain ⟨hxa, hxu⟩ := Finset.mem_inter.mp hx
          obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hxu
          exact Finset.mem_biUnion.mpr
            ⟨i, hi, Finset.mem_inter.mpr ⟨hxa, hxi⟩⟩
        calc (f a ∩ s.biUnion f).card
            ≤ (s.biUnion (fun i => f a ∩ f i)).card :=
              Finset.card_le_card hsub
          _ ≤ ∑ i ∈ s, (f a ∩ f i).card := Finset.card_biUnion_le
          _ ≤ ∑ _i ∈ s, 1 := Finset.sum_le_sum (fun i hi =>
              hpair a (Finset.mem_insert_self a s)
                i (Finset.mem_insert_of_mem hi)
                (fun h => ha (h ▸ hi)))
          _ = s.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      have hunion : (f a).card + (s.biUnion f).card ≤
          ((insert a s).biUnion f).card + s.card := by
        rw [Finset.biUnion_insert]
        have := Finset.card_union_add_card_inter (f a) (s.biUnion f)
        omega
      have hchoose : Nat.choose (s.card + 1) 2 =
          Nat.choose s.card 2 + s.card := by
        rw [Nat.choose_two_right, Nat.choose_two_right]
        exact Nat.triangle_succ s.card
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, hchoose]
      have := ih hpair'
      omega

/-! ### Counting squares in `ZMod q` -/

open Classical in
/-- The square-root fiber count: `1` at zero, `2` at nonzero squares,
`0` at nonsquares (odd `q`). -/
theorem card_sqrt_fiber (hq2 : q ≠ 2) (a : ZMod q) :
    ((Finset.univ : Finset (ZMod q)).filter (fun x => x * x = a)).card =
      if a = 0 then 1 else if IsSquare a then 2 else 0 := by
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl]
    have : (Finset.univ : Finset (ZMod q)).filter (fun x => x * x = 0) =
        {0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, mul_self_eq_zero]
    rw [this, Finset.card_singleton]
  · rw [if_neg ha]
    by_cases hs : IsSquare a
    · rw [if_pos hs]
      obtain ⟨r, hr⟩ := hs
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hr
        exact ha hr
      have hfib : (Finset.univ : Finset (ZMod q)).filter
          (fun x => x * x = a) = {r, -r} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hx
          have : (x - r) * (x + r) = 0 := by
            have : x * x = r * r := hx.trans hr
            ring_nf
            ring_nf at this
            rw [this]
            ring
          rcases mul_eq_zero.mp this with h | h
          · exact Or.inl (sub_eq_zero.mp h)
          · exact Or.inr (eq_neg_of_add_eq_zero_left h)
        · rintro (rfl | rfl)
          · exact hr.symm
          · rw [neg_mul_neg]
            exact hr.symm
      rw [hfib]
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      simp only [Finset.mem_singleton]
      intro h
      have h2r : (2 : ZMod q) * r = 0 := by
        have : r + r = 0 := by
          nth_rewrite 1 [h]
          ring
        rw [two_mul]
        exact this
      rcases mul_eq_zero.mp h2r with h2 | h2
      · exact two_ne_zero_zmod hq2 h2
      · exact hr0 h2
    · rw [if_neg hs]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _
      intro hx
      exact hs ⟨x, hx.symm⟩

open Classical in
/-- Doubled square count: `2·#{squares} = q + 1` for odd prime `q`. -/
theorem two_mul_card_squares (hq2 : q ≠ 2) :
    2 * ((Finset.univ : Finset (ZMod q)).filter
      (fun a => IsSquare a)).card = q + 1 := by
  classical
  -- Partition the q elements of ZMod q by their square.
  have hpart : ∑ a ∈ (Finset.univ : Finset (ZMod q)),
      ((Finset.univ : Finset (ZMod q)).filter
        (fun x => x * x = a)).card = q := by
    rw [← Finset.card_eq_sum_card_fiberwise
      (f := fun x : ZMod q => x * x)
      (fun x _ => Finset.mem_univ _)]
    rw [Finset.card_univ, ZMod.card]
  -- Zero is a square; split it off.
  have h0sq : IsSquare (0 : ZMod q) := ⟨0, by ring⟩
  have h0mem : (0 : ZMod q) ∈ (Finset.univ : Finset (ZMod q)).filter
      (fun a => IsSquare a) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0sq⟩
  have hsplit : (((Finset.univ : Finset (ZMod q)).erase 0).filter
        (fun a => IsSquare a)).card + 1 =
      ((Finset.univ : Finset (ZMod q)).filter (fun a => IsSquare a)).card := by
    rw [Finset.filter_erase]
    exact Finset.card_erase_add_one h0mem
  -- Rewrite the fiber sum with the three-valued fiber count.
  rw [Finset.sum_congr rfl (fun a _ => card_sqrt_fiber hq2 a)] at hpart
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q))] at hpart
  rw [if_pos rfl] at hpart
  have herase : ∑ a ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      (if a = 0 then 1 else if IsSquare a then 2 else 0) =
      ∑ a ∈ (Finset.univ : Finset (ZMod q)).erase 0,
        (if IsSquare a then 2 else 0) := by
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [if_neg (Finset.ne_of_mem_erase ha)]
  have hcount : ∑ a ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      (if IsSquare a then 2 else 0) =
      2 * (((Finset.univ : Finset (ZMod q)).erase 0).filter
        (fun a => IsSquare a)).card := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
  rw [herase, hcount] at hpart
  omega

/-! ### The parabola-tangent construction -/

open Classical in
/-- The classical small Kakeya set in the plane, in closed form: the
union of all tangent lines of the parabola `y = x²` together with one
vertical line. -/
noncomputable def planeWitness (q : ℕ) [NeZero q] :
    Finset (ResiduePoint q 2) :=
  Finset.univ.filter (fun p => IsSquare (p 0 * p 0 - p 1) ∨ p 0 = 0)

/-- The construction is Kakeya (odd prime `q`): slope `s` is realized
by the tangent at `t = s/2`, verticals by the added column. -/
theorem planeWitness_isKakeyaSet (hq2 : q ≠ 2) :
    IsKakeyaSet (planeWitness q) := by
  classical
  intro b
  by_cases hb : b = 0
  · subst hb
    refine ⟨![0, 0], fun t => ?_⟩
    have : residueLine ![0, 0] 0 t = ![0, 0] := by
      funext i
      simp [residueLine]
    rw [this]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ?_⟩
    simp
  · have hkey : CarriesLine (planeWitness q) (dirRep b) := by
      by_cases h0 : b 0 ≠ 0
      · -- Slope representative ![1, s]: the tangent line at t = s/2.
        -- Anchored at (0, −t²) its points are (u, u·s − t²), and the
        -- witness discriminant u² − (u·s − t²) = (u − t)² is a square.
        have hrep : dirRep b = ![1, b 1 * (b 0)⁻¹] := if_pos h0
        set s : ZMod q := b 1 * (b 0)⁻¹ with hs
        set tt : ZMod q := s * (2 : ZMod q)⁻¹ with htt
        have h2 : (2 : ZMod q) ≠ 0 := two_ne_zero_zmod hq2
        have hst : (2 : ZMod q) * tt = s := by
          rw [htt, show (2 : ZMod q) * (s * (2 : ZMod q)⁻¹) =
            s * ((2 : ZMod q) * (2 : ZMod q)⁻¹) by ring,
            mul_inv_cancel₀ h2, mul_one]
        rw [hrep]
        refine ⟨![0, -(tt * tt)], fun u => ?_⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ?_⟩
        have hx : (residueLine ![0, -(tt * tt)] ![1, s] u) 0 = u := by
          show (![0, -(tt * tt)] 0 : ZMod q) + u * (![1, s] 0) = u
          show (0 : ZMod q) + u * 1 = u
          rw [mul_one, zero_add]
        have hy : (residueLine ![0, -(tt * tt)] ![1, s] u) 1 =
            -(tt * tt) + u * s := by
          show (![0, -(tt * tt)] 1 : ZMod q) + u * (![1, s] 1) =
            -(tt * tt) + u * s
          rfl
        rw [hx, hy]
        refine ⟨u - tt, ?_⟩
        rw [← hst]
        ring
      · -- Vertical representative ![0, 1]: the added column.
        push_neg at h0
        have hrep : dirRep b = ![0, 1] := if_neg (by simpa using h0)
        rw [hrep]
        refine ⟨![0, 0], fun u => ?_⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ?_⟩
        show (![0, (0 : ZMod q)] 0) + u * (![0, 1] 0) = 0
        show (0 : ZMod q) + u * 0 = 0
        rw [mul_zero, add_zero]
    obtain ⟨u, hu, hub⟩ := dirRep_smul_self hb
    rw [← hub]
    exact (carriesLine_smul_iff hu).mpr hkey

/-- Doubled size of the construction, subtraction-free:
`2·|W| + 1 = q² + 2q`. -/
theorem two_mul_planeWitness_card (hq2 : q ≠ 2) :
    2 * (planeWitness q).card + 1 = q * q + 2 * q := by
  classical
  -- Column-by-column count.
  have hfw : (planeWitness q).card = ∑ x ∈ (Finset.univ : Finset (ZMod q)),
      ((planeWitness q).filter (fun p => p 0 = x)).card :=
    Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ _)
  -- The zero column is full.
  have hfiber0 : ((planeWitness q).filter (fun p => p 0 = 0)).card = q := by
    rw [show ((planeWitness q).filter (fun p => p 0 = 0)).card =
        ((Finset.univ : Finset (ZMod q))).card from ?_, Finset.card_univ,
      ZMod.card]
    refine Finset.card_bij' (fun p _ => p 1) (fun y _ => ![(0 : ZMod q), y])
      ?_ ?_ ?_ ?_
    · intro p _
      exact Finset.mem_univ _
    · intro y _
      refine Finset.mem_filter.mpr ⟨?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr rfl⟩
    · intro p hp
      exact plane_point_ext ((Finset.mem_filter.mp hp).2.symm) rfl
    · intro y _
      rfl
  -- Every other column has exactly the squares' worth of points.
  have hfiberx : ∀ x : ZMod q, x ≠ 0 →
      ((planeWitness q).filter (fun p => p 0 = x)).card =
      ((Finset.univ : Finset (ZMod q)).filter (fun a => IsSquare a)).card := by
    intro x hx
    refine Finset.card_bij' (fun p _ => x * x - p 1)
      (fun a _ => ![x, x * x - a]) ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨hpw, hp0⟩ := Finset.mem_filter.mp hp
      obtain ⟨-, hpred⟩ := Finset.mem_filter.mp hpw
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases hpred with h | h
      · rwa [hp0] at h
      · exact absurd (hp0 ▸ h) hx
    · intro a ha
      obtain ⟨-, hsq⟩ := Finset.mem_filter.mp ha
      refine Finset.mem_filter.mpr ⟨?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ?_⟩
      show IsSquare (x * x - (x * x - a))
      rwa [sub_sub_cancel]
    · intro p hp
      refine plane_point_ext ((Finset.mem_filter.mp hp).2.symm) ?_
      show x * x - (x * x - p 1) = p 1
      rw [sub_sub_cancel]
    · intro a _
      show x * x - (![x, x * x - a] 1) = a
      show x * x - (x * x - a) = a
      rw [sub_sub_cancel]
  -- Assemble.
  have hrest : ∑ x ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      ((planeWitness q).filter (fun p => p 0 = x)).card =
      (q - 1) * ((Finset.univ : Finset (ZMod q)).filter
        (fun a => IsSquare a)).card := by
    rw [Finset.sum_congr rfl
      (fun x hx => hfiberx x (Finset.ne_of_mem_erase hx)),
      Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem
        (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  have hW : (planeWitness q).card = q + (q - 1) *
      ((Finset.univ : Finset (ZMod q)).filter
        (fun a => IsSquare a)).card := by
    rw [hfw, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q)),
      hfiber0, hrest]
  have h2s := two_mul_card_squares (q := q) hq2
  have hq1 : 1 ≤ q := (Fact.out : q.Prime).one_lt.le
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 :=
    ⟨q - 1, (Nat.succ_pred_eq_of_pos hq1).symm⟩
  rw [hW]
  have hsub : q' + 1 - 1 = q' := rfl
  rw [hsub]
  have hexp : 2 * ((q' + 1) + q' * ((Finset.univ : Finset (ZMod (q' + 1))).filter
      (fun a => IsSquare a)).card) + 1 =
      2 * (q' + 1) + q' * (2 * ((Finset.univ : Finset (ZMod (q' + 1))).filter
        (fun a => IsSquare a)).card) + 1 := by ring
  rw [hexp, h2s]
  ring

/-- The construction bounds the minimum: `2·K(q,2) + 1 ≤ q² + 2q`. -/
theorem two_mul_minKakeyaSize_plane_le (hq2 : q ≠ 2) :
    2 * minKakeyaSize q 2 + 1 ≤ q * q + 2 * q := by
  have hle := minKakeyaSize_le_card (planeWitness_isKakeyaSet hq2)
  have := two_mul_planeWitness_card (q := q) hq2
  omega

/-! ### The schema theorem -/

/-- THE PLANE SCHEMA, odd primes: the fractional cost certificate
holds at the true price `K(q,2)`.  The only geometric inputs are the
truncated inclusion–exclusion (partial menus) and the definition of
the minimum (full menu); the only arithmetic input is the
construction bound above. -/
theorem fractionalCostAt_plane_odd (hq2 : q ≠ 2) :
    FractionalCostAt q 2 (nonzeroDirections q 2) (minKakeyaSize q 2) := by
  classical
  intro S
  set m := minKakeyaSize q 2 with hm
  set C := (nonzeroDirections q 2).filter (fun b => CarriesLine S b)
    with hC
  set R := C.image dirRep with hR
  -- Facts about carried directions and their representatives.
  have hCzero : ∀ b ∈ C, b ≠ 0 := by
    intro b hb
    have := (Finset.mem_filter.mp hb).1
    simpa [nonzeroDirections] using this
  have hCcar : ∀ b ∈ C, CarriesLine S b :=
    fun b hb => (Finset.mem_filter.mp hb).2
  have hRrep : ∀ r ∈ R, dirRep r = r := by
    intro r hr
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hr
    exact dirRep_idem b
  have hRne : ∀ r ∈ R, r ≠ 0 := by
    intro r hr
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hr
    exact dirRep_ne_zero b
  have hRcar : ∀ r ∈ R, CarriesLine S r := by
    intro r hr
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hr
    exact (carriesLine_dirRep_iff (hCzero b hb)).mpr (hCcar b hb)
  -- (i) each class has at most q−1 carried vectors
  have hCbound : C.card ≤ (q - 1) * R.card := by
    have hfib : ∀ r ∈ R, (C.filter (fun b => dirRep b = r)).card ≤ q - 1 := by
      intro r hr
      have hsub : C.filter (fun b => dirRep b = r) ⊆
          (lineFinset 0 r).erase 0 := by
        intro b hb
        obtain ⟨hbC, hbrep⟩ := Finset.mem_filter.mp hb
        obtain ⟨u, hu, hub⟩ := dirRep_smul_self (hCzero b hbC)
        rw [hbrep] at hub
        refine Finset.mem_erase.mpr ⟨hCzero b hbC, ?_⟩
        refine Finset.mem_image.mpr ⟨u, Finset.mem_univ _, ?_⟩
        funext i
        simp only [residueLine, Pi.add_apply, Pi.smul_apply,
          Pi.zero_apply, smul_eq_mul, zero_add]
        exact congrFun hub i
      calc (C.filter (fun b => dirRep b = r)).card
          ≤ ((lineFinset 0 r).erase 0).card := Finset.card_le_card hsub
        _ ≤ (lineFinset 0 r).card - 1 :=
            le_of_eq (Finset.card_erase_of_mem ?_)
        _ = q - 1 := by rw [lineFinset_card (hRne r hr)]
      · refine Finset.mem_image.mpr ⟨0, Finset.mem_univ _, ?_⟩
        funext i
        simp [residueLine]
    calc C.card = ∑ r ∈ R, (C.filter (fun b => dirRep b = r)).card :=
          Finset.card_eq_sum_card_fiberwise (fun b hb =>
            Finset.mem_image_of_mem _ hb)
      _ ≤ ∑ _r ∈ R, (q - 1) := Finset.sum_le_sum hfib
      _ = (q - 1) * R.card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- (iii) at most q+1 classes
  have hRle : R.card ≤ q + 1 := card_reps_le hRrep
  -- Case split on whether every class is carried.
  rcases Nat.lt_or_ge R.card (q + 1) with hRlt | hRfull
  · -- k ≤ q: choose witness lines and run Bonferroni.
    have hex : ∀ r ∈ R, ∃ a, lineFinset a r ⊆ S := by
      intro r hr
      obtain ⟨a, ha⟩ := hRcar r hr
      exact ⟨a, lineFinset_subset_iff.mpr ha⟩
    choose f hf using hex
    set U := R.attach.biUnion
      (fun r => lineFinset (f r.1 r.2) r.1) with hU
    have hUS : U ⊆ S := by
      refine Finset.biUnion_subset.mpr ?_
      intro r _
      exact hf r.1 r.2
    have hpair : ∀ i ∈ R.attach, ∀ j ∈ R.attach, i ≠ j →
        ((fun r : {x // x ∈ R} => lineFinset (f r.1 r.2) r.1) i ∩
         (fun r : {x // x ∈ R} => lineFinset (f r.1 r.2) r.1) j).card ≤ 1 := by
      intro i _ j _ hij
      have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      refine lineFinset_inter_card_le_one (hRne i.1 i.2) (hRne j.1 j.2) ?_
      rw [hRrep i.1 i.2, hRrep j.1 j.2]
      exact hne
    have hbon := sum_card_le_card_biUnion_add_choose R.attach
      (fun r => lineFinset (f r.1 r.2) r.1) hpair
    have hsumq : ∑ r ∈ R.attach,
        (lineFinset (f r.1 r.2) r.1).card = R.card * q := by
      rw [Finset.sum_congr rfl (fun r _ => lineFinset_card (hRne r.1 r.2)),
        Finset.sum_const, smul_eq_mul, Finset.card_attach]
    rw [hsumq, Finset.card_attach] at hbon
    -- Doubled choose identity: 2·C(k,2) = k(k−1).
    have hchoose : 2 * Nat.choose R.card 2 = R.card * (R.card - 1) := by
      rw [Nat.choose_two_right]
      have hev : Even (R.card * (R.card - 1)) := by
        rcases Nat.eq_zero_or_pos R.card with h0 | hpos
        · rw [h0]
          simp
        · have hpred : R.card - 1 + 1 = R.card := Nat.succ_pred_eq_of_pos hpos
          have h := Nat.even_mul_succ_self (R.card - 1)
          rwa [hpred, mul_comm] at h
      exact Nat.two_mul_div_two_of_even hev
    -- Assemble the k ≤ q case arithmetically (over ℤ for comfort).
    have hUcard : U.card ≤ S.card := Finset.card_le_card hUS
    have hmenu : (nonzeroDirections q 2).card + 1 = q * q := by
      have hz : nonzeroDirections q 2 =
          (Finset.univ : Finset (ResiduePoint q 2)).erase 0 := by
        ext b
        simp [nonzeroDirections, Finset.mem_erase, and_comm]
      rw [hz, Finset.card_erase_add_one (Finset.mem_univ _),
        Finset.card_univ]
      rw [show Fintype.card (ResiduePoint q 2) = q ^ 2 from ?_]
      · ring
      · rw [show Fintype.card (ResiduePoint q 2) =
            Fintype.card (ZMod q) ^ Fintype.card (Fin 2) from
            Fintype.card_fun]
        rw [ZMod.card, Fintype.card_fin]
    have hkq : R.card ≤ q := by omega
    have hmconstr := two_mul_minKakeyaSize_plane_le (q := q) hq2
    rcases Nat.eq_zero_or_pos R.card with hk0 | hkpos
    · -- No carried directions at all.
      have : C.card = 0 := by
        have := hCbound
        rw [hk0, mul_zero] at this
        omega
      rw [this, zero_mul]
      exact Nat.zero_le _
    · -- 1 ≤ k ≤ q: the Bonferroni chain.
      -- Notation for the integer computation.
      set k := R.card with hkdef
      set u := U.card
      set sc := S.card
      set D := (nonzeroDirections q 2).card
      -- Key inequality: k · 2m ≤ 2 · sc · (q + 1).
      have hkey : k * (2 * m) ≤ 2 * sc * (q + 1) := by
        -- doubled Bonferroni: 2kq ≤ 2u + k(k−1) ≤ 2sc + k(k−1)
        have hbon2 : 2 * (k * q) ≤ 2 * sc + k * (k - 1) := by
          have h1 : 2 * (k * q) ≤ 2 * u + 2 * Nat.choose k 2 := by omega
          rw [hchoose] at h1
          omega
        have hk1 : 1 ≤ k := hkpos
        have hZbon : (2 : ℤ) * (k * q) ≤ 2 * sc + k * ((k : ℤ) - 1) := by
          zify [hk1] at hbon2
          linarith
        have hZm : (2 : ℤ) * m ≤ q * q + 2 * q - 1 := by
          zify at hmconstr
          linarith
        have hZk : (k : ℤ) ≤ q := by exact_mod_cast hkq
        have hZk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
        have hZq0 : (0 : ℤ) ≤ (q : ℤ) + 1 := by positivity
        have hZk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk1
        have hpoly : (k : ℤ) * (q * q + 2 * q - 1) +
            (q + 1) * (k * ((k : ℤ) - 1)) ≤ (q + 1) * (2 * (k * q)) := by
          nlinarith [mul_nonneg hZk0 (mul_nonneg hZq0 (sub_nonneg.mpr hZk))]
        have hZgoal : (k : ℤ) * (2 * m) ≤ 2 * sc * (q + 1) := by
          have s1 : (k : ℤ) * (2 * m) ≤ k * (q * q + 2 * q - 1) :=
            mul_le_mul_of_nonneg_left hZm hZk0
          have s2 : ((q : ℤ) + 1) * (2 * (k * q)) ≤
              (q + 1) * (2 * sc + k * ((k : ℤ) - 1)) :=
            mul_le_mul_of_nonneg_left hZbon hZq0
          nlinarith [s1, s2, hpoly]
        exact_mod_cast hZgoal
      -- From the key inequality to the certificate inequality.
      have hCk : C.card ≤ (q - 1) * k := hCbound
      have hDq : D + 1 = q * q := hmenu
      -- 2·(C·m) ≤ (q−1)·(k·2m) ≤ (q−1)·2sc(q+1) = 2·sc·D
      have hq1 : 1 ≤ q := (Fact.out : q.Prime).one_lt.le
      have hfinal : 2 * (C.card * m) ≤ 2 * (sc * D) := by
        have h1 : 2 * (C.card * m) ≤ (q - 1) * (k * (2 * m)) := by
          calc 2 * (C.card * m) = C.card * (2 * m) := by ring
            _ ≤ ((q - 1) * k) * (2 * m) :=
                Nat.mul_le_mul_right _ hCk
            _ = (q - 1) * (k * (2 * m)) := by ring
        have h2 : (q - 1) * (k * (2 * m)) ≤ (q - 1) * (2 * sc * (q + 1)) :=
          Nat.mul_le_mul_left _ hkey
        have h3 : (q - 1) * (2 * sc * (q + 1)) = 2 * (sc * ((q-1)*(q+1))) := by
          ring
        have h4 : (q - 1) * (q + 1) = D := by
          obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 :=
            ⟨q - 1, (Nat.succ_pred_eq_of_pos hq1).symm⟩
          have hsq : (q' + 1) * (q' + 1) = q' * (q' + 2) + 1 := by ring
          have hsub : (q' + 1 - 1) * (q' + 1 + 1) = q' * (q' + 2) := by
            simp
          omega
        calc 2 * (C.card * m) ≤ (q - 1) * (k * (2 * m)) := h1
          _ ≤ (q - 1) * (2 * sc * (q + 1)) := h2
          _ = 2 * (sc * ((q - 1) * (q + 1))) := h3
          _ = 2 * (sc * D) := by rw [h4]
      omega
  · -- k = q+1: every class is carried, so S is Kakeya and the
    -- minimum prices it by definition.
    have hRcard : R.card = q + 1 := le_antisymm hRle hRfull
    have hinj : Set.InjOn slopeOf (R : Set (ResiduePoint q 2)) := by
      intro r hr r' hr' h
      have := dirRep_eq_of_slopeOf_eq h
      rwa [hRrep r hr, hRrep r' hr'] at this
    have himg : R.image slopeOf =
        (Finset.univ : Finset (Option (ZMod q))) := by
      refine Finset.eq_univ_of_card _ ?_
      rw [Finset.card_image_of_injOn hinj, hRcard,
        Fintype.card_option, ZMod.card]
    have hSkak : IsKakeyaSet S := by
      intro b
      by_cases hb : b = 0
      · subst hb
        obtain ⟨r, hr⟩ := Finset.card_pos.mp (by omega : 0 < R.card)
        obtain ⟨a, ha⟩ := hRcar r hr
        refine ⟨a, fun t => ?_⟩
        have hline : residueLine a 0 t = a := by
          funext i
          simp [residueLine]
        rw [hline]
        have := ha 0
        rwa [residueLine_zero] at this
      · have hmem : slopeOf (dirRep b) ∈ R.image slopeOf := by
          rw [himg]
          exact Finset.mem_univ _
        obtain ⟨r, hr, hsl⟩ := Finset.mem_image.mp hmem
        have hrb : r = dirRep b := by
          have := dirRep_eq_of_slopeOf_eq hsl
          rwa [hRrep r hr, dirRep_idem] at this
        have hcar : CarriesLine S (dirRep b) := hrb ▸ hRcar r hr
        exact (carriesLine_dirRep_iff hb).mp hcar
    have hms : m ≤ S.card := minKakeyaSize_le_card hSkak
    calc C.card * m ≤ (nonzeroDirections q 2).card * S.card :=
          Nat.mul_le_mul (Finset.card_filter_le _ _) hms
      _ = S.card * (nonzeroDirections q 2).card := Nat.mul_comm _ _

/-- THE PLANE SCHEMA, all primes: the certificate holds at the true
price for every prime modulus (the even prime by the kernel check of
the first certificate section). -/
theorem fractionalCostAt_plane (p : ℕ) [Fact p.Prime] :
    FractionalCostAt p 2 (nonzeroDirections p 2) (minKakeyaSize p 2) := by
  by_cases hp2 : p = 2
  · subst hp2
    rw [minKakeyaSize_two_two]
    exact fractionalCostAt_two_two
  · exact fractionalCostAt_plane_odd hp2

/-- The nonzero menu is nonempty for every prime modulus. -/
theorem nonzeroDirections_nonempty_of_prime (p : ℕ) [Fact p.Prime] :
    (nonzeroDirections p 2).Nonempty := by
  refine ⟨![1, 0], ?_⟩
  simp only [nonzeroDirections, Finset.mem_filter, Finset.mem_univ,
    true_and]
  intro h
  have h0 := congrFun h 0
  simp at h0

/-- Modulus one has minimum one: the singleton space is Kakeya. -/
theorem minKakeyaSize_modulus_one (n : ℕ) : minKakeyaSize 1 n = 1 := by
  refine le_antisymm ?_ (one_le_minKakeyaSize 1 n)
  have h := minKakeyaSize_le_card (univ_isKakeyaSet 1 n)
  have hcard : (Finset.univ : Finset (ResiduePoint 1 n)).card = 1 := by
    rw [Finset.card_univ]
    rw [show Fintype.card (ResiduePoint 1 n) =
        Fintype.card (ZMod 1) ^ Fintype.card (Fin n) from Fintype.card_fun]
    simp
  rwa [hcard] at h

/--
FULL MULTIPLICATIVITY IN THE PLANE: for every squarefree modulus the
Kakeya minimum is the product of the prime minima —
`K(N,2) = ∏_{p ∣ N} K(p,2)`.
-/
theorem minKakeyaSize_squarefree_dim_two :
    ∀ N : ℕ, Squarefree N →
      minKakeyaSize N 2 = ∏ p ∈ N.primeFactors, minKakeyaSize p 2 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    have hN0 : N ≠ 0 := hN.ne_zero
    rcases eq_or_ne N 1 with rfl | hN1
    · simp [minKakeyaSize_modulus_one]
    · -- peel off the least prime factor
      have hp : N.minFac.Prime := Nat.minFac_prime hN1
      set p := N.minFac with hpdef
      set M := N / p with hMdef
      have hNpM : N = p * M := by
        rw [hMdef, mul_comm]
        exact (Nat.div_mul_cancel (Nat.minFac_dvd N)).symm
      have hM0 : M ≠ 0 := by
        intro h
        rw [h, mul_zero] at hNpM
        exact hN0 hNpM
      have hMsq : Squarefree M := hN.squarefree_of_dvd ⟨p, by
        rw [hNpM]; ring⟩
      have hpM : ¬ p ∣ M := by
        intro hdvd
        have hsq : p * p ∣ N := by
          rw [hNpM]
          exact mul_dvd_mul_left p hdvd
        have := hN p hsq
        exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)
      have hcop : Nat.Coprime p M :=
        (Nat.Prime.coprime_iff_not_dvd hp).mpr hpM
      have hMlt : M < N := by
        rw [hNpM]
        exact (Nat.lt_mul_iff_one_lt_left (Nat.pos_of_ne_zero hM0)).mpr
          hp.one_lt
      haveI : NeZero M := ⟨hM0⟩
      haveI : Fact p.Prime := ⟨hp⟩
      have heq := minKakeyaSize_mul_eq_of_fractionalCostAt
        (N₁ := p) (N₂ := M) (n := 2) hcop
        (nonzeroDirections_nonempty_of_prime p)
        (fractionalCostAt_plane p)
      have hihM := ih M hMlt hMsq
      have hpnot : p ∉ M.primeFactors := fun hmem =>
        hpM (Nat.dvd_of_mem_primeFactors hmem)
      have hpf : N.primeFactors = insert p M.primeFactors := by
        rw [hNpM, Nat.primeFactors_mul hp.ne_zero hM0,
          Nat.Prime.primeFactors hp, Finset.singleton_union]
      rw [hpf, Finset.prod_insert hpnot, ← hihM, hNpM, heq]

end PlaneSchema


end KakeyaMultiplicativity
