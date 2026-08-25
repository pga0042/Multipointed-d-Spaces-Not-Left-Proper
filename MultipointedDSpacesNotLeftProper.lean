import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-!
# The q-model structure of multipointed d-spaces is not left proper

This file formalizes the logical and topological core of the counterexample in
P. Gaucher's note on the failure of left properness for multipointed
`d`-spaces.  It is written for Lean 4.33.1 and mathlib v4.33.1.

Mathlib does not currently define multipointed `d`-spaces, the interval
reparametrization categories `G` and `M`, or their q-model structures.  We
therefore isolate the paper-specific input in `GlobularCounterexample`.  Its
fields are exactly the assertions supplied by the construction in the paper:

* the attaching square is a pushout;
* its left vertical map is a cofibration;
* its upper horizontal map is a q-weak equivalence;
* the two distinguished paths are separated before the pushout map by the
  continuous, two-valued maximum invariant;
* they are joined after applying the pushout map.

No field asserts the desired conclusion.  From these inputs Lean proves that
the pushout map is not a weak equivalence and hence that the model structure is
not left proper.  The point-set formulae used in the explicit homotopy after
the pushout are also checked below.  There are no axioms and no `sorry`s.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Function Set Topology

universe v u w

namespace MultipointedDSpacesNotLeftProper

set_option autoImplicit false

/-! ## Left properness and detection on execution-path spaces -/

/-- A model-category-independent formulation of left properness: every
pushout of a weak equivalence along a cofibration is a weak equivalence. -/
def IsLeftProper {C : Type u} [Category.{v} C]
    (weakEquivalence cofibration : MorphismProperty C) : Prop :=
  ∀ {A B X Y : C} (s : A ⟶ B) (i : A ⟶ X) (j : B ⟶ Y) (t : X ⟶ Y),
    IsPushout s i j t → weakEquivalence s → cofibration i →
      weakEquivalence t

/-- A continuous map is injective on path components precisely when it
reflects the relation `Joined`. -/
def InjectiveOnPathComponents {X Y : TopCat.{w}} (f : X ⟶ Y) : Prop :=
  ∀ x y : X, Joined (f x) (f y) → Joined x y

/-- The map induced by a continuous map on zeroth homotopy sets. -/
def piZeroMap {X Y : TopCat.{w}} (f : X ⟶ Y) :
    ZerothHomotopy X → ZerothHomotopy Y :=
  ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (f x)) fun _ _ p =>
    ZerothHomotopy.sound (p.map f.hom.continuous)

@[simp]
theorem piZeroMap_mk {X Y : TopCat.{w}} (f : X ⟶ Y) (x : X) :
    piZeroMap f (ZerothHomotopy.mk x) = ZerothHomotopy.mk (f x) :=
  rfl

/-- The relational formulation used below really is injectivity of the
induced map on `pi_0`. -/
theorem injective_piZeroMap_iff {X Y : TopCat.{w}} (f : X ⟶ Y) :
    Injective (piZeroMap f) ↔ InjectiveOnPathComponents f := by
  constructor
  · intro hinj x y hxy
    have hmk : ZerothHomotopy.mk (f x) = ZerothHomotopy.mk (f y) :=
      Quotient.sound hxy
    have hmk' : ZerothHomotopy.mk x = ZerothHomotopy.mk y := by
      apply hinj
      simpa only [piZeroMap_mk] using hmk
    exact Quotient.exact hmk'
  · intro hreflect a b hab
    induction a using ZerothHomotopy.rec with
    | mk x =>
      induction b using ZerothHomotopy.rec with
      | mk y =>
        apply Quotient.sound
        apply hreflect x y
        exact Quotient.exact hab

/-- The only consequence of the definition of q-weak equivalence needed by
the counterexample is injectivity on path components of every execution-path
space.  For multipointed `d`-spaces this follows from the characterization of
q-weak equivalences: the state map is bijective and every map of execution-path
spaces is a weak homotopy equivalence. -/
structure ExecutionPathDetector (C : Type u) [Category.{v} C]
    (weakEquivalence : MorphismProperty C) where
  path : C ⥤ TopCat.{w}
  weak_reflects_joined :
    ∀ {X Y : C} (f : X ⟶ Y), weakEquivalence f →
      InjectiveOnPathComponents (path.map f)

/-! ## The elementary separating argument -/

/-- A continuous function taking only the values zero and one cannot take
different values at path-connected points.  This is the intermediate value
argument used for the maximum invariant in the counterexample. -/
theorem not_joined_of_two_valued_continuous
    {Z : Type*} [TopologicalSpace Z] {x y : Z}
    (invariant : Z → ℝ) (hinvariant : Continuous invariant)
    (htwo : ∀ z, invariant z = 0 ∨ invariant z = 1)
    (hx : invariant x = 0) (hy : invariant y = 1) :
    ¬ Joined x y := by
  intro hjoined
  let p : Path x y := hjoined.somePath
  let f : unitInterval → ℝ := fun t => invariant (p t)
  have hf : Continuous f := hinvariant.comp p.continuous
  have hhalf : (1 / 2 : ℝ) ∈ Set.range f := by
    apply intermediate_value_univ (0 : unitInterval) (1 : unitInterval) hf
    constructor
    · simp [f, p, hx]
    · norm_num [f, p, hy]
  rcases hhalf with ⟨t, ht⟩
  rcases htwo (p t) with hzero | hone
  · have : f t = 0 := by simpa [f] using hzero
    linarith
  · have : f t = 1 := by simpa [f] using hone
    linarith

/-! ## Abstracted data of Gaucher's globular counterexample -/

/-- The exact input supplied by the globular cell-attachment construction.

In the application, `A → B` is the inclusion whose old execution paths are
respectively `E_1` and `E_{>0}`; `A → X` is the cobase change of the generating
q-cofibration `Glob_P(∅) → Glob_P(D^0)`; `X → Y` is its pushout along `A → B`;
and `c, cb` are the new circle followed, in the second case, by the old bump
path.  The invariant is the maximum of the old-coordinate projection. -/
structure GlobularCounterexample
    (C : Type u) [Category.{v} C]
    (weakEquivalence cofibration : MorphismProperty C)
    (execution : ExecutionPathDetector C weakEquivalence) where
  A : C
  B : C
  X : C
  Y : C
  s : A ⟶ B
  i : A ⟶ X
  j : B ⟶ Y
  t : X ⟶ Y
  pushout : IsPushout s i j t
  s_is_weakEquivalence : weakEquivalence s
  i_is_cofibration : cofibration i
  c : execution.path.obj X
  cb : execution.path.obj X
  invariant : execution.path.obj X → ℝ
  invariant_continuous : Continuous invariant
  invariant_two_valued : ∀ z, invariant z = 0 ∨ invariant z = 1
  invariant_c : invariant c = 0
  invariant_cb : invariant cb = 1
  joined_after_pushout :
    Joined ((execution.path.map t) c) ((execution.path.map t) cb)

namespace GlobularCounterexample

variable {C : Type u} [Category.{v} C]
variable {weakEquivalence cofibration : MorphismProperty C}
variable {execution : ExecutionPathDetector C weakEquivalence}

/-- Before applying the pushout map, the paths `c` and `cb` lie in distinct
path components. -/
theorem not_joined_before
    (d : GlobularCounterexample C weakEquivalence cofibration execution) :
    ¬ Joined d.c d.cb :=
  not_joined_of_two_valued_continuous
    d.invariant d.invariant_continuous d.invariant_two_valued
      d.invariant_c d.invariant_cb

/-- The pushout map in the globular counterexample is not a weak
equivalence: otherwise injectivity on `pi_0` would reflect the path joining
its two distinguished images. -/
theorem pushout_map_is_not_weak
    (d : GlobularCounterexample C weakEquivalence cofibration execution) :
    ¬ weakEquivalence d.t := by
  intro ht
  apply d.not_joined_before
  exact execution.weak_reflects_joined d.t ht d.c d.cb
    d.joined_after_pushout

/-- The formal non-left-properness theorem. -/
theorem not_leftProper
    (d : GlobularCounterexample C weakEquivalence cofibration execution) :
    ¬ IsLeftProper weakEquivalence cofibration := by
  intro hleft
  apply d.pushout_map_is_not_weak
  exact hleft d.s d.i d.j d.t d.pushout d.s_is_weakEquivalence
    d.i_is_cofibration

end GlobularCounterexample

/-! ## Point-set formulae in the homotopy after the pushout -/

/-- The old bump execution path, written on the ambient real line. -/
def bump (t : ℝ) : ℝ := 4 * t * (1 - t)

/-- The scaled old execution path used in the homotopy. -/
def scaledBump (u t : ℝ) : ℝ := u * bump t

/-- The fraction of the parameter interval assigned to the new circle. -/
def circleLength (u : ℝ) : ℝ := 1 - u / 2

@[simp] theorem bump_zero : bump 0 = 0 := by norm_num [bump]
@[simp] theorem bump_one : bump 1 = 0 := by norm_num [bump]
@[simp] theorem bump_half : bump (1 / 2) = 1 := by norm_num [bump]

/-- The scaled bump is immediately nonconstant for every positive scale. -/
theorem scaledBump_positive {u t : ℝ} (hu : 0 < u)
    (ht0 : 0 < t) (ht1 : t < 1) :
    0 < scaledBump u t := by
  exact mul_pos hu (mul_pos (mul_pos (by norm_num) ht0) (sub_pos.mpr ht1))

@[simp]
theorem scaledBump_half (u : ℝ) : scaledBump u (1 / 2) = u := by
  norm_num [scaledBump, bump]

/-- For the homotopy parameter `u ∈ [0,1]`, the circle occupies a valid
subinterval of length between `1/2` and `1`. -/
theorem circleLength_mem {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    1 / 2 ≤ circleLength u ∧ circleLength u ≤ 1 := by
  constructor <;> dsimp [circleLength] <;> linarith

/-- For positive `u`, the second piece of the homotopy has positive length. -/
theorem circleLength_lt_one {u : ℝ} (hu : 0 < u) :
    circleLength u < 1 := by
  dsimp [circleLength]
  linarith

end MultipointedDSpacesNotLeftProper
