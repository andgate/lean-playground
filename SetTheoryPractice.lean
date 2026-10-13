import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice.Indexed

/-!
# Set Theory Practice (Lean 4 + Mathlib)

A growing collection of named theorem exercises. Work top to bottom.
Replace each `sorry` with a proof. All statements are intended to be true.

How to study with Codex:
* Work on ONE theorem at a time, in the order given.
* Ask for an explanation of the goal and relevant definitions before tactics.
* Ask for the smallest possible hint first. Do not reveal complete proofs
  unless explicitly requested.
* Prefer reusing earlier theorems from `SetPractice` instead of invoking a
  Mathlib theorem that proves the entire exercise in one line.
* When introducing a new tactic, explain exactly how it transforms the goal.
* After a proof succeeds, compare a term-style proof and a tactic-style proof
  where this helps explain propositions-as-types.

Notes:
* `sorry` is intentionally a placeholder, not a completed proof.
* These names are in `SetPractice` to avoid conflicts with Mathlib's names.
* Most exercises are polymorphic in the element type (`α`).
* In classical set identities involving complements, you might need the
  `classical` tactic inside your proof.
* The later chapters deliberately introduce more mathematical machinery.

There's a cheatsheet (`docs/CHEATSHEET.md`) that has
a bunch of helpful information for solving theorems.

-/

namespace SetPractice

universe u v w z
variable {α : Type u} {β : Type v} {γ : Type w} {ι : Type z}

/-! ## 01. Membership, inclusion, and commutativity
Begin by transferring the proofs you've already written. -/

-- 001: Every set is a subset of itself.
theorem subset_refl (A : Set α) : A ⊆ A := by
  intro x hx
  exact hx

-- 002: Subset inclusion is transitive.
theorem subset_trans (A B C : Set α)
    (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
  intro x hx
  exact hBC (hAB hx)

-- Same statement, different proof styles for comparison.

-- A proof term: `fun` is a lambda, like Haskell's `\x -> ...`.
-- The arguments are the element (left unnamed) and its membership proof.
theorem subset_trans_1 (A B C : Set α)
    (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C :=
  fun _ hx => hBC (hAB hx)

-- Work backward from the goal using `apply`.
theorem subset_trans_2 (A B C : Set α)
    (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
  intro x hx
  apply hBC -- Changes the goal from `x ∈ C` to `x ∈ B`.
  exact hAB hx

-- Work forward, giving the intermediate membership proof a name.
theorem subset_trans_3 (A B C : Set α)
    (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
  intro x hx
  have hxB : x ∈ B := hAB hx -- Adds `hxB`; the goal is still `x ∈ C`.
  exact hBC hxB

-- 003: Intersection is contained in its left operand.
theorem inter_subset_left (A B : Set α) : A ∩ B ⊆ A := by
  intro x hx
  exact hx.1

-- 004: Intersection is contained in its right operand.
theorem inter_subset_right (A B : Set α) : A ∩ B ⊆ B := by
  intro x hx
  exact hx.2

-- 005: A set is contained in a union with that set on the left.
theorem subset_union_left (A B : Set α) : A ⊆ A ∪ B := by
  intro x hx
  exact Or.inl hx

-- 006: A set is contained in a union with that set on the right.
theorem subset_union_right (A B : Set α) : B ⊆ A ∪ B := by
  intro x hx
  exact Or.inr hx

-- 007: Inclusion is preserved when union operands are swapped.
theorem union_subset_comm (A B : Set α) : A ∪ B ⊆ B ∪ A := by
  intro x hx
  cases hx with
  | inl hA =>
      exact Or.inr hA
  | inr hB =>
      exact Or.inl hB

-- 008: Inclusion is preserved when intersection operands are swapped.
theorem inter_subset_comm (A B : Set α) : A ∩ B ⊆ B ∩ A := by
  intro x hx
  exact And.intro hx.2 hx.1

-- 009: Two sets are equal if each is a subset of the other.
theorem subset_antisymm (A B : Set α)
    (hAB : A ⊆ B) (hBA : B ⊆ A) : A = B := by
  apply Set.ext
  intro x
  constructor
  · intro hxA
    exact hAB hxA
  · intro hxB
    exact hBA hxB

theorem subset_antisymm_1 (A B : Set α)
    (hAB : A ⊆ B) (hBA : B ⊆ A) : A = B := by
  apply Set.ext
  intro x
  constructor
  · exact hAB (a := x)
  · exact hBA (a := x)

-- 010: Union is commutative. Reuse 007 and 009.
theorem union_comm (A B : Set α) : A ∪ B = B ∪ A := by
  apply subset_antisymm (A ∪ B) (B ∪ A)
  · exact union_subset_comm A B
  · exact union_subset_comm B A

-- 011: Intersection is commutative. Reuse 008 and 009.
theorem inter_comm (A B : Set α) : A ∩ B = B ∩ A := by
  apply subset_antisymm (A ∩ B) (B ∩ A)
  · exact inter_subset_comm A B
  · exact inter_subset_comm B A

/-! ## 02. Building larger set proofs from smaller ones -/

-- 012: If A lies in B and C, then it lies in their intersection.
theorem subset_inter_of_subsets (A B C : Set α)
    (hAB : A ⊆ B) (hAC : A ⊆ C) : A ⊆ B ∩ C := by
  intro _ hx
  exact And.intro (hAB hx) (hAC hx)

-- 013: If A and B lie in C, then their union lies in C.
theorem union_subset_of_subsets (A B C : Set α)
    (hAC : A ⊆ C) (hBC : B ⊆ C) : A ∪ B ⊆ C := by
  intro x hx
  cases hx with
  | inl a =>
      exact hAC a
  | inr b =>
      exact hBC b

-- 014: Intersection is idempotent.
theorem inter_self (A : Set α) : A ∩ A = A := by
  apply subset_antisymm (A ∩ A) A
  · intro x hx
    exact hx.2
  · intro x hx
    exact And.intro hx hx

-- 015: Union is idempotent.
theorem union_self (A : Set α) : A ∪ A = A := by
  sorry

-- 016: A is contained in its intersection with A ∪ B.
theorem subset_inter_union_left (A B : Set α) :
    A ⊆ A ∩ (A ∪ B) := by
  sorry

-- 017: Intersection absorbs union.
theorem inter_union_absorb (A B : Set α) :
    A ∩ (A ∪ B) = A := by
  sorry

-- 018: Union absorbs intersection.
theorem union_inter_absorb (A B : Set α) :
    A ∪ (A ∩ B) = A := by
  sorry

-- 019: Intersection is associative.
theorem inter_assoc (A B C : Set α) :
    (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  sorry

-- 020: Union is associative.
theorem union_assoc (A B C : Set α) :
    (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  sorry

/-! ## 03. Empty and universal sets
Work with `∅` and `Set.univ`. -/

-- 021: The empty set is a subset of every set.
theorem empty_subset (A : Set α) : (∅ : Set α) ⊆ A := by
  sorry

-- 022: Every set is a subset of the universal set.
theorem subset_univ (A : Set α) : A ⊆ Set.univ := by
  sorry

-- 023: No element belongs to the empty set.
theorem not_mem_empty (x : α) : x ∉ (∅ : Set α) := by
  sorry

-- 024: Every element belongs to the universal set.
theorem mem_univ (x : α) : x ∈ (Set.univ : Set α) := by
  sorry

-- 025: Intersecting with the empty set yields the empty set.
theorem inter_empty (A : Set α) : A ∩ ∅ = ∅ := by
  sorry

-- 026: Union with the empty set changes nothing.
theorem union_empty (A : Set α) : A ∪ ∅ = A := by
  sorry

-- 027: Intersecting with the universal set changes nothing.
theorem inter_univ (A : Set α) : A ∩ Set.univ = A := by
  sorry

-- 028: Union with the universal set gives the universal set.
theorem union_univ (A : Set α) : A ∪ Set.univ = Set.univ := by
  sorry

-- 029: The empty set on the left of a union changes nothing.
theorem empty_union (A : Set α) : (∅ : Set α) ∪ A = A := by
  sorry

-- 030: The universal set on the left of an intersection changes nothing.
theorem univ_inter (A : Set α) : Set.univ ∩ A = A := by
  sorry

/-! ## 04. Distributive and order laws -/

-- 031: Intersection distributes over union on the left.
theorem inter_union_distrib_left (A B C : Set α) :
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  sorry

-- 032: Intersection distributes over union on the right.
theorem inter_union_distrib_right (A B C : Set α) :
    (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
  sorry

-- 033: Union distributes over intersection on the left.
theorem union_inter_distrib_left (A B C : Set α) :
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  sorry

-- 034: Union distributes over intersection on the right.
theorem union_inter_distrib_right (A B C : Set α) :
    (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C) := by
  sorry

-- 035: Intersections preserve inclusion of each operand.
theorem inter_mono (A B C D : Set α)
    (hAC : A ⊆ C) (hBD : B ⊆ D) : A ∩ B ⊆ C ∩ D := by
  sorry

-- 036: Unions preserve inclusion of each operand.
theorem union_mono (A B C D : Set α)
    (hAC : A ⊆ C) (hBD : B ⊆ D) : A ∪ B ⊆ C ∪ D := by
  sorry

-- 037: Intersection equals its left operand exactly when inclusion holds.
theorem inter_eq_left_iff_subset (A B : Set α) :
    A ∩ B = A ↔ A ⊆ B := by
  sorry

-- 038: Union equals its left operand exactly when reverse inclusion holds.
theorem union_eq_left_iff_subset (A B : Set α) :
    A ∪ B = A ↔ B ⊆ A := by
  sorry

/-! ## 05. Complement and negation
Some proofs use classical logic. Learn what `¬ P` means before this chapter. -/

-- 039: Complement membership means non-membership.
theorem mem_compl_iff (A : Set α) (x : α) :
    x ∈ Aᶜ ↔ x ∉ A := by
  sorry

-- 040: A set and its complement have an empty intersection.
theorem inter_compl (A : Set α) : A ∩ Aᶜ = ∅ := by
  sorry

-- 041: A set and its complement cover the universe.
theorem union_compl (A : Set α) : A ∪ Aᶜ = Set.univ := by
  sorry

-- 042: Complementing twice returns the original set.
theorem compl_compl (A : Set α) : (Aᶜ)ᶜ = A := by
  sorry

-- 043: The complement of the empty set is universal.
theorem compl_empty : (∅ : Set α)ᶜ = Set.univ := by
  sorry

-- 044: The complement of the universal set is empty.
theorem compl_univ : (Set.univ : Set α)ᶜ = ∅ := by
  sorry

-- 045: De Morgan's law for a union.
theorem compl_union (A B : Set α) :
    (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  sorry

-- 046: De Morgan's law for an intersection.
theorem compl_inter (A B : Set α) :
    (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  sorry

-- 047: Complement reverses subset inclusion.
theorem compl_subset_compl (A B : Set α) (h : A ⊆ B) :
    Bᶜ ⊆ Aᶜ := by
  sorry

-- 048: Being disjoint is equivalent to subset inclusion in a complement.
theorem subset_compl_iff_inter_empty (A B : Set α) :
    A ⊆ Bᶜ ↔ A ∩ B = ∅ := by
  sorry

/-! ## 06. Set difference
Here `A \\ B` means elements of A not in B. -/

-- 049: Membership in a difference is membership plus non-membership.
theorem mem_diff_iff (A B : Set α) (x : α) :
    x ∈ A \ B ↔ x ∈ A ∧ x ∉ B := by
  sorry

-- 050: A difference is contained in its left operand.
theorem diff_subset (A B : Set α) : A \ B ⊆ A := by
  sorry

-- 051: Subtracting a set from itself gives the empty set.
theorem diff_self (A : Set α) : A \ A = ∅ := by
  sorry

-- 052: Subtracting the empty set changes nothing.
theorem diff_empty (A : Set α) : A \ ∅ = A := by
  sorry

-- 053: Subtracting anything from the empty set stays empty.
theorem empty_diff (A : Set α) : (∅ : Set α) \ A = ∅ := by
  sorry

-- 054: Subtracting the universal set yields the empty set.
theorem diff_univ (A : Set α) : A \ Set.univ = ∅ := by
  sorry

-- 055: Difference is intersection with complement.
theorem diff_eq_inter_compl (A B : Set α) :
    A \ B = A ∩ Bᶜ := by
  sorry

-- 056: Difference distributes over a union in the right operand.
theorem diff_union (A B C : Set α) :
    A \ (B ∪ C) = (A \ B) ∩ (A \ C) := by
  sorry

-- 057: Difference distributes over an intersection in the right operand.
theorem diff_inter (A B C : Set α) :
    A \ (B ∩ C) = (A \ B) ∪ (A \ C) := by
  sorry

-- 058: Repeated subtraction combines the excluded sets.
theorem diff_diff (A B C : Set α) :
    (A \ B) \ C = A \ (B ∪ C) := by
  sorry

/-! ## 07. Images and preimages of functions
Read `f '' A` as image, `f ⁻¹' B` as preimage. -/

-- 059: Preimage membership is function application.
theorem mem_preimage_iff (f : α → β) (B : Set β) (x : α) :
    x ∈ f ⁻¹' B ↔ f x ∈ B := by
  sorry

-- 060: A preimage preserves the empty set.
theorem preimage_empty (f : α → β) :
    f ⁻¹' (∅ : Set β) = ∅ := by
  sorry

-- 061: A preimage preserves the universal set.
theorem preimage_univ (f : α → β) :
    f ⁻¹' (Set.univ : Set β) = Set.univ := by
  sorry

-- 062: A preimage preserves intersections.
theorem preimage_inter (f : α → β) (B C : Set β) :
    f ⁻¹' (B ∩ C) = (f ⁻¹' B) ∩ (f ⁻¹' C) := by
  sorry

-- 063: A preimage preserves unions.
theorem preimage_union (f : α → β) (B C : Set β) :
    f ⁻¹' (B ∪ C) = (f ⁻¹' B) ∪ (f ⁻¹' C) := by
  sorry

-- 064: A preimage preserves complements.
theorem preimage_compl (f : α → β) (B : Set β) :
    f ⁻¹' Bᶜ = (f ⁻¹' B)ᶜ := by
  sorry

-- 065: A preimage preserves differences.
theorem preimage_diff (f : α → β) (B C : Set β) :
    f ⁻¹' (B \ C) = (f ⁻¹' B) \ (f ⁻¹' C) := by
  sorry

-- 066: The image of an empty set is empty.
theorem image_empty (f : α → β) :
    f '' (∅ : Set α) = ∅ := by
  sorry

-- 067: Images preserve unions.
theorem image_union (f : α → β) (A B : Set α) :
    f '' (A ∪ B) = (f '' A) ∪ (f '' B) := by
  sorry

-- 068: Images preserve subset inclusion.
theorem image_mono (f : α → β) (A B : Set α) (h : A ⊆ B) :
    f '' A ⊆ f '' B := by
  sorry

-- 069: Preimages preserve subset inclusion.
theorem preimage_mono (f : α → β) (B C : Set β) (h : B ⊆ C) :
    f ⁻¹' B ⊆ f ⁻¹' C := by
  sorry

-- 070: Every set is contained in the preimage of its image.
theorem subset_preimage_image (f : α → β) (A : Set α) :
    A ⊆ f ⁻¹' (f '' A) := by
  sorry

-- 071: The image of a preimage is contained in the original set.
theorem image_preimage_subset (f : α → β) (B : Set β) :
    f '' (f ⁻¹' B) ⊆ B := by
  sorry

-- 072: Image of intersection is contained in intersection of images.
theorem image_inter_subset (f : α → β) (A B : Set α) :
    f '' (A ∩ B) ⊆ (f '' A) ∩ (f '' B) := by
  sorry

-- 073: Injectivity makes the previous inclusion an equality.
theorem image_inter_of_injective (f : α → β) (hf : Function.Injective f)
    (A B : Set α) : f '' (A ∩ B) = (f '' A) ∩ (f '' B) := by
  sorry

-- 074: Image of the universal set is the function's range.
theorem image_univ_eq_range (f : α → β) :
    f '' (Set.univ : Set α) = Set.range f := by
  sorry

-- 075: Images compose in the expected order.
theorem image_comp (f : α → β) (g : β → γ) (A : Set α) :
    (g ∘ f) '' A = g '' (f '' A) := by
  sorry

-- 076: Preimages reverse the order of composition.
theorem preimage_comp (f : α → β) (g : β → γ) (C : Set γ) :
    (g ∘ f) ⁻¹' C = f ⁻¹' (g ⁻¹' C) := by
  sorry

/-! ## 08. Indexed families of sets (optional stretch)
`⋃ i, F i` is a union over all indices; `⋂ i, F i` is an intersection.
These connect set theory with `∃` and `∀`. -/

-- 077: Membership in an indexed union is an existential statement.
theorem mem_iUnion_iff (F : ι → Set α) (x : α) :
    x ∈ (⋃ i, F i) ↔ ∃ i, x ∈ F i := by
  sorry

-- 078: Membership in an indexed intersection is a universal statement.
theorem mem_iInter_iff (F : ι → Set α) (x : α) :
    x ∈ (⋂ i, F i) ↔ ∀ i, x ∈ F i := by
  sorry

-- 079: Each member of a family is inside the family's union.
theorem subset_iUnion (F : ι → Set α) (i : ι) :
    F i ⊆ ⋃ j, F j := by
  sorry

-- 080: The family's intersection is contained in each member.
theorem iInter_subset (F : ι → Set α) (i : ι) :
    (⋂ j, F j) ⊆ F i := by
  sorry

-- 081: A common upper bound contains the indexed union.
theorem iUnion_subset_of_forall (F : ι → Set α) (A : Set α)
    (h : ∀ i, F i ⊆ A) : (⋃ i, F i) ⊆ A := by
  sorry

-- 082: A common lower bound lies in the indexed intersection.
theorem subset_iInter_of_forall (F : ι → Set α) (A : Set α)
    (h : ∀ i, A ⊆ F i) : A ⊆ ⋂ i, F i := by
  sorry

-- 083: Preimages preserve arbitrary indexed unions.
theorem preimage_iUnion (f : α → β) (F : ι → Set β) :
    f ⁻¹' (⋃ i, F i) = ⋃ i, f ⁻¹' (F i) := by
  sorry

-- 084: Preimages preserve arbitrary indexed intersections.
theorem preimage_iInter (f : α → β) (F : ι → Set β) :
    f ⁻¹' (⋂ i, F i) = ⋂ i, f ⁻¹' (F i) := by
  sorry

-- 085: Intersection distributes over arbitrary indexed union.
theorem inter_iUnion (A : Set α) (F : ι → Set α) :
    A ∩ (⋃ i, F i) = ⋃ i, (A ∩ F i) := by
  sorry

-- 086: Union distributes over arbitrary indexed intersection.
theorem union_iInter (A : Set α) (F : ι → Set α) :
    A ∪ (⋂ i, F i) = ⋂ i, (A ∪ F i) := by
  sorry

end SetPractice
