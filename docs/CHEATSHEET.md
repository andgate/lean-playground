# Lean 4 + Mathlib Set Theory Cheatsheet

**Companion to `SetPractice` (exercises 001–086)**  
**Purpose:** a reference to consult *while constructing your own proofs*, not an answer key. It intentionally does **not** contain complete proofs for the remaining `sorry`s.

> **The single most useful habit:** look at the current goal (`⊢ ...`), translate it into ordinary logic, and select a tactic that changes that particular logical shape. Read the new goal **after every tactic**.

## Contents

1. [How to read a proof state](#1-how-to-read-a-proof-state)
2. [The set-theory-to-logic dictionary](#2-the-set-theory-to-logic-dictionary)
3. [First tactic to consider: a goal-driven table](#3-first-tactic-to-consider-a-goal-driven-table)
4. [How to use the hypotheses you already have](#4-how-to-use-the-hypotheses-you-already-have)
5. [Large tactic reference: exact transformations](#5-large-tactic-reference-exact-transformations)
6. [Building proof terms directly](#6-building-proof-terms-directly)
7. [Set-specific proof patterns](#7-set-specific-proof-patterns)
8. [Images, preimages, functions, and witnesses](#8-images-preimages-functions-and-witnesses)
9. [Indexed unions and intersections](#9-indexed-unions-and-intersections)
10. [Negation and classical reasoning](#10-negation-and-classical-reasoning)
11. [Worksheet navigation: which skills each exercise tests](#11-worksheet-navigation-which-skills-each-exercise-tests)
12. [Diagnosing common Lean errors](#12-diagnosing-common-lean-errors)
13. [Useful commands, notation, and proof-writing conventions](#13-useful-commands-notation-and-proof-writing-conventions)
14. [Study workflow and further references](#14-study-workflow-and-further-references)

---

## 1. How to read a proof state

A typical state looks like this:

```lean
α : Type u
A B : Set α
hAB : A ⊆ B
x : α
hx : x ∈ A
⊢ x ∈ B
```

| Part | Meaning | What to do with it |
|---|---|---|
| `α : Type u` | `α` is an arbitrary type of elements. | Usually no action needed. |
| `A B : Set α` | `A` and `B` are sets of `α`-elements. | Check that membership statements use the right element type. |
| `hAB : A ⊆ B` | A named *proof* that inclusion holds. | Apply it to a membership proof such as `hx`. |
| `x : α` | A particular, arbitrary element. | Use `x` in membership and function expressions. |
| `hx : x ∈ A` | A proof that `x` belongs to `A`. | It can be passed as an argument to `hAB`. |
| `⊢ x ∈ B` | **Current goal:** construct a proof of `x ∈ B`. | Ask what hypothesis, definition, or lemma produces it. |

The text **above** `⊢` is your *local context*. The text **after** `⊢` is the *target*.

**Lean treats proofs as terms.** A term `h : P → Q` is a function taking a proof of `P` and returning a proof of `Q`; `h hp` is a proof of `Q` if `hp : P`. This is why `hAB hx` works.

### A tiny example independent of the worksheet

```lean
example (P Q : Prop) (hp : P) (hpq : P → Q) : Q := by
  exact hpq hp
```

The same proof, working backward:

```lean
example (P Q : Prop) (hp : P) (hpq : P → Q) : Q := by
  apply hpq  -- New goal: P
  exact hp
```

`exact` supplies the *whole* proof; `apply` can leave obligations for you to prove.

---

## 2. The set-theory-to-logic dictionary

Mathlib's `Set α` is essentially a predicate `α → Prop`. Under the hood, membership `x ∈ A` means the proposition `A x`. Consequently, ordinary set identities are usually logical identities **element by element**.

### Ordinary sets

| Mathematical notation | Lean notation | What membership or inclusion really means | Logical shape |
|---|---|---|---|
| Membership | `x ∈ A` | `A x` | Proposition |
| Non-membership | `x ∉ A` | `¬ (x ∈ A)` | Negation |
| Subset | `A ⊆ B` | `∀ ⦃x⦄, x ∈ A → x ∈ B` | Universal + implication |
| Equality of sets | `A = B` | Prove `∀ x, x ∈ A ↔ x ∈ B` using extensionality | Two implications |
| Intersection | `A ∩ B` | `x ∈ A ∧ x ∈ B` | `And` |
| Union | `A ∪ B` | `x ∈ A ∨ x ∈ B` | `Or` |
| Empty set | `(∅ : Set α)` | `False` | Impossible case |
| Universal set | `(Set.univ : Set α)` | `True` | Trivial case |
| Complement | `Aᶜ` | `¬ (x ∈ A)` | Negation |
| Difference | `A \ B` | `x ∈ A ∧ x ∉ B` | Conjunction + negation |
| Set comprehension | `{x \| P x}` | `P x` | A predicate |

**Important:** `↔` is logical equivalence between *propositions*; `=` is equality between *objects* (including sets). Extensionality connects set equality to membership equivalence.

### Functions and indexed families

| Notation | Element-level meaning | The main proof idea |
|---|---|---|
| `x ∈ f ⁻¹' B` | `f x ∈ B` | A preimage needs no witness. |
| `y ∈ f '' A` | `∃ x, x ∈ A ∧ f x = y` | An image gives/requires a witness. |
| `y ∈ Set.range f` | `∃ x, f x = y` | Like an image without a domain-membership obligation. |
| `Function.Injective f` | `∀ ⦃x y⦄, f x = f y → x = y` | Equal outputs imply equal inputs. |
| `x ∈ (⋃ i, F i)` | `∃ i, x ∈ F i` | Indexed union = existential quantifier. |
| `x ∈ (⋂ i, F i)` | `∀ i, x ∈ F i` | Indexed intersection = universal quantifier. |
| `(g ∘ f) x` | `g (f x)` | Read composition **right to left**. |

**Do not memorize these as arbitrary syntax.** Translate into logic whenever you are stuck.

---

## 3. First tactic to consider: a goal-driven table

In this table, `P`, `Q`, `R` are propositions; `x`, `w`, and `i` are elements or indices.

| Current goal | Good first move | What the goal changes into / why |
|---|---|---|
| `P → Q` | `intro hp` | Adds `hp : P`; goal becomes `Q`. |
| `∀ x, P x` | `intro x` | Adds arbitrary `x`; goal becomes `P x`. |
| `A ⊆ B` | `intro x hx` | Adds `x` and `hx : x ∈ A`; goal becomes `x ∈ B`. |
| `P ∧ Q` | `constructor` | Produces two goals: `P` and `Q`. |
| `P ↔ Q` | `constructor` | Produces `P → Q` and `Q → P`. |
| `P ∨ Q` | `left` or `right` | Choose to prove `P` or `Q`, respectively. |
| `∃ x, P x` | `use w` | Choose witness `w`; goal becomes `P w`. |
| `∃ x, P x` | `refine ⟨w, ?_⟩` | Same witness choice with an explicit proof hole. |
| `¬ P` | `intro hp` | Adds `hp : P`; goal becomes `False`. |
| `False` | `exact hfalse` if available | An existing proof of `False` closes it. |
| `True` | `trivial` | Closes a goal of `True`. |
| `t = t` | `rfl` | Closes equality by reflexivity (also handles definitional equality). |
| `A = B`, with sets | `ext x` | Goal typically becomes `x ∈ A ↔ x ∈ B`. |
| `A = B`, with sets | `apply subset_antisymm A B` | Uses **your earlier theorem**; generates the two subset goals. |
| `f = g`, with functions | `funext x` | Goal becomes `f x = g x`. |
| `P`, and `h : P` | `exact h` | Closes the current goal. |
| `Q`, and `h : P → Q` | `apply h` | Reduces the goal to `P`. |
| `x ∈ A ∩ B` | `constructor` | Must prove `x ∈ A` and `x ∈ B`. |
| `x ∈ A ∪ B` | `left` or `right` | Must prove membership on your chosen side. |
| `x ∈ A \ B` | `constructor` | Must prove `x ∈ A` and `x ∉ B`. |
| `x ∈ Aᶜ` | `intro hxA` | Must derive a contradiction from `hxA : x ∈ A`. |
| `y ∈ f '' A` | `use w` | Need `w ∈ A` and `f w = y`. |
| `x ∈ f ⁻¹' B` | `change f x ∈ B` | Exposes the definition of preimage membership. |
| `x ∈ ⋃ i, F i` | `use i` | Need `x ∈ F i` for one index `i`. |
| `x ∈ ⋂ i, F i` | `intro i` | Must show `x ∈ F i` for arbitrary `i`. |
| `P` with known equivalence `h : P ↔ Q` | `apply h.mpr` (if proving `P`) | Changes goal to `Q`. `h.mp` proves `Q` from `P`. |

**Choosing a side (`left`/`right`) is a commitment:** you need a reason that side can be established. If you only know `h : P ∨ Q`, **split the hypothesis** instead (`rcases h with hp \| hq`).

---

## 4. How to use the hypotheses you already have

The shape of a **hypothesis** often determines the next move just as strongly as the shape of the goal.

| What you have | Tactic or term | Result / meaning |
|---|---|---|
| `h : P ∧ Q` | `rcases h with ⟨hp, hq⟩` | Adds `hp : P` and `hq : Q`. |
| `h : P ∧ Q` | `h.1`, `h.2` | Directly access proofs of `P` and `Q`. |
| `h : P ∨ Q` | `rcases h with hp \| hq` | Two branches: one with `hp : P`, one with `hq : Q`. |
| `h : P ∨ Q` | `cases h with \| inl hp => ... \| inr hq => ...` | An explicit alternative to `rcases`. |
| `h : ∃ x, P x` | `rcases h with ⟨w, hw⟩` | Obtains witness `w` and proof `hw : P w`. |
| `h : ∃ x, P x ∧ Q x` | `rcases h with ⟨w, hp, hq⟩` | Gets the witness and both conjuncts. |
| `h : ∀ x, P x` | `have hw := h w` | Produces the instance `P w`. |
| `h : P → Q`, `hp : P` | `have hq := h hp` | Produces `hq : Q`. |
| `h : P ↔ Q`, `hp : P` | `have hq := h.mp hp` | Forward direction. |
| `h : P ↔ Q`, `hq : Q` | `have hp := h.mpr hq` | Backward direction. |
| `h : ¬ P`, `hp : P` | `exact h hp` (goal `False`) | Applies the negation as a function `P → False`. |
| `h : False` | `cases h` | Discharges any goal: an impossible case. |
| `h : a = b` | `rw [h]` | Rewrites `a` to `b` in the goal where matching. |
| `h : a = b` | `rw [h] at ha` | Rewrites a separate hypothesis `ha`. |
| `h : a = b` | `rw [← h]` | Rewrites in the reverse direction. |
| `h : f x = f y`, `hf : Function.Injective f` | `have hxy := hf h` | Gets `x = y` from injectivity. |
| `h : x ∈ A ∩ B` | `h.1`, `h.2` | Extract membership in each part. |
| `h : x ∈ A ∪ B` | `rcases h with ha \| hb` | Split by which set contains `x`. |
| `h : x ∈ A \ B` | `h.1`, `h.2` | Extract `x ∈ A` and `x ∉ B`. |
| `h : x ∈ Aᶜ` | Use it as `x ∈ A → False` | A membership proof in `A` would contradict it. |
| `h : y ∈ f '' A` | `rcases h with ⟨x, hxA, hfx⟩` | `x ∈ A`, `f x = y`. |
| `h : x ∈ ⋃ i, F i` | `rcases h with ⟨i, hi⟩` | Obtain a specific index and its membership proof. |
| `h : x ∈ ⋂ i, F i` | `have hi := h i` | Obtain membership for the desired index. |

`rcases` patterns correspond to logical constructors:

| Pattern | Means |
|---|---|
| `⟨ha, hb⟩` | Unpack a conjunction or a witness with its proof. |
| `ha \| hb` | Split a disjunction into two cases. |
| `⟨ha, hb \| hc⟩` | Unpack a conjunction and split a disjunction nested inside it. |
| `⟨w, hw, heq⟩` | Unpack a witness, a condition, and an equality. |
| `_` | Ignore a component you do not need. |

**Direction matters:** a proof of `A ⊆ B` converts `x ∈ A` into `x ∈ B`. It does **not** convert membership in `B` back into membership in `A`.

---

## 5. Large tactic reference: exact transformations

### A. Core proof construction

| Tactic / syntax | Example | Exact effect | Typical use |
|---|---|---|---|
| `intro` | `intro x hx` | Introduces the next bound variable(s) / implication premise(s). | Inclusion, universal quantifiers, negation. |
| `rintro` | `rintro x ⟨ha, hb⟩` | Introduces arguments and destructures the specified incoming hypothesis. | `A ∩ B ⊆ C`. |
| `exact` | `exact h` | Supplies a term of the goal's type; closes that goal. | You already have the proof. |
| `apply` | `apply h` | Matches the conclusion of `h` to your goal; makes its necessary premises subgoals. | Work backward through an implication or theorem. |
| `refine` | `refine ⟨?_, ?_⟩` | Specifies a partially complete proof term; `?_` are the remaining subgoals. | Precise construction of pairs or witnesses. |
| `assumption` | `assumption` | Searches the local context for a proof of the goal. | Check whether the goal is already known. |
| `constructor` | `constructor` | Applies a constructor, notably splitting `∧` and `↔` into their proof obligations. | Membership in intersections, two-way equivalence. |
| `left` | `left` | For `P ∨ Q`, changes the goal to `P`. | Prove the left side of a union. |
| `right` | `right` | For `P ∨ Q`, changes the goal to `Q`. | Prove the right side of a union. |
| `use` | `use w` | Supplies the witness for an existential goal and leaves its property to prove. | Images, indexed unions. |
| `exists` | `exists w` | Alternative witness-construction tactic. | Existential goals. |
| `rfl` | `rfl` | Proves equality when sides reduce to the same term. | Reflexive / definitionally equal expressions. |
| `trivial` | `trivial` | Closes elementary goals such as `True` (and other trivial propositions). | Universal-set membership. |
| `change` | `change f x ∈ B` | Replaces the goal with a *definitionally equal* statement. | Reveal the meaning of preimages or set operations. |
| `show` | `show P` | States the goal as a definitionally equal proposition, often for clarity. | Make a logical form visible. |
| `dsimp` | `dsimp` | Performs definitional simplification without theorem-based rewriting. | Reduce definitions. |
| `unfold` | `unfold myDefinition` | Expands a named definition. | Explore how a custom set or function was defined. |

### B. Breaking apart information

| Tactic / syntax | Example | Exact effect | Typical use |
|---|---|---|---|
| `cases` | `cases h with \| inl hp => ... \| inr hq => ...` | Splits a value/proof according to its constructors. | Case analysis for union membership. |
| `rcases` | `rcases h with ⟨x, hx⟩` | Recursively destructures a hypothesis using a pattern. | Extract an image witness. |
| `obtain` | `obtain ⟨x, hx⟩ := h` | Same extraction idea, expressed as a new local binding. | Name an existential witness. |
| `rintro` | `rintro x (ha \| hb)` | Introduces and immediately splits an incoming disjunction. | Concise branches in subset proofs. |
| `have` | `have hq : Q := hpq hp` | Adds a named intermediate proof; the original goal remains. | Work forward with smaller steps. |
| `have ... := by` | `have hq : Q := by ...` | Creates a local subproof of `Q`; afterward makes `hq` available. | Longer intermediate arguments. |
| `let` | `let y := f x` | Adds a local abbreviation/value. | Name a complicated expression. |
| `specialize` | `specialize h w` | Replaces a universally quantified hypothesis with its instance at `w`. | Instantiate `∀ i, ...`. |
| `rename_i` | `rename_i x hx` | Names inaccessible variables/hypotheses introduced by tactics. | Make auto-generated names meaningful. |
| `clear` | `clear h` | Removes a hypothesis if it is no longer needed. | Keep a large context readable. |
| `revert` | `revert x` | Moves a local variable and its dependent declarations back into the goal as binders. | Generalize or reorder a proof. |

### C. Equality, rewriting, and lemma reuse

| Tactic / syntax | Example | Exact effect | Typical use |
|---|---|---|---|
| `rw` | `rw [h]` | Rewrites matching occurrences in goal using an equality or equivalence. | Convert to a known expression. |
| `rw ... at` | `rw [h] at hx` | Rewrites the specified hypothesis instead of the goal. | Align existing evidence with goal. |
| `rw [← ...]` | `rw [← h]` | Rewrites right-hand side to left-hand side. | Reverse a useful equality. |
| `rwa` | `rwa [h]` | Rewrites, then tries `assumption`. | A rewrite reveals an existing proof. |
| `simp` | `simp` | Repeatedly applies simplification lemmas to goal; may close it. | Routine normalization. |
| `simp at` | `simp at hx` | Simplifies a hypothesis. | Normalize membership facts. |
| `simp only` | `simp only [lemma1, lemma2]` | Restricts simplification to the listed lemmas. | Transparent, educational rewriting. |
| `simpa using` | `simpa using h` | Simplifies the goal and type of `h`, then uses `h`. | Two propositions differ by simplification. |
| `ext` | `ext x` | Applies extensionality; for sets usually reduces equality to membership `↔`. | Most set equalities. |
| `funext` | `funext x` | Reduces equality of functions to equality at arbitrary `x`. | Function identities. |
| `congr` | `congr` | Breaks an equality into equalities of corresponding arguments/components where possible. | Compound function expressions. |
| `calc` | `calc ...` | Constructs a chain of equalities/relations, one step at a time. | Reuse named intermediate set identities. |
| `exact?` | `exact?` | Suggests a term or lemma that may close the goal. | Discover available facts; inspect its result. |
| `apply?` | `apply?` | Suggests lemmas applicable to the goal. | Find a useful intermediate theorem. |
| `simp?` | `simp?` | Reports a possible explicit simplification script. | Learn which lemmas `simp` used. |
| `#check` | `#check Set.ext` | **Command, not a tactic:** displays type of a declaration. | Learn theorem signatures. |
| `#print` | `#print Set.ext` | **Command, not a tactic:** displays declaration/definition information. | Inspect how a theorem or definition works. |

### D. Negation and case splitting

| Tactic / syntax | Example | Exact effect | Typical use |
|---|---|---|---|
| `by_cases` | `by_cases hp : P` | Makes two goals, one with `hp : P`, one with `hp : ¬ P`. | Complement identities, distributivity involving a fixed proposition. |
| `classical` | `classical` | Makes classical decision procedures available within the proof. | Classical set identities, case-splitting on arbitrary membership. |
| `by_contra` | `by_contra hnp` | Works by contradiction: adds `hnp : ¬ P` and asks you to prove `False` (using classical reasoning). | Proving difficult propositions indirectly. |
| `exfalso` | `exfalso` | Changes any goal to `False`. | You have reached an impossibility. |
| `contradiction` | `contradiction` | Tries to close a goal from contradictory local hypotheses. | `h : P` alongside `hn : ¬ P`. |
| `push_neg` | `push_neg at h` | Pushes logical negation inward, using logical equivalences. | Turn `¬ ∀` into an existential counterexample, etc. |
| `tauto` | `tauto` | Solves some propositional tautologies automatically (if imported). | Optional check after you understand the proof. |
| `aesop` | `aesop` | Automated proof search (availability depends on imports). | Optional rescue/exploration; not a substitute for learning. |

### E. Structuring a readable proof

| Syntax | Meaning | Example |
|---|---|---|
| `·` | Focuses a separate branch produced by an earlier tactic. | `constructor` followed by `· ...` and `· ...`. |
| `case ... =>` | Names/handles a specific goal or constructor case. | `case inl hp => ...` (when Lean exposes that tag). |
| `;` | Runs the next tactic on **all** goals created by the preceding tactic. | `constructor <;> assumption` (when both hypotheses exist). |
| `<;>` | Applies the right-hand tactic to every subgoal produced on the left. | `constructor <;> assumption`. |
| `first \| t₁ \| t₂` | Tries tactics in order until one succeeds. | Useful for experimenting, but be explicit when learning. |
| `try t` | Attempts `t`; does not fail if `t` is inapplicable. | Optional exploratory convenience. |
| `all_goals t` | Applies `t` to all remaining goals. | Repeated finishing moves. |

**Learning priority:** `intro`, `exact`, `apply`, `constructor`, `left`/`right`, `rcases`, `have`, `ext`, `use`, `rw`. Treat the automation rows as optional.

---

## 6. Building proof terms directly

Tactics are a way to *construct terms*. You can often understand a tactic by identifying the term it would build.

| Logical target | Example proof term | Tactic counterpart |
|---|---|---|
| `P → Q` | `fun hp => ...` | `intro hp` |
| `∀ x, P x` | `fun x => ...` | `intro x` |
| `P ∧ Q` | `⟨hp, hq⟩` or `And.intro hp hq` | `constructor` |
| `P ∨ Q` | `Or.inl hp` | `left` |
| `P ∨ Q` | `Or.inr hq` | `right` |
| `∃ x, P x` | `⟨w, hw⟩` | `use w` |
| `Q` from `hp : P` and `h : P → Q` | `h hp` | `apply h; exact hp` |
| `P` from `h : P ∧ Q` | `h.1` | `exact h.1` |
| `Q` from `h : P ∧ Q` | `h.2` | `exact h.2` |
| `Q` from `h : P ↔ Q`, `hp : P` | `h.mp hp` | `exact h.mp hp` |
| `P` from `h : P ↔ Q`, `hq : Q` | `h.mpr hq` | `exact h.mpr hq` |
| `False` from `hn : ¬ P`, `hp : P` | `hn hp` | `exact hn hp` |
| `a = a` | `rfl` | `rfl` |

**Mini-example (logic only):**

```lean
example (P Q : Prop) : P ∧ Q → Q ∧ P :=
  fun h => ⟨h.2, h.1⟩

example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  exact ⟨h.2, h.1⟩
```

Same mathematical proof, two different presentations. This is the *propositions-as-types* idea in action.

---

## 7. Set-specific proof patterns

### Two ways to prove set equality

| Approach | Initial move | What comes next | Why choose it? |
|---|---|---|---|
| **Elementwise** | `ext x` | Prove `x ∈ A ↔ x ∈ B`, often with `constructor`. | Exposes underlying logic directly. |
| **Two inclusions** | `apply subset_antisymm A B` | Prove `A ⊆ B` and `B ⊆ A`. | Reuses theorem **009** in your worksheet. |

When referencing your own equality helper, remember the **explicit** set arguments:

```lean
-- Inside namespace SetPractice, after theorem 009:
-- apply subset_antisymm A B
-- This produces A ⊆ B and B ⊆ A as goals.
```

This is a *pattern*, not a proof of any exercise.

### The three operations you will see constantly

| Membership fact | Deconstruct a hypothesis | Construct a goal |
|---|---|---|
| `x ∈ A ∩ B` | `rcases hx with ⟨ha, hb⟩` | `exact ⟨ha, hb⟩` if both are available |
| `x ∈ A ∪ B` | `rcases hx with ha \| hb` | `exact Or.inl ha` **or** `exact Or.inr hb` |
| `x ∈ A \ B` | `rcases hx with ⟨ha, hnb⟩` | `exact ⟨ha, hnb⟩` if both are available |

These work because Lean can unfold set membership to the corresponding logical proposition. If a tactic does not recognize the form, use `change` or an appropriate membership lemma to reveal it.

### Reusing earlier results instead of starting over

| Need | Strategy |
|---|---|
| A named subset fact | Call it as a function on a membership proof: `hAB hx`. |
| A named theorem with arguments | `exact myLemma A B` if its result matches; otherwise `apply myLemma ...`. |
| A set equality you proved earlier | `rw [myEarlierEquality ...]` if its orientation matches. |
| A set equality but the sides are reversed | `rw [← myEarlierEquality ...]`. |
| A middle set `B` between `A` and `C` | Consider your `subset_trans` theorem (002). |
| An intersection or union bound | Consider the helper theorems from 003–006 and 012–013 after you prove them. |
| A commuted intersection or union | Prefer your 010–011 once available rather than re-proving every swap. |

**Name collision:** inside `namespace SetPractice`, unqualified names such as `union_comm` may refer to **your** theorems instead of Mathlib's names. This is deliberate. If you need to distinguish declarations, inspect their types with `#check` and use fully qualified names.

---

## 8. Images, preimages, functions, and witnesses

The pivotal difference is **whether an existential witness is needed**.

### Preimage: evaluate the function

```lean
x ∈ f ⁻¹' B
-- means exactly
f x ∈ B
```

No search for an input is required: the input is already `x`.

### Image: find an input whose output is the element

```lean
y ∈ f '' A
-- means
∃ x, x ∈ A ∧ f x = y
```

| Situation | Likely move | What you obtain or owe |
|---|---|---|
| `hy : y ∈ f '' A` | `rcases hy with ⟨x, hxA, hxy⟩` | Witness `x`, membership `hxA`, equality `hxy : f x = y`. |
| Goal `y ∈ f '' A` | `use x` | Supply `x ∈ A` and `f x = y`. |
| Goal `f x ∈ f '' A` | Consider `x` as the witness. | Still show `x ∈ A` and the reflexive equality. |
| `hxy : f x = f y` and injectivity | `have h := hf hxy` | Gets equality `x = y`. |
| A witness equality `f x = y` | `rw [← hxy]` or `subst y`, where appropriate | Align target with the constructed witness. |
| Goal `(g ∘ f) x = g (f x)` | `rfl` may be enough. | Composition unfolds definitionally. |

**Why an image of an intersection is harder:** two image memberships can give you *two different witnesses*. If you want a common input in the intersection, you must justify why those witnesses agree. That is precisely where injectivity becomes relevant in exercise 073. Do not silently assume they are equal.

### Image versus range

| Notion | Form of witness |
|---|---|
| `y ∈ f '' A` | `∃ x, x ∈ A ∧ f x = y` |
| `y ∈ Set.range f` | `∃ x, f x = y` |

The image carries an additional restriction that the input belongs to `A`. For the entire domain (`Set.univ`) this membership obligation is trivial.

---

## 9. Indexed unions and intersections

Read these as quantifiers before doing anything else.

| Set syntax | Logical syntax | Goal introduction | Hypothesis elimination |
|---|---|---|---|
| `x ∈ ⋃ i, F i` | `∃ i, x ∈ F i` | `use i` | `rcases hx with ⟨i, hi⟩` |
| `x ∈ ⋂ i, F i` | `∀ i, x ∈ F i` | `intro i` | `exact hx i` |

An **indexed union** asks you to name *one successful index*. An **indexed intersection** asks you to handle *every index*.

If the index type `ι` might be empty, beware: you cannot pick an arbitrary `i : ι` unless you have one. Your worksheet's theorems carefully distinguish statements that do and do not provide a particular index.

### A simple logical analogy

```lean
-- Treat the family F as a predicate on indices.
example {ι : Type*} (P : ι → Prop) (i : ι) (hi : P i) :
    ∃ j, P j := by
  use i
```

This is the same existential mechanism used when entering an indexed union, without solving the actual set-theory exercises.

**Scope warning:** the binder in `⋃ i, F i` or `⋂ i, F i` extends to the right. Add parentheses if you intend to intersect or union *outside* the indexed expression.

---

## 10. Negation and classical reasoning

`¬ P` is defined as `P → False`, not as a mysterious separate truth value.

| Desired move | Interpretation | Typical syntax |
|---|---|---|
| Prove `¬ P` | Assume `P`, derive `False`. | `intro hp` |
| Use `¬ P` | Give it a proof of `P`, obtain `False`. | `exact hnot hp` |
| Split a proposition `P` into truth cases | Use excluded middle. | `by_cases hp : P` |
| Enable arbitrary proposition decidability in a proof | Classical logic. | `classical` |
| Prove `P` by contradiction | Assume `¬ P`, derive `False`. | `by_contra hnot` |
| Turn negated conjunction/disjunction/quantifiers into a more useful form | Apply logical equivalences. | `push_neg at h` (if available) |

### Which logical equivalences need classical reasoning?

| Equivalence | Constructive? | Why it matters |
|---|---|---|
| `¬(P ∨ Q) ↔ ¬P ∧ ¬Q` | Yes | Complement of union (045). |
| `¬(P ∧ Q) ↔ ¬P ∨ ¬Q` | **Not in general** | Complement of intersection (046). |
| `¬¬P ↔ P` | **Not in general** | Double complement (042). |
| `P ∨ ¬P` | **Not in general** | Union with complement (041). |
| `(P ∨ ∀ i, Q i) ↔ ∀ i, (P ∨ Q i)` | **Not in general** | Indexed distributivity (086); a case split on `P` is useful. |

`classical` lets you use these principles. It **does not** automatically prove a goal; you still construct the proof.

Do not automatically add `classical` everywhere. Several complement identities are constructive. Try reading the goal as logic first.

---

## 11. Worksheet navigation: which skills each exercise tests

This is an **index of techniques**, not a list of proof steps. It deliberately omits completed scripts, so you can keep working top to bottom.

### Chapters 01–04: sets as logical operations

| Exercise | Central shape to recognize | Main tools worth knowing |
|---|---|---|
| 001–002 (completed) | Inclusion / inclusion composition | `intro`, `exact`, `apply`, `have` |
| 003–004 (completed) | Intersection source | `.1`, `.2` |
| 005–007 (completed) | Union target or source | `Or.inl`, `Or.inr`, `cases` |
| 008–009 (completed) | Swapping conjunction; equality from two inclusions | `And.intro`, `Set.ext`, `constructor` |
| 010–011 (completed) | Reusing proved inclusions | Earlier theorems, `subset_antisymm` |
| 012 | Intersection target | `intro`, `constructor` |
| 013 | Union source | `intro`, `rcases` |
| 014 | Idempotent intersection | Two inclusions / elementwise equivalence |
| 015 | Idempotent union | Two inclusions / elementwise equivalence |
| 016 | Inclusion into a conjunction | `intro`, `constructor`, union introduction |
| 017 | Absorption by intersection | Existing 016 and inclusion facts |
| 018 | Absorption by union | Union elimination / earlier subset facts |
| 019 | Associative intersection | Nested conjunction patterns |
| 020 | Associative union | Nested disjunction patterns |
| 021 | Empty set as source | `False` elimination |
| 022 | Universal set as target | `True`, `trivial` |
| 023 | Negation of empty membership | `intro`, contradiction |
| 024 | Universal membership | `trivial` |
| 025 | Intersection with empty | Empty membership impossible |
| 026 | Union with empty | Split union into two cases |
| 027 | Intersection with universal | `True` component of conjunction |
| 028 | Union with universal | `True` disjunct |
| 029 | Empty on left of union | Earlier empty/union facts; `rw` possible |
| 030 | Universal on left of intersection | Earlier intersection/universal facts |
| 031 | Intersection over union | `∧` over `∨`, case split |
| 032 | Union over intersection, opposite orientation | Swap sets or repeat propositional reasoning |
| 033 | Union over intersection | `∨` over `∧`, consider two directions |
| 034 | Intersection / union distributivity, opposite orientation | Symmetry or earlier distributive result |
| 035 | Monotonicity of intersection | Two subset hypotheses; conjunction |
| 036 | Monotonicity of union | Two subset hypotheses; disjunction |
| 037 | Equality iff subset | `constructor` for `↔`; equality for one direction |
| 038 | Equality iff reverse subset | `constructor` for `↔`; union structure |

### Chapters 05–06: complements and differences

| Exercise | Central shape to recognize | Main tools worth knowing |
|---|---|---|
| 039 | Complement membership | `¬`, definitional unfolding |
| 040 | Conjunction with its own negation | `False`, `intro`, contradiction |
| 041 | Excluded middle | `classical` / `by_cases` |
| 042 | Double negation elimination | `classical`, `by_contra` or cases |
| 043 | Negating impossible membership | Empty membership and `True` |
| 044 | Negating universal membership | `False` from `True → False` |
| 045 | Negation of disjunction | Constructive De Morgan reasoning |
| 046 | Negation of conjunction | Classical De Morgan reasoning |
| 047 | Subset contravariance under complement | Assume contrary membership and apply inclusion |
| 048 | Complement inclusion vs empty intersection | `↔`, negation, impossible intersections |
| 049 | Difference membership | `∧` and `¬` |
| 050 | Difference source | First conjunct |
| 051 | Self-difference | Membership and non-membership contradict |
| 052 | Difference from empty | Empty membership impossible |
| 053 | Empty minus anything | Empty membership impossible |
| 054 | Difference from universal | Membership in `univ` contradicts non-membership |
| 055 | Difference as intersection with complement | Same membership predicate on both sides |
| 056 | Difference of union | Negation of `∨` |
| 057 | Difference of intersection | Negation of `∧`; classical reasoning |
| 058 | Repeated difference | Nested conjunctions and negations |

### Chapters 07–08: functions and indexed sets

| Exercise | Central shape to recognize | Main tools worth knowing |
|---|---|---|
| 059 | Preimage membership | `change`, definitional equality |
| 060 | Preimage of empty | `False` after applying `f` |
| 061 | Preimage of universal | `True` after applying `f` |
| 062 | Preimage of intersection | Conjunction after applying `f` |
| 063 | Preimage of union | Disjunction after applying `f` |
| 064 | Preimage of complement | Negation after applying `f` |
| 065 | Preimage of difference | Conjunction plus negation |
| 066 | Image of empty | Witness would have impossible membership |
| 067 | Image of union | Witness plus source disjunction |
| 068 | Image monotonicity | Reuse a witness, change its membership proof |
| 069 | Preimage monotonicity | Apply subset hypothesis to `f x` |
| 070 | Subset of preimage of image | Choose source element as image witness |
| 071 | Image of preimage inclusion | Unpack witness; its membership already mentions `f` |
| 072 | Image/intersection inclusion | One witness yields two image memberships |
| 073 | Injective image/intersection equality | Two witnesses plus injectivity |
| 074 | Image of universe / range | Compare two existential shapes |
| 075 | Composition of images | Nested witnesses and function composition |
| 076 | Composition of preimages | Reassociate function application |
| 077 | Indexed union membership | Existential quantifier over indices |
| 078 | Indexed intersection membership | Universal quantifier over indices |
| 079 | Member set into indexed union | Provide a specific index |
| 080 | Indexed intersection into member | Instantiate at a specific index |
| 081 | Union lies below common bound | Unpack index, instantiate universal hypothesis |
| 082 | Common lower bound lies in intersection | Introduce an index, instantiate hypothesis |
| 083 | Preimage of indexed union | Existential witness + preimage reduction |
| 084 | Preimage of indexed intersection | Universal quantifier + preimage reduction |
| 085 | Intersection over indexed union | Conjunction and existential reasoning |
| 086 | Union over indexed intersection | Universal quantifier and classical case split |

**Skill milestones:**

- **001–020:** Can you consistently tell whether you need to *construct* or *eliminate* an `And`/`Or`?
- **021–038:** Can you move between set equality, inclusions, and logic without relying on `simp`?
- **039–058:** Can you explain *where* classical reasoning is necessary?
- **059–076:** Can you track image witnesses, membership conditions, and the direction of equalities?
- **077–086:** Can you turn every `⋃` into `∃` and every `⋂` into `∀`?

---

## 12. Diagnosing common Lean errors

| What you see | Likely issue | What to try |
|---|---|---|
| `type mismatch` in `exact h` | `h` proves a different proposition than the goal. | Read the full types of both; use `apply`, `rw`, or `change` if justified. |
| `no goals to be solved` | An earlier tactic already finished the branch. | Delete the unnecessary later tactic. |
| `unsolved goals` | `constructor`, `apply`, or another tactic produced obligations. | Inspect the remaining goals and solve them one by one. |
| `no applicable extensionality theorem` | `ext` does not see an appropriate equality or import. | Check goal; try `apply Set.ext` when proving set equality. |
| `tactic 'left' failed` | Goal is not a disjunction (or cannot be reduced to one). | Check whether you instead have a disjunction **hypothesis**. |
| `tactic 'constructor' failed` | Current goal may not be a constructor-shaped proposition. | Use `change` to reveal the logical form, or inspect the goal. |
| `application type mismatch` for `hAB hx` | You may have reversed the inclusion or supplied the wrong membership. | Confirm `hAB : A ⊆ B` and `hx : x ∈ A`. |
| `failed to find instance` / `Decidable` | Lean needs to decide an arbitrary proposition in a classical case. | Add `classical` when the reasoning really uses excluded middle. |
| `unknown tactic` | The tactic isn't available from the present imports. | Consult its import/module; for experimentation try `import Mathlib.Tactic` (if permitted). |
| `unknown identifier` | Name typo, missing import, namespace, or scope. | Use `#check`, check namespace prefix, and verify spelling. |
| `function expected` | Something you applied is not a function/implication with that argument. | Inspect it with `#check` or hover over its type. |
| `don't know how to synthesize implicit argument` | Lean cannot infer a type or argument. | Annotate the type, e.g. `(∅ : Set α)`, or supply named args. |
| Rewriting does nothing / cannot find pattern | Term in goal is not in the expected orientation or form. | Try `rw [← h]`, `change`, or display intermediate definition. |
| A proof unexpectedly needs a witness | You reached `∃ x, ...` (often from `f '' A` or `⋃`). | Find the correct input/index; use `use`. |
| A proof unexpectedly has many branches | You eliminated an `Or` or used `by_cases`. | Work separately in each branch; look at branch-local hypotheses. |
| `simp` closes everything but teaches little | It used existing lemmas that may prove the whole exercise. | Try `simp?`, inspect the lemmas, then replace with explicit logic. |
| A theorem name unexpectedly refers to a different result | Local namespace names can shadow Mathlib names. | Use `#check theoremName` and qualified names. |

### Diagnostic discipline

1. **Copy only the displayed goal** onto paper or into a comment.
2. Translate it to `→`, `∧`, `∨`, `¬`, `∀`, `∃`.
3. Determine whether your next move works on the **goal** or on a **hypothesis**.
4. Run **one** tactic and inspect the new state.
5. If stuck, inspect a **definition** first; seek a theorem only after understanding the statement.

---

## 13. Useful commands, notation, and proof-writing conventions

### Writing and reading notation

| Symbol | Meaning | Common Lean input abbreviation |
|---|---|---|
| `∀` | For all | `\forall` |
| `∃` | There exists | `\exists` |
| `→` | Implication/function arrow | `\to` |
| `↔` | If and only if | `\iff` |
| `∧` / `∨` | And / or | `\and` / `\or` |
| `¬` | Not | `\not` |
| `∈` / `∉` | Member / not a member | `\in` / `\notin` |
| `⊆` | Subset | `\sub` (also check editor completions) |
| `∩` / `∪` | Intersection / union | `\inter` / `\union` |
| `∅` | Empty set | `\empty` |
| `⟨...⟩` | Constructor / tuple / witness | `\langle` / `\rangle` |
| `ᶜ` | Complement | `\compl` (check editor completions) |
| `⋃` / `⋂` | Indexed union/intersection | `\bigcup` / `\bigcap` |
| `\` | Set difference | `\\` as an editor input abbreviation; literal `\` in the worksheet |
| `f '' A` | Image | Two apostrophes following `f` |
| `f ⁻¹' B` | Preimage | Superscript `⁻¹` and an apostrophe |
| `∘` | Function composition | `\circ` |
| `⊢` | Current goal | Displayed by Lean; not normally typed in proofs |

**Input methods may differ between VS Code and other editors.** The literal syntax in the worksheet is authoritative. In Markdown code blocks, `\` is a single backslash in Lean source; editor input sequences are described separately.

### Checking what Mathlib actually provides

Put investigation commands **outside** a theorem proof:

```lean
#check Set.ext
#check Set.mem_image
#check Set.mem_preimage
#check Set.mem_iUnion
#check Set.mem_iInter
#check Function.Injective
#print Set
```

The exact theorem names available can depend on Mathlib version and imports. If a suggested name is unavailable, inspect the corresponding declaration in your installed version rather than treating it as a required incantation.

### Your existing imports

```lean
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice.Indexed
```

Start with these so your proofs match the worksheet. If you deliberately want access to a broader suite of automation/discovery tactics, a common experimental alternative is:

```lean
import Mathlib
```

But loading more automation is **not necessary** to understand your current exercises; many of their proofs can be written with the core structural tactics and the imported set definitions.

### Avoid three common conceptual mistakes

| Mistake | Correction |
|---|---|
| Treating `x ∈ A ∪ B` as requiring both memberships | Union is **or**, not **and**. |
| Treating `f '' A` like `f ⁻¹' B` | An **image** requires an input witness; a **preimage** just applies `f`. |
| Treating `A ⊆ B` as an equality | Subset is **one implication** for each element; equality needs **both directions**. |

---

## 14. Study workflow and further references

### Five-question checklist before every proof

1. **What kind of goal is this?** Equality, subset, conjunction, disjunction, implication, negation, or quantifier?
2. **What does membership mean here?** Expand `∩`, `∪`, `\`, `ᶜ`, image, preimage, `⋃`, or `⋂`.
3. **Which hypotheses can I eliminate?** Split `∧`/`∨`, instantiate `∀`, or extract an `∃` witness.
4. **Can I reuse a theorem I already proved?** Especially 002, 009–013, and later algebraic laws.
5. **What is the smallest next step?** One tactic, then inspect the goal again.

### A sensible tactic learning order

| Stage | Learn these first | Relevant portion of worksheet |
|---|---|---|
| 1 | `intro`, `exact`, `apply`, `have` | 001–013 |
| 2 | `constructor`, `.1`, `.2`, `left`, `right`, `rcases`, `cases` | 003–020 |
| 3 | `ext`, `Set.ext`, `rw`, `rfl`, `change` | 009–038 |
| 4 | `False`, `intro` on negation, `by_cases`, `classical` | 021–058 |
| 5 | `use`, existential `rcases`, equality substitutions, injectivity | 059–076 |
| 6 | `intro i`, `have hi := h i`, existential index witnesses | 077–086 |
| 7 (optional) | `simp only`, `simpa`, `simp?`, `exact?`, `aesop` | After understanding manual proofs |

### Recommended documentation

- [Mathematics in Lean, Chapter 4: Sets and Functions](https://leanprover-community.github.io/mathematics_in_lean/C04_Sets_and_Functions.html) — particularly close to your worksheet.
- [Theorem Proving in Lean 4: Tactics](https://lean-lang.org/theorem_proving_in_lean4/Tactics/) — the meaning of basic tactics and proof states.
- [Mathlib 4 tactic documentation](https://leanprover-community.github.io/mathlib4_docs/tactics.html) — consult when a tactic's exact behavior is unclear.
- [Mathlib 4 library documentation](https://leanprover-community.github.io/mathlib4_docs/) — search for set declarations, membership lemmas, and theorem signatures.

### One final distinction

- **Tactic:** a command to *construct a proof* (`intro`, `rcases`, `apply`).
- **Theorem/lemma:** an *already proved statement* that you can use (`Set.ext`, or your own `subset_trans`).
- **Definition:** what notation *means* (`x ∈ A ∩ B` means `x ∈ A ∧ x ∈ B`).
- **Proof term:** the expression Lean is ultimately checking (`fun hx => ...`, `⟨ha, hb⟩`).

When a theorem feels mysterious, identify which of these four things you are looking at. Most early Lean confusion comes from mixing them up.
