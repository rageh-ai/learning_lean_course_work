/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases'`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  intro h1
  cases' h1 with h2 h3
  exact h2
  done

example : P ∧ Q → Q := by
  intro h1
  cases' h1 with h2 h3
  exact h3
  done

example : (P → Q → R) → P ∧ Q → R := by
  intro h1
  intro h2
  cases' h2 with h3 h4
  apply h1 at h3
  apply h3
  exact h4
  done

example : P → Q → P ∧ Q := by
  intro h1 h2
  constructor
  exact h1
  exact h2
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro h1
  constructor
  cases' h1 with h2 h3
  exact h3
  cases' h1 with h2 h3
  exact h2
  done

example : P → P ∧ True := by
  intro h1
  constructor
  exact h1
  triv
  done

example : False → P ∧ False := by
  intro h1
  constructor
  exfalso
  exact h1
  exact h1
  done

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h1 h2
  cases' h1 with h3 h4
  cases'  h2 with h5 h6
  constructor
  exact h3
  exact h6
  done

example : (P ∧ Q → R) → P → Q → R := by
  intro h1 h2 h3
  apply h1
  constructor
  exact h2
  exact h3
  done
