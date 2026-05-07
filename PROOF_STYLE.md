# Proof Style

We use ssreflect freely.

Settings:

```coq
Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.
```

- Do not use the `by`, `first`, or `last` tacticals. 
- `by` does too much; its terminating behaviour can be enforced by the system better (via the goal selector and strict subproofs settings above).
- Do not use `intro`; use `move` instead, for uniformity.
- All rewriting tactics are fine to use (ssreflect, normal, etc.).
- Do not use the `all:` goal selector. Write the goal numbers explicitly.
- Unification variables (existential variables) should be generated and consumed within the same tactic.
- There is no strict rule against mixing ssreflect and normal tactics. In fact, for automation it is required.
- Every user-defined tactic should be wrapped by `assert_goals`, `ensure_goals`, or `harden`. Use `assert_goals` (hard throw) when a goal-count mismatch indicates a programmer error; use `ensure_goals` (soft failure) when the call site needs to backtrack on a mismatch; fall back to `harden` when you cannot assert a goal count. You may have to prefix your tactic by `idtac;` to prevent eager evaluation (https://rocq-prover.zulipchat.com/#narrow/channel/237977-Rocq-users/topic/Weird.20bug/with/593251599).
- User-defined tactics must not finish with shelved goals. The shelf may be used internally during the tactic's operation, but all shelved goals must be unshelved (or solved) before the tactic returns.

## `dominate`

`dominate` is the project automation tactic, defined in `Tacs.v`. It runs
registered tactics over the focused goals until all goals are either solved or
all the tactics fail. Disclaimer: If a tactic that does not fail, and also does
not make progress (like idtac) is registered, it will `dominate` will loop
forever! It is the client's responsibility to harden their tactics using
`harden` / `ensure_goals` / `assert_goals`.

- `dominate` runs to completion (no gas).
- `dominate n` runs at most `n` outer iterations (gas). Goals are consumed in a dfs manner.
- `dominate_step` runs one pass over the registered list on a single focused goal.
- `curr_dom_list` is an ltac2 list of the currently registered tactics. To change, use 
    `Ltac2 Set curr_dom_list`, and use `append_tac` and `join_tacs`.
- Set `Ltac2 Set dom_debug := true.` to print a trace: the focused goal count
  before each iteration, and the description of each tactic that succeeds
  inside `dominate_step`.

`dominate_step` normalizes the goal with `move=> *` before dispatching the
registered chain, and again on every produced subgoal after a successful
tactic. Contract for chain-step authors: you can assume `move=> *` was just
run on the goal you receive, and `move=> *` will run on every goal you
produce.

After running, all `dominate*` notations apply `goal_hygiene` (revert +
reintroduce) to give clean, fresh hypothesis names.
