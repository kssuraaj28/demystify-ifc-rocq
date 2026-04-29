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

TODO: design an automation tactic called `dominate`.
