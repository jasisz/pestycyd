# Valid mutation seeds

These small exports are accepted by the official Lean kernel and are intended
as starting points for focused mutation campaigns. They avoid `Init`, trusted
primitive reductions, inductives, and imported recursors whenever possible.

| Input | Purpose |
| --- | --- |
| `dependent-id.ndjson` | Minimal dependent `Pi`/lambda seed. `expression-structure-full` on this input found MathGraph's closure-mode comparison bug. |

