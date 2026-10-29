# Valid mutation seeds

These small exports are accepted by the official Lean kernel and are intended
as starting points for focused mutation campaigns. They avoid `Init`, trusted
primitive reductions, inductives, and imported recursors whenever possible.

| Input | Purpose |
| --- | --- |
| `dependent-id.ndjson` | Minimal dependent `Pi`/lambda seed. `expression-structure-full` on this input found MathGraph's closure-mode comparison bug. |
| `proof-param-rec-consumer.ndjson` | Universe-polymorphic proof-parameter recursor with a real downstream consumer, so serialized recursor mutations must survive end-to-end checking instead of dying as unconsumed metadata. |

