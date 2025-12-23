# Plan: Verified ReAct Agent with Z3 Enforcement & Optimization

Build a ReAct agent with ACL2-specified constraints enforced and optimized by Z3 at runtime. Z3 both gates permitted actions AND decides continue-vs-respond based on cost/benefit estimation.

## Steps

1. **Create experiment structure**:
   - `experiments/agents/experiment-01-react-verified.lisp` - ACL2 specification and proofs
   - Generated notebook will include Python/Z3/LangGraph runtime

2. **Define orthogonal permission model** in ACL2:
   - File access enum: `*access-none* 0`, `*access-read* 1`, `*access-read-write* 2`
   - Execute permission: separate boolean `execute-allowed-p`
   - Tool spec: `(name, input-types, output-type, required-file-access, requires-execute, base-cost, time-estimate)`
   - `tool-permitted-p`: `(and (>= granted-access required-access) (implies requires-execute execute-allowed))`

3. **Define LLM cost model** with model registry:
   - `llm-model-spec`: `(name, tokens-per-second, cost-per-1k-input, cost-per-1k-output)`
   - Fetch available models from `http://host.docker.internal:1234/v1/models`
   - Manual performance table initially; side-task notebook for benchmarking if metadata insufficient

4. **Define Z3 optimization logic** (the key innovation):
   - `satisfaction-estimate`: score 0.0-1.0 of how well current response answers the query
   - `marginal-benefit`: expected improvement from one more iteration
   - `marginal-cost`: token + time cost of next tool/LLM call
   - Decision function: `continue-p ≡ (and (budget-sufficient-p next-cost) (> marginal-benefit (* risk-factor marginal-cost)))`
   - On budget exhaustion: `must-respond-p ≡ (or (not (budget-sufficient-p min-cost)) done-p)`

5. **Prove theorems with SMTLink**:
   - Permission safety: `(agent-step state) → (all-actions-permitted-p state)`
   - Budget compliance: `(natp remaining-budget) ∧ (>= remaining-budget 0)` invariant
   - Termination: budget strictly decreases OR satisfaction threshold reached
   - Graceful degradation: `must-respond-p → (produces-response-p (agent-step state))`

6. **Create Python notebook** with UI controls:
   - `%pip install z3-solver langgraph langchain-openai ipywidgets`
   - Permission checkboxes: `☐ Read files` `☐ Write files` `☐ Execute code`
   - Budget sliders: max tokens, max cost ($), max time (seconds)
   - Z3 `Optimize()` solver for continue-vs-respond decision
   - LangGraph agent with `should_continue` calling Z3 optimization

7. **Update `.github/copilot-instructions.md`** with:
   - Agents track overview and SMTLink usage patterns
   - Permission model (file access + execute orthogonal)
   - Z3 dual role: enforcement + optimization

## Further Considerations

1. **Satisfaction estimation**: Use LLM self-assessment ("rate your confidence 0-10"), embedding similarity to query, or structured rubric?
2. **Model benchmark notebook**: Create `experiments/agents/utils/model-benchmark.ipynb` as immediate side-task, or defer until LM Studio metadata proves insufficient?
3. **Risk factor tuning**: Fixed constant, or adaptive based on remaining budget (more conservative as budget depletes)?
