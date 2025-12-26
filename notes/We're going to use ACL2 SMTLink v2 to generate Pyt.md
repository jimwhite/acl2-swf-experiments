<img src="https://r2cdn.perplexity.ai/pplx-full-logo-primary-dark%402x.png" style="height:64px;margin-right:32px"/>

# We're going to use ACL2 SMTLink v2 to generate Python to use Z3 to make the control decisions in Plan-and-Execute.  Will using the Z3 prover will decide the edge transitions work in LangGraph or should we just use LangChain?

Attached is the paper for SMTLink v2 which describes how to generate Python code that runs a verified Z3 program.  Probably should start by converting that doc to an agent skill .md explaining to use it including the code showing how to use it.

Excellent question. After reviewing the SMTLink v2 paper, I can give you a precise technical answer about using verified Z3 decision-making for LangGraph's conditional edge transitions.

## TL;DR: **Use LangGraph with SMTLink-generated Z3 decision functions**

**Why not LangChain:** LangChain doesn't provide the stateful graph architecture needed for this pattern. LangGraph is the correct choice because:

1. **Explicit state and edges** - LangGraph's graph-based architecture naturally represents decision points as conditional edges with named targets
2. **Formal verification integration point** - You can generate verified Python from ACL2/Z3 and inject it directly into LangGraph's `conditional_edges()` without semantic mismatch
3. **Determinism and reproducibility** - SMT solver decisions are deterministic and verifiable, matching LangGraph's requirement for reproducible control flow

***

## How SMTLink V2 Enables This

The key insight from the paper (Section 2.2.5, "smtlink-trusted-cp") is that SMTLink generates **verified Python code** that calls Z3 directly:

```python
# SMTLink generates this verified Python code from ACL2
from z3 import *

def verify_plan_feasible(plan_state):
    """
    Generated from ACL2 theorem proof via SMTLink.
    Uses Z3 to verify the plan can proceed to next stage.
    Returns boolean decision.
    """
    solver = Solver()
    
    # Type extraction (from Section 3.1-3.3 of paper)
    x = Real('x')
    y = Real('y')
    
    # Constraints from plan_state (translated via verified clause processors)
    solver.add(plan_state.constraint_1)
    solver.add(plan_state.constraint_2)
    
    # The actual property being decided
    solver.add(Not(plan_state.property_to_verify))
    
    result = solver.check()
    
    # If Z3 says UNSAT (i.e., negation is unsatisfiable),
    # then the property is proven
    return result == unsat
```


### The SMTLink Translation Pipeline

The paper shows (Figure 1) a sequence of verified clause processors that transform your ACL2 theorem into Python:

```
ACL2 Theorem Goal (G)
    ↓
add-hypo-cp    (add hypotheses)
    ↓
expand-cp      (expand function defs)
    ↓
type-extract-cp (extract types for Z3)
    ↓
uninterpreted-fn-cp (mark functions as uninterpreted if needed)
    ↓
smt-trusted-cp (generate verified Python + Z3 call)
    ↓
Python code calling Z3
```

**Most of this is verified** (Section 2.3). Only the final `smt-trusted-cp` is trusted because we must ultimately trust Z3 as an oracle.

***

## Concrete LangGraph Integration Pattern

Here's how to structure this:

```python
from langgraph.graph import StateGraph, END
from typing import TypedDict, Literal
import sys
sys.path.insert(0, '/path/to/smtlink/generated')  # Where SMTLink puts Python

# Import the verified Z3 functions SMTLink generates
from acl2_proofs.plan_execute_verified import (
    verify_plan_ready_for_execution,
    verify_execution_succeeded,
    verify_needs_replanning
)

class PlanExecuteState(TypedDict):
    input: str
    plan: list[str]
    past_steps: list[tuple[str, str]]
    response: str
    # Additional fields for Z3 solver state
    constraints: dict  # Accumulated constraints from execution

# Define the decision functions using verified Z3 code

def should_execute_next(state: PlanExecuteState) -> Literal["agent", "replan", END]:
    """
    Uses Z3 to decide: is the plan still valid?
    Generated from verified ACL2 proof.
    """
    # Pass state to SMTLink-generated function
    is_valid = verify_plan_ready_for_execution(
        plan=state["plan"],
        executed_steps=state["past_steps"],
        constraints=state["constraints"]
    )
    
    if is_valid:
        return "agent"  # Continue execution
    else:
        return "replan"  # Need to replan

def should_continue_or_finish(state: PlanExecuteState) -> Literal["agent", "replan", END]:
    """
    Uses Z3 to decide: did we complete the goal?
    """
    # Check if we've met the goal constraints
    goal_achieved = verify_execution_succeeded(
        initial_input=state["input"],
        steps_taken=state["past_steps"],
        current_state=state["constraints"]
    )
    
    if goal_achieved:
        return END
    
    # Check if we should replan instead
    can_continue = verify_needs_replanning(
        plan=state["plan"],
        past_steps=state["past_steps"]
    )
    
    return "replan" if not can_continue else "agent"

# Build the graph

workflow = StateGraph(PlanExecuteState)

# Add nodes (planner, agent, replanner as before)
workflow.add_node("planner", plan_step)
workflow.add_node("agent", execute_step)
workflow.add_node("replan", replan_step)

# Use Z3-verified conditional edges
workflow.add_edge("planner", "agent")
workflow.add_conditional_edges(
    "agent",
    should_continue_or_finish,
    {
        "agent": "agent",
        "replan": "replan",
        END: END
    }
)

workflow.add_conditional_edges(
    "replan",
    should_execute_next,
    {
        "agent": "agent",
        "replan": "replan",  # Double-check: still invalid?
        END: END
    }
)

app = workflow.compile()
```


***

## The Soundness Story: Why This Works

From the SMTLink paper (Section 3, "Types, Theories, and Soundness"):

1. **Verified Clause Processors** - The transformation from your ACL2 goal to Z3 is proven sound. Each step (expand, type-extract, etc.) is a verified processor that logically implies the previous form.
2. **One Trusted Link** - The only unverified step is: "If Z3 says UNSAT, then the theorem is true." This is a reasonable trust assumption (Z3 is industry-standard and extensively tested).
3. **Type Safety Bridge** - The paper shows (Section 3.1-3.4) how to translate between ACL2's untyped logic and Z3's many-sorted logic. Critical for decision correctness.
4. **Generated Code Remains Sound** - The Python code SMTLink generates is a direct transliteration of the Z3 constraints. It doesn't introduce new soundness gaps.

***

## Creating the Agent Skill Markdown

Now for your request to create an agent skill `.md` document. This should be a concise guide for wiki3.ai developers on how to use this pattern:
<span style="display:none">[^1]</span>

<div align="center">⁂</div>

[^1]: 1810.04317v1.pdf

