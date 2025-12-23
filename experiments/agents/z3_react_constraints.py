"""
Z3 Runtime Constraints for Verified ReAct Agent
================================================

This module mirrors the ACL2 formal specification from:
- experiment-01-react-verified.lisp (pure ACL2)
- experiment-02-smtlink-react.lisp (SMTLink FTY types)

Instead of compile-time proof, this uses Z3 at RUNTIME to:
1. Enforce permission and budget constraints before tool invocation
2. Determine continue vs respond decisions
3. Optimize tool selection given constraints

The Z3 Datatypes mirror the ACL2 FTY defprod types exactly.
"""

from z3 import (
    Datatype, IntSort, BoolSort, Const, Int, Bool,
    And, Or, Not, Implies, If,
    Solver, Optimize, sat, unsat, Sum
)
from dataclasses import dataclass, field
from typing import Optional, Literal
from enum import IntEnum


# ============================================================================
# Constants (matching ACL2 defconst)
# ============================================================================

class AccessLevel(IntEnum):
    """File access levels - matches ACL2 *access-none/read/read-write*"""
    NONE = 0
    READ = 1
    READ_WRITE = 2


# Budget thresholds - matches ACL2 defconst
MIN_LLM_TOKENS = 100
MIN_ITERATION_COST = 10      # millicents
MIN_ITERATION_TIME = 1000    # milliseconds
SATISFACTION_THRESHOLD = 90  # percentage (0-100), ACL2 uses 9/10


# ============================================================================
# Z3 Datatypes (mirroring FTY defprod from experiment-02)
# ============================================================================

# Agent state datatype
_AgentState = Datatype('AgentState')
_AgentState.declare('mk_agent_state',
    ('iteration', IntSort()),
    ('max_iterations', IntSort()),
    ('token_budget', IntSort()),
    ('cost_budget', IntSort()),
    ('time_budget', IntSort()),
    ('file_access', IntSort()),
    ('exec_allowed', BoolSort()),
    ('satisfaction', IntSort()),  # 0-100 percentage
    ('done', BoolSort()))
AgentState = _AgentState.create()

# Tool specification datatype
_ToolSpec = Datatype('ToolSpec')
_ToolSpec.declare('mk_tool_spec',
    ('required_access', IntSort()),
    ('requires_exec', BoolSort()),
    ('base_cost', IntSort()),
    ('time_estimate', IntSort()),
    ('token_estimate', IntSort()))
ToolSpec = _ToolSpec.create()


# ============================================================================
# Runtime Python Dataclasses (for actual execution state)
# ============================================================================

@dataclass
class AgentStateRT:
    """Runtime agent state - mirrors Z3 AgentState datatype."""
    iteration: int = 0
    max_iterations: int = 10
    token_budget: int = 10000
    cost_budget: int = 1000      # millicents
    time_budget: int = 60000     # milliseconds
    file_access: AccessLevel = AccessLevel.NONE
    exec_allowed: bool = False
    satisfaction: int = 0        # 0-100 percentage
    done: bool = False
    
    def to_z3_constraints(self, z3_var):
        """Generate Z3 constraints binding z3_var to this state's values."""
        return And(
            AgentState.iteration(z3_var) == self.iteration,
            AgentState.max_iterations(z3_var) == self.max_iterations,
            AgentState.token_budget(z3_var) == self.token_budget,
            AgentState.cost_budget(z3_var) == self.cost_budget,
            AgentState.time_budget(z3_var) == self.time_budget,
            AgentState.file_access(z3_var) == int(self.file_access),
            AgentState.exec_allowed(z3_var) == self.exec_allowed,
            AgentState.satisfaction(z3_var) == self.satisfaction,
            AgentState.done(z3_var) == self.done
        )


@dataclass 
class ToolSpecRT:
    """Runtime tool specification - mirrors Z3 ToolSpec datatype."""
    name: str
    required_access: AccessLevel = AccessLevel.NONE
    requires_exec: bool = False
    base_cost: int = 0           # millicents
    time_estimate: int = 0       # milliseconds
    token_estimate: int = 0
    
    def to_z3_constraints(self, z3_var):
        """Generate Z3 constraints binding z3_var to this tool's values."""
        return And(
            ToolSpec.required_access(z3_var) == int(self.required_access),
            ToolSpec.requires_exec(z3_var) == self.requires_exec,
            ToolSpec.base_cost(z3_var) == self.base_cost,
            ToolSpec.time_estimate(z3_var) == self.time_estimate,
            ToolSpec.token_estimate(z3_var) == self.token_estimate
        )


# ============================================================================
# Z3 Constraint Functions (matching ACL2 defun exactly)
# ============================================================================

def access_sufficient(required, granted):
    """
    ACL2: (defun access-sufficient-p (required granted) (<= required granted))
    
    Check if granted access level is sufficient for required level.
    """
    return required <= granted


def tool_permitted(tool, state):
    """
    ACL2: (defun tool-permitted-p (required-access requires-execute 
                                    granted-access execute-allowed)
            (and (access-sufficient-p required-access granted-access)
                 (implies requires-execute execute-allowed)))
    
    Full permission check: file access AND execute permission.
    """
    access_ok = access_sufficient(
        ToolSpec.required_access(tool),
        AgentState.file_access(state)
    )
    exec_ok = Implies(
        ToolSpec.requires_exec(tool),
        AgentState.exec_allowed(state)
    )
    return And(access_ok, exec_ok)


def tool_budget_sufficient(tool, state):
    """
    ACL2: (defun tool-budget-sufficient-p (st tool)
            (and (<= (tool-base-cost tool) (agent-cost-budget st))
                 (<= (tool-time-estimate tool) (agent-time-budget st))
                 (<= (tool-token-estimate tool) (agent-token-budget st))))
    
    Check if there's sufficient budget for a tool call.
    """
    return And(
        ToolSpec.base_cost(tool) <= AgentState.cost_budget(state),
        ToolSpec.time_estimate(tool) <= AgentState.time_budget(state),
        ToolSpec.token_estimate(tool) <= AgentState.token_budget(state)
    )


def can_invoke_tool(tool, state):
    """
    ACL2: (defun can-invoke-tool-p (st tool)
            (and (tool-permitted-p ...) (tool-budget-sufficient-p st tool)))
    
    Check if tool is both permitted AND within budget.
    """
    return And(
        tool_permitted(tool, state),
        tool_budget_sufficient(tool, state)
    )


def must_respond(state):
    """
    ACL2: (defun must-respond-p (st)
            (or (agent-done st)
                (>= (agent-iteration st) (agent-max-iterations st))
                (< (agent-token-budget st) *min-llm-tokens*)
                (< (agent-cost-budget st) *min-iteration-cost*)
                (< (agent-time-budget st) *min-iteration-time*)))
    
    Must respond: no budget for another iteration OR done OR max iterations.
    """
    return Or(
        AgentState.done(state),
        AgentState.iteration(state) >= AgentState.max_iterations(state),
        AgentState.token_budget(state) < MIN_LLM_TOKENS,
        AgentState.cost_budget(state) < MIN_ITERATION_COST,
        AgentState.time_budget(state) < MIN_ITERATION_TIME
    )


def should_continue(state):
    """
    ACL2: (defun should-continue-p (st)
            (and (not (must-respond-p st))
                 (< (agent-satisfaction st) *satisfaction-threshold*)))
    
    Should continue: has budget and below satisfaction threshold.
    """
    return And(
        Not(must_respond(state)),
        AgentState.satisfaction(state) < SATISFACTION_THRESHOLD
    )


# ============================================================================
# Runtime Verification Class
# ============================================================================

class ReactConstraintChecker:
    """
    Z3-based runtime constraint checker for ReAct agent.
    
    Provides methods to verify constraints before actions and
    determine continue/respond decisions.
    """
    
    def __init__(self):
        self.solver = Solver()
    
    def check_tool_invocation(
        self, 
        tool: ToolSpecRT, 
        state: AgentStateRT
    ) -> tuple[bool, Optional[str]]:
        """
        Verify tool can be invoked given current state.
        
        Returns:
            (True, None) if tool invocation is permitted
            (False, reason) if tool invocation is blocked
        """
        self.solver.push()
        
        # Create symbolic variables
        z3_tool = Const('tool', ToolSpec)
        z3_state = Const('state', AgentState)
        
        # Bind to actual values
        self.solver.add(tool.to_z3_constraints(z3_tool))
        self.solver.add(state.to_z3_constraints(z3_state))
        
        # Assert the NEGATION of can_invoke_tool
        # If UNSAT, the constraint holds (tool CAN be invoked)
        # If SAT, the constraint fails (tool CANNOT be invoked)
        self.solver.add(Not(can_invoke_tool(z3_tool, z3_state)))
        
        result = self.solver.check()
        self.solver.pop()
        
        if result == unsat:
            # Negation is unsatisfiable => constraint holds
            return (True, None)
        else:
            # Negation is satisfiable => constraint violated
            return (False, self._diagnose_tool_failure(tool, state))
    
    def check_continue_decision(
        self, 
        state: AgentStateRT
    ) -> Literal['continue', 'respond', 'satisfied']:
        """
        Determine whether agent should continue, respond, or is satisfied.
        
        Returns:
            'respond' - must respond (budget exhausted or done)
            'continue' - should continue (has budget, below threshold)
            'satisfied' - satisfaction threshold met
        """
        z3_state = Const('state', AgentState)
        
        # Check must_respond
        self.solver.push()
        self.solver.add(state.to_z3_constraints(z3_state))
        self.solver.add(must_respond(z3_state))
        must_respond_result = self.solver.check()
        self.solver.pop()
        
        if must_respond_result == sat:
            return 'respond'
        
        # Check should_continue
        self.solver.push()
        self.solver.add(state.to_z3_constraints(z3_state))
        self.solver.add(should_continue(z3_state))
        should_continue_result = self.solver.check()
        self.solver.pop()
        
        if should_continue_result == sat:
            return 'continue'
        
        return 'satisfied'
    
    def _diagnose_tool_failure(
        self, 
        tool: ToolSpecRT, 
        state: AgentStateRT
    ) -> str:
        """Generate human-readable failure reason."""
        reasons = []
        
        # Permission checks
        if tool.required_access > state.file_access:
            reasons.append(
                f"insufficient file access: need {AccessLevel(tool.required_access).name}, "
                f"have {state.file_access.name}"
            )
        if tool.requires_exec and not state.exec_allowed:
            reasons.append("execute permission required but not granted")
        
        # Budget checks
        if tool.base_cost > state.cost_budget:
            reasons.append(
                f"cost budget exceeded: need {tool.base_cost}, have {state.cost_budget}"
            )
        if tool.time_estimate > state.time_budget:
            reasons.append(
                f"time budget exceeded: need {tool.time_estimate}ms, have {state.time_budget}ms"
            )
        if tool.token_estimate > state.token_budget:
            reasons.append(
                f"token budget exceeded: need {tool.token_estimate}, have {state.token_budget}"
            )
        
        return "; ".join(reasons) if reasons else "unknown constraint violation"


# ============================================================================
# Z3 Optimization
# ============================================================================

def optimize_tool_selection(
    tools: list[ToolSpecRT],
    state: AgentStateRT,
    objective: Literal['min_cost', 'min_time', 'min_tokens'] = 'min_cost'
) -> Optional[ToolSpecRT]:
    """
    Use Z3 Optimize to select the best permitted tool.
    
    Args:
        tools: List of available tools
        state: Current agent state
        objective: What to minimize ('min_cost', 'min_time', 'min_tokens')
    
    Returns:
        The optimal tool, or None if no tool is permitted
    """
    if not tools:
        return None
    
    opt = Optimize()
    z3_state = Const('state', AgentState)
    
    # Bind state values
    opt.add(state.to_z3_constraints(z3_state))
    
    # Create choice variable (index into tools list)
    choice = Int('choice')
    opt.add(choice >= 0, choice < len(tools))
    
    # For each tool, create constraints
    z3_tools = []
    for i, tool in enumerate(tools):
        z3_tool = Const(f'tool_{i}', ToolSpec)
        opt.add(tool.to_z3_constraints(z3_tool))
        z3_tools.append(z3_tool)
        
        # If this tool is chosen, it must be invocable
        opt.add(Implies(choice == i, can_invoke_tool(z3_tool, z3_state)))
    
    # At least one tool must be chosen (and invocable)
    opt.add(Or(*[can_invoke_tool(z3_tools[i], z3_state) for i in range(len(tools))]))
    
    # Set optimization objective
    if objective == 'min_cost':
        cost_expr = Sum([If(choice == i, tools[i].base_cost, 0) for i in range(len(tools))])
        opt.minimize(cost_expr)
    elif objective == 'min_time':
        time_expr = Sum([If(choice == i, tools[i].time_estimate, 0) for i in range(len(tools))])
        opt.minimize(time_expr)
    else:  # min_tokens
        token_expr = Sum([If(choice == i, tools[i].token_estimate, 0) for i in range(len(tools))])
        opt.minimize(token_expr)
    
    if opt.check() == sat:
        model = opt.model()
        chosen_idx = model[choice].as_long()
        return tools[chosen_idx]
    
    return None


# ============================================================================
# State Update Functions (matching ACL2 state transitions)
# ============================================================================

def deduct_tool_cost(state: AgentStateRT, tool: ToolSpecRT) -> AgentStateRT:
    """
    ACL2: deduct-tool-cost
    
    Deduct tool costs from state, flooring at 0.
    """
    return AgentStateRT(
        iteration=state.iteration,
        max_iterations=state.max_iterations,
        token_budget=max(0, state.token_budget - tool.token_estimate),
        cost_budget=max(0, state.cost_budget - tool.base_cost),
        time_budget=max(0, state.time_budget - tool.time_estimate),
        file_access=state.file_access,
        exec_allowed=state.exec_allowed,
        satisfaction=state.satisfaction,
        done=state.done
    )


def increment_iteration(state: AgentStateRT) -> AgentStateRT:
    """ACL2: increment-iteration"""
    return AgentStateRT(
        iteration=state.iteration + 1,
        max_iterations=state.max_iterations,
        token_budget=state.token_budget,
        cost_budget=state.cost_budget,
        time_budget=state.time_budget,
        file_access=state.file_access,
        exec_allowed=state.exec_allowed,
        satisfaction=state.satisfaction,
        done=state.done
    )


def update_satisfaction(state: AgentStateRT, new_satisfaction: int) -> AgentStateRT:
    """ACL2: update-satisfaction"""
    return AgentStateRT(
        iteration=state.iteration,
        max_iterations=state.max_iterations,
        token_budget=state.token_budget,
        cost_budget=state.cost_budget,
        time_budget=state.time_budget,
        file_access=state.file_access,
        exec_allowed=state.exec_allowed,
        satisfaction=max(0, min(100, new_satisfaction)),  # clamp to 0-100
        done=state.done
    )


def mark_done(state: AgentStateRT) -> AgentStateRT:
    """ACL2: mark-done"""
    return AgentStateRT(
        iteration=state.iteration,
        max_iterations=state.max_iterations,
        token_budget=state.token_budget,
        cost_budget=state.cost_budget,
        time_budget=state.time_budget,
        file_access=state.file_access,
        exec_allowed=state.exec_allowed,
        satisfaction=state.satisfaction,
        done=True
    )


# ============================================================================
# Example Tool Definitions
# ============================================================================

EXAMPLE_TOOLS = {
    'read_file': ToolSpecRT(
        name='read_file',
        required_access=AccessLevel.READ,
        requires_exec=False,
        base_cost=1,
        time_estimate=100,
        token_estimate=500
    ),
    'write_file': ToolSpecRT(
        name='write_file',
        required_access=AccessLevel.READ_WRITE,
        requires_exec=False,
        base_cost=2,
        time_estimate=200,
        token_estimate=300
    ),
    'run_python': ToolSpecRT(
        name='run_python',
        required_access=AccessLevel.NONE,
        requires_exec=True,
        base_cost=5,
        time_estimate=5000,
        token_estimate=1000
    ),
    'web_search': ToolSpecRT(
        name='web_search',
        required_access=AccessLevel.NONE,
        requires_exec=False,
        base_cost=10,
        time_estimate=2000,
        token_estimate=2000
    ),
}


if __name__ == '__main__':
    # Quick smoke test
    checker = ReactConstraintChecker()
    
    state = AgentStateRT(
        file_access=AccessLevel.READ,
        exec_allowed=False,
        token_budget=5000,
        cost_budget=100,
        time_budget=30000
    )
    
    # Should succeed - read_file only needs READ access
    allowed, reason = checker.check_tool_invocation(EXAMPLE_TOOLS['read_file'], state)
    print(f"read_file: allowed={allowed}, reason={reason}")
    
    # Should fail - write_file needs READ_WRITE
    allowed, reason = checker.check_tool_invocation(EXAMPLE_TOOLS['write_file'], state)
    print(f"write_file: allowed={allowed}, reason={reason}")
    
    # Should fail - run_python needs execute permission
    allowed, reason = checker.check_tool_invocation(EXAMPLE_TOOLS['run_python'], state)
    print(f"run_python: allowed={allowed}, reason={reason}")
    
    # Test continue/respond decision
    decision = checker.check_continue_decision(state)
    print(f"Decision: {decision}")
    
    # Test optimization
    best = optimize_tool_selection(list(EXAMPLE_TOOLS.values()), state, 'min_cost')
    print(f"Optimal tool (min_cost): {best.name if best else None}")
