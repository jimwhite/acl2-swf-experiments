#!/usr/bin/env python3
"""
Forest Friends Frenzy — Logic Puzzle Solver & Solution Verifier
================================================================
Uses python-constraint to enumerate ALL valid solutions and check
whether the proposed solution grid is correct and unique.

Friends:    Winnie the Pooh, Piglet, Tigger, Eeyore
Activities: honey tasting, bouncing, exploring, gardening
Times:      morning(1), noon(2), afternoon(3), evening(4)

Clues:
  1. Tigger does his activity earlier than Eeyore.
  2. Honey tasting happens later than exploring.
  3. Piglet performs his activity in the morning.
  4. Winnie the Pooh does not like gardening.
"""

from constraint import Problem, AllDifferentConstraint

# ── Encoding ────────────────────────────────────────────────────
TIMES      = {"morning": 1, "noon": 2, "afternoon": 3, "evening": 4}
ACTIVITIES = {"honey_tasting": 1, "bouncing": 2, "exploring": 3, "gardening": 4}
FRIENDS    = ["pooh", "piglet", "tigger", "eeyore"]

TIME_NAME     = {v: k for k, v in TIMES.items()}
ACTIVITY_NAME = {v: k for k, v in ACTIVITIES.items()}


def solve():
    p = Problem()

    # Variables: each friend gets a time slot and an activity
    for f in FRIENDS:
        p.addVariable(f"{f}_time", list(TIMES.values()))
        p.addVariable(f"{f}_activity", list(ACTIVITIES.values()))

    # All-different constraints
    p.addConstraint(AllDifferentConstraint(), [f"{f}_time" for f in FRIENDS])
    p.addConstraint(AllDifferentConstraint(), [f"{f}_activity" for f in FRIENDS])

    # Clue 3: Piglet performs his activity in the morning
    p.addConstraint(lambda t: t == TIMES["morning"], ["piglet_time"])

    # Clue 1: Tigger does his activity earlier than Eeyore
    p.addConstraint(lambda tt, et: tt < et, ["tigger_time", "eeyore_time"])

    # Clue 4: Winnie the Pooh does not like gardening
    p.addConstraint(lambda a: a != ACTIVITIES["gardening"], ["pooh_activity"])

    # Clue 2: The friend who loves honey tasting performs later
    #          than the friend who enjoys exploring.
    # We need to find which friend does honey tasting and which does
    # exploring, then compare their times.
    # Encode: for every pair of friends (f1, f2),
    #   if f1 does honey tasting and f2 does exploring, then f1_time > f2_time
    for f1 in FRIENDS:
        for f2 in FRIENDS:
            if f1 == f2:
                continue
            p.addConstraint(
                lambda a1, t1, a2, t2: (
                    (a1 != ACTIVITIES["honey_tasting"] or
                     a2 != ACTIVITIES["exploring"] or
                     t1 > t2)
                ),
                [f"{f1}_activity", f"{f1}_time",
                 f"{f2}_activity", f"{f2}_time"],
            )

    solutions = p.getSolutions()
    return solutions


def format_solution(sol):
    rows = []
    for f in FRIENDS:
        t = TIME_NAME[sol[f"{f}_time"]]
        a = ACTIVITY_NAME[sol[f"{f}_activity"]]
        rows.append(f"  {f:10s}  {a:16s}  {t}")
    return "\n".join(rows)


# ── Proposed solution from the puzzle description ───────────────
PROPOSED = {
    "pooh_activity":   ACTIVITIES["bouncing"],
    "pooh_time":       TIMES["afternoon"],
    "piglet_activity": ACTIVITIES["gardening"],
    "piglet_time":     TIMES["morning"],
    "tigger_activity": ACTIVITIES["exploring"],
    "tigger_time":     TIMES["noon"],
    "eeyore_activity": ACTIVITIES["honey_tasting"],
    "eeyore_time":     TIMES["evening"],
}


def main():
    solutions = solve()

    print(f"Total valid solutions: {len(solutions)}\n")
    for i, sol in enumerate(solutions, 1):
        print(f"── Solution {i} ──")
        print(format_solution(sol))
        print()

    # Check whether proposed solution appears
    proposed_match = any(
        all(sol[k] == v for k, v in PROPOSED.items())
        for sol in solutions
    )
    print(f"Proposed solution is valid: {proposed_match}")

    if len(solutions) == 1:
        print("The puzzle has a UNIQUE solution. ✓")
    else:
        print(f"⚠  The puzzle has {len(solutions)} solutions — it is NOT unique.")
        print("   The clues are under-constrained.")

    # ── Detailed reasoning trace ────────────────────────────────
    print("\n── Reasoning trace ──")
    print("Step 1 (Clue 3): Piglet → Morning  ✓  (direct)")
    print("Step 2 (Clue 1): Tigger < Eeyore.")
    print("   Remaining slots for {Pooh, Tigger, Eeyore}: Noon, Afternoon, Evening")
    print("   Possible orderings (Tigger, Eeyore, Pooh):")
    orderings = []
    for sol in solutions:
        tt = TIME_NAME[sol["tigger_time"]]
        et = TIME_NAME[sol["eeyore_time"]]
        pt = TIME_NAME[sol["pooh_time"]]
        orderings.append((tt, et, pt))
    for o in sorted(set(orderings)):
        print(f"     Tigger={o[0]}, Eeyore={o[1]}, Pooh={o[2]}")

    # Check the puzzle description's flawed step
    print("\n── Checking puzzle description reasoning ──")
    desc_claim = "Tigger=Noon, Eeyore=Afternoon (then Pooh=Evening)"
    noon_afternoon = any(
        sol["tigger_time"] == TIMES["noon"] and
        sol["eeyore_time"] == TIMES["afternoon"]
        for sol in solutions
    )
    print(f'Description claims: "{desc_claim}"')
    print(f"  Is this the only possibility?  {noon_afternoon and len(orderings) == 1}")
    if not (noon_afternoon and len(set(orderings)) == 1):
        print("  ⇒  The reasoning in the description has a LOGICAL ERROR.")


if __name__ == "__main__":
    main()
