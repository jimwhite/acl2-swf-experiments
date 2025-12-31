#!/usr/bin/env python3
"""
ACL2 MCP Client Integration Tests

Tests the ACL2 mcp-client.lisp code by running ACL2 and executing
the MCP client functions against a live mcp-proxy server.

Prerequisites:
- mcp-proxy running: mcp-proxy acl2-mcp --transport streamablehttp --port 8000 --pass-environment
- mcp-client.lisp certified

Run with: python test_acl2_mcp_client.py
"""

import subprocess
import sys
import re

MCP_ENDPOINT = "http://localhost:8000/mcp"

def run_acl2_test(test_name: str, acl2_code: str, success_pattern: str) -> bool:
    """Run ACL2 code and check output for success pattern."""
    print(f"Test: {test_name}...")
    
    # Wrap code in proper ACL2 session
    full_code = f'''(include-book "mcp-client")
{acl2_code}
'''
    
    try:
        result = subprocess.run(
            ["acl2"],
            input=full_code,
            capture_output=True,
            text=True,
            timeout=30,
            cwd="/workspaces/acl2-swf-experiments/experiments/agents"
        )
        output = result.stdout + result.stderr
        
        if re.search(success_pattern, output):
            print(f"  PASS")
            return True
        else:
            print(f"  FAIL: Pattern '{success_pattern}' not found")
            print(f"  Output (last 500 chars): {output[-500:]}")
            return False
            
    except subprocess.TimeoutExpired:
        print(f"  FAIL: Timeout")
        return False
    except Exception as e:
        print(f"  FAIL: {e}")
        return False


def test_mcp_connect() -> bool:
    """Test mcp-connect establishes a session."""
    code = f'''
(mv-let (err conn state)
  (mcp-connect "{MCP_ENDPOINT}" state)
  (prog2$ (cw "TEST-RESULT: err=~x0 conn=~x1~%" err conn)
          (mv err conn state)))
'''
    # Success: err is NIL and conn has session-id
    return run_acl2_test(
        "mcp-connect",
        code,
        r'TEST-RESULT: err=NIL'
    )


def test_mcp_evaluate() -> bool:
    """Test mcp-acl2-evaluate computes (+ 1 2 3) = 6."""
    code = f'''
(mv-let (err conn state)
  (mcp-connect "{MCP_ENDPOINT}" state)
  (if err
      (prog2$ (cw "TEST-RESULT: connect-err=~s0~%" err)
              (mv err nil state))
    (mv-let (eval-err result state)
      (mcp-acl2-evaluate conn "(+ 1 2 3)" state)
      (prog2$ (cw "TEST-RESULT: eval-err=~x0 result-contains-6=~x1~%" 
                  eval-err
                  (search "6" result))
              (mv eval-err result state)))))
'''
    # Success: result contains "6" (search returns position, not nil)
    return run_acl2_test(
        "mcp-acl2-evaluate",
        code,
        r'TEST-RESULT: eval-err=NIL result-contains-6=[0-9]+'
    )


def test_mcp_admit() -> bool:
    """Test mcp-acl2-admit accepts a valid function definition."""
    code = f'''
(mv-let (err conn state)
  (mcp-connect "{MCP_ENDPOINT}" state)
  (if err
      (prog2$ (cw "TEST-RESULT: connect-err=~s0~%" err)
              (mv err nil state))
    (mv-let (admit-err result state)
      (mcp-acl2-admit conn "(defun my-test-fn (x) (+ x 1))" state)
      (prog2$ (cw "TEST-RESULT: admit-err=~x0 contains-fn=~x1~%" 
                  admit-err
                  (search "MY-TEST-FN" result))
              (mv admit-err result state)))))
'''
    # Success: no error and result mentions the function
    return run_acl2_test(
        "mcp-acl2-admit",
        code,
        r'TEST-RESULT: admit-err=NIL contains-fn=[0-9]+'
    )


def test_mcp_prove() -> bool:
    """Test mcp-acl2-prove proves a simple theorem."""
    code = f'''
(mv-let (err conn state)
  (mcp-connect "{MCP_ENDPOINT}" state)
  (if err
      (prog2$ (cw "TEST-RESULT: connect-err=~s0~%" err)
              (mv err nil state))
    (mv-let (prove-err result state)
      (mcp-acl2-prove conn "(defthm plus-commutes-test (equal (+ a b) (+ b a)))" state)
      (prog2$ (cw "TEST-RESULT: prove-err=~x0 contains-qed=~x1~%" 
                  prove-err
                  (search "Q.E.D" result))
              (mv prove-err result state)))))
'''
    # Success: result contains Q.E.D.
    return run_acl2_test(
        "mcp-acl2-prove",
        code,
        r'TEST-RESULT: prove-err=NIL contains-qed=[0-9]+'
    )


def main():
    print("=" * 60)
    print("ACL2 MCP Client Integration Tests")
    print("=" * 60)
    print()
    print(f"Endpoint: {MCP_ENDPOINT}")
    print()
    
    results = []
    results.append(("mcp-connect", test_mcp_connect()))
    results.append(("mcp-acl2-evaluate", test_mcp_evaluate()))
    results.append(("mcp-acl2-admit", test_mcp_admit()))
    results.append(("mcp-acl2-prove", test_mcp_prove()))
    
    # Summary
    print()
    print("=" * 60)
    print("Summary")
    print("=" * 60)
    
    passed = sum(1 for _, ok in results if ok)
    total = len(results)
    
    for name, ok in results:
        print(f"  {name}: {'PASS' if ok else 'FAIL'}")
    
    print()
    print(f"Passed: {passed}/{total}")
    
    if passed == total:
        print("\nAll tests passed!")
        return 0
    else:
        print("\nSome tests failed.")
        return 1


if __name__ == "__main__":
    sys.exit(main())
