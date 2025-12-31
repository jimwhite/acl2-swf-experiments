#!/usr/bin/env python3
"""
MCP Client Integration Tests

Tests the MCP proxy endpoint at localhost:8000 using the streamable HTTP transport.
Run with: python test_mcp_integration.py

Requires: requests library (pip install requests)
"""

import json
import sys
import requests

MCP_ENDPOINT = "http://localhost:8000/mcp"
TIMEOUT = 10

def test_initialize():
    """Test MCP initialize and get session ID."""
    print("Test 1: Initialize connection...")
    
    request = {
        "jsonrpc": "2.0",
        "method": "initialize",
        "params": {
            "protocolVersion": "2024-11-05",
            "clientInfo": {"name": "python-test", "version": "0.1.0"},
            "capabilities": {}
        },
        "id": 1
    }
    
    headers = {
        "Content-Type": "application/json",
        "Accept": "application/json, text/event-stream"
    }
    
    try:
        resp = requests.post(MCP_ENDPOINT, json=request, headers=headers, timeout=TIMEOUT)
    except requests.exceptions.ConnectionError:
        print("  FAIL: Cannot connect to MCP proxy at", MCP_ENDPOINT)
        print("  Make sure mcp-proxy is running:")
        print("    mcp-proxy acl2-mcp --transport streamablehttp --port 8000 --pass-environment")
        return None
    
    if resp.status_code != 200:
        print(f"  FAIL: HTTP {resp.status_code}: {resp.text}")
        return None
    
    session_id = resp.headers.get("mcp-session-id")
    if not session_id:
        print("  FAIL: No mcp-session-id in response headers")
        print("  Response headers:", dict(resp.headers))
        return None
    
    result = resp.json()
    if "result" not in result:
        print(f"  FAIL: No result in response: {result}")
        return None
    
    print(f"  PASS: Got session ID: {session_id[:16]}...")
    return session_id


def test_evaluate(session_id: str):
    """Test MCP evaluate tool."""
    print("Test 2: Evaluate (+ 1 2 3)...")
    
    request = {
        "jsonrpc": "2.0",
        "method": "tools/call",
        "params": {
            "name": "evaluate",
            "arguments": {"code": "(+ 1 2 3)"}
        },
        "id": 2
    }
    
    headers = {
        "Content-Type": "application/json",
        "Accept": "application/json",
        "Mcp-Session-Id": session_id
    }
    
    resp = requests.post(MCP_ENDPOINT, json=request, headers=headers, timeout=TIMEOUT)
    
    if resp.status_code != 200:
        print(f"  FAIL: HTTP {resp.status_code}: {resp.text}")
        return False
    
    result = resp.json()
    if "error" in result:
        print(f"  FAIL: JSON-RPC error: {result['error']}")
        return False
    
    # Extract text content from MCP response
    content = result.get("result", {}).get("content", [])
    if not content:
        print(f"  FAIL: No content in result: {result}")
        return False
    
    text = content[0].get("text", "")
    if "6" in text:
        print(f"  PASS: Got result containing '6'")
        return True
    else:
        print(f"  FAIL: Expected '6' in result, got: {text[:100]}")
        return False


def test_admit(session_id: str):
    """Test MCP admit tool (test definition without saving)."""
    print("Test 3: Admit function definition...")
    
    request = {
        "jsonrpc": "2.0",
        "method": "tools/call",
        "params": {
            "name": "admit",
            "arguments": {"code": "(defun test-double (x) (* 2 x))"}
        },
        "id": 3
    }
    
    headers = {
        "Content-Type": "application/json",
        "Accept": "application/json",
        "Mcp-Session-Id": session_id
    }
    
    resp = requests.post(MCP_ENDPOINT, json=request, headers=headers, timeout=TIMEOUT)
    
    if resp.status_code != 200:
        print(f"  FAIL: HTTP {resp.status_code}: {resp.text}")
        return False
    
    result = resp.json()
    if "error" in result:
        print(f"  FAIL: JSON-RPC error: {result['error']}")
        return False
    
    content = result.get("result", {}).get("content", [])
    if not content:
        print(f"  FAIL: No content in result: {result}")
        return False
    
    text = content[0].get("text", "")
    if "TEST-DOUBLE" in text.upper() or "success" in text.lower():
        print(f"  PASS: Definition admitted")
        return True
    else:
        print(f"  FAIL: Unexpected result: {text[:200]}")
        return False


def test_prove(session_id: str):
    """Test MCP prove tool."""
    print("Test 4: Prove simple theorem...")
    
    request = {
        "jsonrpc": "2.0",
        "method": "tools/call",
        "params": {
            "name": "prove",
            "arguments": {"code": "(defthm plus-commutes-test (equal (+ a b) (+ b a)))"}
        },
        "id": 4
    }
    
    headers = {
        "Content-Type": "application/json",
        "Accept": "application/json",
        "Mcp-Session-Id": session_id
    }
    
    resp = requests.post(MCP_ENDPOINT, json=request, headers=headers, timeout=TIMEOUT)
    
    if resp.status_code != 200:
        print(f"  FAIL: HTTP {resp.status_code}: {resp.text}")
        return False
    
    result = resp.json()
    if "error" in result:
        print(f"  FAIL: JSON-RPC error: {result['error']}")
        return False
    
    content = result.get("result", {}).get("content", [])
    if not content:
        print(f"  FAIL: No content in result: {result}")
        return False
    
    text = content[0].get("text", "")
    # Look for success indicators
    if "Q.E.D." in text or "PLUS-COMMUTES-TEST" in text.upper():
        print(f"  PASS: Theorem proved")
        return True
    else:
        print(f"  FAIL: Proof may have failed: {text[:200]}")
        return False


def test_list_sessions(session_id: str):
    """Test MCP list_sessions tool."""
    print("Test 5: List sessions...")
    
    request = {
        "jsonrpc": "2.0",
        "method": "tools/call",
        "params": {
            "name": "list_sessions",
            "arguments": {}
        },
        "id": 5
    }
    
    headers = {
        "Content-Type": "application/json",
        "Accept": "application/json",
        "Mcp-Session-Id": session_id
    }
    
    resp = requests.post(MCP_ENDPOINT, json=request, headers=headers, timeout=TIMEOUT)
    
    if resp.status_code != 200:
        print(f"  FAIL: HTTP {resp.status_code}: {resp.text}")
        return False
    
    result = resp.json()
    if "error" in result:
        print(f"  FAIL: JSON-RPC error: {result['error']}")
        return False
    
    content = result.get("result", {}).get("content", [])
    if not content:
        print(f"  FAIL: No content in result: {result}")
        return False
    
    text = content[0].get("text", "")
    # Should return something (even "No active sessions")
    if text:
        print(f"  PASS: Got sessions list")
        return True
    else:
        print(f"  FAIL: Empty result")
        return False


def main():
    print("=" * 60)
    print("MCP Integration Tests")
    print("=" * 60)
    print()
    
    # Test 1: Initialize
    session_id = test_initialize()
    if not session_id:
        print("\nFATAL: Cannot establish MCP session. Aborting.")
        sys.exit(1)
    
    print()
    
    # Run remaining tests
    results = []
    results.append(("evaluate", test_evaluate(session_id)))
    print()
    results.append(("admit", test_admit(session_id)))
    print()
    results.append(("prove", test_prove(session_id)))
    print()
    results.append(("list_sessions", test_list_sessions(session_id)))
    
    # Summary
    print()
    print("=" * 60)
    print("Summary")
    print("=" * 60)
    
    passed = sum(1 for _, ok in results if ok)
    total = len(results) + 1  # +1 for initialize
    
    print(f"  Initialize: PASS")
    for name, ok in results:
        print(f"  {name}: {'PASS' if ok else 'FAIL'}")
    
    print()
    print(f"Passed: {passed + 1}/{total}")
    
    if passed + 1 == total:
        print("\nAll tests passed!")
        sys.exit(0)
    else:
        print("\nSome tests failed.")
        sys.exit(1)


if __name__ == "__main__":
    main()
