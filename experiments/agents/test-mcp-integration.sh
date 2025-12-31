#!/bin/bash
# Integration tests for MCP client using curl
# 
# Prerequisites: mcp-proxy running on port 8000
#   mcp-proxy acl2-mcp --transport streamablehttp --port 8000 --allow-origin='*' --pass-environment
#
# Usage: ./test-mcp-integration.sh

ENDPOINT="http://localhost:8000/mcp"
PASS=0
FAIL=0

echo "===== MCP Integration Tests ====="
echo "Endpoint: $ENDPOINT"
echo ""

# Test 1: Initialize and get session ID
echo -n "Test 1: Initialize connection... "
INIT_RESPONSE=$(curl -s -i -X POST "$ENDPOINT" \
  -H "Content-Type: application/json" \
  -H "Accept: application/json, text/event-stream" \
  -d '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2024-11-05","capabilities":{},"clientInfo":{"name":"test","version":"1.0"}}}')

SESSION_ID=$(echo "$INIT_RESPONSE" | grep -i "mcp-session-id:" | cut -d' ' -f2 | tr -d '\r')

if [ -n "$SESSION_ID" ]; then
  echo "PASS (session=$SESSION_ID)"
  PASS=$((PASS + 1))
else
  echo "FAIL (no session ID in response)"
  echo "$INIT_RESPONSE"
  FAIL=$((FAIL + 1))
  echo ""
  echo "===== Results: $PASS passed, $FAIL failed ====="
  exit 1
fi

# Test 2: Evaluate simple expression
echo -n "Test 2: Evaluate (+ 1 2 3)... "
EVAL_RESPONSE=$(curl -s -X POST "$ENDPOINT" \
  -H "Content-Type: application/json" \
  -H "Accept: application/json" \
  -H "Mcp-Session-Id: $SESSION_ID" \
  -d '{"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"evaluate","arguments":{"code":"(+ 1 2 3)"}}}')

if echo "$EVAL_RESPONSE" | grep -q '"result"'; then
  echo "PASS"
  PASS=$((PASS + 1))
else
  echo "FAIL"
  echo "$EVAL_RESPONSE"
  FAIL=$((FAIL + 1))
fi

# Test 3: Admit a function
echo -n "Test 3: Admit defun... "
ADMIT_RESPONSE=$(curl -s -X POST "$ENDPOINT" \
  -H "Content-Type: application/json" \
  -H "Accept: application/json" \
  -H "Mcp-Session-Id: $SESSION_ID" \
  -d '{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"admit","arguments":{"code":"(defun test-fn (x) (+ x 1))"}}}')

if echo "$ADMIT_RESPONSE" | grep -q '"result"'; then
  echo "PASS"
  PASS=$((PASS + 1))
else
  echo "FAIL"
  echo "$ADMIT_RESPONSE"
  FAIL=$((FAIL + 1))
fi

# Test 4: Prove simple theorem
echo -n "Test 4: Prove theorem... "
PROVE_RESPONSE=$(curl -s -X POST "$ENDPOINT" \
  -H "Content-Type: application/json" \
  -H "Accept: application/json" \
  -H "Mcp-Session-Id: $SESSION_ID" \
  -d '{"jsonrpc":"2.0","id":4,"method":"tools/call","params":{"name":"prove","arguments":{"code":"(defthm test-thm (equal (+ 1 1) 2))"}}}')

if echo "$PROVE_RESPONSE" | grep -q '"result"'; then
  echo "PASS"
  PASS=$((PASS + 1))
else
  echo "FAIL"
  echo "$PROVE_RESPONSE"
  FAIL=$((FAIL + 1))
fi

# Test 5: List sessions
echo -n "Test 5: List sessions... "
LIST_RESPONSE=$(curl -s -X POST "$ENDPOINT" \
  -H "Content-Type: application/json" \
  -H "Accept: application/json" \
  -H "Mcp-Session-Id: $SESSION_ID" \
  -d '{"jsonrpc":"2.0","id":5,"method":"tools/call","params":{"name":"list_sessions","arguments":{}}}')

if echo "$LIST_RESPONSE" | grep -q '"result"'; then
  echo "PASS"
  PASS=$((PASS + 1))
else
  echo "FAIL"
  echo "$LIST_RESPONSE"
  FAIL=$((FAIL + 1))
fi

echo ""
echo "===== Results: $PASS passed, $FAIL failed ====="

if [ $FAIL -gt 0 ]; then
  exit 1
fi
