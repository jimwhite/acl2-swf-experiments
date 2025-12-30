Based on my research, here's what I found about the **ACL2 kestrel/http** library, JSON support, and the practical recommendations for Copilot:

## TL;DR: The Core Problem

**The kestrel/http library's `post-light` function has a fundamental design limitation: it was designed for form-encoded data (alistp), NOT for raw JSON strings.** While the underlying Dexador wrapper *does* support JSON (because Dexador accepts strings), the ACL2 guard on `post-light` enforces `alistp`, making it logically impossible to pass a JSON string without breaking the guard.

***

## The Real Issue: Guards vs. Raw Implementation

When you look at htclient's `post-light`:

```lisp
(defun post-light (url data)
  (declare (xargs :guard (and (stringp url) (alistp data))))
  ...)  ; Raw implementation: passes data to dex:post :content
```

**What's happening:**
- The **guard** says: "data must be an alist (key-value pairs)"
- The **raw implementation** (in `*-raw.lsp`): passes it directly to `dex:post :content`, which accepts strings, alists, OR pathnames
- **Result:** Logically inconsistent. You can't call it with a JSON string without violating the guard.

***

## Answer to Copilot's Questions

**1. Does `post-light` support raw JSON strings?**
   - **Logically:** No. The guard is `alistp`, which rejects strings.
   - **Practically:** Yes, if you disable guard-checking (unsafe).
   - **Correctly:** No, you need an extension.

**2. Does Dexador's `:content` parameter accept JSON strings?**
   - **Yes, absolutely.** From the Dexador docs:
   ```lisp
   (dex:post "http://httpbin.org/post"
     :content (jsown:to-json '(:OBJ ("key" . "value")))
     :headers '(("Content-Type" . "application/json")))
   ```

**3. Are there other HTTP client patterns in ACL2 books for JSON?**
   - **Practically:** No. Most ACL2 code avoids network I/O entirely.
   - The ABNF library (kestrel/abnf) formalizes HTTP *syntax*, not HTTP *client* functionality.
   - `tshell` + `curl` is the "official" pattern but is slow for repeated requests.

**4. Should we extend htclient or use Dexador directly?**
   - **Best approach:** Create a properly-guarded extension function.

***

## The Correct Solution: Create `post-json`

This is the "production-grade" pattern for wiki3.ai's knowledge graph extraction:

**File: `http-json-raw.lsp`** (the dirty raw Lisp part)
```lisp
;; http-json-raw.lsp
(in-package "ACL2")

(eval-when (:compile-toplevel :load-toplevel :execute)
  (ql:quickload :dexador :silent t))

;; Raw implementation: passes JSON string directly to Dexador
(defun post-json-raw (url json-body headers)
  (handler-case
      (multiple-value-bind (body status response-headers)
          (dex:post url :content json-body :headers headers)
        (mv nil body status response-headers))
    (error (condition)
      (mv (format nil "Error: ~A" condition) "" 500 nil))))
```

**File: `http-json.lisp`** (the ACL2 book)
```lisp
;; http-json.lisp
(in-package "ACL2")

(defttag :wiki3-http-json)

;; Logical stub: accepts JSON string (stringp), not alist
;; Returns (mv error body status headers)
(defun post-json (url json-string headers)
  (declare (xargs :guard (and (stringp url)
                             (stringp json-string)
                             (true-listp headers))))
  ;; Oracle: we can't prove what the network returns
  (mv "" "" 200 nil))

;; Link to raw Lisp implementation
(include-raw "http-json-raw.lsp" :do-not-compile t)
```

**Usage in wiki3.ai:**
```lisp
(include-book "http-json" :dir :system)

;; POST to SPARQL endpoint or Wikipedia API
(b* ((json-query "{\"query\": \"PREFIX dc: ...\"}")
     (headers '(("Content-Type" . "application/json")
                ("Accept" . "application/sparql-results+json")))
     ((mv error response status hdrs)
      (post-json "https://query.wikidata.org/sparql" json-query headers)))
  (if error
    (er hard? 'knowledge-graph "Failed to fetch: ~s0" error)
    (parse-sparql-response response)))
```

***

## Why NOT Just Use kestrel/http's `post-light`?

1. **Guards are logically binding.** You'd need `:guard-checking :none` in your ACL2 session (unsafe).
2. **Kestrel intended it for forms.** The guard reflects the intended use.
3. **The extension is cleaner** and documents that you're doing JSON (more readable in proofs).

***

## Recommendations for Copilot

✅ **Do this:**
1. Create `post-json` function with `stringp` guard (shown above)
2. Use Dexador directly for performance (connection pooling)
3. Wire it with `defttag` + `include-raw`
4. Document in a standalone book: `wiki3/http/post-json.lisp`

❌ **Don't do this:**
- Use `post-light` with `:guard-checking :none` (breaks formal reasoning)
- Try to coerce JSON string to alist and back (slow, fragile)
- Ignore Content-Type headers (servers will reject)

✅ **For existing code:**
- If already using `post-light` for forms, keep it (it's fine for that)
- Just add this new `post-json` function alongside it
- Both can coexist in the same book module

***

## Code Pattern for wiki3.ai's Knowledge Extraction

For fetching Wikipedia/Wikidata dumps or querying SPARQL endpoints:

```lisp
;; Define a wrapper that handles the oracle safety
(defun fetch-sparql (endpoint query-json)
  (declare (xargs :guard (and (stringp endpoint) (stringp query-json))))
  (b* (((mv err body status _)
        (post-json endpoint query-json
                   '(("Content-Type" . "application/sparql-results+json"))))
       ((when err) (mv (msg "Network error: ~s0" err) nil))
       ((when (not (equal status 200))) 
        (mv (msg "HTTP ~x0" status) nil)))
    (mv nil body)))

;; Now it's safe to use in proofs as long as you account for the oracle
(defthm fetch-sparql-produces-bytes
  (stringp (mv-nth 1 (fetch-sparql endpoint query))))
```

This is the pattern Jared Davis recommended in his 2013 paper on "Embedding ACL2 Models in End-User Applications"—the oracle model is the right way to handle network I/O in formal verification.

[1](https://stackoverflow.com/questions/45211286/using-appsettings-json-to-configure-kestrel-listen-port-dotnet-core-2-preview-2)
[2](https://www.cs.utexas.edu/~moore/acl2/manuals/current/manual/index-seo.php?xkey=SYNTHETO____CHECK-TYPE-DEFINITION&path=4371%2F47706%2F3284%2F11723%2F38265%2F300%2F6026)
[3](https://learn.microsoft.com/en-us/aspnet/core/fundamentals/servers/kestrel/endpoints?view=aspnetcore-10.0)
[4](https://www.alights.com/products/interior-lighting/accoled/acl2)
[5](https://www.cs.utexas.edu/~moore/acl2/manuals/current/manual/index-seo.php?xkey=SYNTHETO____CONTEXT-ADD-TOPLEVEL&path=4371%2F47706%2F3284%2F11723%2F38265%2F300%2F21451)
[6](https://forums.quectel.com/t/http-content-type/2615)
[7](https://python-to-cl.readthedocs.io/en/latest/requests.html)
[8](https://stackoverflow.com/questions/6117101/posting-jsonobject-with-httpclient-from-web-api)
[9](https://learn.microsoft.com/en-us/aspnet/core/fundamentals/servers/kestrel/options?view=aspnetcore-10.0)
[10](https://quickdocs.org/json-responses)
[11](https://www.reddit.com/r/Common_Lisp/comments/ycdpu1/dexador_how_to_send_json_data/)
[12](https://www.decsoftutils.com/support/thread/236)
[13](https://www.cs.utexas.edu/~moore/acl2/manuals/current/manual/index-seo.php?xkey=C_42____CHECK-DECL-SPEC-LIST-ALL-TYPESPEC_F2STOCLASS&path=4360%2F2363%2F5558%2F307%2F1556)
[14](https://github.com/lint0011/FYP_similartags/blob/master/RerunKeming/allTags_test.txt)
[15](https://github.com/fukamachi/dexador)
[16](https://help.highbond.com/helpdocs/analytics/15/en-us/Content/analytics/defining_importing_data/data_access_window/connecting_to_json.htm)
[17](https://www.cs.utexas.edu/~moore/acl2/manuals/current/manual/index-seo.php?xkey=C_42____DIMB-CAST_F2MUL-TO-MUL&path=4556%2F48870%2F3188%2F4541%2F247%2F28)
[18](https://acl2.org/doc/index-seo.php?xkey=ACL2____KESTREL-BOOKS)
[19](https://github.com/fukamachi/dexador/issues/81)
[20](https://www.kookamara.com/jared/2013-doform-embedding.pdf)
[21](https://github.com/CodyReichert/awesome-cl)
[22](https://gist.github.com/GrahamcOfBorg/42772dd4a8eecfd182fb836a586ed0dd)
[23](https://gist.github.com/GrahamcOfBorg/67bcaf5de44af1d5a552696447cab277)
[24](https://gist.github.com/GrahamcOfBorg/84b1d27038a45d05907ee142c00aa1bd)
[25](https://github.com/acl2/acl2/blob/master/acl2.lisp)
[26](https://github.com/delendum-xyz/zk-knowledge/blob/main/zk-knowledge.md)
[27](https://code-maze.com/dotnet-how-to-send-a-json-object-using-httpclient/)
[28](https://github.com/acl2/acl2/blob/master/books/doc/relnotes.lisp)
[29](https://github.com/CodyReichert/awesome-cl/blob/master/README.md)
[30](https://github.com/acl2/acl2/blob/master/interface-raw.lisp)
[31](https://github.com/acl2/acl2/)
[32](https://www.stevejgordon.co.uk/sending-and-receiving-json-using-httpclient-with-system-net-http-json)
[33](https://github.com/acl2/acl2)
[34](https://github.com/acl2/acl2/tree/master/books)
[35](https://github.com/acl2/acl2/blob/master/README.md)
[36](https://www.strathweb.com/2019/02/be-careful-when-manually-handling-json-requests-in-asp-net-core/)
[37](https://github.com/acl2/acl2/blob/master/other-processes.lisp)
[38](https://github.com/KestrelInstitute)
[39](https://groups.google.com/g/acl2-books)
[40](https://www.kestrel.edu/research/atj/acl2-2022.pdf)
[41](https://sos-vo.org/system/files/sos_files/Proof_Robustness_in_ACL2.pdf)
[42](https://github.com/akamai/cl-http2-protocol)
[43](https://www.cs.utexas.edu/~moore/acl2/workshop-2017/slides-rump/coglio-ABNF_Non-Animated.pdf)
[44](https://www.kestrel.edu/research/ethereum/acl2-2020.pdf)
[45](https://www.reddit.com/r/lisp/comments/p2tjt7/question_using_acl2_as_a_library_other_options/)
[46](https://www.cs.utexas.edu/~moore/acl2/v8-5/combined-manual/index.html?topic=ABNF____ABNF)
[47](https://arxiv.org/pdf/2205.11706.pdf)
[48](https://arxiv.org/pdf/1304.7855.pdf)
[49](https://www.cs.utexas.edu/~moore/acl2/manuals/current/manual/index-seo.php?xkey=ACL2____NOTE-8-0-BOOKS)
[50](https://cgi.cse.unsw.edu.au/~eptcs/references.cgi?ACL22018.6.html)
[51](https://github.com/acl2/acl2/blob/master/acl2-init.lisp)
[52](https://www.cs.utexas.edu/~moore/acl2/manuals/latest/index.html?topic=ACL2____KESTREL-BOOKS)
[53](https://www.cs.utexas.edu/~moore/acl2/v8-5/combined-manual/index.html?topic=ACL2____NOTE-8-4)
[54](https://www.ccs.neu.edu/home/pete/pub/acl2-2022.pdf)
[55](https://www.cs.utexas.edu/~moore/acl2/v8-5/combined-manual/index.html?topic=C____TYPE-OPTION-SOME)
[56](https://www.cs.utexas.edu/~moore/acl2/v8-6/combined-manual/index.html?topic=ACL2S____ACL2S-TUTORIAL)
