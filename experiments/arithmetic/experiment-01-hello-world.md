---
jupyter:
  jupytext:
    text_representation:
      extension: .md
      format_name: markdown
      format_version: '1.3'
      jupytext_version: 1.18.1
  kernelspec:
    display_name: ACL2
    language: acl2
    name: acl2
---

# ACL2 Hello World - Basic arithmetic theorem
This demonstrates a simple proof that addition is commutative

```acl2
(in-package "ACL2")
```

```acl2
; A simple theorem: addition is commutative
; ACL2 can prove this automatically
(defthm addition-commutative
  (equal (+ x y)
         (+ y x)))
```

```acl2
; Another basic theorem: associativity of addition
(defthm addition-associative
  (equal (+ (+ x y) z)
         (+ x (+ y z))))
```

```acl2
; A slightly more interesting theorem
; Need to specify that x is a number (ACL2's + is defined on all ACL2 objects)
(defthm add-zero
  (implies (acl2-numberp x)
           (equal (+ x 0)
                  x)))
```

```acl2
; Double a number is the same as adding it to itself
(defthm double-is-add
  (equal (* 2 x)
         (+ x x)))
```
