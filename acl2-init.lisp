(when (find-package "ACL2")
  ;; Suppress as much as possible at startup except for the LD info.
  (set (intern "*PRINT-STARTUP-BANNER*" "ACL2") nil))
