;;; -*- Mode: Lisp; Base: 8. ; -*-


(DEFMIC OCCURS-IN 1600 (KEY TERM) T)
(DEFMIC %INVOKE 1601 (CONTINUATION) T)
(DEFMIC %CELL0 1602 () T)
(DEFMIC %UNTRAIL 1603 (MARK) T)
(DEFMIC %UNIFY-TERM-WITH-TERM 1604 (TERM-1 TERM-2) T)
(DEFMIC %CONSTRUCT 1605 (TEMPLATE) T) 
(DEFMIC %UNIFY-TERM-WITH-TEMPLATE 1606 (TERM TEMPLATE) T)
(DEFMIC %CELL 1607 (VARIABLE-NAME) T)
(DEFMIC %REFERENCE 1610 (TERM) T)
(DEFMIC %DEREFERENCE 1611 (TERM) T)
(DEFMIC %CURRENT-ENTRYPOINT 1612 (PREDICATOR ALIST-LOCATION) T)

