;;this is for generating a new LM-Prolog load band

(login-setq base 10. ibase 10. *nopoint t zwei:*file-versions-kept* 1.)

(load "load")
(COND ((STRING-EQUAL SITE-NAME "UPMAIL")	;You way want this too
       (make-system site-name)))
(load-prolog)

;;typing control-y will yank this into the read buffer
#-symbolics
(zwei:kill-string "(disk-save ")
