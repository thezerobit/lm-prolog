;;; -*- Mode: Lisp; Package: Prolog; Base: 10. ; -*-
;;; Written in 1983 by Ken Kahn and Mats Carlsson.


;;; This file contains code to support reset lists for variable bindings and
;;; unwind-protects.

;Trails are arrays, 10000. long for the top-level, 500. for lazy bags and the like.
;They are recycled.  It is arranged so that the variable *TRAIL* is invisibly linked
;to the current trail's active count. 
;DEALLOCATE-A-TRAIL below ensures that arrays are restored
;to empty state before recycling them.

(defresource trail (size)
  :constructor (make-array size ':leader-length 2 ':leader-list (list 0 size))
  :deinitializer untrail-fully)

(defresource symbol-table ()
  :constructor (make-hash-table)
  :deinitializer clrhash)

(defun link-*trail*-count ()
  (%p-store-tag-and-pointer
    (value-cell-location '*trail*)
    dtp-external-value-cell-pointer
    (locf (fill-pointer *trail-array*)))
  (%p-store-cdr-code (locf *trail-array*) cdr-next))

;;The compiler uses a trail.
(defvar *original-trail-array* (allocate-resource 'trail 500))

;;Keep track of top level trails.
(defvar *top-level-trail-array* (allocate-resource 'trail 100))

(setq *trail-array* *original-trail-array*)

(link-*trail*-count)

(defmacro with-trail (array &body body)
  `(let ((*trail-array* ,array) (*trail*))
     (link-*trail*-count)
     ,@body))

(defun allocate-a-trail (&optional (size 500.))
  (let (array)
    (unwind-protect
      (setq array (allocate-resource 'trail size))
      (and array (trail (continuation (funcall 'deallocate-a-trail array)))))))

(defun deallocate-a-trail (array)
  (with-trail array (untrail 0))
  (deallocate-resource 'trail array))

(defun untrail-fully (array)
  (with-trail array (untrail 0)))

