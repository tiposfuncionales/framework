;;; Fri Feb 26 00:57:46 1993 by Mark Kantrowitz <mkant@GLINDA.OZ.CS.CMU.EDU>
;;; framework-examples.lisp -- 1477 bytes

;;; ****************************************************************
;;; FrameWork Examples *********************************************
;;; ****************************************************************

;;; This file contains a few examples of using FrameWork. The examples
;;; were written by Nick Afshartous <nick@dmi.stevens-tech.edu> or 
;;; <afshar@cs.nyu.edu>.

(eval-when (compile load eval)
  (unless (find :framework *features*)
    (warn "FrameWork must be loaded before using this file.")))

;;; Some defclass examples 

;;; Special symbols like if-needed, if-added, value must be keywords to
;;; avoid package problems. This is also true in (init, before, and after)
;;; method definitions.

(fw:defclass pane ()
  (pane-slot
   (:IF-NEEDED (format t "~&if-needed daemon"))))
   
(fw:defclass door (pane)
  (door-size 
   (:IF-ADDED  (format t "~&if-added  daemon------------------"))
   (:IF-NEEDED (format t "~&if-needed daemon------------------")))
  (fred
   (:IF-ADDED  (fw:send fw:%frame :init))))
   
(fw:defmethod (:init door :before) ()
  (format t "~&in :BEFORE method, self = ~a" fw:%frame))

(fw:defmethod (:init door) ()
   (format t "~&in primary method"))
(fw:defmethod (:init door :after) ()
   (format t "~&in :AFTER method"))

;;; execute :if-needed demon
(fw:frameget 'door 'door-size :value nil)

;;; execute methods via :if-added demon
(fw:frameput 'door 'fred :value 5)

;;; *EOF*
