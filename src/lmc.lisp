;;;; lmc.lisp
;;;;
;;;; @author  Ayoub Chouak (a.chouak@protonmail.com)
;;;; @brief   AOT LMC Assembler and Execution Engine
;;;; @license MIT
;;;;

;;; Functions
(defun filter (fn lst)
  (cond ((null lst) nil)
	((funcall fn (first lst))
	 (cons (first lst) (filter fn (rest lst))))
	(T (filter fn (rest lst)))))

;;; Structs
(defstruct dfa-delta next-state)
(defstruct dfa-delta-ex next-state output)

;;; Regex constants
(defun char-list-range (start end)
  (cond ((char= start end) (list end))
	(T (cons start (char-list-range
			(code-char
			 (+ (char-code start) 1))
			end)))))
(defun rx-match (symbol rx-const)
  (member symbol rx-const))

(defvar [a-z] (char-list-range #\a #\z))
(defvar [a-z]^ (char-list-range #\A #\Z))
(defvar [0-9] (char-list-range #\0 #\9))
(defvar \s (list #\Space #\Tab))

;;; @section Lexer
(defun dfa-delta-chk (state state-chk symbol rx)
  (and (string= state state-chk) (rx-match symbol rx)))

;;; Check if `state` is final
(defun dfa-final (state)
  (member state *lex-final-states*))

;;; Delta function handler
(defun dfa-delta (state symbol mem)
  (cond ((dfa-delta-chk state "q0" symbol \s)
         (make-dfa-delta :next-state "q1_ws"))
        ((dfa-delta-chk state "q1_ws" symbol \s)
         (make-dfa-delta :next-state "q1_ws"))
        (T nil)))

;;; Initial and final states
(defvar *lex-initial-state* "q0")
(defvar *lex-final-states* (list "q1_ws"))

(defun lex-delta-db-lookup (state)
  (find state *lex-delta-db* :test #'dfa-delta-test-fn))

;;; @section DFA (Deterministic Finite Automata)
(defun dfa-accept (str state mem lex)
  (cond ((> (length str))
         (let ((next (dfa-delta state (char str 0) mem)))
           (when (not (null next))
             (dfa-accept (subseq str 1)
                         (dfa-delta-next-state next)
                         (string-append mem (char str 0))
                         lex)))
         ;;; Accept
         ((dfa-final state) (append lex '(mem)))
         (T nil))))