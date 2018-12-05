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

;;; Lexer
(defun dfa-delta (state symbol)
  (cond ((rx-match symbol \s) nil)))

(defvar *lex-initial-state* nil)
(defvar *lex-final-state* nil)

(defun lex-delta-db-lookup (state)
  (find state *lex-delta-db* :test #'dfa-delta-test-fn))

;;; DFA (Deterministic Finite Automata)
(defun dfa-accept (str state mem lex) nil)
