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

(defun char-to-string (char)
  (format nil "~a" char))

(defun string-append (str1 str-or-char)
  (let ((str2 (if (typep str-or-char 'character)
		  (char-to-string str-or-char)
		  str-or-char)))
	(concatenate 'string str1 str2)))

;;; Structs
(defstruct dfa-delta next-state output)
(defstruct lex-token type payload)

;;; Regex constants
(defun char-list-range-impl (start end)
  (cond ((char= start end) (list end))
	(T (cons start (char-list-range
			(code-char
			 (+ (char-code start) 1))
			end)))))

(defun char-list-range (start end &key (range-type 'char))
  (cond ((eq range-type 'char) (char-list-range-impl start end))
	((eq range-type 'code) (char-list-range-impl
				(code-char start) (code-char end)))
	(T nil)))

(defun rx-match (symbol rx-const)
  (member symbol rx-const))

(defun rx-not-in (rx not-in-rx)
  (reverse (set-difference rx not-in-rx)))

(defvar [a-z] (char-list-range #\a #\z))
(defvar [a-z]^ (char-list-range #\A #\Z))
(defvar [a-z]%^ (append [a-z] [a-z]^))
(defvar [0-9] (char-list-range #\0 #\9))
(defvar [1-9] (char-list-range #\1 #\9))
(defvar \s (list #\Space #\Tab))
(defvar \nl (list #\Return #\Linefeed))
(defvar \w (append (append [0-9] (list #\_))
		   (append [a-z] [a-z]^)))
(defvar \wx (append \s (char-list-range 33 255 :range-type 'code)))

;;; @section Lexer
;;; Initial and final states
(defvar *lex-initial-state* "q0")
(defvar *lex-final-states* (list "q1-ws" "q1-imm" "q2-imm" "q1-nl" "q2-cm"
				 "q1-op-lbl"))

(defun dfa-delta-chk (state state-chk symbol rx &key (not-in nil))
  (and (string= state state-chk) (if (null not-in)
				     (rx-match symbol rx)
				     (not (rx-match symbol rx)))))

;;; Check if `state` is final
(defun dfa-final (state)
  (not (null (member state *lex-final-states* :test #'string=))))

;;; Delta function handler
(defun dfa-delta (state symbol mem)
  (let ((lexeme mem))
    (cond
      ;;; Whitespaces
      ((dfa-delta-chk state "q0" symbol \s)
       (make-dfa-delta :next-state "q1-ws"))
      ((dfa-delta-chk state "q1-ws" symbol \s)
       (make-dfa-delta :next-state "q1-ws"))
      ((dfa-delta-chk state "q1-ws" symbol \s :not-in T)
       (make-dfa-delta :next-state "q0"
		       :output (tokenize lexeme 'whitespace)))
      ;;; Integer immediates
      ((dfa-delta-chk state "q0" symbol [1-9])
       (make-dfa-delta :next-state "q1-imm"))
      ((dfa-delta-chk state "q1-imm" symbol [0-9])
       (make-dfa-delta :next-state "q2-imm"))
      ((dfa-delta-chk state "q2-imm" symbol [0-9])
       (make-dfa-delta :next-state "q2-imm"))
      ((or (dfa-delta-chk state "q2-imm" symbol [0-9] :not-in T)
	   (dfa-delta-chk state "q1-imm" symbol [0-9] :not-in T))
       (make-dfa-delta :next-state "q0"
		       :output (tokenize lexeme 'immediate)))
      ;;; Newlines
      ((dfa-delta-chk state "q0" symbol \nl)
       (make-dfa-delta :next-state "q1-nl"))
      ((dfa-delta-chk state "q1-nl" symbol \nl)
       (make-dfa-delta :next-state "q1-nl"))
      ((dfa-delta-chk state "q1-nl" symbol \nl :not-in T)
       (make-dfa-delta :next-state "q0"
		       :output (tokenize lexeme 'immediate)))
      ;;; Comments
      ((dfa-delta-chk state "q0" symbol (list #\\))
       (make-dfa-delta :next-state "q1-cm"))
      ((dfa-delta-chk state "q1-cm" symbol (list #\\))
       (make-dfa-delta :next-state "q2-cm"))
      ((dfa-delta-chk state "q2-cm" symbol \wx)
       (make-dfa-delta :next-state "q2-cm"))
      ((dfa-delta-chk state "q2-cm" symbol \wx :not-in T)
       (make-dfa-delta :next-state "q0"
		       :output (tokenize lexeme 'comment)))
      ;;; Labels/Opcodes
      ((dfa-delta-chk state "q0" symbol (rx-not-in \w [0-9]))
       (make-dfa-delta :next-state "q1-op-lbl"))
      ((dfa-delta-chk state "q1-op-lbl" symbol \w)
       (make-dfa-delta :next-state "q1-op-lbl"))
      ((dfa-delta-chk state "q1-op-lbl" symbol \w :not-in T)
       (make-dfa-delta :next-state "q0"
		       :output (tokenize lexeme 'opcode-or-label)))
      (T nil))))

;;; @section DFA (Deterministic Finite Automata)
(defun dfa-accept (str state mem lex)
  (cond ((> (length str) 0)
         (let ((next (dfa-delta state (char str 0) mem)))
           (unless (null next)
             (let* ((mem-next (if (null (dfa-delta-output next))
				 (string-append mem (char str 0))
				 ""))
		    (str-next (if (null (dfa-delta-output next))
				  (subseq str 1)
				  str)))
		 (dfa-accept str-next
                         (dfa-delta-next-state next)
                         mem-next
			 (lex-append (dfa-delta-output next) lex))))))
         ;;; Accept
	 ((dfa-final state) (lex-append
			     (dfa-delta-output (dfa-delta state nil mem))
			     lex))
         (T nil)))

(defun lex-append (token lex)
  (if (null token)
      lex
      (append lex (list token))))

;;; LMC Assembly
(defstruct lmc-opcode op arity)

(defvar *lmc-opcode-tbl* (list
			  (make-lmc-opcode :op "add" :arity 1)
			  (make-lmc-opcode :op "sub" :arity 1)))

;;; @todo add arity check
(defun opcode (str &key (arity 1))
  (first (member str *lmc-opcode-tbl*
	  :key #'lmc-opcode-op
	  :test #'equalp)))

;;; Tokenizers
(defun tokenize (str token-type)
  (cond ((eq token-type 'opcode-or-label)
	 (let ((opcode (opcode str)))
	   (if (not (null opcode))
	       (make-lex-token :type "$opcode" :payload (lmc-opcode-op opcode))
	       (make-lex-token :type "$label" :payload str))))
	((eq token-type 'immediate) (make-lex-token :type "$imm" :payload str))
	((eq token-type 'whitespace) (make-lex-token :type "$ws"))
	((eq token-type 'newline) (make-lex-token :type "$nl"))
	((eq token-type 'comment) (make-lex-token :type "$cm"))
	(T nil)))
