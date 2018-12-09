;;;; lmc.lisp
;;;;
;;;; @author  Ayoub Chouak (a.chouak@protonmail.com)
;;;; @brief   AOT LMC Assembler and Execution Engine
;;;; @license MIT
;;;;

;;; @section Helper functions
(defun filter (fn lst)
  (cond ((null lst) nil)
	((funcall fn (first lst))
	 (cons (first lst) (filter fn (rest lst))))
	(T (filter fn (rest lst)))))

(defun find-all (item lst &key (test #'equal))
  (cond ((null lst) nil)
	(T (if (funcall test item (first lst))
	       (cons (first lst) (find-all item (rest lst) :test test))
	       (find-all item (rest lst) :test test)))))
		
(defun char-to-string (char)
  (format nil "~a" char))

;;; Appends a string/character to a string
(defun string-append (str1 str-or-char)
  (let ((str2 (if (typep str-or-char 'character)
		  (char-to-string str-or-char)
		  str-or-char)))
	(concatenate 'string str1 str2)))

;;; Elvis operator extension
(defun ?? (assertee fallback)
  (if (not (null assertee)) assertee fallback))

(defun log-error (fmt &rest args)
  (let ((fmt-err (string-append (string-append "[!] " fmt) "~%")))
    (format t fmt-err args)))

;;; @section Structs
(defstruct dfa-delta next-state output)
(defstruct lex-token type payload)

(defstruct pda-delta next-state stack)

(defstruct state acc pc mem in out flag)
(defstruct halted-state acc pc mem in out flag)

;;; @section LMC Assembly
(defstruct lmc-opcode op arity)
(defstruct lmc-instruction opcode imm)

;;; Opcode table
(defvar *lmc-opcode-tbl* (list
			  (make-lmc-opcode :op "add" :arity 1)
			  (make-lmc-opcode :op "sub" :arity 1)
			  (make-lmc-opcode :op "sta" :arity 1)
			  (make-lmc-opcode :op "lda" :arity 1)
			  (make-lmc-opcode :op "bra" :arity 1)
			  (make-lmc-opcode :op "brz" :arity 1)
			  (make-lmc-opcode :op "brp" :arity 1)
			  (make-lmc-opcode :op "inp" :arity 0)
			  (make-lmc-opcode :op "out" :arity 0)
			  (make-lmc-opcode :op "hlt" :arity 0)
			  (make-lmc-opcode :op "dat" :arity 1)
			  (make-lmc-opcode :op "dat" :arity 0)))
			  

;;; Opcode-to-Bytecode translation table
(defvar *lmc-bytecode-tbl* (list
			    (cons "add" "1")
			    (cons "sub" "2")
			    (cons "sta" "3")
			    (cons "lda" "5")
			    (cons "bra" "6")
			    (cons "brz" "7")
			    (cons "brp" "8")
			    (cons "inp" "901")
			    (cons "out" "902")
			    (cons "hlt" "000")))

(defun bytecode (opcode)
  (cdr (find opcode *lmc-bytecode-tbl* :key #'car :test #'string=)))

(defun opcode (str &key (arity -1))
  (find-all str *lmc-opcode-tbl*
		   :test (lambda (str x)
			 (and (equalp str (lmc-opcode-op x))
			      (or (= arity -1)
				  (= arity (lmc-opcode-arity x)))))))

;;; @section Regex constants
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
      ((dfa-delta-chk state "q0" symbol [0-9])
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
		       :output (tokenize lexeme 'newline)))
      ;;; Comments
      ((dfa-delta-chk state "q0" symbol (list #\/))
       (make-dfa-delta :next-state "q1-cm"))
      ((dfa-delta-chk state "q1-cm" symbol (list #\/))
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

;;; @section Parser grammar
(defvar *parse-initial-state* "r0")
(defvar *parse-final-states* (list "r0" "r2-op"))

(defun imm-domain-chk (imm)
  (let ((int-imm (parse-integer imm)))
    (and (>= int-imm 0) (<= int-imm 999))))

(defun pda-delta-chk (state state-chk token-type token-type-chk)
  (and (string= state state-chk)
       (string= token-type token-type-chk)))

(defun pda-final (state)
  (not (null (member state *parse-final-states* :test #'string=))))

(defun pda-delta (state lalr-list stack)
  (let* ((token (first lalr-list))
	 (token-la (if (null (second lalr-list))
		       (make-lex-token)
		       (second lalr-list)))
	 (type (lex-token-type token))
	 (payload (lex-token-payload token)))
    (cond
      ((pda-delta-chk state "r0" type "$nl")
       (make-pda-delta :next-state "r0"
		       :stack stack))
      ((pda-delta-chk state "r0" type "$label")
       (make-pda-delta :next-state "r1-lbl"
		       :stack (cons type stack)))
      ((pda-delta-chk state "r0" type "$opcode")
       ;; Lookahead for arity
       (cond ((or (string= "$label" (lex-token-type token-la))
		  (string= "$imm" (lex-token-type token-la)))
	     ;; Arity = 1
	     (unless (null (opcode payload :arity 1))
	       (make-pda-delta :next-state "r1-op-1"
			       :stack (cons type stack))))
	     ;; Arity = 0
	     (T (unless (null (opcode payload :arity 0))
		  (make-pda-delta :next-state "r2-op"
				:stack stack)))))
       ((pda-delta-chk state "r1-lbl" type "$opcode")
	;; Lookahead for arity
	(cond ((or (string= "$label" (lex-token-type token-la))
		   (string= "$imm" (lex-token-type token-la)))
	     ;; Arity = 1
	     (unless (null (opcode payload :arity 1))
	       (make-pda-delta :next-state "r1-op-0"
			       :stack (cons type stack))))
	     (T (unless (null (opcode payload :arity 0))
		(make-pda-delta :next-state "r2-op"
				:stack (rest stack))))))
       ((or (pda-delta-chk state "r1-op-0" type "$imm")
	    (pda-delta-chk state "r1-op-0" type "$label"))
	(let* ((delta (make-pda-delta :next-state "r2-op"
				      :stack (rest (rest stack)))))
	  (when (or (and (string= type "$imm") (imm-domain-chk payload))
		    (string= type "$label"))
	    delta)))
       ((or (pda-delta-chk state "r1-op-1" type "$imm")
	    (pda-delta-chk state "r1-op-1" type "$label"))
	(let* ((delta (make-pda-delta :next-state "r2-op"
				      :stack (rest stack))))
	  (when (or (and (string= type "$imm") (imm-domain-chk payload))
		    (string= type "$label"))
	    delta)))
       ((pda-delta-chk state "r2-op" type "$nl")
	(make-pda-delta :next-state "r0"
			:stack stack)))))


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

;;; @section PDA (Pushdown Automata)
(defun pda-accept (lex state stack)
  (cond ((not (null lex))
	 (let ((next (pda-delta state lex stack)))
	   (unless (null next)
	     (pda-accept (rest lex)
			 (pda-delta-next-state next)
			 (pda-delta-stack next)))))
	((pda-final state) T)
	(T nil)))     
		    
;;; @section Tokenizers
(defun tokenize (str token-type)
  (cond ((eq token-type 'opcode-or-label)
	 (let ((opcode (first (opcode str))))
	   (if (not (null opcode))
	       (make-lex-token :type "$opcode" :payload (lmc-opcode-op opcode))
	       (make-lex-token :type "$label" :payload str))))
	((eq token-type 'immediate) (make-lex-token :type "$imm" :payload str))
	((eq token-type 'whitespace) (make-lex-token :type "$ws"))
	((eq token-type 'newline) (make-lex-token :type "$nl"))
	((eq token-type 'comment) (make-lex-token :type "$cm"))
	(T nil)))


;;; @section IO
(defun read-file-to-string-impl (in aux)
  (let ((char (read-char in nil 'the-end)))
    (if (characterp char)
	(read-file-to-string-impl in
				  (string-append aux char))
	aux)))

(defun read-file-to-string (filename)
  (let ((in (open filename :if-does-not-exist nil)))
    (unless (null in)
      (let ((input (read-file-to-string-impl in "")))
	(close in)
	input))))


;;; @section Execution engine
(defun lexify (asm)
  (dfa-accept asm *lex-initial-state* "" '()))

(defun lex-strip (lex symbols)
  (filter (lambda (x) (not (member (lex-token-type x)
			      symbols
			      :test #'string=)))
	  lex))

(defun extract-bpt-impl (parse rva)
  (cond ((null parse) nil)
	((string= (lex-token-type (first (first parse)))
		  "$label")
	 (cons (cons (lex-token-payload (first (first parse)))
		     (write-to-string rva))
	       (extract-bpt-impl (rest parse) (+ rva 1))))
	(T (extract-bpt-impl (rest parse) (+ rva 1)))))

;;; @TODO Handle duplicate labels (fail)
(defun extract-bpt-thunk (parse)
  (extract-bpt-impl parse 0))

(defun extract-bpt (parse)
  (let ((bpt (extract-bpt-thunk parse)))
    (let ((bpt-sorted (sort (copy-list bpt) #'string<= :key #'car)))
      (unless (null (reduce (lambda (x y) (cond ((null x) nil)
						((string= x y) nil)
						(T y)))
			    (mapcar #'car bpt-sorted)))
	bpt))))

;;; Patches the trimmed instruction with an entry in the BPT
(defun patch-instr-bpt (instr-t bpt)
  (let ((last-token (first (last instr-t))))
    (if (string= (lex-token-type last-token) "$label")
	(cons (first instr-t)
	      (list (make-lex-token :type "$imm"
				    :payload (cdr (assoc (lex-token-payload
						     last-token)
						    bpt
						    :test #'string=)))))
	instr-t)))

;;; Patches the parsed assembly with the BPT
(defun patch-parse-bpt (parse bpt)
  (cond ((null parse) nil)
	(T (let ((instr (first parse)))
	     (cond ((string= (lex-token-type (first instr)) "$label")
		    (let ((instr-t (rest instr)))
		      (cons (patch-instr-bpt instr-t bpt)
			    (patch-parse-bpt (rest parse) bpt))))
		   (T (cons (patch-instr-bpt instr bpt)
			    (patch-parse-bpt (rest parse) bpt))))))))

(defun parse-unflatten (parse)
  (parse-unflatten-impl parse '() '()))

(defun parse-unflatten-impl (parse aux parse-u)
  (cond ((null parse)
	 (if (null aux)
	     parse-u
	     (append parse-u (list aux))))
	((string= (lex-token-type (first parse))
		  "$nl")
	 (if (null aux)
	     (parse-unflatten-impl (rest parse) aux parse-u)
	     (parse-unflatten-impl (rest parse) '() (append parse-u
						       (list aux)))))
	(T (parse-unflatten-impl (rest parse)
				 (append aux (list (first parse)))
				 parse-u))))

(defun parse-to-instrs (parse)
  (mapcar (lambda (x)
	    (let* ((opcode (lex-token-payload (first x)))
		   (imm (if (null (second x)) nil
			    (lex-token-payload (second x)))))
		   (make-lmc-instruction :opcode opcode
					 :imm imm)))
	  parse))
  
(defun parse (lex)
  (let ((lex-s (lex-strip lex '("$ws" "$cm"))))
    (unless (null (pda-accept lex-s *parse-initial-state* '()))
      (let ((parse-u (parse-unflatten lex-s)))
	parse-u))))

(defun normalize-imm-impl (imm &key size)
  (if (<= size 0)
      imm
      (normalize-imm-impl (string-append "0" imm) :size (- size 1)))) 

(defun normalize-imm (imm &key (size 3))
  (if (null imm)
      nil
      (let ((imm-t (write-to-string
		    (mod (parse-integer imm)
			 (expt 10 size)))))
	(normalize-imm-impl imm-t :size (- size (length imm-t))))))

(defun __emit (instr)
  (let ((opcode (lmc-instruction-opcode instr))
	(imm (lmc-instruction-imm instr)))
    (cond ((and (string= opcode "dat") (null imm))
	   (normalize-imm "0"))
	  ((string= opcode "dat")
	   (normalize-imm imm))
	  (T (string-append (bytecode opcode)
			    (normalize-imm imm :size 2)))))) 
	  

(defun assemble (src)
  (if (null src) nil
      (cons (__emit (first src)) (assemble (rest src)))))

(defun one-instruction (state) nil)
(defun execution-loop (state) nil)

(defun lmc-load (filename)
  (let ((asm (read-file-to-string filename)))
    (if (null asm)
	(log-error "Could not open file ~a." filename)
	(let ((lex (lexify asm)))
	  (if (null lex)
	      (log-error "Lexical error: unrecognized sequence.")
	      (let ((parse (parse lex)))
		(if (null parse)
		    (log-error "Syntax error: ill-formed sequence.")
		    (let ((bpt (extract-bpt parse)))
		      (if (null bpt)
			  (log-error "Duplicate label detected.")
			  (let ((src (parse-to-instrs
				      (patch-parse-bpt parse bpt))))
			    (assemble src)))))))))))

(defun lmc-run (filename input)
  (let ((mem (lmc-load filename)))
    mem))
