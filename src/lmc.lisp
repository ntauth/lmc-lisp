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
  (let ((str2 (if str-or-char
		  (if (typep str-or-char 'character)
		      (char-to-string str-or-char)
		      str-or-char)
		  "")))
	(concatenate 'string str1 str2)))

(defun log-error (fmt &rest args)
  (let ((fmt-err (string-append (string-append "[!] " fmt) "~%")))
    (format t fmt-err args)))

;;; @section LMC Assembly
(defstruct lmc-opcode op arity type)
(defstruct lmc-instruction opcode imm)

;;; Opcode table
(defvar *lmc-opcode-tbl* (list
			  (make-lmc-opcode :op "add" :arity 1 :type 'imm-or-lbl)
			  (make-lmc-opcode :op "sub" :arity 1 :type 'imm-or-lbl)
			  (make-lmc-opcode :op "sta" :arity 1 :type 'imm-or-lbl)
			  (make-lmc-opcode :op "lda" :arity 1 :type 'imm-or-lbl)
			  (make-lmc-opcode :op "bra" :arity 1 :type 'imm-or-lbl)
			  (make-lmc-opcode :op "brz" :arity 1 :type 'imm-or-lbl)
			  (make-lmc-opcode :op "brp" :arity 1 :type 'imm-or-lbl)
			  (make-lmc-opcode :op "inp" :arity 0)
			  (make-lmc-opcode :op "out" :arity 0)
			  (make-lmc-opcode :op "hlt" :arity 0)
			  (make-lmc-opcode :op "dat" :arity 1 :type 'imm)
			  (make-lmc-opcode :op "dat" :arity 0)))
			  

;;; Opcode-to-Bytecode translation table
(defvar *lmc-bytecode-tbl* (list
			    (cons "add" 1)
			    (cons "sub" 2)
			    (cons "sta" 3)
			    (cons "lda" 5)
			    (cons "bra" 6)
			    (cons "brz" 7)
			    (cons "brp" 8)
			    (cons "inp" 901)
			    (cons "out" 902)
			    (cons "hlt" 0)))

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
(defstruct dfa-delta next-state output)
(defstruct lex-token type payload)

;;; Initial and final states
(defvar *lex-initial-state* "q0")
(defvar *lex-final-states* (list "q1-ws" "q1-imm" "q2-imm" "q1-nl" "q2-cm"
				 "q1-op-lbl"))

(defun dfa-delta-chk (state state-chk symbol rx &key (not-in nil))
  (and (string= state state-chk) (if (null not-in)
				     (rx-match symbol rx)
				     (not (rx-match symbol rx)))))

;;; Checks if `state` is final
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
(defstruct pda-delta next-state stack)

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
       (let ((opcode0 (first (opcode payload :arity 0)))
	     (opcode1 (first (opcode payload :arity 1))))
	  (cond ((or (string= "$label" (lex-token-type token-la))
		     (string= "$imm" (lex-token-type token-la)))
		 ;; Arity = 1
		 (unless (null opcode1)
		   (when (or (and (string= "$imm" (lex-token-type token-la))
				  (eq (lmc-opcode-type opcode1) 'imm))
			     (eq (lmc-opcode-type opcode1) 'imm-or-lbl))
		     (make-pda-delta :next-state "r1-op-1"
				     :stack (cons type stack)))))
		;; Arity = 0
		(T (unless (null opcode0)
		     (make-pda-delta :next-state "r2-op"
				     :stack stack))))))
      ((pda-delta-chk state "r1-lbl" type "$opcode")
       (let ((opcode0 (first (opcode payload :arity 0)))
	     (opcode1 (first (opcode payload :arity 1))))
	 ;; Lookahead for arity
	 (cond ((or (string= "$label" (lex-token-type token-la))
		    (string= "$imm" (lex-token-type token-la)))
		;; Arity = 1
		(unless (null opcode1)
		  (when (or (and (string= "$imm" (lex-token-type token-la))
				 (eq (lmc-opcode-type opcode1) 'imm))
			    (eq (lmc-opcode-type opcode1) 'imm-or-lbl))
		      (make-pda-delta :next-state "r1-op-0"
				      :stack (cons type stack)))))
	       (T (unless (null opcode0)
		    (make-pda-delta :next-state "r2-op"
				    :stack (rest stack)))))))
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
             (let ((mem-next (if (null (dfa-delta-output next))
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
	(read-file-to-string-impl in (string-append aux char))
	aux)))

(defun read-file-to-string (filename)
  (let ((in (open filename :if-does-not-exist nil)))
    (unless (null in)
      (let ((input (read-file-to-string-impl in "")))
	(close in)
	input))))


;;; @section Execution engine
(defstruct state acc pc mem in out flag)
(defstruct halted-state acc pc mem in out flag)

;; Packs a state struct into a plist
(defun pack-state (state)
  (cond ((eq (type-of state) 'state)
	 (list 'state
	       :acc (state-acc state)
	       :pc (state-pc state)
	       :mem (state-mem state)
	       :in (state-in state)
	       :out (state-out state)
	       :flag (state-flag state)))
	((eq (type-of state) 'halted-state)
	 (list 'halted-state
	       :acc (halted-state-acc state)
	       :pc (halted-state-pc state)
	       :mem (halted-state-mem state)
	       :in (halted-state-in state)
	       :out (halted-state-out state)
	       :flag (halted-state-flag state)))
	(T nil)))

;; Unpacks a plist into a state struct
(defun unpack-state (state*)
  (let ((state (subseq state* 1)))
    (cond ((eq (first state*) 'state)
	   (make-state :acc (getf state :acc)
		       :pc (getf state :pc)
		       :mem (getf state :mem)
		       :in (getf state :in)
		       :out (getf state :out)
		       :flag (getf state :flag)))
	  ((eq (first state*) 'halted-state)
	   (make-halted-state :acc (getf state :acc)
			      :pc (getf state :pc)
			      :mem (getf state :mem)
			      :in (getf state :in)
			      :out (getf state :out)
			      :flag (getf state :flag)))
	  (T nil))))


(defun lexify (asm)
  (dfa-accept asm *lex-initial-state* "" '()))

(defun lex-strip (lex symbols)
  (filter (lambda (x) (not (member (lex-token-type x)
			      symbols
			      :test #'string=)))
	  lex))

;;; State plist setter
(defun setp (plst key value)
  (let ((plst* (copy-list (rest plst))))
    (setf (getf plst* key) value)
    (append (list (first plst)) plst*)))

(defun extract-bpt-impl (parse rva)
  (cond ((null parse) nil)
	((string= (lex-token-type (first (first parse)))
		  "$label")
	 (cons (cons (string-downcase
		      (lex-token-payload (first (first parse))))
		     (write-to-string rva))
	       (extract-bpt-impl (rest parse) (+ rva 1))))
	(T (extract-bpt-impl (rest parse) (+ rva 1)))))

(defun extract-bpt-thunk (parse)
  (extract-bpt-impl parse 0))

(defun extract-bpt (parse)
  (let* ((bpt (extract-bpt-thunk parse))
	 (bpt-sorted (sort (copy-list bpt) #'string<= :key #'car)))
    (unless (null (reduce (lambda (x y) (cond ((null x) nil)
					      ((string= x y) nil)
					      (T y)))
			  (mapcar #'car bpt-sorted)))
      bpt)))

;;; Patches the trimmed instruction with an entry in the BPT
(defun patch-instr-bpt (instr-t bpt)
  (let ((last-token (first (last instr-t))))
    (if (string= (lex-token-type last-token) "$label")
	(let ((payload (cdr (assoc (string-downcase
				    (lex-token-payload last-token))
				   bpt
				   :test #'string=))))
	  (cons (first instr-t)
		(list (make-lex-token :type "$imm"
				      :payload (if (null payload)
						   'unresolved
						   payload)))))
	instr-t)))

;;; Patches the parsed assembly with the BPT
(defun patch-parse-bpt-impl (parse bpt)
  (cond ((null parse) nil)
	(T (let ((instr (first parse)))
	     (cond ((string= (lex-token-type (first instr)) "$label")
		    (let ((instr-t (rest instr)))
		      (cons (patch-instr-bpt instr-t bpt)
			    (patch-parse-bpt (rest parse) bpt))))
		   (T (cons (patch-instr-bpt instr bpt)
			    (patch-parse-bpt (rest parse) bpt))))))))

(defun patch-parse-bpt (parse bpt)
  (let ((pparse (patch-parse-bpt-impl parse bpt)))
    (unless (null pparse)
      (if (member (make-lex-token :type "$imm" :payload 'unresolved) pparse
		  :key (lambda (x) (first (last x))) :test #'equalp)
	  nil
	  pparse))))

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
	    (let ((opcode (lex-token-payload (first x)))
		  (imm (if (null (second x)) 0
			   (parse-integer (lex-token-payload (second x))
					  :junk-allowed T))))
	      (make-lmc-instruction :opcode opcode
				    :imm imm)))
	  parse))
  
(defun parse (lex)
  (let ((lex-s (lex-strip lex '("$ws" "$cm"))))
    (unless (null (pda-accept lex-s *parse-initial-state* '()))
      (let ((parse-u (parse-unflatten lex-s)))
	parse-u))))

(defun __emit (instr)
  (let* ((opcode (lmc-instruction-opcode instr))
	 (imm (mod (lmc-instruction-imm instr) 1000))
	 (bc (bytecode opcode)))
    (cond ((string= opcode "dat") imm)
	  ((< bc 10) (+ (* (bytecode opcode) 100) (mod imm 100)))
	  (T bc))))

;; Instructions
(defun __asm_deref (state va*)
  (let* ((mem (state-mem state))
	 (va (mod va* 100)))
    (nth va mem)))

(defun __asm_hlt (state)
  (make-halted-state :acc (state-acc state)
		     :pc (state-pc state)
		     :mem (state-mem state)
		     :in (state-in state)
		     :out (state-out state)
		     :flag (state-flag state)))

(defun __asm_add (state imm)
  (let* ((op2 (__asm_deref state imm))
	 (res (+ (state-acc state) op2))
	 (res-wrap (mod (+ (state-acc state) op2) 1000))
	 (flag (if (> res 999) 'flag 'noflag)))
    (make-state :acc res-wrap
		:pc (state-pc state)
		:mem (state-mem state)
		:in (state-in state)
		:out (state-out state)
		:flag flag)))
    
(defun __asm_sub (state imm)
  (let* ((op2 (__asm_deref state imm))
	 (res (- (state-acc state) op2))
	 (res-wrap (mod (- (state-acc state) op2) 1000))
	 (flag (if (< res 0) 'flag 'noflag)))
    (make-state :acc res-wrap
		:pc (state-pc state)
		:mem (state-mem state)
		:in (state-in state)
		:out (state-out state)
		:flag flag)))

(defun __asm_sta (state imm)
  (let* ((mem* (copy-list (state-mem state)))
	 (op (state-acc state))
	 (next-mem (replace mem* (list op) :start1 imm :end1 (+ imm 1))))
    (make-state :acc op
		:pc (state-pc state)
		:mem next-mem
		:in (state-in state)
		:out (state-out state)
		:flag (state-flag state))))

(defun __asm_lda (state imm)
  (let ((op (nth imm (state-mem state))))
    (make-state :acc op
		:pc (state-pc state)
		:mem (state-mem state)
		:in (state-in state)
		:out (state-out state)
		:flag (state-flag state))))

(defun __asm_bra (state imm)
  (let ((branch-target (- imm 1)))
    (make-state :acc (state-acc state)
		:pc branch-target
		:mem (state-mem state)
		:in (state-in state)
		:out (state-out state)
		:flag (state-flag state))))

(defun __asm_brz (state imm)
  (let ((branch-target (if (and (equal (state-flag state) 'noflag)
				(= (state-acc state) 0))
			   (- imm 1)
			   (state-pc state))))
    (make-state :acc (state-acc state)
		:pc branch-target
		:mem (state-mem state)
		:in (state-in state)
		:out (state-out state)
		:flag (state-flag state))))

(defun __asm_brp (state imm)
  (let ((branch-target (if (equal (state-flag state) 'noflag)
			   (- imm 1)
			   (state-pc state))))
    (make-state :acc (state-acc state)
		:pc branch-target
		:mem (state-mem state)
		:in (state-in state)
		:out (state-out state)
		:flag (state-flag state))))

(defun __asm_inp (state)
  (let ((in (nth 0 (state-in state))))
    (if (null in)
	(__asm_panic state)
	(make-state :acc (mod in 1000)
		    :pc (state-pc state)
		    :mem (state-mem state)
		    :in (subseq (state-in state) 1)
		    :out (state-out state)
		    :flag (state-flag state)))))

(defun __asm_out (state)
  (let ((out (state-acc state)))
    (make-state :acc (state-acc state)
		:pc (state-pc state)
		:mem (state-mem state)
		:in (state-in state)
		:out (append (state-out state) `(,out))
		:flag (state-flag state))))

(defun __asm_panic (state &optional msg)
  (unless (null msg)
    (log-error "[PANIC] ~a" msg))
  (make-halted-state :acc (state-acc state)
		     :pc (state-pc state)
		     :mem (state-mem state)
		     :in (state-in state)
		     :out (state-out state)
		     :flag (state-flag state)))
   
(defun __asm (bytecode state)
  (multiple-value-bind (bc imm)
      (floor bytecode 100)
    (cond ((= bc 0)
	   (__asm_hlt state))
	  ((= bc 1)
	   (__asm_add state imm))
	  ((= bc 2)
	   (__asm_sub state imm))
	  ((= bc 3)
	   (__asm_sta state imm))
	  ((= bc 5)
	   (__asm_lda state imm))
	  ((= bc 6)
	   (__asm_bra state imm))
	  ((= bc 7)
	   (__asm_brz state imm))
	  ((= bc 8)
	   (__asm_brp state imm))
	  ((= bytecode 901)
	   (__asm_inp state))
	  ((= bytecode 902)
	   (__asm_out state))
	  (T (__asm_panic state "Invalid Opcode")))))
	  
(defun assemble (src)
  (if (null src) nil
      (cons (__emit (first src)) (assemble (rest src)))))

(defun one-instruction (state)
  (let* ((state (unpack-state state))
	 (bytecode (nth (state-pc state) (state-mem state)))
	 (next-state-u (__asm bytecode state))
	 (next-state (pack-state next-state-u)))
    (setp next-state :pc (mod
			  (+ (getf (subseq next-state 1) :pc) 1)
			  100))))

(defun execution-loop (state)
  (let ((next-state (one-instruction state)))
    (cond ((eq (first next-state) 'halted-state)
	   (getf (subseq next-state 1) :out))
	  (T (execution-loop next-state)))))

(defun flat-mem-generate (bin &key (size 100))
  (append bin (make-list (- size (length bin))
			 :initial-element (bytecode "hlt"))))

(defun lmc-load (filename)
  (let ((asm (read-file-to-string filename)))
    (if (null asm)
	(log-error "Could not open file ~a." filename)
	;; Lex
	(let ((lex (lexify asm)))
	  (if (null lex)
	      (log-error "Lexical error: unrecognized sequence.")
	      ;; Parse
	      (let ((parse (parse lex)))
		(if (null parse)
		    (log-error "Syntax error: ill-formed sequence.")
		    ;; Backpatch
		    (let ((bpt (extract-bpt parse)))
		      (if (null bpt)
			  (log-error "Duplicate label detected.")
			  (let ((src (parse-to-instrs
				      (patch-parse-bpt parse bpt))))
			    ;; Assemble
			    (let ((bin (assemble src)))
			      (if (> (length bin) 100)
				  (log-error "Program doesn't fit in memory.")
				  ;; Generate memory
				  (flat-mem-generate bin)))))))))))))

(defun lmc-run (filename input)
  (let ((mem (lmc-load filename)))
    (unless (null mem)
      (execution-loop (pack-state (make-state :acc 0
					      :pc 0
					      :mem mem
					      :in input
					      :out '()
					      :flag 'noflag))))))

