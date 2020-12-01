; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s

#|
-----------------------------------------------------------------------------------
In words:

Given a function:

(definec f (x :nat y :nat) :nat
  (let ((a alpha_const)
        (b beta_const))
        (* x (+ (* b y) a))))


For all x,y belonging to the natural numbers, any accumulator and non-accumulation function of the form:
(
(definec acc-fn (x :nat acc :nat) :nat
  (cond ((zp  x)    acc)
        (t        (acc-fn (1- x) (f x acc)))))

(definec non-acc-fn (x :nat) :nat
  (cond ((zp  x) 0)
        (t       (f x (non-acc-fn (1- x))))))


are equal.

-------------------------------------------------------------------------------------

Conjecture:
(implies (and (natp x) (natp acc) (zp acc))
         (equal (acc-fn x acc) (non-acc-fn x)))
         
3 CASES:

1.) (implies (and (and (natp x) (natp acc) (zp acc) (not (and (natp x) (natp acc) (zp acc)))))
         (equal (acc-fn x acc) (non-acc-fn x)))
         
2.) (implies (and (natp x) (zp x) (natp acc) (zp acc))
         (equal (acc-fn x acc) (non-acc-fn x)))
         
3.) (implies (and (natp x) (not (zp x)) (natp acc) (zp acc)
                   (implies (and (natp (1- x)) (natp (f x acc)))
                                 (equal (acc-fn (1- x) (f x acc)) (f x (non-acc-fn (1- x))))))
         (equal (acc-fn x acc) (non-acc-fn x)))
         
-------------------------------------------------------------------------------------
CASE 1: Contract Case   

Conjecture:
(implies (and (and (natp x) (natp acc) (zp acc) (not (and (natp x) (natp acc) (zp acc)))))
         (equal (acc-fn x acc) (non-acc-fn x)))
Context:
C1. (natp x)
C2. (natp acc)
C3. (zp acc)
C4. (not (and (natp x) (natp acc) (zp acc)))

Derived Context:
D1. nil {C1, C4, and-axioms}

QED

-------------------------------------------------------------------------------------
CASE 2: Base Case   

Conjecture:
(implies (and (natp x) (zp x) (natp acc) (zp acc))
         (equal (acc-fn x acc) (non-acc-fn x)))
         
Context:
C1. (natp x)
C2. (zp x)
C3. (natp acc)
C4. (zp acc)


Derived Context:


Goal:
(equal (acc-fn x acc) (non-acc-fn x))

Proof:

(non-acc-fn x)

= {Def non-acc-fn}
(cond ((zp  x)    0)
        (t        (f x (non-acc-fn (1- x)))))

= {if-axioms, C2}
0

= {if-axioms, C2}
(cond ((zp  x)    0)
        (t        (acc-fn (1- x) (f x 0))))
        
= {C4}
(cond ((zp  x)    acc)
        (t        (acc-fn (1- x) (f x acc))))
        
= {Def acc-fn}
(acc-fn x acc)

QED


-------------------------------------------------------------------------------------
CASE 3: Inductive Case   

Conjecture:
(implies (and (natp x) (natp acc) (zp acc)
                   (implies (not (zp x))
                   (implies (and (natp (1- x)) (natp (f x acc)))
                                 (equal (acc-fn (1- x) (f x acc)) (f x (non-acc-fn (1- x)))))))
         (equal (acc-fn x acc) (non-acc-fn x)))
         
Exportation:
(implies (and (natp x) (not (zp x)) (natp acc) (zp acc)
                   (implies (and (natp (1- x)) (natp (f x acc)))
                                 (equal (acc-fn (1- x) (f x acc)) (f x (non-acc-fn (1- x)))))))
         (equal (acc-fn x acc) (non-acc-fn x)))
         
Context:
C1. (natp x)
C2. (not (zp x))
C3. (natp acc)
C4. (zp acc)
C5. (implies (and (natp (1- x)) (natp (f x acc)))
                                 (equal (acc-fn (1- x) (f x acc)) (f x (non-acc-fn (1- x)))))

Derived Context:
D1. (natp (1- x))                        {C1, C2, Def natp}
D2. (natp (f x acc))                     {C1, C3, Def f, Def natp}
D3. (equal (acc-fn (1- x) (f x acc))
           (f x (non-acc-fn (1- x))))    {D1, D2, C5, Def impl}
           
Goal:
(equal (acc-fn x acc) (non-acc-fn x))

Proof:
(acc-fn x acc)

= {Def acc-fn}
(cond ((zp  x)    acc)
        (t        (acc-fn (1- x) (f x acc))))
        
= {C2, if-axioms}
(acc-fn (1- x) (f x acc))

= {D3}
(f x (non-acc-fn (1- x)))

= {if-axioms, C2}
 (cond ((zp  x)    0)
        (t        (f x (non-acc-fn (1- x)))))
        
= {Def of non-acc-fn}
(non-acc-fn x)

QED


|#


