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

; CS2800 Project
; Kaiheng Hu

(set-defunc-termination-strictp nil)
(set-defunc-function-contract-strictp nil)
(set-defunc-body-contracts-strictp nil)

#|
(defdata loi (listof integer))

(definec loip2 (x :all) :bool
  (and (tlp x)
       (or (equal x '())
           (and (integerp (car x))
                (loip2 (cdr x))))))

(test? (implies (allp x)
                (equal (loip x) (loip2 x))))

(check= (loip2 '()) t)
|#


(definec app2 (a :tl b :tl) :tl
  (if (endp a)
    b
    (cons (first a) (app2 (rest a) b))))

(definec rev2 (x :tl) :tl
  (if (endp x)
    nil
    (app2 (rev2 (rest x)) (list (first x)))))

(definec in2 (a :all X :tl) :bool
  (and (consp X)
       (or (equal a (first X))
           (in2 a (rest X)))))

(definec len2 (x :tl) :nat
  (if (endp x)
    0
    (+ 1 (len2 (rest x)))))

(definec all-in-range (x :tl a :integer b :integer) :bool
  :ic (>= b a)
  (cond ((endp x) t)
        ((if (not (integerp (car x))) 
           (all-in-range (cdr x) a b)
           (and (>= (car x) a)
                (<= (car x) b)
                (all-in-range (cdr x) a b))))))


(check= (all-in-range '() 1 2) t)
(check= (all-in-range '(1) 1 1) t)
(check= (all-in-range '(2) 1 1) nil)
(check= (all-in-range '(1 2 3) -1 4) t)
(check= (all-in-range '(-100 0 100) 1 2) nil)
(check= (all-in-range '(-100 0 100) -101 101) t)




Lemma range-app2:
(implies (and (tlp x)
              (tlp y)
              (integerp a)
              (integerp b)
              (>= b a))
         (equal (all-in-range (app2 x y) a b)
                (and (all-in-range x a b)
                     (all-in-range y a b))))

Proof by: Induction on (tlp x)
Induction Case range-app2-base:
(implies (and (tlp x)
              (tlp y)
              (integerp a)
              (integerp b)
              (>= b a)
              (not (consp x)))
         (equal (all-in-range (app2 x y) a b)
                (and (all-in-range x a b)
                     (all-in-range y a b))))

Context:
C1. (tlp x)
C2. (tlp y)
C3. (integerp a)
C4. (integerp b)
C5. (>= b a)
C6. (not (consp x))

Derived Context:
D1. (endp x) { C1, C6 }

Goal:
(equal (all-in-range (app2 x y) a b)
       (and (all-in-range x a b)
            (all-in-range y a b)))

Proof:
(equal (all-in-range (app2 x y) a b)
       (and (all-in-range x a b)
            (all-in-range y a b)))
= { Def app2, C1, C2, D1 }
(equal (all-in-range y a b)
       (and (all-in-range x a b)
            (all-in-range y a b)))
= { Def all-in-range, C1, C3, C4, C5, D1 }
(equal (all-in-range y a b)
       (and t (all-in-range y a b)))
= { PL }
(equal (all-in-range y a b)
       (all-in-range y a b))
= { PL }
t

QED

Induction Case range-app2-ind:
(implies (and (tlp x)
              (tlp y)
              (integerp a)
              (integerp b)
              (>= b a)
              (consp x)
              (implies (and (tlp (cdr x))
                            (tlp y)
                            (integerp a)
                            (integerp b)
                            (>= b a))
                       (equal (all-in-range (app2 (cdr x) y) a b)
                              (and (all-in-range (cdr x) a b)
                                   (all-in-range y a b)))))
         (equal (all-in-range (app2 x y) a b)
                (and (all-in-range x a b)
                     (all-in-range y a b))))

Context:
C1. (tlp x)
C2. (tlp y)
C3. (integerp a)
C4. (integerp b)
C5. (>= b a)
C6. (consp x)
C7. (implies (and (tlp (cdr x))
                  (tlp y)
                  (integerp a)
                  (integerp b)
                  (>= b a))
             (equal (all-in-range (app2 (cdr x) y) a b)
                    (and (all-in-range (cdr x) a b)
                         (all-in-range y a b))))

Derived Context:
D1. (tlp (cdr x)) { C1, C6, cons axiom }
D2. (equal (all-in-range (app2 (cdr x) y) a b)
           (and (all-in-range (cdr x) a b)
                (all-in-range y a b))) { D1, C2, C3, C4, C5, C7, MP }

Goal:
(equal (all-in-range (app2 x y) a b)
       (and (all-in-range x a b)
            (all-in-range y a b)))

Proof:
(equal (all-in-range (app2 x y) a b)
       (and (all-in-range x a b)
            (all-in-range y a b)))
= { Def app2, C1, C2, C6 }
(equal (all-in-range (cons (car x) (app2 (cdr x) y)) a b)
       (and (all-in-range x a b)
            (all-in-range y a b)))
= { Def all-in-range, cons axiom }
(equal (if (not (integerp (car x)))
         (all-in-range (app2 (cdr x) y) a b)
         (and (>= (car x) a)
              (<= (car x) b)
              (all-in-range (app2 (cdr x) y) a b)))
       (and (all-in-range x a b)
            (all-in-range y a b)))
= { Def all-in-range, C1, C6, C3, C4, C5 }
(equal (if (not (integerp (car x)))
         (all-in-range (app2 (cdr x) y) a b)
         (and (>= (car x) a)
              (<= (car x) b)
              (all-in-range (app2 (cdr x) y) a b)))
       (and (if (not (integerp (car x))) 
              (all-in-range (cdr x) a b)
              (and (>= (car x) a)
                   (<= (car x) b)
                   (all-in-range (cdr x) a b)))
            (all-in-range y a b)))
= { if axiom, PL }
(equal (all-in-range (app2 (cdr x) y) a b)
       (and (all-in-range (cdr x) a b)
            (all-in-range y a b)))
= { PL }
t

QED

QED



Conjecture range-rev2:
(implies (and (tlp x)
              (integerp a)
              (integerp b)
              (>= b a))
         (equal (all-in-range x a b)
                (all-in-range (rev2 x) a b)))

Proof by: Induction on (tlp x)
Induction Case range-rev2-base:
(implies (and (tlp x)
              (integerp a)
              (integerp b)
              (>= b a)
              (not (consp x)))
         (equal (all-in-range x a b)
                (all-in-range (rev2 x) a b)))

Context:
C1. (tlp x)
C2. (integerp a)
C3. (integerp b)
C4. (>= b a)
C5. (not (consp x))

Derived Context:
D1. (endp x) { C1, C5 }

Goal:
(equal (all-in-range x a b)
       (all-in-range (rev2 x) a b))

Proof:
(equal (all-in-range x a b)
       (all-in-range (rev2 x) a b))
= { Def all-in-range, C1, C2, C3, C4, D1 }
(equal t (all-in-range (rev2 x) a b))
= { Def rev2, C1, D1 }
(equal t (all-in-range nil a b))
= { Def all-in-range }
(equal t t)
= { PL }
t

QED

Induction Case range-rev2-ind:
(implies (and (tlp x)
              (integerp a)
              (integerp b)
              (>= b a)
              (consp x)
              (implies (and (tlp (cdr x))
                            (integerp a)
                            (integerp b)
                            (>= b a))
                       (equal (all-in-range (cdr x) a b)
                              (all-in-range (rev2 (cdr x)) a b))))
         (equal (all-in-range x a b)
                (all-in-range (rev2 x) a b)))

Context:
C1. (tlp x)
C2. (integerp a)
C3. (integerp b)
C4. (>= b a)
C5. (consp x)
C6. (implies (and (tlp (cdr x))
                  (integerp a)
                  (integerp b)
                  (>= b a))
             (equal (all-in-range (cdr x) a b)
                    (all-in-range (rev2 (cdr x)) a b)))

Derived Context:
D1. (tlp (cdr x)) { cons axiom, C1, C5 }
D2. (equal (all-in-range (cdr x) a b)
           (all-in-range (rev2 (cdr x)) a b)) { C6, D1, C2, C3, C4, MP }

Goal: 
(equal (all-in-range x a b)
       (all-in-range (rev2 x) a b))

Proof:
(equal (all-in-range x a b)
       (all-in-range (rev2 x) a b))
= { Def rev2, C1, C5 }
(equal (all-in-range x a b)
       (all-in-range (app2 (rev2 (rest x)) (list (first x))) a b))
= { Def all-in-range, C1, C2, C3, C4, C5 }
(equal (if (not (integerp (car x))) (all-in-range (cdr x) a b)
         (and (>= (car x) a)
              (<= (car x) b)
              (all-in-range (cdr x) a b)))
       (all-in-range (app2 (rev2 (rest x)) (list (first x))) a b))
= { Lemma range-app2((x (rev2 (rest x))) (y (list (first x))) (a a) (b b)) }
(equal (if (not (integerp (car x))) (all-in-range (cdr x) a b)
         (and (>= (car x) a)
              (<= (car x) b)
              (all-in-range (cdr x) a b)))
       (and (all-in-range (rev2 (rest x)) a b)
            (all-in-range (list (first x)) a b)))
= { Def all-in-range, cons axiom }
(equal (if (not (integerp (car x))) (all-in-range (cdr x) a b)
         (and (>= (car x) a)
              (<= (car x) b)
              (all-in-range (cdr x) a b)))
       (and (if (not (integerp (car x))) (all-in-range '() a b)
              (and (>= (car x) a)
                   (<= (car x) b)
                   (all-in-range nil a b)))
            (all-in-range (rev2 (rest x)) a b)))
= { if axiom, PL }
(equal (all-in-range (cdr x) a b)
       (and (all-in-range nil a b)
            (all-in-range (rev2 (rest x)) a b)))
= { Def all-in-range }
(equal (all-in-range (cdr x) a b)
       (and t (all-in-range (rev2 (rest x)) a b)))
= { PL, D2 }
t

QED

QED

