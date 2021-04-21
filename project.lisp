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

; Data definition of a list of integers
(defdata loi (listof integer))


; Definitions of utility functions

; Append 2 lists
(definec app2 (a :tl b :tl) :tl
  (if (endp a)
    b
    (cons (first a) (app2 (rest a) b))))

; Reverse a list
(definec rev2 (x :tl) :tl
  (if (endp x)
    nil
    (app2 (rev2 (rest x)) (list (first x)))))

; Length of a list
(definec len2 (x :tl) :nat
  (if (endp x)
    0
    (+ 1 (len2 (rest x)))))

; Are all elements in a list of integers between lower bound a 
; and upper bound b?
(definec all-in-range (x :loi a :integer b :integer) :bool
  :ic (>= b a)
  (cond ((endp x) t)
        (t (and (>= (car x) a)
                (<= (car x) b)
                (all-in-range (cdr x) a b)))))


(check= (all-in-range '() 1 2) t)
(check= (all-in-range '(1) 1 1) t)
(check= (all-in-range '(2) 1 1) nil)
(check= (all-in-range '(1 2 3) -1 4) t)
(check= (all-in-range '(-100 0 100) 1 2) nil)
(check= (all-in-range '(-100 0 100) -101 101) t)





; Appending 2 lois yields another loi
(defthm app2-loi
  (implies (and (loip x) (loip y))
           (loip (app2 x y))))

; Reversing a loi yields another loi
(defthm rev2-loi
  (implies (loip x)
           (loip (rev2 x))))

; If 2 lois both satisfy all-in-range between 2 integers a and b,
; then the result of appending these 2 lois also satisfies 
; all-in-range between a and b.
(defthm range-app2
  (implies (and (loip x)
                (loip y)
                (integerp a)
                (integerp b)
                (>= b a))
         (equal (all-in-range (app2 x y) a b)
                (and (all-in-range x a b)
                     (all-in-range y a b))))
  :hints (("Goal" 
           :induct (loip x))))

; If a loi satisfies all-in-range between a and b,
; then the reverse of this loi also satisfies the same condition.
(defthm range-rev2
  (implies (and (loip x)
                (integerp a)
                (integerp b)
                (>= b a)
                (all-in-range x a b))
           (all-in-range (rev2 x) a b))
  :hints (("Goal" 
           :induct (loip x))))


; Data definition of an integer between 0 and 9
(defdata numerals (range integer (0 <= _ <= 9)))

; Data definition of a list of integers between 0 and 9
(defdata lon (listof numerals))

; The sum of a lon
(definec sum-all (l :lon) :nat
  (if (endp l)
    0
    (+ (car l) (sum-all (cdr l)))))

; The reverse of a lon is also a lon
(defthm rev2-lon
  (implies (lonp x)
           (lonp (rev2 x))))

; Appending 2 lons yields another lon
(defthm app2-lon
  (implies (and (lonp x)
                (lonp y))
           (lonp (app2 x y))))

; The sum of 2 lons is the same as the sum of 1 lon plus the 
; sum of the other lon.
(defthm sum-all-app2
  (implies (and (lonp x)
                (lonp y))
           (equal (sum-all (app2 x y))
                  (+ (sum-all x) (sum-all y)))))

; The sum of a lon is the same as the sum of its reverse.
(defthm sum-all-rev2
  (implies (lonp x)
           (equal (sum-all x) (sum-all (rev2 x)))))

; The sum of any lon must be less than or equal to 9 multiplied by
; the length of that lon.
(defthm sum-all-numerals
  (implies (lonp x)
           (<= (sum-all x) (* 9 (len2 x))))
  :hints (("Goal"
           :in-theory (disable sum-all-rev2))))

; The sum of a reverse of any lon must be less than or equal to 9
; multiplied by the lenght of that lon.
(defthm sum-all-numerals-rev2
  (implies (lonp x)
           (<= (sum-all (rev2 x)) (* 9 (len2 x))))
  :hints (("Goal"
           :in-theory (disable sum-all-rev2)
           :use (sum-all-numerals))))
