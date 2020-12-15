(definec acc-fn-sum (x :nat acc :nat) :nat
  (cond ((zp  x)    acc)
        (t        (acc-fn-sum (1- x) (+ x acc)))))

(definec non-acc-fn-sum (x :nat) :nat
  (cond ((zp  x) 0)
        (t       (+ x (non-acc-fn-sum  (1- x))))))

(definec acc-fn-sum-interface (x :nat) :nat
  (acc-fn-sum x 0))

; Sanity check, does test? find any counterexamples? No. :D
(test? (implies (and (natp x) (natp acc) (zp acc))
              (equal (non-acc-fn-sum x) (acc-fn-sum x acc))))

#|
(set-gag-mode nil)
:brr t
(cw-gstack :frames 30)
|#


#|
Description:
In order to prove sum-associativity-zero, we must prove associativity in the
general case for our accumulator function.

That is, adding to the accumulator is the same as adding to the result of the function.

|#
(defthm sum-associativity-general
  (implies (and (natp a) (natp b) (natp c))
           (equal (acc-fn-sum a (+ c b))
                  (+ b (acc-fn-sum a c)))))

#|
Description:
sum-associativity-zero is required to prove a specific case in rec=acc-sum.
In paticular this handles the case in which c+b = 0, or when acc = 0: the base case.
This unwinding of the recursion is required to be explicitly handled as a theorem
for ACL2s to prove rec=acc-sum.

|#
(defthm sum-associativity-zero
  (implies (and (natp a) (natp b) (= acc 0))
           (equal (acc-fn-sum a b)
                  (+ b (acc-fn-sum a acc)))))

#|
Description:
rec=acc-sum claims that the non-accumulator version of the nth triangular number
equals the accumulator version describing the same function for all natural numbers x.

|#
(defthm rec=acc-sum
   (implies (and (natp x))
           
              (= (non-acc-fn-sum x) 
                 (acc-fn-sum-interface x))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definec acc-fn-mult (x :nat acc :nat) :nat
  (cond ((zp  x)    acc)
        (t        (acc-fn-mult (1- x) (* x acc)))))

(definec non-acc-fn-mult (x :nat) :nat
  (cond ((zp  x) 1)
        (t       (* x (non-acc-fn-mult  (1- x))))))

(definec acc-fn-mult-interface (x :nat) :nat
  (acc-fn-mult x 1))

; Sanity check, does test? find any counterexamples? No. :D
(test? (implies (and (natp x) (natp acc) (= 1 acc))
              (equal (non-acc-fn-mult x) (acc-fn-mult x acc))))


#|
Description:
In order to prove mult-associativity-one, we must prove associativity in the
general case for our accumulator function.

That is, adding to the accumulator is the same as adding to the result of the function.
|#


(defthm mult-associativity-general
  (implies (and (natp a) (natp b) (natp c))
           (equal (acc-fn-mult a (* c b))
                  (* b (acc-fn-mult a c)))))

#|
Description:
mult-associativity-one is required to prove a specific case in rec=acc-sum.
In paticular, this handles the case in which c * b = 1, or when acc = 1, which is the base case.
This unwinding of the recursion is required to be explicitly handled as a theorem
for ACL2s to prove rec=acc-sum.
|#

(defthm mult-associativity-one
  (implies (and (natp a) (natp b) (= acc 1))
           (equal (acc-fn-mult a b)
                  (* b (acc-fn-mult a acc)))))

#|
Description:
rec=acc-mult claims that the non-accumulator version of the nth factorial
equals the accumulator version describing the same function for all natural numbers x.

|#
(defthm rec=acc-mult
   (implies (and (natp x))
           
              (= (non-acc-fn-mult x) 
                 (acc-fn-mult-interface x))))#|ACL2s-ToDo-Line|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Failed General Multiplication Proof:
(definec acc-fn-gen (x :nat acc :nat b :nat) :nat
  (cond ((zp  x)    acc)
        (t        (acc-fn-gen (1- x) (* x (* b acc)) b))))

(definec non-acc-fn-gen (x :nat b :nat) :nat
  (cond ((zp  x) 1)
        (t       (* x (* b (non-acc-fn-gen (1- x) b) )))))

(definec acc-fn-gen-interface (x :nat b :nat) :nat
  (acc-fn-gen x 1 b))

; Sanity check, does test? find any counterexamples? No. :D
(test? (implies (and (natp x) (natp acc) (= acc 1) (natp b))
              (equal (non-acc-fn-gen x b) (acc-fn-gen x acc b))))


#|
Description:
In order to prove gen-mult-associativity-one, we must prove associativity in the
general case for our accumulator function.

That is, adding to the accumulator is the same as adding to the result of the function.
|#


(defthm gen-mult-associativity-general
  (implies (and (natp a) (natp b) (natp c))
           (equal (acc-fn-gen a (* c b) b)
                  (* b (acc-fn-gen a c b)))))

#|
Description:
gen-mult-associativity-one is required to prove a specific case in rec=acc-gen.
Unfortunately, this was the step that failed, due to the fact that ACL2s could
not perform the appropriate, in order to prove the statement.
|#

(defthm gen-mult-associativity-one
  (implies (and (natp a) (natp b) (= acc 1))
           (equal (acc-fn-gen a (* acc b) b)
                  (* b (acc-fn-gen a acc b)))))

#|
Description:
rec=acc-gen claims that the non-accumulator version of a constant times the nth factorial
equals the accumulator version describing the same function for all natural numbers x.

|#
(defthm rec=acc-gen
   (implies (and (natp x) (natp b))
              (= (non-acc-fn-gen x b) 
                 (acc-fn-gen-interface x b))))

