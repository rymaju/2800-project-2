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

