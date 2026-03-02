#lang racket
(define (string-lowercase? s)
  (and (string? s)
       (for/and ([ch (in-string s)])
         (or (not (char-alphabetic? ch))
             (char-lower-case? ch)))))

(struct agda-implicit (name val)
  #:transparent
  #:property prop:custom-write
  (λ (x out mode)
    (define (W v) (print v out mode)) ; respects write/display/print mode
    (display "{" out)
    (W (agda-implicit-name x))
    (display " = " out)
    (W (agda-implicit-val x))
    (display "}" out)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Natural numbers → Agda constructors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-τ-to-name
  (λ (name)
    (string->symbol
     (string-append (symbol->string name) "τ"))))

(define from-nat
  (λ (n)
    (if (zero? n)
        'Zero
        `(Suc ,(from-nat (sub1 n))))))

(define from-bool
  (λ (b)
    (if (or (eqv? b #t) b 'true) 'True 'False)))

(define from-nat-ty
  (λ (n)
    (if (zero? n)
        'τ-zero
        `(τ-suc ,(from-nat-ty (sub1 n))))))

(define (var? x)
  (and (symbol? x)
       (string-lowercase? (symbol->string x))))

(define (ty-var? x)
  (and (symbol? x) (not (string-lowercase? x))))

(define (has-generic-ty? τ)
  (memv '∀ τ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lookup (only for term translation)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lex
  (lambda (ls v)
    (call/cc (λ (k)
               (letrec ([lex-helper
                         (λ (ls v acc)
                           (cond
                             [(null? ls) (k #f)]
                             [(eqv? (caar ls) v) (k acc)]
                             [else (lex-helper (cdr ls) v (add1 acc))]))])
                 (lex-helper ls v 0))))))

;; lex-ty : [ListOf TypeVar] TypeVar -> NaturalNumber
;;
(define lex-ty
  (lambda (ls v)
    (cond
      [(null? ls)
       (printf "ls=~a, v=~a\n" ls v)
       (error "this shouldn't occur")]
      [(eqv? (car ls) v) 0]
      [(add1 (lex-ty (cdr ls) v))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Type → Agda term (for Fix annotation)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; type->agda-term : Type [ListOf TypeVar] -> AgdaTerm
;;
(define type->agda-term
  (λ (ty tyvars)
    (match ty
      ['Nat `Nat]
      ['Bool `Bool]
      [`,v #:when (ty-var? v) `(TVar ,(lex-ty tyvars v))]
      [`,v #:when (var? v) (error "TODO.")]
      [`(∀ ,A ,body) `(∀' ,(type->agda-term body (cons A tyvars)))]
      [`(,x ⇒ ,y) `(,(type->agda-term x tyvars) ⇒ ,(type->agda-term y tyvars))]
      [`(List ,v) `(List ,(type->agda-term v tyvars))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Type → Agda type object
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; type->agda-type : Type [ListOf TypeVar] -> AgdaType
;;
(define type->agda-type
  (λ (ty tyvars)
    (match ty
      ['Nat `ty-nat]
      ['Bool `ty-bool]
      [`,v #:when (ty-var? v) `(ty-var ,(agda-implicit 'n (lex-ty tyvars v)) refl)]
      [`(∀ ,_ ,body) `(ty-all ,(type->agda-type body tyvars))]
      [`(,x ⇒ ,y) `(ty-arr ,(type->agda-type x tyvars) ,(type->agda-type y tyvars))]
      [`(List ,v) `(ty-list ,(type->agda-type v tyvars))])))


;; count-∀ : Term -> [ListOf TypeVar]
;;
(define count-∀
  (λ (term)
    (match term
      [`(∀ ,t ,body) (append (count-∀ body) (list t))]
      [_ '()])))

;; create-foralls-ty : Type NaturalNumber -> AgdaType
;;
(define create-foralls-ty
  (λ (ty n)
    (cond
      [(zero? n) ty]
      [`(τ-lamT ,(create-foralls-ty ty (sub1 n)))])))

;; create-foralls-ty : Term NaturalNumber -> AgdaTerm
;;
(define create-foralls
  (λ (term n)
    (cond
      [(zero? n) term]
      [`(LamT ,(create-foralls term (sub1 n)))])))
      

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; interp : surface → Agda term
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; interp : Term [AssocOf Var Type] [ListOf TypeVar] -> AgdaTerm
;;
(define interp
  (λ (exp Γ Δ)
    (printf "exp=~a\n" exp)
    (match exp
      [`,v #:when (var? v)
           (let ([lookup (lex Γ v)])
             (if (false? lookup) v `(Var ,lookup)))]
      [`,v #:when (ty-var? v) `(TVar ,(lex Δ v))]
      [`,n #:when (number? n) (from-nat n)]
      [`,b #:when (boolean? b) (from-bool b)]
      [`(null? ,e) `(Nil? ,(interp e Γ Δ))]
      [`(add1 ,e) `(Suc ,(interp e Γ Δ))]
      [`(sub1 ,e) `(Pred ,(interp e Γ Δ))]
      [`(zero? ,e) `(Zero? ,(interp e Γ Δ))]
      [`(first ,e) `(First ,(interp e Γ Δ))]
      [`(rest ,e) `(Rest ,(interp e Γ Δ))]
      [`(lcons ,x ,xs) `(LCons ,(interp x Γ Δ) ,(interp xs Γ Δ))]
      [`(lambda (,v : ,τ) ,body) `(Lam ,(interp body (cons (cons v τ) Γ) Δ))]
      [`(if ,p ,c ,a)
       `(If ,(interp p Γ Δ)
            ,(interp c Γ Δ)
            ,(interp a Γ Δ))]
      [`(case ,scrut ,left ((,x : ,τ) => ,right))
       `(Case ,(interp scrut Γ Δ)
              ,(interp left (cons (cons '() 'Unit) Γ) Δ)
              ,(interp right (cons (cons x τ) Γ) Δ))]
      [`(,rator ,rand)
       `(App ,(interp rator Γ Δ) ,(interp rand Γ Δ))]
      [`(,rator @ ,ty)
       `(AppT ,(interp rator Γ Δ)
              ,(type->agda-term ty Δ))]
      [`(fix ,τ ,name ,e)
       (let* ([Δ′ (count-∀ τ)])
         `(Fix ,(type->agda-term τ Δ′)
               ,(create-foralls (interp e
                                        (cons (cons name τ) Γ)
                                        Δ′)
                                (length Δ′))))])))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; interp-ty : surface → Agda typing proof
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; interp-ty : Term [AssocOf Var Type] [ListOf TypeVar] -> AgdaType
;;
(define interp-ty
  (λ (exp Γ Δ)
    (match exp
      [`,v #:when (var? v)
           (let ([lookup (lex Γ v)])
             (if (false? lookup)
                 `(weaken-closed ,(add-τ-to-name v))
                 `(τ-var ,(agda-implicit 'n lookup) ,(type->agda-type (cdr (assv v Γ)) Δ) refl)))]
      [`,v #:when (ty-var? v) `(τ-var ,(lex Δ v))]
      [`,n #:when (number? n) (from-nat-ty n)]
      [`,b #:when (boolean? b) `τ-bool]
      [`(null? ,e) `(τ-nil? ,(interp-ty e Γ Δ))]
      [`(add1 ,e) `(τ-suc ,(interp-ty e Γ Δ))]
      [`(sub1 ,e) `(τ-pred ,(interp-ty e Γ Δ))]
      [`(zero? ,e) `(τ-zero? ,(interp-ty e Γ Δ))]
      [`(first ,e) `(τ-first ,(interp-ty e Γ Δ))]
      [`(rest ,e) `(τ-rest ,(interp-ty e Γ Δ))]
      [`(lcons ,x ,xs) `(τ-lcons ,(interp-ty x Γ Δ) ,(interp-ty xs Γ Δ))]
      [`(case ,scrut ,left ((,x : ,τ) => ,right))
       `(τ-case ,(interp-ty scrut Γ Δ)
                ,(interp-ty left (cons (cons '() 'Unit) Γ) Δ)
                ,(interp-ty right (cons (cons x τ) Γ) Δ))]
      [`(lambda (,v : ,τ) ,body)
       `(τ-lam
          ,(type->agda-type τ Δ)
          ,(interp-ty body (cons (cons v τ) Γ) Δ))]
      [`(if ,p ,c ,a)
       `(τ-if ,(interp-ty p Γ Δ)
              ,(interp-ty c Γ Δ)
              ,(interp-ty a Γ Δ))]
      [`(,rator @ ,ty)
       `(τ-appT ,(type->agda-type ty Δ)
                ,(interp-ty rator Γ Δ))]
      [`(,rator ,rand) `(τ-app ,(interp-ty rator Γ Δ) ,(interp-ty rand Γ Δ))]
      [`(fix ,ty ,name ,e)
       (let* ([Δ′ (count-∀ ty)])
         `(τ-fix ,(type->agda-type ty Δ′)
               ,(create-foralls-ty (interp-ty e
                                        (cons (cons name ty) Γ)
                                        Δ′)
                                (length Δ′))))]
      [`(∀ ,A ,body) `(τ-lamT ,(interp-ty body Γ (cons A Δ)))])))


(define fact-example
  '(fix (Nat ⇒ Nat)
        fact
        (lambda (x : Nat)
          (if (zero? x) 1 ((mul x) (fact (sub1 x)))))))

#;(pretty-print (interp fact-example '() '()))
#;(pretty-print (interp-ty fact-example '() '()))

(define add-example
  '(fix (Nat ⇒ (Nat ⇒ Nat))
        add
        (lambda (x : Nat)
          (lambda (y : Nat)
            (if (zero? x) y ((add (sub1 x)) (add1 y)))))))

#;(pretty-print (interp add-example '() '()))
#;(pretty-print (interp-ty add-example '() '()))

(define mul-example
  '(fix (Nat ⇒ (Nat ⇒ Nat))
        mul
        (lambda (x : Nat)
          (lambda (y : Nat)
            (if (zero? x)
                0
                ((add y) ((mul (sub1 x)) y)))))))

#;(pretty-print (interp mul-example '() '()))
#;(pretty-print (interp-ty mul-example '() '()))


(define length-example
  `(fix (∀ A ((List A) ⇒ Nat))
        length
        (lambda (ls : (List A))
          (if (null? ls)
              0
              (add1 ((length @ A) (rest ls)))))))


(define append-example
  `(fix (∀ A ((List A) ⇒ ((List A) ⇒ (List A))))
           append
           (lambda (ls1 : (List A))
             (lambda (ls2 : (List A))
               (if (null? ls1) ls2
                   (case (first ls1)
                     ls2
                     ((h : A) => (lcons h (((append @ A)
                                            (rest ls1))
                                           ls2)))))))))

(define map-example
  `(fix (∀ A (∀ B ((A ⇒ B) ⇒ ((List A) ⇒ (List B)))))
        map
        (lambda (f : (A ⇒ B))
          (lambda (ls : (List A))
            (if (null? ls) ls
                (case (first ls)
                  ls
                  ((h : A) => (lcons (f h) ((((append @ A) @ B) f) (rest ls))))))))))

(define leq-example
  `(fix (Nat ⇒ (Nat ⇒ Bool))
        leq
        (lambda (a : Nat)
          (lambda (b : Nat)
            (if (zero? a)
                #t
                (if (zero? b)
                    #f
                    ((leq (sub1 a)) (sub1 b))))))))

(define insert-into-sorted-example
  `(fix (∀ A ((A ⇒ (A ⇒ Bool)) ⇒ (A ⇒ ((List A) ⇒ (List A)))))
        insert-into-sorted
        (lambda (cmpleq : (A ⇒ (A ⇒ Bool)))
          (lambda (v : A)
            (lambda (ls : (List A))
              (if (null? ls)
                  (lcons v nil)
                  (case (first ls)
                    ls
                    ((h : A) => (if ((cmpleq v) h)
                                    (lcons v ls)
                                    (lcons h ((((insert-into-sorted @ A) cmpleq) v) (rest ls))))))))))))

(define isort-example
  `(fix (∀ A ((A ⇒ (A ⇒ Bool)) ⇒ ((List A) ⇒ (List A))))
        isort
        (lambda (cmpleq : (A ⇒ (A ⇒ Bool)))
          (lambda (ls : (List A))
            (if (null? ls)
                ls
                ((((insert-into-sorted @ A) cmpleq) (first ls)) (((isort @ A) cmpleq) (rest ls))))))))

(define isort
  (lambda (cmpleq)
    (lambda (ls)
      (if (null? ls)
          ls
          (((insert-into-sorted cmpleq) (first ls)) ((isort cmpleq) (rest ls)))))))

(define insert-into-sorted
  (lambda (cmpleq)
    (lambda (v)
      (lambda (ls)
        (if (null? ls)
            (list v)
            (if (cmpleq v (first ls))
                (cons v ls)
                (cons (first ls) (((insert-into-sorted cmpleq) v) (rest ls)))))))))
        

(printf "---------------------------------------\n")
(printf "-------------   LENGTH ----------------\n")
(pretty-print (interp length-example '() '()))
(pretty-print (interp-ty length-example '() '()))

(printf "---------------------------------------\n")
(printf "-------------   APPEND ----------------\n")
(pretty-print (interp append-example '() '()))
(pretty-print (interp-ty append-example '() '()))

(printf "---------------------------------------\n")
(printf "-------------   MAP -------------------\n")
(pretty-print (interp map-example '() '()))
(pretty-print (interp-ty map-example '() '()))

(printf "---------------------------------------\n")
(printf "-------------   LEQ -------------------\n")
(pretty-print (interp leq-example '() '()))
(pretty-print (interp-ty leq-example '() '()))

(printf "---------------------------------------\n")
(printf "-------------   ISort -------------------\n")
(pretty-print (interp isort-example '() '()))
(pretty-print (interp-ty isort-example '() '()))

;; Convenience: run these in the REPL
;; (interp append-example '() '())
;; (interp-ty append-example '() '() '())