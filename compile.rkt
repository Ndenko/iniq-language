#lang racket
(provide (all-defined-out))
(require "ast.rkt" "types.rkt" "compile-ops.rkt" a86/ast)
;;added
(require "interp.rkt" "parse.rkt")
;; Registers used
(define rax 'rax) ; return
(define rbx 'rbx) ; heap
(define rsp 'rsp) ; stack
(define rdi 'rdi) ; arg
(define r11 'r11)
(define r9 'r9)
(define r8 'r8)

;; type CEnv = [Listof Variable]

;; Prog -> Asm
(define (compile p)
  (match p
    [(Prog ds e)
    ;;(displayln e)
     (prog (externs)
           (Global 'entry)
           (Label 'entry)
           (Push rbx)
           (Push r15)
           (Mov rbx rdi) ; recv heap pointer
           (compile-e e '())
           (Pop r15)
           (Pop rbx)
           (Ret)
           (compile-defines ds)
           (Label 'raise_error_align)
           pad-stack
           (Call 'raise_error))]))

(define (externs)
  (seq (Extern 'peek_byte)
       (Extern 'read_byte)
       (Extern 'write_byte)
       (Extern 'raise_error)))

;; [Listof Defn] -> Asm
(define (compile-defines ds)
  ;;(displayln ds)
  (match ds
    ['() (seq)]
    [(cons h t) ;;(displayln h)
                ;;(displayln t)
                (seq (compile-define h)
                      (compile-defines t))]))

;; Defn -> Asm
(define (compile-define d)
  (match d
    [(Defn f fun) ;;(displayln (length (FunPlain-xs fun)))
                  ;;(displayln (FunPlain-xs fun))
                  ;;not the same(let ((r (gensym 'ret)))
                  
                  (seq
                    ;;make label that func call will jump to
                    (compile-fun f fun)  
                  )
    ]))

;; Id Fun -> Asm
(define (compile-fun f fun)
  (match fun
    [(FunPlain xs e) ;;(displayln (length xs))
      (let ((same_arity (gensym 'l1)))
      (seq (Label (symbol->label f))
            ;; TODO: check arity
          
            ;;and we dont want the control flow to skip it when it jumps
            ;;compare the number of func application args stored in r9, 
            ;;to the number of args in func definition, cause error if
            (Cmp 'r9  (length (FunPlain-xs fun)))
            (Je same_arity)
            ;;raise error if not same
            (Jmp 'raise_error_align)
            (Label same_arity)
            
            (compile-e e (reverse xs))
            (Add rsp (* 8 (length xs)))
            (Ret)))        
    ]
    [
      (FunRest pre post body) ;;(displayln body)
                  (let ((valid_arity (gensym 'valid_arity)))
                    (seq (Label (symbol->label f))
                          (Cmp r9 (length pre))
                          (Jge valid_arity)
                          (Jmp 'raise_error_align)
                          (Label valid_arity)
                          (compile-e (Empty) '())
                          (Sub r9 (length pre))
                          (handle-list)
                          (compile-e body (reverse (append pre (list post))))
                          (Add rsp (* 8 (+ (length pre) 1)))
                          (Ret)))
    ]
    [(FunCase x)  ;;(displayln x)
                  ;;(displayln (FunCase-cs fun))
                  ;;(displayln (car(cdr (FunCase-cs fun))))
                  ;;(displayln (FunPlain-xs (list-ref (FunCase-cs fun) 0)))
                  ;;(for ([item (FunCase-cs fun)]) (displayln item))
                    
                  (seq
                    (Label (symbol->label f))
                    (FunCase-iterate f x)
          
                  )               
    ]
    
    ;; TODO: handle other kinds of functions
    [_
     (seq)]))

(define (compile-fun-no-label f fun)
  (match fun
    [(FunPlain xs e) ;;(displayln (length xs))
      (let ((same_arity (gensym 'l1)))
      (seq 
            ;; TODO: check arity
          
            ;;and we dont want the control flow to skip it when it jumps
            ;;compare the number of func application args stored in r9, 
            ;;to the number of args in func definition, cause error if
            (Cmp 'r9  (length (FunPlain-xs fun)))
            (Je same_arity)
            ;;raise error if not same
            (Jmp 'raise_error_align)
            (Label same_arity)
            
            (compile-e e (reverse xs))
            (Add rsp (* 8 (length xs)))
            (Ret)))        
    ]
    [
      (FunRest xs y e)
                      (let ((valid_arity (gensym 'valid_arity)))
                        (seq 
                              (Cmp r9 (length xs))
                              (Jge valid_arity)
                              (Jmp 'raise_error_align)
                              (Label valid_arity)
                              (compile-e (Empty) '())
                              (Sub r9 (length xs))
                              (handle-list)
                              (compile-e e (reverse (append xs (list y))))
                              (Add rsp (* 8 (+ (length xs) 1)))
                              (Ret)))
    ]
    [(FunCase x) 
                    (seq)
                  
    ]
    ;; TODO: handle other kinds of functions
    [_
     (seq)]))

(define (handle-list)
  (let ((l1 (gensym 'top))
        (l2 (gensym 'bot)))
    (seq (Cmp r9 0)
         (Je l2)
         (Label l1)
         (Mov (Offset rbx 0) rax)
         (Pop rax)
         (Mov (Offset rbx 8) rax)
         (Mov rax rbx)
         (Or rax type-cons)
         (Add rbx 16)
         (Sub r9 1)
         (Cmp r9 0)
         (Jg l1)
         (Label l2)
         (Push rax))))


(define (FunCase-iterate f lst)
  (match lst 
    ['() (seq)]
    [(cons h t)  
                (seq
                  (FunCase-solve f h)
                  (FunCase-iterate f t)
                )
                  
    ]
  )
)


(define (FunCase-solve f fun)
  (match fun
    [(FunPlain xs e)    
                      ;;(displayln fun)
                      ;;(displayln xs)
                      (let ((same_length (gensym 'same_length))
                      (end (gensym 'end)))

                      
                        (seq
                          ;;if length of xs is same as length of es, do
                          (Cmp 'r9 (length xs))
                          (Jne end)
                          (Je same_length)

                          (Label same_length)
                         
                          (compile-fun-no-label f fun)

                          (Label end)                    
                        )
                      )
    ]
    [
      (FunRest xs y e) 
                    (let ((same_length (gensym 'same_length))
                      (end (gensym 'end)))
                        (seq                    
                          (compile-fun-no-label f fun)                   
                        )
                      )
    ]
  )
)

;; Expr CEnv -> Asm
(define (compile-e e c)
  (match e
    [(Int i)            (compile-value i)]
    [(Bool b)           (compile-value b)]
    [(Char c)           (compile-value c)]
    [(Eof)              (compile-value eof)]
    [(Empty)            (compile-value '())]
    [(Var x)            (compile-variable x c)]
    [(Str s)            (compile-string s)]
    [(Prim0 p)          (compile-prim0 p c)]
    [(Prim1 p e)        (compile-prim1 p e c)]
    [(Prim2 p e1 e2)    (compile-prim2 p e1 e2 c)]
    [(Prim3 p e1 e2 e3) (compile-prim3 p e1 e2 e3 c)]
    [(If e1 e2 e3)      (compile-if e1 e2 e3 c)]
    [(Begin e1 e2)      (compile-begin e1 e2 c)]
    [(Let x e1 e2)      (compile-let x e1 e2 c)]
    [(App f es)         (compile-app f es c)]
    [(Apply f es e)     (compile-apply f es e c)]))

;; Value -> Asm
(define (compile-value v)
  (seq (Mov rax (value->bits v))))

;; Id CEnv -> Asm
(define (compile-variable x c)
;;(displayln x)
;;(displayln c)
  (let ((i 
          (lookup x c))
       )
       (seq (Mov rax (Offset rsp i)))))

;; String -> Asm
(define (compile-string s)
  (let ((len (string-length s)))
    (if (zero? len)
        (seq (Mov rax type-str))
        (seq (Mov rax len)
             (Mov (Offset rbx 0) rax)
             (compile-string-chars (string->list s) 8)
             (Mov rax rbx)
             (Or rax type-str)
             (Add rbx
                  (+ 8 (* 4 (if (odd? len) (add1 len) len))))))))

;; [Listof Char] Integer -> Asm
(define (compile-string-chars cs i)
  (match cs
    ['() (seq)]
    [(cons c cs)
     (seq (Mov rax (char->integer c))
          (Mov (Offset rbx i) 'eax)
          (compile-string-chars cs (+ 4 i)))]))

;; Op0 CEnv -> Asm
(define (compile-prim0 p c)
  (compile-op0 p))

;; Op1 Expr CEnv -> Asm
(define (compile-prim1 p e c)
  (seq (compile-e e c)
       (compile-op1 p)))

;; Op2 Expr Expr CEnv -> Asm
(define (compile-prim2 p e1 e2 c)
  (seq (compile-e e1 c)
       (Push rax)
       (compile-e e2 (cons #f c))
       (compile-op2 p)))

;; Op3 Expr Expr Expr CEnv -> Asm
(define (compile-prim3 p e1 e2 e3 c)
  (seq (compile-e e1 c)
       (Push rax)
       (compile-e e2 (cons #f c))
       (Push rax)
       (compile-e e3 (cons #f (cons #f c)))
       (compile-op3 p)))

;; Expr Expr Expr CEnv -> Asm
(define (compile-if e1 e2 e3 c)
  (let ((l1 (gensym 'if))
        (l2 (gensym 'if)))
    (seq (compile-e e1 c)
         (Cmp rax (value->bits #f))
         (Je l1)
         (compile-e e2 c)
         (Jmp l2)
         (Label l1)
         (compile-e e3 c)
         (Label l2))))

;; Expr Expr CEnv -> Asm
(define (compile-begin e1 e2 c)
  (seq (compile-e e1 c)
       (compile-e e2 c)))

;; Id Expr Expr CEnv -> Asm
(define (compile-let x e1 e2 c)
  (seq (compile-e e1 c)
       (Push rax)
       (compile-e e2 (cons x c))
       (Add rsp 8)))

;; Id [Listof Expr] CEnv -> Asm
;; The return address is placed above the arguments, so callee pops
;; arguments and return address is next frame
(define (compile-app f es c)
  ;;(displayln f)
  ;;(displayln es)
  ;;(displayln c)
  (let ((r (gensym 'ret)))
    (seq (Lea rax r)
         (Push rax)
         (compile-es es (cons #f c))
         (Mov r9  (length es))
         ;; TODO: communicate argument count to called function
         (Jmp (symbol->label f))
         (Label r))))



;; Id [Listof Expr] Expr CEnv -> Asm
#;
(define (compile-apply f es e c)
  ;; TODO: implement apply
  ;;(displayln e)
  ;;(displayln (compile-e e c))

  (match e
  [(Prim2 p e1 e2)  ;;(displayln e1) 
                    ;;(displayln e2)
                    ;;(displayln (compile-e e1 c)) 
                    ;;(displayln (compile-e e2 c)) 
                    
                    (let ((r (gensym 'ret)))
                    (seq  (Lea rax r)
                          (Push rax)
                          (compile-e e1 c)
                          (Push 'rax)
                          (compile-apply-help e2 c)
                          (Push 'rax)
                          (Mov 'r9 2)
                          (Jmp (symbol->label f))
                          (Label r)
                    )
                    ) 
                    
  ]

  [_    (displayln "no match")
        (seq)]
  ) 
)

;; Id [Listof Expr] Expr CEnv -> Asm
(define (compile-apply f es e c)
  (match e

  [(Prim2 'cons e1 e2)
     (let ((r (gensym 'return))
     (valid_compile (gensym 'valid_compile1)))
       (seq (Lea rax r)
            (Push rax)
            (Mov r9 0)
            (Mov r8 0)
            (Mov r11 0)
            (push_stack es (length es))
            (Add r9 (length es))
            (Mov r8 0)
            (Add r11 r8)
            (Label valid_compile)
            (compile-apply-help2 e)
            (Jmp (symbol->label f))
            (Label r)))]
    [(App list es2)
     (let ((r (gensym 'return))
     (valid_compile (gensym 'valid_compile2)))
       (seq (Lea rax r)
            (Push rax)
            (push_stack es (length es))
            (Mov r8 0)
            (Mov r11 0)
            (Add r11 r8)
            (push_stack es2 (length es2))
            (Mov r8 0)
            (Mov r11 0)
            (Add r11 r8)
            (Label valid_compile)
            (Mov r9 (+ (length es) (length es2)))
            (Jmp (symbol->label f))
            (Label r)))]
    
    [es2
     (let ((r (gensym 'return))
           (l1 (gensym 'compile_app_label))
           (valid_compile (gensym 'valid_compile3)))
       (seq (Lea rax r)
            (Push rax)
            (Mov r9 0)
            (Mov r8 0)
            (push_stack es (length es))
            (Mov r8 0)
           (Mov r11 0)
            (Add r9 (length es))
            (compile-e es2 c)
            (Mov r8 0)
            (Mov r11 0)
            (Cmp rax 152)
            (Je l1)
            (Push rax)
            (Mov r8 0)
            (Label valid_compile)
            (Label l1)
            (Jmp (symbol->label f))
            (Label r)))]))

(define (compile-apply-help2 e)
  (match e
    [(Prim2 'cons e1 e2)
     (seq (compile-e e1 '())
          (Push rax)
          (Mov 'r8 0)
          (Add r9 1)
          (compile-apply-help2 e2))]
    [(Empty) (Mov rax 152)]))

(define (push_stack ls len)
  (match ls
    ['() (seq)]   
    [(cons l ls)
     (seq (compile-e l '())
          (Push rax)
          (push_stack ls len))]))


(define (compile-apply-help e c)
  ;; TODO: implement apply
  ;;(displayln e)
  ;;(displayln (compile-e e c))

  (match e
  [(Empty) (seq) ]
  [(Prim2 p e1 e2) (seq 
                    (compile-e e1 c) 
                    (compile-apply-help e2 c)
                    )
  ]
  )
)

;; [Listof Expr] CEnv -> Asm
(define (compile-es es c)
  ;;(displayln es)
  ;;(displayln c)
  (match es
    ['() '()]
    [(cons h t) ;;(displayln t)
                ;;(displayln (cons #f c))
     (seq (compile-e h c)
          (Push rax)
          (compile-es t (cons #f c)))]))

;; Id CEnv -> Integer
(define (lookup x cenv)
  (match cenv
    ['() (error "undefined variable:" x)]
    [(cons h rest)
     (match (eq? x h)
       [#t 0]
       [#f (+ 8 (lookup x rest))])]))

;; Symbol -> Label
;; Produce a symbol that is a valid Nasm label
(define (symbol->label s)
  (string->symbol
   (string-append
    "label_"
    (list->string
     (map (λ (c)
            (if (or (char<=? #\a c #\z)
                    (char<=? #\A c #\Z)
                    (char<=? #\0 c #\9)
                    (memq c '(#\_ #\$ #\# #\@ #\~ #\. #\?)))
                c
                #\_))
         (string->list (symbol->string s))))
    "_"
    (number->string (eq-hash-code s) 16))))



;;(compile(parse-define'(define (f x) x)))

;;(compile-e (parse-e'(f 3))'())

#;
(parse
'[
  (define (f x y) x)
(f 3)]
)

#;
(compile(parse
'[
  (define (f x y) x)
(f 3)]
))


#;
(parse
  '[; an append that works on any number of lists
    (define (append . xss)
      (if (empty? xss)
          '()
          (if (empty? (car xss))
              (apply append (cdr xss))
              (cons (car (car xss))
                    (apply append (cdr (car xss)) (cdr xss))))))
    ; the list function!
    (define (list . xs) xs)

    (append (list 1 2 3) (list 4) (list 5 6 7))])

;;(value->bits '())