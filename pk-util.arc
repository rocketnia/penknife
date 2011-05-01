; pk-util.arc
; Penknife miscellaneous stuff.
;
; This depends on the following non-core Penknife utilities:
;
; defined in pk-parse.arc: fn-ifword parse-calculation
; parse-expression t-core-text parse-sip-expression
; parse-form-expression
;
; defined in pk-ast.arc: default-expression express-calculation
; express-form t-expr-var t-expr-call parse-identifier
;
; This also depends on 'pkc-letdecaps, defined in pk-ast.arc.
;
; TODO: Implement the following Penknife utility: force-stringify
;
; TODO: Document the following Penknife types:
;   t-token
;   t-sip-form
;   t-get-expression-er
;   t-expr-form
;   t-expr-calculation
;   t-ast-set-call
;   t-ast-set-var
;   t-ast-binding
;   t-ast-literal

; TODO: Implement things like express-form and express-call for the
; expression types unique to here.
pk-core-type.t-token
pk-core-type.t-sip-form
pk-core-type.t-get-expression-er
pk-core-type.t-expr-form
pk-core-type.t-expr-calculation
pk-core-type.t-ast-set-call
pk-core-type.t-ast-set-var
pk-core-type.t-ast-binding
pk-core-type.t-ast-literal


; depends on Penknife: fn-ifword t-expr-form t-get-expression-er

(mac pkc-failletwords (fail vars text . body)
  (if no.vars
    (w/uniq g-fail
      `(let ,g-fail ,fail
         (pkc-failcall pkc.fn-ifword ,g-fail ,text
           (pkc-abfn:pkc-call
             ,g-fail pkc-wrap.t-too-many-args-failure)
           (pkc-thunk ,@body))))
      atom.vars
    `(let ,vars ,text ,@body)
    (let (first . rest) vars
      (w/uniq (g-fail g-text g-rest)
        `(with (,g-fail ,fail ,g-text ,text)
           (pkc-failcall pkc.fn-ifword ,g-fail ,g-text
             (pkc-fn (,first ,g-rest)
               (pkc-failletwords ,g-fail ,rest ,g-rest ,@body))
             (pkc-thunk:pkc-call
               ,g-fail pkc-wrap.t-too-few-args-failure)))))))

(mac pkc-letwords (vars text . body)
  `(pkc-failletwords pkc.raise-failure ,vars ,text
     ,@body))

; NOTE: This exposes a lot of anaphoric variables.
(mac pkc-failformop-expr (fail args . body)
  `(pkc-wrap t-expr-form
     (pkc-fn ,fail (body lexid static-hyperenv)
       (pkc-failletwords ,fail ,args body
         ,@body))))

; NOTE: This exposes a lot of anaphoric variables.
(mac pkc-formop (args . body)
  `(pkc-wrap t-get-expression-er
     (pkc-fn (expr-hyperenv hypervar)
       (pkc-failformop-expr fail ,args ,@body))))

; NOTE: This exposes a lot of anaphoric variables.
(mac pk-core-formop (name args . body)
  `(pk-core-def ,name (pkc-formop ,args ,@body)))


; depends on Penknife: express-calculation t-expr-calculation
; express-form t-expr-form

(pk-core-rule express-calculation (expr)
                express-calculation/expr-calculation
  (pkc-relycall:pkc-relyunwrap t-expr-calculation expr))

(pk-core-rule express-form (op-expr body-text lexid static-hyperenv)
                express-form/expr-form
  (pkc-relycall (pkc-relyunwrap t-expr-form op-expr)
    body-text lexid static-hyperenv))


; depends on Penknife: fn-ifword t-expr-form t-get-expression-er
; t-expr-calculation parse-expression t-ast-set-call t-expr-call
; parse-calculation t-ast-set-var t-expr-var

pk-core-rulebook.express-assignment

(pk-core-rule express-assignment (place body lexid static-hyperenv)
                express-assignment/expr-var
  (pkc-wrap t-ast-set-var
    (list (pkc-relyunwrap t-expr-var place)
          pkc-wrap.t-ast-get-raise-failure
          (pkc-failletwords fail (val) body
            (pkc:parse-calculation val lexid static-hyperenv)))))

(pk-core-rule express-assignment (place body lexid static-hyperenv)
                express-assignment/expr-call
  (pkc-letdecaps (func . args) (pkc-relyunwrap t-expr-call place)
    (pkc-failletwords fail (val) body
      (pkc-wrap t-ast-set-call
        (pkc-list func pkc-wrap.t-ast-get-raise-failure args
          (pkc:parse-calculation val lexid static-hyperenv))))))

pk-core-rulebook.parse-assignment

(pk-core-rule parse-assignment (place body lexid static-hyperenv)
                parse-assignment/express-assignment
  (pkc:express-assignment
    (pkc-relycall pkc.parse-expression place lexid static-hyperenv)
    body lexid static-hyperenv))

(pk-core-formop = (place . body)
  (pkc-wrap t-expr-calculation
    (pkc-thunk:pkc:parse-assignment
      place body lexid static-hyperenv)))


; depends on Penknife: fn-ifword t-expr-form t-get-expression-er
; t-expr-calculation t-ast-binding parse-identifier

(pk-core-formop binding (var)
  (pkc-wrap t-expr-calculation
    (pkc-thunk:pkc-wrap t-ast-binding
      (pkc:parse-identifier var lexid))))


; TODO: See if this is enough.
(pk-core-fun core-is (a b then else)
  (if (is a b) then else))


; depends on Penknife: fn-ifword t-expr-form t-get-expression-er
; t-expr-calculation t-ast-literal force-stringify

(pk-core-formop s contents
  (pkc-wrap t-expr-calculation
    (pkc-thunk:pkc-wrap t-ast-literal
      (pkc:force-stringify contents))))


; depends on Penknife: fn-ifword t-expr-form t-get-expression-er
; parse-expression express-form t-core-text t-sip-form
; parse-sip-expression parse-form-expression

(pk-core-rule parse-sip-expression (sip lexid static-hyperenv)
                parse-sip-expression/sip-form
  (let (op body) (pkc-relyunwrap t-sip-form sip)
    (pkc-relycall pkc.parse-form-expression
      op body lexid static-hyperenv)))

(pk-core-formop : a
  (zap [pkc-relycall pkc.parse-expression _ lexid static-hyperenv] a)
  (pkc-failformop-expr fail b
    (pkc-failformop-expr fail body
      (pkc-relycall pkc.express-form op
        (pkc-wrap t-core-text
          (list:pkc-wrap t-sip-form (list b body)))
        lexid static-hyperenv))))


; depends on Penknife: t-expr-call parse-expression parse-calculation

pk-core-rulebook.express-call

(pk-core-rule express-call (expr) express-call/expr-call
  (pkc-relyunwrap t-expr-call expr))

pk-core-rulebook.parse-call

(pk-core-rule parse-call (text lexid static-hyperenv)
                parse-call/express-call
  (pkc:express-call:pkc-relycall pkc.parse-expression
    text lexid static-hyperenv))

(pk-core-formop call-using (caller call)
  (pkc-wrap t-expr-call
    (pkc-thunk:pkc-list*
      (pkc:parse-calculation caller lexid static-hyperenv)
      (pkc:parse-call call lexid static-hyperenv))))


; TODO: Make some rules for this.
pk-core-rulebook.core-set-call


; depends on Penknife: t-token

(pk-core-fun token ()
  pkc-wrap.t-token)
