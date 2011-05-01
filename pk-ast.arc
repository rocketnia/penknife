; Penknife AST stuff.
;
; This depends on the following non-core Penknife utilities:
;
; defined in "parser stuff": fn-ifword parse-calculation
;
; defined in "core environment stuff": t-hyperenv
;
; TODO: Document the following Penknife types:
;   t-expr-var
;   t-expr-call
;   t-ast-get-raise-failure
;   t-ast-var
;   t-ast-call


(mac pkc-failletdecaps (fail vars seq . body)
  (if no.vars
    (w/uniq g-fail
      `(let ,g-fail ,fail
         (pkc-failcall pkc.fn-ifdecap ,g-fail ,seq
           (pkc-abfn:pkc-call
             ,g-fail pkc-wrap.t-too-many-args-failure)
           (pkc-thunk ,@body))))
      atom.vars
    `(let ,vars ,seq ,@body)
    (let (first . rest) vars
      (w/uniq (g-fail g-seq g-rest)
        `(with (,g-fail ,fail ,g-seq ,seq)
           (pkc-failcall pkc.fn-ifdecap ,g-fail ,g-seq
             (pkc-fn (,first ,g-rest)
               (pkc-failletdecaps ,g-fail ,rest ,g-rest ,@body))
             (pkc-thunk:pkc-call
               ,g-fail pkc-wrap.t-too-few-args-failure)))))))

(mac pkc-letdecaps (vars seq . body)
  `(pkc-failletdecaps pkc.raise-failure ,vars ,seq
     ,@body))


pk-core-type.t-expr-var
pk-core-type.t-expr-call
pk-core-type.t-ast-get-raise-failure
pk-core-type.t-ast-var
pk-core-type.t-ast-call


; depends on Penknife: t-expr-var

(pk-core-fun default-expression (hyperenv hypervar)
  (pkc-wrap t-expr-var hypervar))


; depends on Penknife: t-ast-var t-expr-var t-ast-call t-expr-call

pk-core-rulebook.express-calculation

(pk-core-rule express-calculation (expr)
                express-calculation/t-expr-var
  (pkc-wrap t-ast-var (pkc-list pkc-wrap.t-ast-get-raise-failure
                                (pkc-relyunwrap t-expr-var expr))))

(pk-core-rule express-calculation (expr)
                express-calculation/t-expr-call
  (pkc-letdecaps (func . args) (pkc-relyunwrap t-expr-var expr)
    (pkc-wrap t-ast-call
      (pkc-list* func pkc-wrap.t-ast-get-raise-failure args))))


; depends on Penknife: t-expr-call t-expr-var t-hyperenv
; express-calculation fn-ifword parse-calculation

pk-core-rulebook.default-express-form

(pk-core-rule default-express-form (op-expr body-text lexid
                                    static-hyperenv)
                default-express-form/hyperenv
  (pkc-relyunwrap t-hyperenv static-hyperenv)
  (pkc-wrap t-expr-call
    (pkc-list* (pkc-relycall pkc.express-calculation op-expr)
      (ut:xloop body body-text rev-args nil
        (pkc:fn-ifword body
          (pkc-fn (margin arg rest)
            (do.next rest (cons (pkc:parse-calculation
                                  arg lexid static-hyperenv)
                                rev-args)))
          (pkc-thunk:pkc-arc-to-list rev.rev-args))))))

pk-core-rulebook.express-form

(mac pk-core-def-default-express-form (label type)
  `(pk-core-rule express-form (op-expr body-text lexid
                               static-hyperenv)
                   ,(sym:+ "express-form/" label)
     (pkc-relyunwrap ,type op-expr)
     (pkc-relycall pkc.default-express-form
       op-expr body-text lexid static-hyperenv)))

(pk-core-def-default-express-form expr-var t-expr-var)
(pk-core-def-default-express-form expr-call t-expr-call)
