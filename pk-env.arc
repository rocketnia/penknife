; Penknife core environment stuff.
;
; This depends on the following non-core Penknife utilities:
;
; defined in "parser stuff": t-hyped-sym strict-stringify
;
; defined in "AST stuff": default-expression
;
; This also depends on 'pkc-letdecaps, defined in pk-ast.arc.
;
; TODO: Implement the following Penknife utility: captured-hyperenv
;
; TODO: Document the following Penknife types:
;   t-base-lexid
;   t-capture-lexid
;   t-hyperenv
;   t-hyperenv-failget-env-failure
;   t-complete-env


(def fn-memo-thunk (body)
  (let result nil
    (thunk:car:or= result (list call.body))))

(mac memo-thunk body
  `(fn-memo-thunk:thunk ,@body))

; This is a table where each key is either a cons cell containing
; other valid keys or an atom that's a valid key for regular Arc
; tables, which we're assuming are limited to symbol keys. The "sl"
; stands for "symbol list."
(def sl-table ()
  (annotate 'sl-table (list (table) (memo-thunk:sl-table))))

(def sl-table-get (table key (o val-thunk thunk.nil))
  (if atom.key
    (or= rep.table.0.key call.val-thunk)
    (fn-sl-table-get
      (fn-sl-table-get (rep.table.1) head sl-table) tail val-thunk)))

(def sl-table-set (table key (o val))
  (if atom.key
    (= rep.table.0.key val)
    (fn-sl-table-set
      (fn-sl-table-get (rep.table.1) head sl-table) tail val)))


pk-core-type.t-base-lexid
pk-core-type.t-capture-lexid
pk-core-type.t-hyperenv
pk-core-type.t-hyperenv-failget-env-failure
pk-core-type.t-complete-env


; depends on Penknife: t-base-lexid t-capture-lexid t-hyped-sym

pk-core-rulebook.lexid->sl

(pk-core-rule lexid->sl (lexid) lexid->sl/base-lexid
  (pkc:unwrap pkc.t-core-string (pkc-relyunwrap t-base-lexid lexid)))

(pk-core-rule lexid->sl (lexid) lexid->sl/capture-lexid
  (pkc-letdecaps (capturevar parent) (pkc-relyunwrap
                                       t-capture-lexid lexid)
    (pkc-letdecaps (name capture-lexid) (pkc:unwrap
                                          pkc.t-hyped-sym lexid)
      (cons (cons (pkc:unwrap pkc.t-core-string name)
                  (pkc:lexid->sl name))
            (pkc:lexid->sl parent)))))


; depends on Penknife: t-complete-env strict-stringify

pk-core-rulebook.env-failget-binding

(pk-core-rule env-failget-binding (env inner-fail varname)
                env-failget-binding/complete-env
  (zap [pkc-relyunwrap t-complete-env _] env)
  (zap [pkc-relycall pkc.strict-stringify _] varname)
  (!1:sl-table-get env (pkc:unwrap pkc.t-core-string varname)
    (thunk:list varname call.pk-make-binding)))

(pk-core-rule env-failget-binding (env inner-fail varname)
                env-failget-binding/partial-env
  (zap [pkc-relyunwrap t-partial-env _] env)
  (zap [pkc-relycall pkc.strict-stringify _] varname)
  (!1:sl-table-get env (pkc:unwrap pkc.t-core-string varname)
    (thunk:pkc-call
      inner-fail (pkc-wrap t-env-failget-binding-failure nil))))


; depends on Penknife: t-hyperenv lexid->sl
; t-hyperenv-failget-env-failure

pk-core-rulebook.hyperenv-failget-env

(pk-core-rule hyperenv-failget-env (hyperenv inner-fail lexid)
                hyperenv-failget-env/hyperenv
  (aif (sl-table-get (pkc-relyunwrap t-hyperenv hyperenv)
                     (pkc-relycall pkc.lexid->sl lexid))
    it.1
    (pk-call
      inner-fail (pkc-wrap t-hyperenv-failget-env-failure nil))))


; depends on Penknife utilities: t-hyped-sym t-capture-lexid
; captured-hyperenv hyperenv-failget-env env-failget-binding

(mac pkc-if-env-get-binding (var env varname then else)
  (w/uniq (g-fail g-failure)
    `(pkc-failcall (pkc-failfn ,g-fail ()
                     (let ,var (pkc:env-failget-binding
                                 ,env ,g-fail ,varname)
                       ,then))
                   (pkc-fn ,g-failure ,else))))

(mac pkc-if-hyperenv-get-env (var hyperenv lexid then else)
  (w/uniq (g-fail g-failure)
    `(pkc-failcall (pkc-failfn ,g-fail ()
                     (let ,var (pkc:hyperenv-failget-env
                                 ,hyperenv ,g-fail ,lexid)
                       ,then))
                   (pkc-fn ,g-failure ,else))))

(pk-core-fun hyperenv-get (hyperenv hypervar)
  (pkc:binding-get:pkc-relycall
    pkc.hyperenv-get-binding hyperenv hypervar))

(pk-core-fun hyperenv-get-binding (hyperenv hypervar)
  (pkc-relycall pkc.hyperenv-failget-binding hyperenv fail hypervar))

(pk-core-fun hyperenv-failget-binding (hyperenv inner-fail hypervar)
  (pkc-letdecaps (varname lexid) (pkc-relyunwrap t-hyped-sym hypervar)
    (pkc:hyperenv-failget-binding-from
      hyperenv inner-fail varname lexid)))

(pk-core-fun hyperenv-failget-binding-from (hyperenv inner-fail
                                            varname lexid)
  (pkc-if-hyperenv-get-env env hyperenv lexid
    (pkc-if-env-get-binding binding env varname
      binding
      (pkc:lexid-failget-binding lexid inner-fail hyperenv varname))
    (pkc:lexid-failget-binding lexid inner-fail hyperenv varname)))

pk-core-rulebook.lexid-failget-binding

(pk-core-rule lexid-failget-binding (lexid inner-fail hyperenv
                                     varname)
                lexid-failget-binding/capture-lexid
  (pkc-letdecaps (capturevar parent) (pkc-relyunwrap
                                       t-capture-lexid lexid)
    (hyperenv-failget-binding-from
      (pkc:captured-hyperenv:pkc-hyperenv-get hyperenv capturevar)
      inner-fail varname parent)))


; depends on Penknife: default-expression hyperenv-get

pk-core-rulebook.rb-get-expression

(pk-core-fun get-expression (x hyperenv hypervar)
  (pkc-itifsuccess (pkc.rb-get-expression x hyperenv hypervar)
    it
    (pkc-relycall pkc.default-expression hyperenv hypervar)))

(pk-core-fun hyperenv-get-var-expression (hyperenv hypervar)
  (pkc:get-expression
    (pkc-relycall pkc.hyperenv-get hyperenv hypervar)
    hyperenv hypervar))
