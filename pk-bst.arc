; pk-bst.arc
; Penknife identification and compilation-to-Arc stuff.
;
; A "bst" is a "bound syntax tree." It's an abstract syntax tree with
; all the abstract references (like variable names) filled in with
; things that should actually be used for the computation (like
; variable bindings). We might call this a "concrete" syntax tree,
; except the text representation of syntax is concrete in its own
; equally legitimate sense.
;
;
; This depends on the following non-core Penknife utilities:
;
; defined in pk-env.arc: hyperenv-get-binding
;
; defined in pk-ast.arc:
;   t-ast-get-raise-failure
;   t-ast-var
;   t-ast-call
;
; defined in pk-util.arc:
;   t-ast-set-call
;   t-ast-binding
;   t-ast-literal
;
; TODO: Implement the following Penknife utilities:
;
;   prompt-b-rb-binding-get
;   prompt-b-rb-core-call
;   prompt-b-raise-failure
;   prompt-b-t-fn
;   prompt-b-t-rulebook
;   prompt-b-t-rulebook-failure
;   prompt-b-t-cons
;   prompt-b-t-nil
;   prompt-b-core-set-call
;   t-bst-binding-get-failure
;   t-bst-binding-get
;   t-bst-literal
;   t-bst-call
;   t-bst-set-call


; depends on Penknife: prompt-b-rb-binding-get prompt-b-rb-core-call
; prompt-b-raise-failure prompt-b-t-fn prompt-b-t-rulebook
; prompt-b-t-rulebook-failure prompt-b-t-cons prompt-b-t-nil

(mac pkc-identify-call-list* body
  `(pkc-list*
     (pkc-relycall pkc.prompt-b-rb-binding-get prompt-info)
     (pkc-relycall pkc.prompt-b-rb-core-call prompt-info)
     (pkc-relycall pkc.prompt-b-raise-failure prompt-info)
     (pkc-relycall pkc.prompt-b-t-fn prompt-info)
     (pkc-relycall pkc.prompt-b-t-rulebook prompt-info)
     (pkc-relycall pkc.prompt-b-t-rulebook-failure prompt-info)
     (pkc-relycall pkc.prompt-b-t-stray-failure-error prompt-info)
     (pkc-relycall pkc.prompt-b-t-cons prompt-info)
     (pkc-relycall pkc.prompt-b-t-nil prompt-info)
     ,@body))

(mac pkc-map-list (op list)
  `(ut:xloop rest ,list
     (pkc:fn-ifdecap rest
       (pkc-fn (first rest)
         (pkc-list* (,op first) do.next.rest)))
     (pkc-thunk:pkc-list)))


; depends on Penknife: t-bst-literal hyperenv-get-binding
; t-ast-binding t-ast-literal t-ast-set-call t-bst-set-call
; prompt-b-core-set-call t-ast-call t-bst-call t-ast-var
; t-bst-binding-get t-ast-get-raise-failure t-bst-binding-get-failure
; prompt-b-raise-failure

pk-core-rulebook.identify

(pk-core-rule identify (ast prompt-info static-hyperenv)
                identify/ast-get-raise-failure
  (pkc-relyunwrap t-ast-get-raise-failure ast)
  (pkc-wrap t-bst-binding-get-failure
    (pkc-relycall pkc.prompt-b-raise-failure prompt-info)))

(mac pkc-identify (ast)
  `(pkc:identify ,ast prompt-info static-hyperenv))

(mac pkc-identify-list (list)
  `(pkc-map-list pkc-identify ,list))

(pk-core-rule identify (ast prompt-info static-hyperenv)
                identify/ast-var
  (pkc-letdecaps (onfail var) (pkc-relyunwrap t-ast-var ast)
    (pkc-wrap t-bst-binding-get
      (pkc-identify-call-list*:pkc-list pkc-identify.onfail
        (pkc:hyperenv-get-binding static-hyperenv var)))))

(pk-core-rule identify (ast prompt-info static-hyperenv)
                identify/ast-call
  (pkc-letdecaps (func onfail . args) (pkc-relyunwrap t-ast-call ast)
    (pkc-wrap t-bst-call
      (pkc-identify-call-list*:pkc-list pkc-identify.func
        pkc-identify.onfail pkc-identify-list.args))))

(pk-core-rule identify (ast prompt-info static-hyperenv)
                identify/ast-set-call
  (pkc-letdecaps (func fail args newcomer) (pkc-relyunwrap
                                             t-ast-set-call ast)
    (pkc-wrap t-bst-set-call
      (pkc-identify-call-list*:pkc-list
        (pkc-relycall pkc.prompt-b-core-set-call prompt-info)
        pkc-identify.func pkc-identify.fail pkc-identify-list.args
        pkc-identify.newcomer))))

(pk-core-rule identify (ast prompt-info static-hyperenv)
                identify/ast-literal
  (pkc-wrap t-bst-literal (pkc-relyunwrap t-ast-literal ast)))

(pk-core-rule identify (ast prompt-info static-hyperenv)
                identify/ast-binding
  (pkc-wrap t-bst-literal
    (pkc:hyperenv-get-binding static-hyperenv
      (pkc-relyunwrap t-ast-binding ast))))


; depends on Penknife: t-bst-literal t-bst-set-call t-bst-binding-get
; t-bst-binding-get-failure

(def embed (val)
  `(,thunk.val))

pk-core-rulebook.arcify-bst

(pk-core-rule arcify-bst (bst) arcify-bst/bst-binding-get-failure
  `(pk-binding-get-failure
     ,(embed:pkc-relyunwrap t-bst-binding-get-failure bst)))

(pk-core-rule arcify-bst (bst) arcify-bst/bst-binding-get
  (pkc-letdecaps (b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
                  fail binding)
                 (pkc-relyunwrap t-bst-binding-get bst)
    `(pk-binding-get ,embed.b-rbg ,embed.b-rcc ,embed.b-rf ,embed.b-tf
       ,embed.b-tr ,embed.b-trf ,embed.b-tsfe ,embed.b-tc ,embed.b-tn
       ,(pkc:arcify-bst fail) ,embed.binding)))

(mac pkc-arcify-bst-list (list)
  `(pkc-map-list pkc:arcify-bst ,list))

(pk-core-rule arcify-bst (bst) arcify-bst/bst-call
  (pkc-letdecaps (b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
                  func fail args)
                 (pkc-relyunwrap t-bst-call bst)
    `(pk-core-call ,embed.b-rbg ,embed.b-rcc ,embed.b-rf ,embed.b-tf
       ,embed.b-tr ,embed.b-trf ,embed.b-tsfe ,embed.b-tc ,embed.b-tn
       ,(pkc:arcify-bst func) ,(pkc:arcify-bst fail)
       ,pkc-arcify-bst-list.args)))

; TODO: Put this abbreviation with the others (which are in
; pk-core.arc).
;
; b-csc    = binding for core-set-call
;
(pk-core-rule arcify-bst (bst) arcify-bst/bst-set-call
  (pkc-letdecaps (b-rbg b-rcc b-rf b-tf b-tr b-trf b-tsfe b-tc b-tn
                  b-csc func fail args newcomer)
                 (pkc-relyunwrap t-bst-set-call bst)
    (w/uniq (gb-rbg gb-rcc gb-rf gb-tf gb-tr gb-trf gb-tsfe gb-tc
             gb-tn)
      (with (rf `(pk-binding-get-failure ,gb-rf)
             common-gbs `(,gb-rbg ,gb-rcc ,gb-rf ,gb-tf ,gb-tr ,gb-trf
                          ,gb-tsfe ,gb-tc ,gb-tn))
        `(with (,gb-rbg ,embed.b-rgb ,gb-rcc ,embed.b-rcc
                ,gb-rf ,embed.b-rf ,gb-tr ,embed.b-tr
                ,gb-trf ,embed.b-trf ,gb-tsfe ,embed.b-tsfe
                ,gb-tc ,embed.b-tc ,gb-tn ,embed.b-tn)
           (pk-core-call ,@common-gbs
             (pk-binding-get ,@common-gbs ,rf ,embed.b-csc) ,rf
             (pk-list ,@common-gbs ,(pkc:arcify-bst func)
               ,(pkc:arcify-bst fail) ,pkc-arcify-bst-list.args
               ,(pkc:arcify-bst newcomer))))))))

(pk-core-rule arcify-bst (bst) arcify-bst/bst-literal
  (embed:pkc-relyunwrap t-bst-literal bst))
